//! pow implementation

use std::convert::TryInto;

use crate::*;

/// Compute bd**exp using exponentiation by squaring algorithm, while maintaining the
/// precision specified in ctx (the number of digits would otherwise explode).
///
/// Algorithm comes from https://en.wikipedia.org/wiki/Exponentiation_by_squaring
pub(crate) fn impl_pow_with_context(bd: &BigDecimal, exp: i64, ctx: &Context) -> BigDecimal {
    if exp == 0 {
        return 1.into();
    }

    // When performing a multiplication between 2 numbers, we may lose up to 2 digits
    // of precision.
    // "Proof": https://github.com/akubera/bigdecimal-rs/issues/147#issuecomment-2793431202
    const MARGIN_PER_MUL: u64 = 2;

    fn trim_precision(bd: BigDecimal, ctx: &Context, margin: u64) -> BigDecimal {
        let prec = ctx.precision().get() + margin;
        if bd.digits() > prec {
            bd.with_precision_round(prec.try_into().unwrap(), ctx.rounding_mode())
        } else {
            bd
        }
    }


    // Count the number of multiplications we're going to perform, one per "1" binary digit
    // in exp, and the number of times we can divide exp by 2.
    let mut n = exp.abs() as u64;
    let mut margin = MARGIN_PER_MUL * (n.count_ones() + n.ilog2() - 1) as u64;

    let mut bd_y: BigDecimal = 1.into();
    let mut bd_x = if exp >= 0 {
        bd.clone()
    } else {
        bd.inverse_with_context(&ctx.with_precision((ctx.precision().get() + margin + MARGIN_PER_MUL).try_into().unwrap()))
    };

    while n > 1 {
        if n % 2 == 1 {
            bd_y = trim_precision(&bd_x * bd_y, ctx, margin);
            margin -= MARGIN_PER_MUL;
            n -= 1;
        }
        bd_x = trim_precision(bd_x.square(), ctx, margin);
        margin -= MARGIN_PER_MUL;
        n /= 2;
    }
    debug_assert_eq!(margin, 0);

    return trim_precision(bd_x * bd_y, ctx, 0);
}

#[cfg(test)]
mod test {
    use super::*;
    use stdlib::num::NonZeroU64;

    // Test that the 2 numbers are the same, assuming precision in ctx.
    fn compare(bd: BigDecimal, bd_expected: BigDecimal, ctx: &Context) {
        let bd_expected_round = bd_expected.with_precision_round(ctx.precision(), ctx.rounding_mode());
        println!("100d  0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789");
        println!("exp   {bd_expected}");
        println!("val   {bd}");
        println!("exprd {bd_expected_round}");

        assert_eq!(bd, bd_expected_round);
    }

    macro_rules! impl_case {
        ($name:ident: $start:expr, $exp:literal => $expected:literal) => {
            #[test]
            fn $name() {
                let start = BigDecimal::from($start);
                let exp = $exp;
                let expected = $expected;
                let ctx = Context::default();

                println!("Compute {start}**{exp}");

                let bd = start.pow_with_context(exp, &ctx);
                let bd_expected = BigDecimal::from_str(expected).unwrap();

                compare(bd, bd_expected, &ctx);
            }
        };
    }

    mod pow_known {
        use super::*;

        // Wolfram Alpha can get us to these precise values with a bit of log trickery, e.g.:
        // 2**3000000000 = 10**log_10(2**3000000000) = 10**(3000000000 * log_10(2))
        impl_case!(case_2_3000: 2, 3000 => "1.230231922161117176931558813276752514640713895736833715766118029160058800614672948775360067838593459582429649254051804908512884180898236823e903");
        impl_case!(case_2_2048: 2, 2048 => "3.231700607131100730071487668866995196044410266971548403213034542752465513886789089319720141152291346368871796092189801949411955915049092109e616");
        impl_case!(case_2_2001: 2, 2001 => "2.296261390548509048465666402355363968044635404177390400955285473651532522784740627713318972633012539836891929277974925546894237921726110662e602");
        impl_case!(case_2_3000000000: 2, 3000000000 => "9.8162042336235053508313854078782835648991393286913072670026492205522618203568834202759669215027003865712110468405800021098042607617495e903089986");
        // This works as 2 can be exactly inverted with only 1 digit (0.5).
        impl_case!(case_0_5_30000000: BigDecimal::from(2).inverse(), 30000000 => "1.34921314623699835510360889355448887159595110457423959780496317685705095413905406464421931122265203166201415504288117880522818881981650e-9030900");
        impl_case!(case_0_5_minus3000000000: BigDecimal::from(2).inverse(), -3000000000 => "9.8162042336235053508313854078782835648991393286913072670026492205522618203568834202759669215027003865712110468405800021098042607617495e903089986");
        impl_case!(case_2_minus30000000: 2, -30000000 => "1.34921314623699835510360889355448887159595110457423959780496317685705095413905406464421931122265203166201415504288117880522818881981650e-9030900");
        // This tests that the inverse operation carries enough digits to keep the precision.
        impl_case!(case_3_minus30000000: 3, -30000000 => "2.2824965348198962029744520058679746159742143842721452620663907608967745444344346503448190515521985159162206416095535917875712100566195e-14313638");
    }

    macro_rules! impl_case {
        ($name:ident: $start:expr, $exp:expr) => {
            #[test]
            fn $name() {
                let start = BigDecimal::from_str($start).unwrap();
                let exp = $exp.into();
                let ctx = Context::new(50.try_into().unwrap(), RoundingMode::HalfEven);
                let ctx_large = Context::new(500.try_into().unwrap(), RoundingMode::HalfEven);

                println!("Compute {start}**{exp}");

                let bd = start.pow_with_context(exp, &ctx);
                let bd_expected = start.pow_with_context(exp, &ctx_large);

                compare(bd, bd_expected, &ctx);
            }
        };
    }

    mod pow_misc {
        use super::*;

        // Test a few more misc values, checking that contexts with 50 or 500 precision
        // get the same number, after scaling down the 500 precision result to 50.

        impl_case!(case_misc_1: "-1.87421916986125215986", 3000912415i64);
        impl_case!(case_misc_2: "230231922161117176931558813276752514640713895736833715766118029160058800614672948775360067838593459582429649254051804908512884180898236823e903", 1000151);
        impl_case!(case_misc_3: "9.4215159218712961e-123", u32::MAX);
        impl_case!(case_misc_4: "213", 3);
        impl_case!(case_misc_5: "230231922161117176931558813276752514640713895736833715766118029160058800614672948775360067838593459582429649254051804908512884180898236823e903", -1000151);
        impl_case!(case_misc_6: "9.4215159218712961e-123", i32::MIN);
    }
}
