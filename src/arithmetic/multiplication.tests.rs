use num_bigint::{BigUint, BigInt};

mod multiply_big_int_with_ctx {
    use super::*;

    // test (2^5000-1) * (2^1500-1)
    mod mul_2p5000m1_2p1501m1 {
        use super::*;

        fn test_input() -> (BigInt, BigInt) {
            let x: BigInt = "141246703213942603683520966701614733366889617518454111681368808585711816984270751255808912631671152637335603208431366082764203838069979338335971185726639923431051777851865399011877999645131707069373498212631323752553111215372844035950900535954860733418453405575566736801565587405464699640499050849699472357900905617571376618228216434213181520991556677126498651782204174061830939239176861341383294018240225838692725596147005144243281075275629495339093813198966735633606329691023842454125835888656873133981287240980008838073668221804264432910894030789020219440578198488267339768238872279902157420307247570510423845868872596735891805818727796435753018518086641356012851302546726823009250218328018251907340245449863183265637987862198511046362985461949587281119139907228004385942880953958816554567625296086916885774828934449941362416588675326940332561103664556982622206834474219811081872404929503481991376740379825998791411879802717583885498575115299471743469241117070230398103378615232793710290992656444842895511830355733152020804157920090041811951880456705515468349446182731742327685989277607620709525878318766488368348965015474997864119765441433356928012344111765735336393557879214937004347568208665958717764059293592887514292843557047089164876483116615691886203812997555690171892169733755224469032475078797830901321579940127337210694377283439922280274060798234786740434893458120198341101033812506720046609891160700284002100980452964039788704335302619337597862052192280371481132164147186514169090917191909375".parse().unwrap();
            let y: BigInt = "35074662110434038747627587960280857993524015880330828824075798024790963850563322203657080886584969261653150406795437517399294548941469959754171038918004700847889956485329097264486802711583462946536682184340138629451355458264946342525383619389314960644665052551751442335509249173361130355796109709885580674313954210217657847432626760733004753275317192133674703563372783297041993227052663333668509952000175053355529058880434182538386715523683713208549375".parse().unwrap();
            (x, y)
        }

        #[test]
        fn case_prec20() {
            let (x, y) = test_input();
            let ctx = Context::default().with_prec(20).unwrap();
            let product = multiply_big_int_with_ctx(&x, &y, ctx);

            let expected: BigInt = "49541803894417944073".parse().unwrap();
            let exp = 1937;

            assert_eq!(&expected, &product.value);
            assert_eq!(&exp, &product.scale);
        }

        #[test]
        fn case_prec100() {
            let (x, y) = test_input();
            let ctx = Context::default().with_prec(100).unwrap();
            let product = multiply_big_int_with_ctx(&x, &y, ctx);

            let expected: BigInt = "4954180389441794407302644533158844937036173071799942385207702899881096950794929284226174201155309760".parse().unwrap();
            let exp = 1857;

            assert_eq!(&expected, &product.value);
            assert_eq!(&exp, &product.scale);
        }
    }

    mod multiply_big_int_with_ctx {
        use super::*;

        fn test_input() -> (BigInt, BigInt) {
            let x: BigInt = "31331330514777647459696918012218766637269396231379435058341584170846149718531941093035596483272466942484919002494751588025494203950111183556196762802239021663296916615390846043521157975900649".parse().unwrap();
            let y: BigInt = "1409125393389843319552855599302577071349036214812589000980540875883362915766473073232671889".parse().unwrap();
            (x, y)
        }

        #[test]
        fn case_full_precision() {
            let (x, y) = test_input();
            let p = x * y;
            let expected: BigInt = "44149773437063254678149469396251230458443452710019771114377331920312228495036605502543146558201981056772851870606187717471634519393139631393769297684773531284154562671396651882745113413784696354015721073630190690162770887707923095632780007819514677121000367593109419444597479155961".parse().unwrap();
            assert_eq!(expected, p);
        }

        #[test]
        fn case_prec100() {
            let (x, y) = test_input();
            let expected: BigInt = "4414977343706325467814946939625123045844345271001977111437733192031222849503660550254314655820198106".parse().unwrap();
            let exp = 181;

            // let x = [
            //     14731519223619563738,
            //     2405657302403958407,
            //     10725034070426109052,
            //     12618659131331217150,
            //     17515250887032402398,
            //     2066,
            // ];

            let ctx = Context::default().with_prec(100).unwrap();
            let product = multiply_big_int_with_ctx(&x, &y, ctx);

            assert_eq!(&expected, &product.value);
            assert_eq!(&exp, &product.scale);
        }

        #[test]
        fn case_prec50() {
            let (x, y) = test_input();
            let expected: BigInt =
                "44149773437063254678149469396251230458443452710020".parse().unwrap();
            let exp = 231;

            let ctx = Context::default().with_prec(50).unwrap();
            let product = multiply_big_int_with_ctx(&x, &y, ctx);

            assert_eq!(&expected, &product.value);
            assert_eq!(&exp, &product.scale);

            // let zz = [
            //     0,
            //     0,
            //     0,
            //     385227092930854912,
            //     7532158039382434494,
            //     9844605054510536212,
            //     16088462575472628634,
            //     1434294631195542896,
            //     17151985756858815671,
            //     17565837050785020630,
            //     15636533030619248522,
            //     17260383999288194180,
            //     1022303687606097677,
            //     10639567590217968514,
            //     83570377573
            // ];
            // dbg!(zz);
        }
        #[test]
        fn case_prec21() {
            let (x, y) = test_input();
            let expected: BigInt = "441497734370632546781".parse().unwrap();
            let exp = 260;

            let ctx = Context::default().with_prec(21).unwrap();
            let product = multiply_big_int_with_ctx(&x, &y, ctx);

            // let ee = [17222620675312859613, 23];

            assert_eq!(&expected, &product.value);
            assert_eq!(&exp, &product.scale);
        }
    }
}

// #[test]
// fn multiply_stuff() {
//     let x: BigInt = "31331330514777647459696918012218766637269396231379435058341584170846149718531941093035596483272466942484919002494751588025494203950111183556196762802239021663296916615390846043521157975900649".parse().unwrap();
//     let y: BigInt = "1409125393389843319552855599302577071349036214812589000980540875883362915766473073232671889".parse().unwrap();
//     // let xv: Vec<u64> = x.iter_u64_digits().collect();
//     // let yv: Vec<u64> = y.iter_u64_digits().collect();
//     let expected: BigInt = "4414977343706325467814946939625123045844345271001977111437733192031222849503660550254314655820198106".parse().unwrap();

//     let ctx = Context::default().with_prec(50).unwrap();
//     let product = multiply_big_int_with_ctx(x, y, ctx);

//     assert_eq!(&expected, &product.value);

//     // let mut p = BigDigitVec::new();
//     // multiply_with_prec_into(
//     //     &mut p,
//     //     BigDigitSlice::from_slice(&xv),
//     //     BigDigitSlice::from_slice(&yv),
//     //     // 230
//     //     100
//     // );
//     // assert_eq!(&expected, &value);
//     // dbg!();
//     // // 4414977343706325467814946939625123045844345271001977111437733192031222849503660550254314655820198106
//     // let expected = [
//     //     // 14162501339517004025,
//     //     // 17904384892821476550,
//     //     // 15126569004981673977,
//     //     // 10405836664442004247,
//     //     //  2675685814645510795,
//     //     // 12436132728874226750,
//     //     // 15914516659996520248,
//     //     // 16906384975365281894,
//     //     //  4815920382763188498,
//     //     //  8969876167025813160,
//     //     16769938138519858112,
//     //     14540805706160053231,
//     //      1022303687606097677,
//     //     10639567590217968514,
//     //              83570377573,
//     // ];

//     // // let fromj
//     // assert_eq!(&p.digits, &expected);
// }

/// multiply_quad_spread_into
///
pub(crate) fn multiply_quad_spread_into_wrapping(
    dest: &mut [u32],
    idx: usize,
    a: u32,
    b: u32,
    y: u32,
    z: u32,
) {
    let ay = a as u64 * y as u64;
    let az = a as u64 * z as u64;

    let by = b as u64 * y as u64;
    let bz = b as u64 * z as u64;

    let (ayh, ayl) = split_u64(ay);
    let (azh, azl) = split_u64(az);
    let (byh, byl) = split_u64(by);
    let (bzh, bzl) = split_u64(bz);

    let wrap = dest.len();
    let mut idx = idx % wrap;

    let (carry, r0) = split_u64(dest[idx] as u64 + ayl * 2);
    dest[idx] = r0 as u32;

    idx = (idx + 1) % wrap;
    let (carry, r1) = split_u64(dest[idx] as u64 + carry + (ayh + azl + byl) * 2);
    dest[idx] = r1 as u32;

    idx = (idx + 1) % wrap;
    let (carry, r2) = split_u64(dest[idx] as u64 + carry + (azh + byh + bzl) * 2);
    dest[idx] = r2 as u32;

    idx = (idx + 1) % wrap;
    let (mut carry, r3) = split_u64(dest[idx] as u64 + carry + bzh * 2);
    dest[idx] = r3 as u32;

    while carry != 0 {
        idx = (idx + 1) % wrap;
        let (c, overflow) = split_u64(dest[idx] as u64 + carry);
        dest[idx] = overflow as u32;
        carry = c as u64;
    }
}

#[cfg(test)]
mod test_multiply_quad_spread_into {
    use super::*;

    #[test]
    fn case_25597123371_684026673_1163340730_1823138616() {
        let a = 2559712337;
        let b = 684026673;
        let y = 1163340730;
        let z = 1823138616;

        let mut result = vec![0; 8];

        multiply_quad_spread_into(&mut result, 2, a, b, y, z);
        assert_eq!(&result, &[0, 0, 3001179060, 4203670869, 1059648540, 580714756, 0, 0]);
    }

    #[test]
    fn case_25597123371_684026673_1163340730_1823138616_wrapping() {
        let a = 2559712337;
        let b = 684026673;
        let y = 1163340730;
        let z = 1823138616;

        let mut result = vec![0; 8];

        multiply_quad_spread_into_wrapping(&mut result, 6, a, b, y, z);
        assert_eq!(&result, &[1059648540, 580714756, 0, 0, 0, 0, 3001179060, 4203670869]);
    }

    #[test]
    fn case_4294967296() {
        let a = 4294967295;
        let b = 4294967295;
        let y = 4294967295;
        let z = 4294967295;

        let mut result = vec![0; 6];

        multiply_quad_spread_into(&mut result, 1, a, b, y, z);
        assert_eq!(&result, &[0, 2, 0, 4294967292, 4294967295, 1]);
    }
}
