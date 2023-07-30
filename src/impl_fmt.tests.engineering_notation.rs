

macro_rules! impl_case {
    ($name:ident : $in:literal => $ex:literal) => {
        #[test]
        fn $name() {
            let n: BigDecimal = $in.parse().unwrap();
            let s = n.to_engineering_notation();
            assert_eq!(&s, $ex);
        }
    };
}

impl_case!(case_4_1592480782835e9 : "4159248078.2835" => "4.1592480782835e9");
impl_case!(case_12_34e_6 : "0.00001234" => "12.34e-6");
impl_case!(case_0 : "0" => "0e0");
impl_case!(case_1 : "1" => "1e0");
impl_case!(case_2_00e0 : "2.00" => "2.00e0");
impl_case!(case_neg_5_70e1 : "-57.0" => "-57.0e0");
impl_case!(case_5_31e5 : "5.31e5" => "531e3");
