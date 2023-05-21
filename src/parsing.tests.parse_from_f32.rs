

#[test]
fn case_45En1() {
    let n = 4.5f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "4.5".parse().unwrap());
}


#[test]
fn case_15625En5() {
    let n = 0.15625f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "0.15625".parse().unwrap());
}


#[test]
fn case_n15625En5() {
    let n = -0.15625f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "-0.15625".parse().unwrap());
}


#[test]
fn case_n1192092896En7() {
    let n = -1.192092896e-07_f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "-1.1920928955078125E-7".parse().unwrap());
}

#[test]
fn case_1401757440() {
    let n = 1401757440_f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "1401757440".parse().unwrap());
}

#[test]
fn case_215092En1() {
    let n = 21509.2f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "21509.19921875".parse().unwrap());
}

#[test]
fn case_2289620000() {
    let n = 2289620000.0f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "2289619968".parse().unwrap());
}

#[test]
fn case_10000000() {
    let n = 10000000f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "10000000".parse().unwrap());
}

#[test]
fn case_1en05() {
    let n = 1e-05f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "0.00000999999974737875163555145263671875".parse().unwrap());
}

#[test]
fn case_80000197() {
    let n = 80000197f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "80000200".parse().unwrap());
}

#[test]
fn case_23283064En16() {
    let n = 2.3283064e-10f32;
    let d = parse_from_f32(n);
    assert_eq!(d, "0.00000000023283064365386962890625".parse().unwrap());
}

#[test]
fn case_14693861798803098En17() {
    let n = 0.14693861798803098;
    let d = parse_from_f32(n);
    assert_eq!(d, "0.146938621997833251953125".parse().unwrap());
}

#[test]
fn case_nan() {
    let n = f32::NAN;
    let d = parse_from_f32(n);
    assert_eq!(d, "510423550381407695195061911147652317184".parse().unwrap());
}


#[test]
fn case_try_from_nan() {
    let n = f32::NAN;
    let d = try_parse_from_f32(n);
    assert!(d.is_err());
}
