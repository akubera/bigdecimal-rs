use bigdigit::radix::RADIX_10p9_u32;
use bigdigit::radix::RADIX_10p19_u64;


#[test]
fn split_987654321_low_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_low(3).split(987654321);
    assert_eq!(hi, 987654000);
    assert_eq!(lo, 000000321)
}

#[test]
fn split_987654321_high_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_high(3).split(987654321);
    assert_eq!(hi, 987000000);
    assert_eq!(lo, 000654321)
}

#[test]
fn split_and_shift_987654321_high_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_high(3).split_and_shift(987654321);
    assert_eq!(hi, 000000987);
    assert_eq!(lo, 654321000)
}

#[test]
fn split_and_shift_987654321_low_3() {
    let (hi, lo) = BigDigitSplitter::<RADIX_10p9_u32>::mask_low(3).split_and_shift(987654321);
    assert_eq!(hi, 000987654);
    assert_eq!(lo, 321000000)
}


fn splitter_iter_pi() {
    let digits = &[
        3141592653589793238,4626433832795028841,9716939937510582097,4944592307816406286,2089986280348253421
    ];

    let iter = BigDigitSplitterIter::<RADIX_10p19_u64>::from_slice_starting_top(digits, 1);
    let result: Vec<u64> = iter.collect();
    assert_eq!(
        3, 1415926535897932384, 6264338327950288419, 71693993751058209, 7494459230781640628, 6208998628034825342, 1000000000000000000
}
