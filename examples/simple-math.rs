extern crate bigdecimal;
use bigdecimal::*;
use std::str::FromStr;

fn main() {
    println!("Hello, Big Decimals!");
    let input = "0.8";
    let dec = BigDecimal::from_str(&input).unwrap();
    let float = f32::from_str(&input).unwrap();
    println!("Input ({}) with 10 decimals: {} vs {})", input, dec, float);

    let bd_square = dec.square();
    println!("square {}", bd_square);

    let bd_from_prim = BigDecimal::from_f64(3.3);
    println!("From Prim: {}", bd_from_prim.unwrap());

    let bd_match: BigDecimal = match BigDecimal::from_f64(33.9) {
        Some(bd) => bd,
        None => BigDecimal::zero(),
    };
    println!("match test {}", bd_match);

    let bd_add1 = BigDecimal::from_f64(24.0).unwrap();
    let bd_add2 = BigDecimal::from_f64(34.0).unwrap();
    println!("sum: {}", &bd_add1 + &bd_add2);
    println!("components: {}, {}", bd_add1, bd_add2);

    let mut bd_add3 = BigDecimal::from_f64(24.0).unwrap();
    let bd_add4 = BigDecimal::from_f64(24.0).unwrap();
    bd_add3 += bd_add4;
    println!("sum mut: {}", bd_add3);

    let bd_nez = BigDecimal::from_f64(0.0).unwrap();
    if bd_nez != BigDecimal::zero() {
        println!("{} is not equal to zero", &bd_nez);
    } else {
        println!("{} IS equal to zero", &bd_nez);
    }

    let bd_div1 = BigDecimal::from_f64(24.0).unwrap();
    let bd_div2 = BigDecimal::from_f64(1.0).unwrap();
    if bd_div2.ne(&BigDecimal::zero()) {
        let bd_div3: BigDecimal = bd_div1 / bd_div2;
        println!("divide: {}", bd_div3);
    } else {
        println!("cannot divide by zero");
    }
}
