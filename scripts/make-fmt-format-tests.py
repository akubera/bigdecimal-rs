#!/usr/bin/env python
#
# Generate Rust code given Decimals and formatting strings
#

import textwrap
from decimal import *


FORMATS = [
    "{}",
    "{:+05.1}",
    "{:.1}",
    "{:.4}",
    "{:4.1}",
    "{:>4.3}",
    "{:>4.4}",
    "{:<4.1}",
]

# FORMATS = [
#     "{:.4}",
#     "{:.8}",
# ]

FORMATS = [
    "{}",
    "{:+05.7}",
    "{:.3}",
    "{:0.4}",
    "{:4.1}",
    "{:>8.3}",
    "{:>8.4}",
    "{:<8.1}",
]


# Decimal strings to the testing formats
INPUTS = {
    "1": [
        "{}",
        "{:.1}",
        "{:.4}",
        "{:4.1}",
        "{:>4.1}",
        "{:<4.1}",
        "{:+05.1}",
    ],
    "123456": [
        "{}",
        "{:+05.1}",
        "{:.1}",
        "{:.4}",
        "{:4.1}",
        "{:>4.3}",
        "{:>4.4}",
        "{:<4.1}",
    ],
    "9999999": [
        "{:.4}",
        "{:.8}",
    ],
    "19073.97235939614856": [
        "{}",
        "{:+05.7}",
        "{:.3}",
        "{:0.4}",
        "{:4.1}",
        "{:>8.3}",
        "{:>8.4}",
        "{:<8.1}",
    ],
    "491326e-12": [
        "{}",
        "{:+015.7}",
        "{:.3}",
        "{:0.4}",
        "{:4.1}",
        "{:>8.3}",
        "{:>8.4}",
        "{:<8.1}",
    ],
}


def main():
    for dec_str, formats in INPUTS.items():
        dec = Decimal(dec_str)
        mod_name = "dec_%s" % gen_name_from_dec(dec_str)

        formats_and_outputs = [
            (fmt, gen_name_from_fmt(fmt), fmt.format(dec)) for fmt in formats
        ]

        max_name_len = max(len(name) + 7 for _, name, _ in formats_and_outputs)

        max_len_fmt = max(len(fmt) + 5 for fmt, _, _ in formats_and_outputs)

        max_len_name_and_fmt = max(
            len(fmt) + len(name) for fmt, name, _ in formats_and_outputs
        )

        lines = []
        for fmt, name, value in formats_and_outputs:
            spacer = " " * (max_len_name_and_fmt - (len(fmt) + len(name)) + 2)
            # fmt = f'"{fmt}" =>'.rjust(max_len_fmt)
            # fmt = fmt.rjust(max_len_fmt)
            lines.append(f'impl_case!(fmt_{name}:{spacer}"{fmt}" => "{value}");')
            # print('impl_case!(fmt_%s: "%s" => "%s");' % (name, fmt, ))

        body = textwrap.indent("\n".join(lines), "    ")
        text = textwrap.dedent(
            f"""
            mod {mod_name} {{
                use super::*;

                fn test_input() -> BigDecimal {{
                    "{dec_str}".parse().unwrap()
                }}

            %s
            }}"""
        )

        print(text % body)
        continue

        print(
            "\n".join(
                [
                    f"mod {mod_name} {{",
                    "use super::*;",
                    f'fn test_input() -> BigDecimal {{ "{dec_str}".parse().unwrap() }}',
                    body,
                    "}",
                ]
            )
        )


# x = Decimal("1")
x = 123456.0


def gen_name_from_dec(s: str) -> str:
    return "".join(map_fmt_char_to_name_char(c) for c in s)


def gen_name_from_fmt(fmt: str) -> str:
    if fmt == "{}":
        return "default"
    else:
        return "".join(map_fmt_char_to_name_char(c) for c in fmt[2:-1])


def map_fmt_char_to_name_char(c: str) -> str:
    match c:
        case ".":
            return "d"
        case "+":
            return "p"
        case "-":
            return "n"
        case "<":
            return "l"
        case ">":
            return "r"
        case ":":
            return "c"
        case _:
            return str(c)


if __name__ == "__main__":
    main()
