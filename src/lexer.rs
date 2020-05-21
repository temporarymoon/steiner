use nom::branch::alt;
use nom::bytes::complete::{escaped, is_a, tag, take_till1};
use nom::character::complete::{alphanumeric1, multispace0, one_of, space1};
use nom::combinator::{all_consuming, map, map_opt, value};
use nom::multi::many0;
use nom::number::complete::double;
use nom::sequence::{delimited, terminated};
use nom::IResult;

// This is a simple macro for making parsers which replace a tag with a custom value
macro_rules! tagged {
    ($tag:expr,$value:expr) => {
        value($value, tag($tag))
    };
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PunctuationKind {
    OpenParenthesis,
    CloseParenthesis,
    Backslash,
    DoubleColon,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum KeywordKind {
    If,
    Then,
    Else,
    Let,
    In,
}

macro_rules! keyword {
    ($tag: expr, $keyword: expr) => {
        value($keyword, terminated(tag($tag), space1))
    };
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Token<'a> {
    FloatLit(f64),
    StringLit(&'a [u8]),
    Punctuation(PunctuationKind),
    Keyword(KeywordKind),
    Operator(&'a [u8]),
    Identifier(&'a [u8]),
}

const OPERATOR_CHARS: &[u8] = b"<=>+-/*!$%^&|";
const KEYWORDS: [&[u8]; 5] = [b"if", b"then", b"else", b"let", b"in"];

pub fn lex(input: &[u8]) -> IResult<&[u8], Vec<Token>> {
    let parse_float_literal = map(double, Token::FloatLit);
    let parse_punctuation = map(
        alt((
            tagged!(b"(", PunctuationKind::OpenParenthesis),
            tagged!(b")", PunctuationKind::CloseParenthesis),
            tagged!(b"\\", PunctuationKind::Backslash),
            tagged!(b"::", PunctuationKind::DoubleColon),
        )),
        Token::Punctuation,
    );

    let parse_double_quote = tag("\"");

    let parse_string = map(
        delimited(
            &parse_double_quote,
            escaped(take_till1(|v| v == b'"'), '\\', one_of("\"n\\")),
            &parse_double_quote,
        ),
        Token::StringLit,
    );

    let parse_keyword = map(
        alt((
            keyword!(KEYWORDS[0], KeywordKind::If),
            keyword!(KEYWORDS[1], KeywordKind::Then),
            keyword!(KEYWORDS[2], KeywordKind::Else),
            keyword!(KEYWORDS[3], KeywordKind::Let),
            keyword!(KEYWORDS[4], KeywordKind::In),
        )),
        Token::Keyword,
    );

    let parse_operator = map(is_a(OPERATOR_CHARS), Token::Operator);
    let parse_identifier = map_opt(alphanumeric1, |id| {
        if KEYWORDS.contains(&id) {
            None
        } else {
            Some(Token::Identifier(id))
        }
    });

    let parse = all_consuming(many0(terminated(
        alt((
            parse_float_literal,
            parse_string,
            parse_punctuation,
            parse_keyword,
            parse_operator,
            parse_identifier,
        )),
        multispace0,
    )));

    parse(input)
}
