pub fn is_syntax_character(c: u32) -> bool {
    char::from_u32(c).map_or(false, |c| {
        matches!(
            c,
            '^' | '$' | '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{' | '}' | '|'
        )
    })
}