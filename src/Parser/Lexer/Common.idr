module Parser.Lexer.Common

import public Libraries.Text.Lexer

%default total

||| In `comment` we are careful not to parse closing delimiters as
||| valid comments. i.e. you may not write many dashes followed by
||| a closing brace and call it a valid comment.
export
comment : Lexer
comment
   =  is '-' <+> is '-'                  -- comment opener
  <+> many (is '-') <+> reject (is '}')  -- not a closing delimiter
  <+> many (isNot '\n')                  -- till the end of line

mutual
  ||| The mutually defined functions represent different states in a
  ||| small automaton.
  ||| `toEndComment` is the default state and it will munch through
  ||| the input until we detect a special character (a dash, an
  ||| opening brace, or a double quote) and then switch to the
  ||| appropriate state.
  toEndComment : (k : Nat) -> Recognise (k /= 0)
  toEndComment Z = empty
  toEndComment (S k)
               = some (pred (\c => c /= '-' && c /= '{' && c /= '"' && c /= '\''))
                        <+> (eof <|> toEndComment (S k))
             <|> is '{' <+> singleBrace k
             <|> is '-' <+> singleDash k
             <|> (charLit <|> pred (== '\'')) <+> toEndComment (S k)
             <|> stringLit <+> toEndComment (S k)

  ||| After reading a single brace, we may either finish reading an
  ||| opening delimiter or ignore it (e.g. it could be an implicit
  ||| binder).
  singleBrace : (k : Nat) -> Lexer
  singleBrace k
     =  is '-' <+> many (is '-')              -- opening delimiter
               <+> (eof <|> singleDash (S k)) -- `singleDash` handles the {----} special case
                                              -- `eof` handles the file ending with {---
    <|> toEndComment (S k)                    -- not a valid comment

  ||| After reading a single dash, we may either find another one,
  ||| meaning we may have started reading a line comment, or find
  ||| a closing brace meaning we have found a closing delimiter.
  singleDash : (k : Nat) -> Lexer
  singleDash k
     =  is '-' <+> doubleDash k    -- comment or closing delimiter
    <|> is '}' <+> toEndComment k  -- closing delimiter
    <|> toEndComment (S k)         -- not a valid comment

  ||| After reading a double dash, we are potentially reading a line
  ||| comment unless the series of uninterrupted dashes is ended with
  ||| a closing brace in which case it is a closing delimiter.
  doubleDash : (k : Nat) -> Lexer
  doubleDash k = with Prelude.(::)
      many (is '-') <+> choice            -- absorb all dashes
        [ is '}' <+> toEndComment k                      -- closing delimiter
        , many (isNot '\n') <+> toEndComment (S k)       -- line comment
        ]

export
blockComment : Lexer
blockComment = is '{' <+> is '-' <+> many (is '-') <+> (eof <|> toEndComment 1)

-- Identifier Lexer
-- There are multiple variants.

public export
data Flavour = AllowDashes | Capitalised | Normal

-- True for chars in the Unicode Mathematical Operators blocks,
-- or selected General Punctuation chars used as operators.
-- These are excluded from identifier chars so they lex as Symbol tokens.
isUnicodeMathOp : Char -> Bool
isUnicodeMathOp c =
  let o = ord c
  in o == 0x2016  -- ‖ DOUBLE VERTICAL LINE (squash types ‖A‖)
  || (o >= 0x2200 && o <= 0x22FF)
  || (o >= 0x2A00 && o <= 0x2AFF)

isIdentStart : Flavour -> Char -> Bool
isIdentStart _           '_' = True
isIdentStart Capitalised  x  = isUpper x || (x > chr 160 && not (isUnicodeMathOp x))
isIdentStart _            x  = isAlpha x || (x > chr 160 && not (isUnicodeMathOp x))

isIdentTrailing : Flavour -> Char -> Bool
isIdentTrailing AllowDashes '-'  = True
isIdentTrailing _           '\'' = True
isIdentTrailing _           '_'  = True
isIdentTrailing _            x   = isAlphaNum x || (x > chr 160 && not (isUnicodeMathOp x))

export %inline
isIdent : Flavour -> String -> Bool
isIdent flavour string =
  case unpack string of
    []      => False
    (x::xs) => isIdentStart flavour x && all (isIdentTrailing flavour) xs

export %inline
ident : Flavour -> Lexer
ident flavour =
  (pred $ isIdentStart flavour) <+>
    (many . pred $ isIdentTrailing flavour)

export
isIdentNormal : String -> Bool
isIdentNormal = isIdent Normal

export
identNormal : Lexer
identNormal = ident Normal

export
identAllowDashes : Lexer
identAllowDashes = ident AllowDashes

namespaceIdent : Lexer
namespaceIdent = ident Capitalised <+> many (is '.' <+> ident Capitalised <+> expect (is '.'))

export
namespacedIdent : Lexer
namespacedIdent = namespaceIdent <+> opt (is '.' <+> identNormal)

export
spacesOrNewlines : Lexer
spacesOrNewlines = some (space <|> newline)
