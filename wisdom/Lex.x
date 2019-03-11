-- Example lexer written for Alex (the Haskell lexer generator).
-- This file uses the "posn" wrapper so you can get the position of each token,
-- but the token type does not actually carry the position so you'll have to
-- implement that yourself.

{
module Lex (lexString, Token(..)) where
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
       $white+                         ;
       \/\/.*$                         ;
       \/\*([^\*]|\*[^\/])*\*\/        ;
       $digit+                         { \pos s -> Num (read s) }
       \+                              { \pos s -> Plus }
       \=\=                            { \pos s -> EqualEqual }
       \=                              { \pos s -> Equal }
       \<                              { \pos s -> LessThan }
       \>                              { \pos s -> GreaterThan }
       var                             { \pos s -> Var }
       if                              { \pos s -> If }
       while                           { \pos s -> While }
       die                             { \pos s -> Die }
       def                             { \pos s -> Def }
       pass                            { \pos s -> Pass }
       return                          { \pos s -> Return }
       \(                              { \pos s -> OpenParen }
       \)                              { \pos s -> CloseParen }
       \{                              { \pos s -> OpenBrace }
       \}                              { \pos s -> CloseBrace }
       \@                              { \pos s -> At }
       \;                              { \pos s -> Semicolon }
       \:                              { \pos s -> Colon }
       \,                              { \pos s -> Comma }
       \!                              { \pos s -> Bang }
       [$alpha \_][$alpha $digit \_]*  { \pos s -> Id s }

{

data Token =
    Id String
  | Num Integer
  | Var | If | While | Die | Def | Pass | Return
  | Plus | Equal | LessThan | GreaterThan
  | At | EqualEqual | Colon | Semicolon | Comma | Bang
  | OpenParen | CloseParen | OpenBrace | CloseBrace
  deriving (Eq, Show)

lexString :: String -> [Token]
lexString = alexScanTokens

}
