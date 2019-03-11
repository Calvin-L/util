-- Example parser written for Happy (the Haskell parser generator).
-- This file uses the "Lex" module (see Lex.x).
-- It frustrates me that you need to duplicate the list of tokens between the
-- lexer and parser, but I suppose that's life.

{
module Parse (parse) where

import FrontendSyntax
import Lex
}

%name parseTokens
%tokentype { Token }

%token
    id          { Id $$ }
    int         { Num $$ }
    'var'       { Var }
    'if'        { If }
    'while'     { While }
    'die'       { Die }
    'def'       { Def }
    'pass'      { Pass }
    'return'    { Return }
    '('         { OpenParen }
    ')'         { CloseParen }
    '{'         { OpenBrace }
    '}'         { CloseBrace }
    '@'         { At }
    '='         { Equal }
    '=='        { EqualEqual }
    '<'         { LessThan }
    '>'         { GreaterThan }
    ':'         { Colon }
    ';'         { Semicolon }
    ','         { Comma }
    '+'         { Plus }
    '!'         { Bang }

%left '!'
%left '+'
%left '==' '<' '>'

%%

Program
  : Decls { Program $1 }

Decls
  : { [] }
  | Decl Decls { $1 : $2 }

Decl
  : Annotations 'def' id '(' Args ')' '{' Stms '}' { DProc $1 $3 $5 $8 }
  | 'var' id ':' Type '=' Exp ';' { DGlobal $2 $4 $6 }

Annotations
  : { [] }
  | Annotation Annotations { $1 : $2 }

Annotation
  : '@' id { case $2 of { "entry" -> EntryPoint; other -> error $ "not a legal annotation: " ++ show other } }

Args
  : { [] }
  -- TODO

Type
  : id MaybeTypeArgs { case $2 of { Nothing -> TNamed $1; Just args -> TApp $1 args } }

MaybeTypeArgs
  : { Nothing }
  | '<' TypeList1 '>' { Just $2 }

TypeList1
  : Type { [$1] }
  | Type ',' TypeList1 { $1 : $3 }

Stms
  : { SNoOp }
  | Stm Stms { SSeq $1 $2 }

Stm
  : id '=' Exp ';' { SAssign $1 $3 }
  | 'var' id ':' Type '=' Exp ';' { SDecl $2 $4 $6 }
  | 'pass' ';' { SNoOp }
  | 'die' ';' { SDie }
  | 'if' Exp '{' Stms '}' { SIf $2 $4 SNoOp }
  | 'while' Exp '{' Stms '}' { SWhile $2 $4 }
  | 'return' Exp ';' { SReturn $2 }

Exp
  : int         { EInt $1 }
  | id MaybeCall { let id = $1 in case $2 of { Nothing -> EVar id; Just args -> ECall id args } }
  | Exp '+' Exp { EPlus $1 $3 }
  | Exp '==' Exp { EEq $1 $3 }
  | Exp '>' Exp { EGt $1 $3 }
  | Exp '<' Exp { ELt $1 $3 }
  | '!' Exp { ENot $2 }
  | '(' Exp ')' { $2 }

MaybeCall
  : { Nothing }
  | '(' ExpList ')' { Just $2 }

ExpList
  : { [] }
  | ExpList1 { $1 }

ExpList1
  : Exp { [$1] }
  | Exp ',' ExpList1 { $1 : $3 }

{

happyError :: [Lex.Token] -> a
happyError = error . ("Parse error at " ++) . show

parse :: String -> Program
parse = parseTokens . lexString

}
