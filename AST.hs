module AST where

data Expr = Var Name 
          | Lit Lit
          | Infix Op Expr Expr | App Expr Expr | Lam Name Expr
          | Case Expr Expr (Name, Name, Expr) | If Expr Expr Expr
  deriving (Eq, Show)

data FunDef = FunDef Name Expr deriving (Eq, Show)

data Program = Program [FunDef] deriving Show

data Op = Add | Sub | Mult | Div
        | Eq | GTh | LTh 
        | And | Or
        | Cons | Comp | Append
  deriving (Eq, Show)

data Lit = LitInt Integer | LitBool Bool | LitNil
  deriving (Eq, Show)

type Name  = String
