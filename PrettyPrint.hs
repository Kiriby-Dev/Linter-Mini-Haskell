{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module PrettyPrint where
import AST
import Control.Monad
import Data.List

class PrettyPrint a where
  pp :: a -> String

instance PrettyPrint Lit where
  pp (LitInt i) = show i
  pp (LitBool b) = show b
  pp LitNil = "[]"

instance PrettyPrint Op where
  pp Add  = "+"
  pp Sub  = "-"
  pp Mult = "*"
  pp Div  = "`div`"
  pp Eq   = "=="
  pp GTh  = ">"
  pp LTh  = "<"
  pp And  = "&&"
  pp Or   = "||"
  pp Cons = ":"
  pp Comp = "."
  pp Append = "++"

prec :: Op -> Int
prec Add  = 6
prec Sub  = 6
prec Mult = 7
prec Div  = 7
prec Eq   = 4
prec GTh  = 4
prec LTh  = 4
prec And  = 3
prec Or   = 2
prec Cons = 5
prec Append = 5
prec Comp   = 9

instance PrettyPrint FunDef where
  pp (FunDef nam body) =
    nam ++ " = " ++ pp body

instance PrettyPrint Expr where
 pp = fst . flip ppPrec 1

wrapIf b s = if b then "(" ++ s ++ ")" else s


ppPrec :: Expr -> Int -> (String, Int)
ppPrec (Var v) c = (v, 10)
ppPrec (Lit l) c = (pp l, 10)
ppPrec (App t u) c =
 let (sl, pl) = ppPrec t c 
     (sr, pr) = ppPrec u c
 in case (t, u) of
    (Lam _ _, Var _ ) -> (mconcat ["(", sl, ") ", sr], 10)
    (Lam _ _, _ )     -> (mconcat ["(", sl, ") (", sr, ")"], 10)
    (App _ _, Var _ ) -> (mconcat [sl, " ", sr], 10)
    (App _ _, Lit _ ) -> (mconcat [sl, " ", sr], 10)
    (App _ _, _ )     -> (mconcat [sl, " (", sr, ")"], 10)
    (Var _  , Var _)  -> (mconcat [sl, " ", sr], 10)
    (Var _  , Lit _)  -> (mconcat [sl, " ", sr], 10)
    (Var _  , _)      -> (mconcat [sl, " (", sr, ")"], 10)
    (_      , Var _)  -> (mconcat ["(", sl, ") ", sr], 10)
    (_      , Lit _)  -> (mconcat ["(", sl, ") ", sr], 10)
    (_,      _)       -> (mconcat ["(",sl, ") (", sr, ")"], 10)
ppPrec (Lam n e) c = ('\\':n ++ " -> " ++ fst (ppPrec e c), 1)
ppPrec (Case e ncase (x,xs,ccase)) c =
    ("case " ++ pp e ++ " of \n" ++ replicate (4*c) ' ' ++  "[] -> "
     ++ fst (ppPrec ncase (c + 1))
     ++ "; \n" ++ replicate (4*c) ' ' ++ "(" ++ x ++ " : " ++ xs ++ ") -> "
     ++ fst (ppPrec ccase (c + 1)), 10)
ppPrec (If c t e) cs =
  ("if " ++ fst (ppPrec c cs)
  ++ " then " ++ fst (ppPrec t cs) ++ " else "
  ++ fst (ppPrec e cs) ,10)
ppPrec (Infix op l r) c =
   let (sl, leftPrec ) = ppPrec l c
       (sr, rightPrec) = ppPrec r c
       currPrec = prec op
   in ( mconcat [ wrapIf (leftPrec < currPrec) sl,
                  " ", pp op, " ",
                  wrapIf (rightPrec <= currPrec) sr]
      , currPrec)

instance PrettyPrint Program where
  pp (Program p) = intercalate "\n\n" $ map pp p
