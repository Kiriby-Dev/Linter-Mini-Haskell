module LintTypes where

import AST
import PrettyPrint

data LintSugg = LintCompCst Expr Expr
              | LintBool    Expr Expr
              | LintRedIf   Expr Expr
              | LintNull    Expr Expr
              | LintAppend  Expr Expr  
              | LintComp    Expr Expr
              | LintEta     Expr Expr
              | LintMap     FunDef FunDef
  deriving Show

instance PrettyPrint LintSugg where
  pp (LintCompCst e r) = suggestionTemplate "Constante" e r
  pp (LintBool    e r) = suggestionTemplate "Eliminar chequeo reduntante" e r
  pp (LintRedIf   e r) = suggestionTemplate "If redundante" e r
  pp (LintNull    e r) = suggestionTemplate "Usar null" e r  
  pp (LintAppend  e r) = suggestionTemplate "Eliminar concatenación" e r
  pp (LintComp    e r) = suggestionTemplate "Usar composición" e r
  pp (LintEta     e r) = suggestionTemplate "Usar eta-reducción" e r
  pp (LintMap     f r) = suggestionTemplate "Usar map" f r

suggestionTemplate sugg pre pos =
  "**Sugerencia para:\n"
    ++ pp pre
    ++ "\n"
    ++ sugg
    ++ ". Reemplazar por:\n"
    ++ pp pos


type Linting a = a -> (a, [LintSugg])
