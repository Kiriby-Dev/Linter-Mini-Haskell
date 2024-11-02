module Lintings where
import Debug.Trace (trace)
import AST
import LintTypes
import System.Win32 (xBUTTON1)


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables = undefined


--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)
lintComputeConstant :: Linting Expr
lintComputeConstant = undefined


--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool expr@(Infix Eq (Var x) (Lit (LitBool True))) = (Var x, [LintBool expr (Var x)])
lintRedBool expr@(Infix Eq (Lit (LitBool True)) (Var x)) = (Var x, [LintBool expr (Var x)])
lintRedBool expr@(Infix Eq (Var x) (Lit (LitBool False))) = (App (Var "not") (Var x), [LintBool expr (App (Var "not") (Var x))])
lintRedBool expr@(Infix Eq (Lit (LitBool False)) (Var x)) = (App (Var "not") (Var x), [LintBool expr (App (Var "not") (Var x))])
lintRedBool expr@(Infix Eq (Var x) (Var y)) = (expr, [])

-- Caso para comparar expresiones de forma recursiva
lintRedBool expr@(Infix op left right) =
    let (newLeft, leftSuggestions) = lintRedBool left
        (newRight, rightSuggestions) = lintRedBool right
        newExpr = Infix op newLeft newRight
        -- Solo aplicamos lintRedBool a newExpr si es diferente de expr
    in if newExpr == expr
            then case newExpr of
                -- Simplificamos nuevamente si tenemos una expresión comparada con True o False
                Infix Eq e (Lit (LitBool True)) -> (e, leftSuggestions ++ rightSuggestions ++ [LintBool newExpr e])
                Infix Eq (Lit (LitBool True)) e -> (e, leftSuggestions ++ rightSuggestions ++ [LintBool newExpr e])
                Infix Eq e (Lit (LitBool False)) -> (App (Var "not") e, leftSuggestions ++ rightSuggestions ++ [LintBool newExpr (App (Var "not") e)])
                Infix Eq (Lit (LitBool False)) e -> (App (Var "not") e, leftSuggestions ++ rightSuggestions ++ [LintBool newExpr (App (Var "not") e)])
                _ -> (newExpr, leftSuggestions ++ rightSuggestions)
        else (newExpr, leftSuggestions ++ rightSuggestions)  -- Aplicamos la simplificación recursiva si hay cambios

lintRedBool (Lam name expr) = 
    let (newExpr, suggestions) = lintRedBool expr
    in (Lam name newExpr, suggestions)

lintRedBool (If expr1 expr2 expr3) =
    let (newExpr1, suggestions1) = lintRedBool expr1
        (newExpr2, suggestions2) = lintRedBool expr2
        (newExpr3, suggestions3) = lintRedBool expr3
    in (If newExpr1 newExpr2 newExpr3, suggestions1 ++ suggestions2 ++ suggestions3)

lintRedBool (App expr1 expr2) = 
    let (newExpr1, suggestions1) = lintRedBool expr1
        (newExpr2, suggestions2) = lintRedBool expr2
    in (App newExpr1 newExpr2, suggestions1 ++ suggestions2)

lintRedBool (Case expr1 expr2 (name1, name2, expr3)) = 
    let (newExpr1, suggestions1) = lintRedBool expr1
        (newExpr2, suggestions2) = lintRedBool expr2
        (newExpr3, suggestions3) = lintRedBool expr3
    in (Case newExpr1 newExpr2 (name1, name2, newExpr3), suggestions1 ++ suggestions2 ++ suggestions3)

lintRedBool expr = (expr, [])
    

--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond = undefined

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd = undefined

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr = undefined

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull = undefined

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend = undefined

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp = undefined


--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta = undefined


--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = undefined


--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------


-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc lintExpr (FunDef name expr) =
    let (newExpr, suggestions) = lintExpr expr
    in (FunDef name newExpr, suggestions)

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
(lint1 >==> lint2) expr =
    let (expr1, suggestions1) = lint1 expr
        (expr2, suggestions2) = lint2 expr1
    in (expr2, suggestions1 ++ suggestions2)

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Eq a => Linting a -> Linting a
lintRec lints expr =
    let (newExpr, suggestions) = lints expr
    in if newExpr == expr
       then (newExpr, suggestions)
       else let (finalExpr, finalSuggestions) = lintRec lints newExpr
            in (finalExpr, suggestions ++ finalSuggestions)