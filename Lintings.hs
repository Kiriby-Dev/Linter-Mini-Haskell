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
lintComputeConstant expr@(Infix Add (Lit (LitInt x)) (Lit (LitInt y))) = (Lit (LitInt (x + y)), [LintCompCst expr (Lit (LitInt (x + y)))])
lintComputeConstant expr@(Infix Sub (Lit (LitInt x)) (Lit (LitInt y)))
                    | y < x     = (Lit (LitInt (x - y)), [LintCompCst expr (Lit (LitInt (x - y)))])
                    | otherwise = (expr, [])  -- Sin sugerencia si el resultado es negativo
lintComputeConstant expr@(Infix Mult (Lit (LitInt x)) (Lit (LitInt y))) = (Lit (LitInt (x * y)), [LintCompCst expr (Lit (LitInt (x * y)))])
lintComputeConstant expr@(Infix Div (Lit (LitInt x)) (Lit (LitInt y)))
                    | y /= 0    = (Lit (LitInt (x `div` y)), [LintCompCst expr (Lit (LitInt (x `div` y)))])
                    | otherwise = (expr, [])  -- Sin sugerencia si el divisor es 0
lintComputeConstant expr@(Infix And (Lit (LitBool x)) (Lit (LitBool y))) = (Lit (LitBool (x && y)), [LintCompCst expr (Lit (LitBool (x && y)))])
lintComputeConstant expr@(Infix Or (Lit (LitBool x)) (Lit (LitBool y))) = (Lit (LitBool (x || y)), [LintCompCst expr (Lit (LitBool (x || y)))])

lintComputeConstant expr@(Infix op left right) =
    let (simplLeft, leftSuggestions) = lintComputeConstant left
        (simplRight, rightSuggestions) = lintComputeConstant right
        partialExpr = Infix op simplLeft simplRight
        (finalExpr, newSuggestions) = case partialExpr of
            -- Simplificaciones aritméticas
            Infix Add (Lit (LitInt x)) (Lit (LitInt y)) -> (Lit (LitInt (x + y)), [LintCompCst partialExpr (Lit (LitInt (x + y)))])
            Infix Sub (Lit (LitInt x)) (Lit (LitInt y))
                    | y < x     -> (Lit (LitInt (x - y)), [LintCompCst expr (Lit (LitInt (x - y)))])
                    | otherwise -> (expr, [])  -- Sin sugerencia si el resultado es negativo
            Infix Mult (Lit (LitInt x)) (Lit (LitInt y)) -> (Lit (LitInt (x * y)), [LintCompCst partialExpr (Lit (LitInt (x * y)))])
            Infix Div (Lit (LitInt x)) (Lit (LitInt y))
                | y /= 0    -> (Lit (LitInt (x `div` y)), [LintCompCst partialExpr (Lit (LitInt (x `div` y)))])
                | otherwise -> (partialExpr, [])  -- Evita división por 0
            -- Simplificaciones booleanas
            Infix And (Lit (LitBool x)) (Lit (LitBool y)) -> (Lit (LitBool (x && y)), [LintCompCst partialExpr (Lit (LitBool (x && y)))])
            Infix Or (Lit (LitBool x)) (Lit (LitBool y)) -> (Lit (LitBool (x || y)), [LintCompCst partialExpr (Lit (LitBool (x || y)))])

            _ -> (partialExpr, [])
    in (finalExpr, leftSuggestions ++ rightSuggestions ++ newSuggestions)

lintComputeConstant (Lam name expr) = 
    let (newExpr, suggestions) = lintComputeConstant expr
    in (Lam name newExpr, suggestions)

lintComputeConstant (If expr1 expr2 expr3) =
    let (newExpr1, suggestions1) = lintComputeConstant expr1
        (newExpr2, suggestions2) = lintComputeConstant expr2
        (newExpr3, suggestions3) = lintComputeConstant expr3
    in (If newExpr1 newExpr2 newExpr3, suggestions1 ++ suggestions2 ++ suggestions3)

lintComputeConstant (App expr1 expr2) = 
    let (newExpr1, suggestions1) = lintComputeConstant expr1
        (newExpr2, suggestions2) = lintComputeConstant expr2
    in (App newExpr1 newExpr2, suggestions1 ++ suggestions2)

lintComputeConstant (Case expr1 expr2 (name1, name2, expr3)) = 
    let (newExpr1, suggestions1) = lintComputeConstant expr1
        (newExpr2, suggestions2) = lintComputeConstant expr2
        (newExpr3, suggestions3) = lintComputeConstant expr3
    in (Case newExpr1 newExpr2 (name1, name2, newExpr3), suggestions1 ++ suggestions2 ++ suggestions3)

lintComputeConstant expr = (expr, [])

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
    let (simplLeft, leftSuggestions) = lintRedBool left
        (simplRight, rightSuggestions) = lintRedBool right
        partialExpr = Infix op simplLeft simplRight
        (finalExpr, newSuggestions) = case partialExpr of
            -- Simplificamos nuevamente si tenemos una expresión comparada con True o False
            Infix Eq e (Lit (LitBool True)) -> (e, [LintBool partialExpr e])
            Infix Eq (Lit (LitBool True)) e -> (e, [LintBool partialExpr e])
            Infix Eq e (Lit (LitBool False)) -> (App (Var "not") e, [LintBool partialExpr (App (Var "not") e)])
            Infix Eq (Lit (LitBool False)) e -> (App (Var "not") e, [LintBool partialExpr (App (Var "not") e)])
            _ -> (partialExpr, [])
    in (finalExpr, leftSuggestions ++ rightSuggestions ++ newSuggestions)

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
lintRedIfCond expr@(If (Lit (LitBool True)) (Var x) _) = (Var x, [LintRedIf expr (Var x)])
lintRedIfCond expr@(If (Lit (LitBool False)) _ (Var x)) = (Var x, [LintRedIf expr (Var x)])
lintRedIfCond expr@(If (Lit (LitBool True)) (Lit x) _) = (Lit x, [LintRedIf expr (Lit x)])
lintRedIfCond expr@(If (Lit (LitBool False)) _ (Lit x)) = (Lit x, [LintRedIf expr (Lit x)])

lintRedIfCond (If expr1 expr2 expr3) =
    let (simplifiedExpr1, suggestions1) = lintRedIfCond expr1
        (simplifiedExpr2, suggestions2) = lintRedIfCond expr2
        (simplifiedExpr3, suggestions3) = lintRedIfCond expr3
        partialExpr = If simplifiedExpr1 simplifiedExpr2 simplifiedExpr3
        (finalExpr, newSuggestions) = case simplifiedExpr1 of
            Lit (LitBool True)  -> (simplifiedExpr2, [LintRedIf partialExpr simplifiedExpr2])
            Lit (LitBool False) -> (simplifiedExpr3, [LintRedIf partialExpr simplifiedExpr3])
            _ -> (partialExpr, [])
    in (finalExpr, suggestions1 ++ suggestions2 ++ suggestions3 ++ newSuggestions)

lintRedIfCond (Infix op left right) = 
    let (simplLeft, leftSuggestions) = lintRedIfCond left
        (simplRight, rightSuggestions) = lintRedIfCond right
        finalExpr = Infix op simplLeft simplRight
    in (finalExpr, leftSuggestions ++ rightSuggestions)

lintRedIfCond (Lam name expr) = 
    let (newExpr, suggestions) = lintRedIfCond expr
    in (Lam name newExpr, suggestions)

lintRedIfCond (App expr1 expr2) = 
    let (newExpr1, suggestions1) = lintRedIfCond expr1
        (newExpr2, suggestions2) = lintRedIfCond expr2
    in (App newExpr1 newExpr2, suggestions1 ++ suggestions2)

lintRedIfCond (Case expr1 expr2 (name1, name2, expr3)) = 
    let (newExpr1, suggestions1) = lintRedIfCond expr1
        (newExpr2, suggestions2) = lintRedIfCond expr2
        (newExpr3, suggestions3) = lintRedIfCond expr3
    in (Case newExpr1 newExpr2 (name1, name2, newExpr3), suggestions1 ++ suggestions2 ++ suggestions3)

lintRedIfCond expr = (expr, [])  
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