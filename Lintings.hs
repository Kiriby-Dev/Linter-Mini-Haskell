module Lintings where
import Debug.Trace (trace)
import AST
import LintTypes
import System.Win32

--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var x) = [x] -- CASO BASE
freeVariables (Lit _) = [] -- CASO BASE
-- RECURSIÓN: 
freeVariables (Infix _ e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Lam x e) = filter (/= x) (freeVariables e) -- Elimina x, pq quedará ligada.
freeVariables (Case e1 e2 (x, y, e3)) = 
    freeVariables e1 ++ freeVariables e2 ++ filter (\v -> v /= x && v /= y) (freeVariables e3)  -- Elimina x e y pq ya están ligadas (ME QUEDAN DUDAS PERO NO ENTENDÍ BIEN LA DEF DEL CASE).
freeVariables (If e1 e2 e3) = freeVariables e1 ++ freeVariables e2 ++ freeVariables e3

applyRecursively :: Linting Expr -> Linting Expr
applyRecursively lint expr@(Lam name body) = 
    let (newBody, suggestions) = lint body
    in (Lam name newBody, suggestions)

applyRecursively lint expr@(App expr1 expr2) = 
    let (newExpr1, suggestions1) = lint expr1
        (newExpr2, suggestions2) = lint expr2
    in (App newExpr1 newExpr2, suggestions1 ++ suggestions2)

applyRecursively lint expr@(If cond expr1 expr2) = 
    let (newCond, suggestionsCond) = lint cond
        (newExpr1, suggestions1) = lint expr1
        (newExpr2, suggestions2) = lint expr2
    in (If newCond newExpr1 newExpr2, suggestionsCond ++ suggestions1 ++ suggestions2)

applyRecursively lint expr@(Infix op expr1 expr2) = 
    let (newExpr1, suggestions1) = lint expr1
        (newExpr2, suggestions2) = lint expr2
    in (Infix op newExpr1 newExpr2, suggestions1 ++ suggestions2)

applyRecursively lint expr@(Case expr1 expr2 (name1, name2, expr3)) = 
    let (newExpr1, suggestions1) = lint expr1
        (newExpr2, suggestions2) = lint expr2
        (newExpr3, suggestions3) = lint expr3
    in (Case newExpr1 newExpr2 (name1, name2, newExpr3), suggestions1 ++ suggestions2 ++ suggestions3)
    
applyRecursively _ expr = (expr, [])

-- Función de orquestación para probar múltiples reducciones
lintRedIfCombined :: Linting Expr
lintRedIfCombined expr = 
    let
        -- Intentar aplicar cada función de reducción en orden
        (reducedExpr1, suggestions1) = lintRedIfCond expr
        (reducedExpr2, suggestions2) = if reducedExpr1 == expr then lintRedIfAnd expr else (reducedExpr1, suggestions1)
        (reducedExpr3, suggestions3) = if reducedExpr2 == expr then lintRedIfOr expr else (reducedExpr2, suggestions2)
    in
        if reducedExpr3 == expr 
        then (expr, suggestions1 ++ suggestions2 ++ suggestions3)
        else (reducedExpr3, suggestions3)

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
lintComputeConstant expr@(Infix op left right) =
    let (simplLeft, leftSuggestions) = lintComputeConstant left
        (simplRight, rightSuggestions) = lintComputeConstant right
        partialExpr = Infix op simplLeft simplRight
        (finalExpr, newSuggestions) = case partialExpr of
            -- Simplificaciones aritméticas
            Infix Add (Lit (LitInt x)) (Lit (LitInt y)) -> (Lit (LitInt (x + y)), [LintCompCst partialExpr (Lit (LitInt (x + y)))])
            Infix Sub (Lit (LitInt x)) (Lit (LitInt y))
                    | y < x     -> (Lit (LitInt (x - y)), [LintCompCst partialExpr (Lit (LitInt (x - y)))])
                    | otherwise -> (partialExpr, [])  -- Sin sugerencia si el resultado es negativo
            Infix Mult (Lit (LitInt x)) (Lit (LitInt y)) -> (Lit (LitInt (x * y)), [LintCompCst partialExpr (Lit (LitInt (x * y)))])
            Infix Div (Lit (LitInt x)) (Lit (LitInt y))
                    | y /= 0    -> (Lit (LitInt (x `div` y)), [LintCompCst partialExpr (Lit (LitInt (x `div` y)))])
                    | otherwise -> (partialExpr, [])  -- Evita división por 0
            -- Simplificaciones booleanas
            Infix And (Lit (LitBool x)) (Lit (LitBool y)) -> (Lit (LitBool (x && y)), [LintCompCst partialExpr (Lit (LitBool (x && y)))])
            Infix Or (Lit (LitBool x)) (Lit (LitBool y)) -> (Lit (LitBool (x || y)), [LintCompCst partialExpr (Lit (LitBool (x || y)))])

            _ -> (partialExpr, [])
    in (finalExpr, leftSuggestions ++ rightSuggestions ++ newSuggestions)

lintComputeConstant expr = applyRecursively lintComputeConstant expr 
--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)

lintRedBool :: Linting Expr
-- Caso para comparar expresiones de forma recursiva
lintRedBool expr@(Infix Eq left right) =
    let (simplLeft, leftSuggestions) = lintRedBool left
        (simplRight, rightSuggestions) = lintRedBool right
        partialExpr = Infix Eq simplLeft simplRight
        (finalExpr, newSuggestions) = case partialExpr of
            -- Simplificamos nuevamente si tenemos una expresión comparada con True o False
            Infix Eq e (Lit (LitBool True)) -> (e, [LintBool partialExpr e])
            Infix Eq (Lit (LitBool True)) e -> (e, [LintBool partialExpr e])
            Infix Eq e (Lit (LitBool False)) -> (App (Var "not") e, [LintBool partialExpr (App (Var "not") e)])
            Infix Eq (Lit (LitBool False)) e -> (App (Var "not") e, [LintBool partialExpr (App (Var "not") e)])
            _ -> (partialExpr, [])
    in (finalExpr, leftSuggestions ++ rightSuggestions ++ newSuggestions)

lintRedBool expr = applyRecursively lintRedBool expr 

--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)

lintRedIfCond :: Linting Expr
lintRedIfCond (If expr1 expr2 expr3) =
    let (simplifiedExpr2, suggestions2) = lintRedIfCombined expr2
        (simplifiedExpr3, suggestions3) = lintRedIfCombined expr3
        partialExpr = If expr1 simplifiedExpr2 simplifiedExpr3
        (finalExpr, newSuggestions) = case expr1 of
            Lit (LitBool True)  -> (simplifiedExpr2, [LintRedIf partialExpr simplifiedExpr2])
            Lit (LitBool False) -> (simplifiedExpr3, [LintRedIf partialExpr simplifiedExpr3])
            _ -> (partialExpr, [])
    in (finalExpr, suggestions2 ++ suggestions3 ++ newSuggestions)

lintRedIfCond expr = applyRecursively lintRedIfCond expr 
--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)

lintRedIfAnd :: Linting Expr
lintRedIfAnd (If expr2 expr3 expr1) =
    let (simplifiedExpr2, suggestions2) = lintRedIfCombined expr2
        (simplifiedExpr3, suggestions3) = lintRedIfCombined expr3
        partialExpr = If simplifiedExpr2 simplifiedExpr3 expr1 
        (finalExpr, newSuggestions) = case expr1 of
            Lit (LitBool False) -> (Infix And simplifiedExpr2 simplifiedExpr3, [LintRedIf partialExpr (Infix And simplifiedExpr2 simplifiedExpr3)])
            _ -> (partialExpr, [])
    in (finalExpr, suggestions2 ++ suggestions3 ++ newSuggestions)

lintRedIfAnd expr = applyRecursively lintRedIfAnd expr

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)

lintRedIfOr :: Linting Expr
lintRedIfOr (If expr2 expr1 expr3) =
    let (simplifiedExpr2, suggestions2) = lintRedIfCombined expr2
        (simplifiedExpr3, suggestions3) = lintRedIfCombined expr3 
        partialExpr = If simplifiedExpr2 expr1 simplifiedExpr3
        (finalExpr, newSuggestions) = case expr1 of
            Lit (LitBool True) -> (Infix Or simplifiedExpr2 simplifiedExpr3, [LintRedIf partialExpr (Infix Or simplifiedExpr2 simplifiedExpr3)])
            _ -> (partialExpr, [])
    in (finalExpr, suggestions2 ++ suggestions3 ++ newSuggestions)

lintRedIfOr expr = applyRecursively lintRedIfOr expr

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull expr@(Infix Eq e (Lit LitNil)) = (App (Var "null") e, [LintNull expr (App (Var "null") e)])
lintNull expr@(Infix Eq (Lit LitNil) e) = (App (Var "null") e, [LintNull expr (App (Var "null") e)])
lintNull expr@(Infix Eq (App (Var "length") e) (Lit (LitInt 0))) = (App (Var "null") e, [LintNull expr (App (Var "null") e)])
lintNull expr@(Infix Eq (Lit (LitInt 0)) (App (Var "length") e)) = (App (Var "null") e, [LintNull expr (App (Var "null") e)])

lintNull expr = applyRecursively lintNull expr
--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend expr@(Infix Append left right) =
    let (simplRight, rightSuggestions) = lintAppend right
        partialExpr = Infix Append left simplRight
        (finalExpr, newSuggestions) = case partialExpr of
            Infix Append (Infix Cons x (Lit LitNil)) xs -> (Infix Cons x xs, [LintAppend partialExpr (Infix Cons x xs)])
            _ -> (partialExpr, [])
    in (finalExpr, rightSuggestions ++ newSuggestions)

lintAppend expr = applyRecursively lintAppend expr

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp expr@(App outerExpr innerExpr) = 
    let (simplifiedInner, suggestionsInner) = lintComp innerExpr
        partialExpr = App outerExpr simplifiedInner
        (finalExpr, newSuggestions) = case partialExpr of
            App outerFunc (App innerFunc expr) -> 
                (App (Infix Comp outerFunc innerFunc) expr, 
                 [LintComp partialExpr (App (Infix Comp outerFunc innerFunc) expr)])
            _ -> (partialExpr, [])
    in (finalExpr, suggestionsInner ++ newSuggestions)

lintComp expr = applyRecursively lintComp expr
--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta expr@(Lam x (App e (Var y))) 
    | x == y && x `notElem` freeVariables e = 
        let (reducedExpr, suggestions) = lintEta e
            partialExpr = Lam x (App reducedExpr (Var y))
        in (reducedExpr, suggestions ++ [LintEta partialExpr reducedExpr])

lintEta expr = applyRecursively lintEta expr

-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap expr@(FunDef name (Lam l (Case (Var l') (Lit LitNil) (x, xs, body))))
    | l == l' =
        let (extractedExpr, matchesPattern) = 
                case body of
                    Infix Cons e (App (Var funcName) innerExpr)
                        | funcName == name && innerExpr == Var xs -> (e, True)
                    _ -> (body, False)
        in case matchesPattern of
            True 
                | notElem name (freeVariables extractedExpr) && notElem xs (freeVariables extractedExpr) && notElem l (freeVariables extractedExpr) -> 
                    let suggestion = LintMap expr (FunDef name (App (Var "map") (Lam x extractedExpr)))
                    in (FunDef name (App (Var "map") (Lam x extractedExpr)), [suggestion])
            _ -> (expr, [])
    | otherwise = (expr, [])

lintMap expr = (expr, [])

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