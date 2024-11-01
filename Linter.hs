module Main where

import System.Environment
import System.IO
import Control.Monad
import Data.List
import Data.Either

import AST
import Parser
import PrettyPrint
import Lintings
import LintTypes

debug = False

data Action = Compile | Suggest | SuggestAST

main = do
  args <- getArgs
  let (eAction, args1) = actionFromFlag args
  let (eLint, args2)   = lintFromFlag args1
  let eFilename        = fileNameFromArgs args2
  let eRes = do
        a <- eAction
        l <- eLint
        f <- eFilename
        return $ lint l a f
  either (\err -> putStrLn err >> putStrLn usage) id eRes


sep = putStrLn $ replicate 80 '-'

actionFromFlag :: [String] -> (Either String Action, [String])
actionFromFlag ("-c" : xs) = (Right Compile, xs)
actionFromFlag ("-s" : xs) = (Right Suggest, xs)
actionFromFlag ("-v" : xs) = (Right SuggestAST, xs)
actionFromFlag (x : xs) | "-" `isPrefixOf` x =
  (Left $ "Acción no reconocida: " ++ x, xs)
actionFromFlag _        = (Left "Debe especificar una acción", [])


lintFromFlag :: [String] -> (Either String (Linting FunDef), [String])
lintFromFlag ("-lintComputeConstant" : xs) =
  (Right $ liftToFunc lintComputeConstant, xs)
lintFromFlag ("-lintRedBool"      : xs) = (Right $ liftToFunc lintRedBool, xs)
lintFromFlag ("-lintRedIfCond" : xs) = (Right $ liftToFunc lintRedIfCond, xs)
lintFromFlag ("-lintRedIfAnd"  : xs) = (Right $ liftToFunc lintRedIfAnd, xs)
lintFromFlag ("-lintRedIfOr"   : xs) = (Right $ liftToFunc lintRedIfOr, xs)
lintFromFlag ("-lintNull"      : xs) = (Right $ liftToFunc lintNull, xs)
lintFromFlag ("-lintAppend"    : xs) = (Right $ liftToFunc lintAppend, xs)
lintFromFlag ("-lintComp"      : xs) = (Right $ liftToFunc lintComp, xs)
lintFromFlag ("-lintEta"       : xs) = (Right $ liftToFunc lintEta, xs)
lintFromFlag ("-lintMap"       : xs) = (Right lintMap, xs)
lintFromFlag (x : xs) | "-" `isPrefixOf` x =
  (Left $ "Linting no reconocido: " ++ x, xs)
lintFromFlag xs = (Right allLints, xs)

fileNameFromArgs :: [String] -> Either String String
fileNameFromArgs [x] = Right x
fileNameFromArgs []  = Left "Debe especificar un archivo"
fileNameFromArgs _   = Left "Debe especificar un único archivo"



lint lints action filename = do
  p <- readFile filename
  when debug $ (putStrLn $ "recognized:\n" ++ p) >> sep >> sep
  case parser p of
    Left error -> do
      putStrLn "error de parsing:"
      putStrLn $ show $ error
    Right program@(Program funcs) ->
      case action of
        Suggest -> do
          lintSugg pp lints program
          when
            debug
            ((>>) sep $ putStrLn $
              pp $
              Program $ map (optimizeAllFunc lints) funcs)
          when debug $ putStrLn $ show program
          when debug $ putStrLn $ show
            $ Program $ map (optimizeAllFunc lints) funcs
        SuggestAST -> do
          lintSugg show lints program
          when
            debug
            ((>>) sep $ putStrLn $
              pp $
              Program $ map (optimizeAllFunc lints) funcs)
          when debug $ putStrLn $ show program
          when debug $ putStrLn $ show
            $ Program $ map (optimizeAllFunc lints) funcs
        Compile ->
          putStrLn $
          pp $
          Program $ map (optimizeAllFunc lints) funcs

lintSugg' lint (Program funcs) =
  sequence_ $ map (lintFuncSugg' lint) funcs

lintSugg :: (LintSugg -> String) -> Linting FunDef -> Program -> IO ()
lintSugg disp lint (Program funcs) =
  sequence_ $ map (lintFuncSugg disp lint) funcs

lintFuncSugg' lint f@(FunDef name body) = do
  putStrLn $ "Función: " ++ name
  mapM_ putStrLn $ nilv "Sin sugerencias." $ map pp $ snd $ lintRec lint f
  sep

lintFuncSugg disp lint f@(FunDef name body) = do
  putStrLn $ "Función: " ++ name
  mapM_ putStrLn $ nilv "Sin sugerencias." $ map disp $ snd $ lintRec lint f
  sep

nilv :: a -> [a] -> [a]
nilv v [] = [v]
nilv _ xs = xs

allLints =
         liftToFunc lintComputeConstant
    >==> liftToFunc lintRedBool
    >==> liftToFunc lintRedIfCond
    >==> liftToFunc lintRedIfAnd
    >==> liftToFunc lintRedIfOr
    >==> liftToFunc lintNull
    >==> liftToFunc lintAppend
    >==> liftToFunc lintComp
    >==> liftToFunc lintEta
    >==> lintMap

optimizeAllFunc lints = fst . lintRec lints

usage =
     "Instrucciones:\n"
  ++ "Linter (-s | -v | -c) {flag} <fuente> (compilado)\n"
  ++ "runhaskell Linter.hs (-s | -v | -c) {flag} <fuente> (interpretado)\n"
  ++ "Opciones (exactamente una):\n"
  ++ " -s: imprime sugerencias en la salida estandar\n"
  ++ " -v: imprime el AST de las sugerencias en la salida estandar\n"
  ++ " -c: aplica las sugerencias e imprime el programa resultante\n"
  ++ "Banderas (a lo sumo una): -<nombre lint>"
  ++ "ejemplos:\n"
  ++ "Linter -c ejemplos/ejemplo3.mhs\n"
  ++ "Linter -s ejemplos/ejemplo3.mhs\n"
  ++ "Linter -v ejemplos/ejemplo3.mhs\n"
  ++ "Linter -s -lintEta ejemplos/ejemplo3.mhs\n"
