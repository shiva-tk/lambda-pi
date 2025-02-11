module Main where

import LambdaArrow

import Data.List
import System.IO (hFlush, stdout)

main :: IO ()
main = do
  putStrLn "Starting λ→ REPL ..."
  replLoop []

replLoop :: Context -> IO ()
replLoop gamma = do
  putStr "> "
  hFlush stdout
  input <- getLine
  command gamma input

command :: Context -> String -> IO ()
command gamma input
  | input == ":q"               = putStrLn "Exiting λ→ ..."
  | "assume" `isPrefixOf` input = do
      gamma' <- updateContext gamma input
      replLoop gamma'
  | otherwise                   = do
      readEvaluate gamma input
      replLoop gamma

readEvaluate :: Context -> String -> IO ()
readEvaluate gamma input =
  case readInferable input of
    Left err -> putStrLn $ "Parse error: " ++ show err
    Right (e, _) -> do
      case infer gamma e of
        Left err -> putStrLn $ "Type error: " ++ err
        Right t -> do
          let v = evalInferable e []
          putStrLn $ "(" <> (show (quote v)) <> ")" <> " :: " <> show t

updateContext :: Context -> String -> IO Context
updateContext gamma input =
  case readAssume input of
    Left err -> do
      putStrLn $ "Parse error: " ++ show err
      return gamma
    Right gamma' -> return $ gamma ++ gamma'
