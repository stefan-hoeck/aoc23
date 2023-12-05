module Util

import Data.Fuel
import Data.List1
import public Data.String
import System.File

%default total

export
trimSplit : Char -> String -> List String
trimSplit c = map trim . forget . split (c ==)

export
lines : String -> IO (List String)
lines file =
  let path := "resources/\{file}.txt"
   in do
     Right (_,ls) <- readFilePage 0 (limit 1_000_000) path
       | Left err => putStrLn "Error when reading \{path}: \{show err}" $> []
     pure (filter ("" /=) $ map trim ls)

export covering
text : String -> IO String
text file =
  let path := "resources/\{file}.txt"
   in do
     Right s <- readFile path
       | Left err => putStrLn "Error when reading \{path}: \{show err}" $> ""
     pure s
