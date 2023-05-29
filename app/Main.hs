{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import FirstOrder
import Parser hiding (one)
import System.IO

prover = tautology

main :: IO ()
main = do
  eof <- hIsEOF stdin
  if eof
    then return ()
    else do
      line <- getLine -- read the input
      let phi = parseString line -- call the parser
      let res = prover phi -- call the prover
      if res
        then putStrLn "1" -- write 1 if the formula is a tautology
        else putStrLn "0" -- write 0 if the formula is not a tautology