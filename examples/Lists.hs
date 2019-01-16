-- Some usual list functions.
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, RankNTypes, ConstraintKinds, FlexibleContexts #-}
import QuickSpec

import Data.List

prop_delete :: Integer -> [Integer] -> Bool
prop_delete x xs = x `notElem` delete x xs

count x = length . filter (==x)

main = quickSpec [
  withMaxTests 1000,
  
--  con "map" (map :: (A -> B) -> [A] -> [B]),
--  con "length" (length :: [A] -> Int),
--  con "concat" (concat :: [[A]] -> [A]),
  predicate "prop_delete" prop_delete,
  predicate "not_prop_delete"  ((not .) . prop_delete),
  

  background [ 
  predicate "/=" ((/=) :: Int -> Int -> Bool),
  predicate "/=" ((/=) :: Integer -> Integer -> Bool),
  con "False" False,
  con "count" (count :: Integer -> [Integer] -> Int),
  predicate "<=" ((<=) :: Int -> Int -> Bool),
  predicate "<=" ((<=) :: Integer -> Integer -> Bool),
  con "delete" (delete :: Integer -> [Integer] -> [Integer]),
  con "reverse" (reverse :: [A] -> [A]),
  con "++" ((++) :: [A] -> [A] -> [A]),
  con "[]" ([] :: [A]) ],

  -- Add some numeric functions to get more laws about length.
  arith (Proxy :: Proxy Int) ]
