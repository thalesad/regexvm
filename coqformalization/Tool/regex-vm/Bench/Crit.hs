{-# LANGUAGE TupleSections #-}

module Crit where

import Control.Monad
import Data.Maybe
import Instances
import Semantics
import Conversion
import Test.QuickCheck
import Criterion.Main

import qualified Text.Regex.Applicative as A

tests :: [Integer]
tests = [1..20]

e1 :: Regex
e1 = Star (Choice (Choice (Chr 'a') (Chr 'b')) (Cat (Chr 'a') (Chr 'b')))

expr1 :: Integer -> Regex
expr1 n = Cat (foldl1 Cat (replicate' n (Choice (Chr 'a') Eps)))
              (foldl1 Cat (replicate' n (Chr 'a')))


applicative :: (Regex, String) -> Bool
applicative (e,s) = isJust $ s A.=~ (toRE e)


vm :: (Regex, String) -> Bool
vm (e,s)
  = isJust (interp e s)

replicate' :: Integer -> a -> [a]
replicate' n x
  | n <= 0 = []
  | otherwise = x : replicate' (n - 1) x

abInput :: Integer -> String
abInput n = concat $ replicate' (1000 * n) "ab"

aInput :: Integer -> String
aInput n = replicate' (1000 * n) 'a'

step s f g n = bench (s ++ show n) $ nf f (g n)

vm1 s = vm (e1, s)

app1 s = applicative (e1, s)

vm2 n s = vm (expr1 n, s)
app2 n s = applicative (expr1 n, s)

main :: IO ()
main
  = defaultMain
    [
      bgroup "abs" 
        [
          bgroup
             "vm"
             (map (step "vm " vm1 abInput) [1..50])
        ,
          bgroup
             "applicative"
             (map (step "re-app " app1 abInput) [1..50])
        ]
    , bgroup "as" 
        [
          bgroup
             "vm"
             (map (step "vm " vm1 aInput) [1..50])
        ,
          bgroup
             "applicative"
             (map (step "re-app " app1 aInput) [1..50])
        ]
    , bgroup "backtracking"
        [
          bgroup
             "vm"
             (map (\ n -> step "vm " (vm2 n) aInput n) [1..50])
        ,
          bgroup
             "applicative"
             (map (\ n -> step "re-app " (app2 n) aInput n) [1..50])
        ]
    ]
