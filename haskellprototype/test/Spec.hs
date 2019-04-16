{-# LANGUAGE StandaloneDeriving #-}

module Main where

import Control.Monad

import Data.Maybe(fromJust, isJust, isNothing)

import Syntax.Regex
import Syntax.Tree
import Semantics.Accept
import Semantics.ThompsonMachine
import Semantics.MaybeMachine

import Test.QuickCheck


absMatcherCorrect :: Regex -> String -> Property
absMatcherCorrect e s
  = let (r,bs) = taccept s e
    in (accept e s === r) .&&. validCode s bs e

maybeMatcherCorrect :: Regex -> String -> Property
maybeMatcherCorrect e s
  = ((isJust r) === accept e s) .&&. ((isNothing r) || validCode s (fromJust r) e)
    where
      r = Semantics.MaybeMachine.vm s e

validCode :: String -> Code -> Regex -> Bool
validCode _ [] _ = True
validCode s bs e = case decode e bs of
                     Just t -> and [tc t e, flatten t == s, code t e == bs]
                     _      -> False

genInput :: Gen (Regex, String)
genInput
   = do
       e <- arbitrary :: Gen Regex
       s <- randomMatch e
       return (e, s)

genNonInput :: Gen (Regex, String)
genNonInput
  = do
      e <- liftM unprob $ arbitrary :: Gen Regex
      s <- randomNonMatch e
      return (e, s)

absMatcherNonProp :: Property
absMatcherNonProp = forAll genNonInput (\(e,s) -> absMatcherCorrect e s)

absMatcherProp :: Property
absMatcherProp
  = forAll genInput (\(e,s) -> absMatcherCorrect e s) 

deriving instance Eq Bit

genInputCorrect :: Property
genInputCorrect = forAll genInput (uncurry accept)


maybeMatcherProp :: Property
maybeMatcherProp = forAll genInput (uncurry maybeMatcherCorrect)

maybeMatcherNonProp :: Property
maybeMatcherNonProp = forAll genNonInput (uncurry maybeMatcherCorrect)

unprobProp :: Property
unprobProp = forAll genInput (\(e,s) -> accept e s === accept (unprob e) s)



main :: IO ()
main = do
         quickCheckWith stdArgs { maxSuccess = 100000 } unprobProp
         quickCheckWith stdArgs { maxSuccess = 100000 } absMatcherProp
         quickCheckWith stdArgs { maxSuccess = 100000 } absMatcherNonProp
         quickCheckWith stdArgs { maxSuccess = 100000 } maybeMatcherProp
         quickCheckWith stdArgs { maxSuccess = 100000 } maybeMatcherNonProp
  
