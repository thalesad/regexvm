{-# LANGUAGE StandaloneDeriving #-}

module Instances where

import Control.Monad
import Semantics
import Test.QuickCheck

deriving instance Show Regex
deriving instance Eq Regex
deriving instance Show Bit


parens :: String -> String
parens s = "(" ++ s ++ ")" 

genChar :: Gen Char
genChar = elements (['a'.. 'z'] ++ ['1'.. '9'])

instance Arbitrary Regex where
  arbitrary
    = do
        n <- choose (1,5)
        unprob <$> sizedRegex n

sizedRegex :: Int -> Gen Regex
sizedRegex n
  | n <= 1 =  frequency
              [
               (10, return Eps), 
               (90, Chr <$> genChar) ]
  | otherwise 
    = frequency
         [
           (10, return Eps) ,
           (30, Chr <$> genChar)
         , (20, Cat <$> sizedRegex n2 <*> sizedRegex n2)
         , (20, Choice <$> sizedRegex n2 <*> sizedRegex n2)
         , (20, Star <$> (sizedRegex n2))
         ]
         where n2 = n `div` 2

randomMatch :: Regex -> Gen String
randomMatch Eps
  = return ""
randomMatch (Chr c)
  = return [c]
randomMatch (Cat e e')
  = liftM2 (++) (randomMatch e) (randomMatch e')
randomMatch (Choice e e')
  = do
     b <- arbitrary :: Gen Bool
     if b then randomMatch e
       else randomMatch e'
randomMatch (Star e)
  = do 
      n <- suchThat (choose (0,3) :: Gen Int) (>= 0)
      randomMatches n e
randomMatch _ = error "Impossible!"

randomMatches :: Int -> Regex -> Gen String
randomMatches m e'
  | m <= 0 = return []
  | otherwise = liftM2 (++) (randomMatch e')
                            (randomMatches (m - 1) e')


genInput :: Gen (Regex,String)
genInput
  = do
      e <- arbitrary :: Gen Regex
      liftM (\s -> (e,s)) (randomMatch e)
