module Syntax.Regex where

import Control.Monad
import Test.QuickCheck

data Regex =
    Epsilon
  | Chr Char
  | Regex :@: Regex
  | Regex :+: Regex
  | Star Regex
  deriving (Eq, Show)

infixr 9 :@:
infixr 5 :+:

nullable :: Regex -> Bool
nullable Epsilon = True
nullable (Chr _) = False
nullable (e :@: e') = nullable e && nullable e'
nullable (e :+: e') = nullable e || nullable e'
nullable (Star _) = True


empty :: Regex -> Bool
empty Epsilon = True
empty (Chr _) = False
empty (e :@: e') = empty e && empty e'
empty (e :+: e') = empty e && empty e'
empty (Star e)   = empty e

unprob :: Regex -> Regex
unprob (e :@: e') = unprob e :@: unprob e'
unprob (e :+: e') = unprob e :+: unprob e'
unprob (Star e)
   | not (nullable e) = Star (unprob e)
   | empty e          = Epsilon
   | otherwise        = Star (unprob' e)
unprob e = e

unprob' :: Regex -> Regex
unprob' (e :@: e') = unprob' (e :+: e')
unprob' (e :+: e')
  | empty e && nullable e' = unprob' e'
  | empty e && not (nullable e') = unprob e'
  | nullable e && empty e' = unprob' e
  | not (nullable e) && empty e' = unprob e
  | not (nullable e) && not (empty e') = unprob e :+: unprob' e'
  | not (empty e) && not (nullable e') = unprob' e :+: unprob e'
  | otherwise = unprob' e :+: unprob' e'
unprob' (Star e)
  | nullable e = unprob' e
  | otherwise  = unprob e
unprob' _ = undefined 

-- generating random regexes using quickcheck

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
               (10, return Epsilon), 
               (90, Chr <$> genChar) ]
  | otherwise 
    = frequency
         [
           (10, return Epsilon) ,
           (30, Chr <$> genChar)
         , (20, (:@:) <$> sizedRegex n2 <*> sizedRegex n2)
         , (20, (:+:) <$> sizedRegex n2 <*> sizedRegex n2)
         , (20, Star <$> (sizedRegex n2))
         ]
         where n2 = n `div` 2

-- generating a string that matches a given regex.

randomMatch :: Regex -> Gen String
randomMatch Epsilon
  = return ""
randomMatch (Chr c)
  = return [c]
randomMatch (e :@: e')
  = liftM2 (++) (randomMatch e) (randomMatch e')
randomMatch (e :+: e')
  = do
     b <- arbitrary :: Gen Bool
     if b then randomMatch e
       else randomMatch e'
randomMatch (Star e)
  = do 
      n <- suchThat (choose (0,3) :: Gen Int) (>= 0)
      randomMatches n e

randomMatches :: Int -> Regex -> Gen String
randomMatches m e'
  | m <= 0 = return []
  | otherwise = liftM2 (++) (randomMatch e')
                            (randomMatches (m - 1) e')


randomNonMatch :: Regex -> Gen String
randomNonMatch Epsilon
  = do
     n <- choose (1,4) :: Gen Int
     c <- genChar
     return (replicate n c)
randomNonMatch (Chr c)
  = (\x -> [x]) <$> suchThat genChar (/= c)
randomNonMatch (e :@: e')
  = (++) <$> randomNonMatch e <*> randomNonMatch e'
randomNonMatch (e :+: e')
  = oneof [randomNonMatch e, randomNonMatch e']
randomNonMatch (Star e)
  = do
      s <- randomNonMatch e
      n <- choose (1,4) :: Gen Int
      return (concat (replicate n s))
