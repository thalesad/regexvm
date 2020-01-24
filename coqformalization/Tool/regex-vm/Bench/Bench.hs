{-# LANGUAGE TupleSections #-}

module Bench where

import Control.Monad
import Data.Maybe
import Instances
import Semantics
import Conversion
import System.TimeIt
import System.Process
import Test.QuickCheck

import qualified Text.Regex.Applicative as A

tests :: [Integer]
tests = [1..20]

e1 :: Regex
e1 = Star (Choice (Choice (Chr 'a') (Chr 'b')) (Cat (Chr 'a') (Chr 'b')))

expr1 :: Integer -> Regex
expr1 n = Cat (foldl1 Cat (replicate' n (Choice (Chr 'a') Eps)))
              (foldl1 Cat (replicate' n (Chr 'a')))

email :: Regex
email = Cat (Cat pre (Chr '@')) (Cat mid (Cat dot end))
        where
          lett = foldl1 Choice (map Chr (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['1' .. '9']))
          pre  = Star lett
          mid  = Star lett
          end  = Star lett
          dot  = Chr '.'

replicate' :: Integer -> a -> [a]
replicate' n x
  | n <= 0 = []
  | otherwise = x : replicate' (n - 1) x

replicateM' :: Monad m => Integer -> m a -> m [a]
replicateM' n m
  | n <= 0 = return []
  | otherwise
    = (:) <$> m <*> replicateM' (n - 1) m

asInput :: Integer -> String
asInput n = replicate' (n * 1000) 'a'

abInput :: Integer -> String
abInput n = concat $ replicate' (n * 1000) "ab"

applicative :: (Regex, String) -> Bool
applicative (e,s) = isJust $ s A.=~ (toRE e)


vm :: (Regex, String) -> Bool
vm (e,s)
  = isJust (interp e s)


singleBench :: ((Regex,String) -> Bool) -> -- parse function
               Regex                    -> -- parse thing
               String                   -> -- input string
               IO Double                   -- single run in seconds
singleBench parse ex inp
  = fst <$> timeItT (return (parse (ex,inp)))


benchMedian :: ((Regex,String) -> Bool) -> -- parse function
               Regex                    -> -- parse thing
               String                   -> -- input string
               Integer                  -> -- runs
               IO Double                   -- median of runs
benchMedian parse ex inp runs
  = do
       let runs1 = runs * 100
       rs <- replicateM' runs1 (singleBench parse ex inp)
       return ((realToFrac $ sum rs) / (fromIntegral runs1))


benchRuns :: ((Regex,String) -> Bool) -> -- parse function
             Regex                    -> -- parse thing
             (Integer -> String)      -> -- input string generation
             [Integer]                -> -- input string size
             Integer                  -> -- runs
             IO [(Integer, Double)]      -- median for size
benchRuns parse ex inpGen sizes runs
  = mapM (\n -> (n,) <$> benchMedian parse ex (inpGen n) runs) sizes


writeBenchResult :: FilePath -> [(Integer,Double,Double)] -> IO ()
writeBenchResult file rs
  = do
      let content = foldr step "" rs
          step (n,t,t') ac = show n ++ "," ++ show t ++ "," ++
                             show t' ++ "\n" ++ ac
      writeFile file content

backMedian :: ((Regex,String) -> Bool) -> Integer -> [(Integer, Regex, String)] -> IO [(Integer, Double)]
backMedian parse runs 
  = mapM (\(i, e, s) -> (i,) <$> benchMedian parse e s runs) 


-- random (quickcheck based) benchmark

parseProp :: ((Regex,String) -> Bool) -> Property
parseProp parse
  = forAll genInput ((\ x -> x === x) . parse)

randomMedian :: ((Regex,String) -> Bool) -> Integer -> Integer -> IO Double
randomMedian parse runs size
  = do
      rs <- map fst <$> replicateM (fromInteger runs) (timeItT (quickCheckWith (stdArgs {maxSuccess = (fromInteger size), chatty = False}) (parseProp parse)))
      return ((realToFrac $ sum rs) / (fromIntegral runs))

singleRandom :: ((Regex,String) -> Bool) -> Integer -> Integer -> IO (Integer, Double)
singleRandom parse runs size
  = (size,) <$> randomMedian parse runs size


randomExec :: Integer -> Integer -> IO (Integer, Double, Double)
randomExec runs size
  = do
      (i,t) <- singleRandom applicative runs size
      (_,t') <- singleRandom vm runs size
      return (i,t,t')

randomBench :: Integer -> [Integer] -> IO ()
randomBench runs sizes
  = do
       rs <- mapM (randomExec runs) sizes
       writeBenchResult "random.csv" rs

-- backtracking benchmark


backtrack :: [Integer] -> Integer -> IO ()
backtrack sizes runs
  = do
      let inps = map step sizes
          step n = (n, expr1 n, asInput n)
      rs <- backMedian applicative runs inps
      rs' <- backMedian vm runs inps
      let comb (i,t)(_,t') = (i,t,t')
      rs1 <- backMedian vm runs (map (step . (* 1000)) tests)
      writeBenchResult "back.csv" (zipWith comb rs rs')
      writeBenchResult "back1.csv" (zipWith comb rs1 rs1)


-- simple benchmark for (a + b + ab)*


benchmark :: (Integer -> String)      -> -- input string generation
             [Integer]                -> -- input string size
             Integer                  -> -- runs
             FilePath             -> -- output file name
             IO ()
benchmark inGen sizes runs file
  = do
      rs <- benchRuns applicative e1 inGen sizes runs
      rs' <- benchRuns vm e1 inGen sizes runs
      let comb (i,t)(_,t') = (i,t,t')
      writeBenchResult file (zipWith comb rs rs')

main :: IO ()
main   
  = do
      let
          runs  = 100
          ss    = map (* 200) tests
          sis   = take 20 (iterate (*10) 1) 
      -- putStrLn "Starting benchmark of parsing a* with (a + b + ab)*"
      -- benchmark  asInput sis runs "results-as.csv"
      -- putStrLn "Starting benchmark of parsing (ab)* with (a + b + ab)*"
      -- benchmark abInput sis runs "results-abs.csv"
      -- putStrLn "Starting benchmark of backtracking RE"
      -- backtrack sis runs
      putStrLn "Starting benchmark of random REs and strings"
      randomBench 30 (map (* 1000) tests)
      _ <- readProcess "gnuplot" ["graph.gp"] ""
      putStrLn "Finished!"
      return ()
