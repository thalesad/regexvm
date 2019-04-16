{-# LANGUAGE TupleSections #-}

module Main where

import Control.Monad
import Data.Maybe
import Instances
import Semantics
import Conversion
import System.TimeIt
import System.Process
import Test.QuickCheck

import qualified Text.Regex.Applicative as A

e1 :: Regex
e1 = Star (Choice (Choice (Chr 'a') (Chr 'b')) (Cat (Chr 'a') (Chr 'b')))

expr1 :: Int -> Regex
expr1 n = Cat (foldl1 Cat (replicate n (Choice (Chr 'a') Eps)))
              (foldl1 Cat (replicate n (Chr 'a')))

email :: Regex
email = Cat (Cat pre (Chr '@')) (Cat mid (Cat dot end))
        where
          lett = foldl1 Choice (map Chr (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['1' .. '9']))
          pre  = Star lett
          mid  = Star lett
          end  = Star lett
          dot  = Chr '.'

asInput :: Int -> String
asInput n = replicate (n * 1000) 'a'

abInput :: Int -> String
abInput n = concat $ replicate (n * 1000) "ab"

applicative :: (Regex, String) -> Bool
applicative (e,s) = isJust $ s A.=~ (toRE e)


vm :: (Regex, String) -> Bool
vm (e,s)
  = case interp e s of
      Unknown -> False
      _       -> True


singleBench :: ((Regex,String) -> Bool) -> -- parse function
               Regex                    -> -- parse thing
               String                   -> -- input string
               IO Double                   -- single run in seconds
singleBench parse ex inp
  = fst <$> timeItT (print (parse (ex,inp)))


benchMedian :: ((Regex,String) -> Bool) -> -- parse function
               Regex                    -> -- parse thing
               String                   -> -- input string
               Int                      -> -- runs
               IO Double                   -- median of runs
benchMedian parse ex inp runs
  = do
       rs <- replicateM runs (singleBench parse ex inp)
       return ((realToFrac $ sum rs) / (fromIntegral $ runs))


benchRuns :: ((Regex,String) -> Bool) -> -- parse function
             Regex                    -> -- parse thing
             (Int -> String)      -> -- input string generation
             [Int]                -> -- input string size
             Int                  -> -- runs
             IO [(Int, Double)]      -- median for size
benchRuns parse ex inpGen sizes runs
  = mapM (\n -> (n,) <$> benchMedian parse ex (inpGen n) runs) sizes


writeBenchResult :: FilePath -> [(Int,Double,Double)] -> IO ()
writeBenchResult file rs
  = do
      let content = foldr step "" rs
          step (n,t,t') ac = show n ++ "," ++ show t ++ "," ++
                             show t' ++ "\n" ++ ac
      writeFile file content

backMedian :: ((Regex,String) -> Bool) -> Int -> [(Int, Regex, String)] -> IO [(Int, Double)]
backMedian parse runs inps
  = mapM (\(i, e, s) -> (i,) <$> benchMedian parse e s runs) inps


-- random (quickcheck based) benchmark

parseProp :: ((Regex,String) -> Bool) -> Property
parseProp parse
  = forAll genInput ((\ x -> x === x) . parse)

randomMedian :: ((Regex,String) -> Bool) -> Int -> Int -> IO Double
randomMedian parse runs size
  = do
      rs <- map fst <$> replicateM runs (timeItT (quickCheckWith (stdArgs {maxSuccess = size, chatty = False}) (parseProp parse)))
      return ((realToFrac $ sum rs) / (fromIntegral $ runs))

singleRandom :: ((Regex,String) -> Bool) -> Int -> Int -> IO (Int, Double)
singleRandom parse runs size
  = (size,) <$> randomMedian parse runs size


randomExec :: Int -> Int -> IO (Int, Double, Double)
randomExec runs size
  = do
      (i,t) <- singleRandom applicative runs size
      (_,t') <- singleRandom vm runs size
      return (i,t,t')

randomBench :: Int -> [Int] -> IO ()
randomBench runs sizes
  = do
       rs <- mapM (randomExec runs) sizes
       writeBenchResult "random.csv" rs

-- backtracking benchmark


backtrack :: [Int] -> Int -> IO ()
backtrack sizes runs
  = do
      let inps = map step sizes
          step n = (n, expr1 n, asInput n)
      rs <- backMedian applicative runs inps
      rs' <- backMedian vm runs inps
      let comb (i,t)(_,t') = (i,t,t')
      rs1 <- backMedian vm runs (map (step . (* 1000)) [1..10])
      writeBenchResult "back.csv" (zipWith comb rs rs')
      writeBenchResult "back1.csv" (zipWith comb rs1 rs1)


-- simple benchmark for (a + b + ab)*


benchmark :: (Int -> String)      -> -- input string generation
             [Int]                -> -- input string size
             Int                  -> -- runs
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
      let sizes = map (* 1000) [1..10]
          runs  = 100
          ss    = map (* 200) [1..10]
      putStrLn "Starting benchmark of parsing a* with (a + b + ab)*"
      benchmark  asInput sizes runs "results-as.csv"
      putStrLn "Starting benchmark of parsing (ab)* with (a + b + ab)*"
      benchmark abInput sizes runs "results-abs.csv"
      putStrLn "Starting benchmark of backtracking RE"
      backtrack ss runs
      putStrLn "Starting benchmark of random REs and strings"
      randomBench 100 (map (* 1000) [1..10])
      _ <- readProcess "gnuplot" ["graph.gp"] ""
      putStrLn "Finished!"
      return ()
