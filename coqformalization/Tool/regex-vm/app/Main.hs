module Main where

import Parser (parseRegex)
import Instances
import Semantics hiding (Input)
import Options.Applicative

data Input = FileInput FilePath | StdInput String deriving Show

data Options
  = Options {
      regex :: String
    , input :: Input
    } deriving Show

inputParser :: Parser Input
inputParser = fileInput <|> stdInput

fileInput :: Parser Input
fileInput
  = FileInput <$> strOption ( long "file"
                            <> short 'f'
                            <> metavar "FILENAME"
                            <> help "Input file name")

stdInput :: Parser Input
stdInput
  = StdInput <$> strOption (  long "input"
                           <> short 'i'
                           <> metavar "TEXTINPUT"
                           <> help "Text to be parsed")

optionsParser :: Parser Options
optionsParser
  = Options <$> strOption (long "Regex"    <>
                           short 'R'       <>
                           metavar "REGEX" <>
                           help "regular expression to be used in the parsing algorithm")
                <*> inputParser


main :: IO ()
main = vm =<< execParser opts
       where
         opts = info (optionsParser <**> helper)
                     (  fullDesc
                     <> progDesc "RE parsing tool"
                     <> header "Virtual Machine-based RE parsing tool")

vm :: Options -> IO ()
vm (Options re inp)
  = either regexParseError
           (execute inp)
           (parseRegex re)

regexParseError :: String -> IO ()
regexParseError = putStrLn

execute :: Input -> Regex -> IO ()
execute (FileInput name) re
  = exec re =<< readFile name
execute (StdInput inp) re
  = exec re inp

exec :: Regex -> String -> IO ()
exec re s
  = case interp re s of
      Unknown   -> putStrLn "No match"
      Found _ _ -> putStrLn "Match found" 
