{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds             #-}

module Main where

import           Control.Applicative  as App
import           Control.Monad
import qualified Control.Monad.Fail   as Fail
import           Data.Array
import qualified Data.ByteString      as BS
import qualified Data.ByteString.UTF8 as UTF8
import           Data.List
import           Data.String
import           Data.Typeable
import           Data.Version         ()
import           System.Directory     (getDirectoryContents)
import           System.Environment
import           System.Exit
import           System.FilePath      ((</>))
import           Text.Regex.Base

import qualified Text.Regex.TDFA      as TDFA

import           AdditionalTests

default(Int)

type RSource = String
type RType = String -- can be changed to any Extract instance
newtype RegexSource = RegexSource {unSource :: RSource} deriving Show
newtype RegexStringOf a = RegexString {unString :: a} deriving Show
type RegexString = RegexStringOf RType

dictionary :: [Char]
dictionary = ['a'..'c']++['A'..'C']++"_"


type A = Array Int (Int,Int)

maxItems :: Int
maxItems=100

testOne :: t -> (t -> t1 -> Array Int (Int, Int)) -> t1 -> String
testOne s op r =
  let foo ::  String
      foo = concatMap (\(o,l) -> show (o,(o+l))) (take maxItems $ elems (op s r :: Array Int (Int,Int)))
  in if null foo then "NOMATCH" else foo

testOne' :: A -> String
testOne' input =
  let foo ::  String
      foo = concatMap (\(o,l) -> show (o,(o+l))) (take maxItems $ elems input)
  in if null foo then "NOMATCH" else foo

toTest :: String -> (Int,String,String,String)
toTest line = let [n,regex,input,output] = words line
                  noQ []       = []
                  noQ ('?':xs) = '-':'1':noQ xs
                  noQ (x:xs)   = x:noQ xs
                  input' = if input == "NULL" then "" else unN input
              in (read n,regex,input',noQ output)

toTest' :: String -> String -> (String,(Int,String,String,String))
toTest' oldRegex line =
  let [n,regex,input,output] = words line
      noQ []       = []
      noQ ('?':xs) = '-':'1':noQ xs
      noQ (x:xs)   = x:noQ xs
      input' = if input == "NULL" then "" else input
      regex' = if regex == "SAME" then oldRegex else regex
  in (regex',(read n,regex',input',noQ output))

load,load' :: String -> [(Int, String, String, String)]
load = map toTest . lines
load' = snd . mapAccumL toTest' "X_X_X_" . lines

checkTest :: PFT A -> (Int,String,String,String) -> IO [Int]
checkTest opM (n,regex,input,output) = do
  let Result output'e = opM input regex
      p = putStrLn
  p ""
  case output'e of
    Left msg -> do
      p ("############################# Unexpected Error # "++show n ++ " #############################" )
      p ("Searched text: "++show input)
      p ("Regex pattern: "++show regex)
      p ("Expected output: "++show output)
      p ("Error message: "++msg)
      return [n]
    Right output'a -> do
      let output' = testOne' output'a
      case (n<0 , output==output') of
        (False,True) -> p ("Expected Pass #"++show n)
        (False,False) -> p ("############################# Unexpected Fail # "++show n ++ " #############################" )
        (True,True) -> p ("############################# Unexpected Pass # "++show n ++ " #############################" )
        (True,False) ->  p ("Expected Fail #"++show n)
      if (output == output')
        then do p ("text and pattern: "++show input)
                p ("Regex pattern: "++show regex)
                p ("Outputs agree: "++show output)
                return (if n<0 then [n] else [])
        else do p ""
                p ("Searched text: "++show input)
                p ("Regex pattern: "++show regex)
                p ("Expected output: "++show output)
                p ("Actual result  : "++show output')
                return (if n<0 then [] else [n])

checkFile :: (RType -> RSource -> Result A) -> (FilePath, String) -> IO (FilePath,[Int])
checkFile opM (filepath, contents) = do
  putStrLn $ "\nUsing Tests from: "++filepath
  vals <- liftM concat (mapM (checkTest opM) (load' contents))
  return (filepath,vals)

checkTests :: (RType -> RSource -> Result A) -> [(FilePath,String)] -> IO [(String, [Int])]
checkTests opM testCases = mapM (checkFile opM) testCases

readTestCases :: FilePath -> IO [(String, String)]
readTestCases folder = do
  fns <- filter (isSuffixOf ".txt") <$> getDirectoryContents folder
  when (null fns) $
    fail ("readTestCases: No test-cases found in " ++ show folder)
  forM (sort fns) $ \fn -> do
    bs <- BS.readFile (folder </> fn)
    return (fn, UTF8.toString bs)

newtype Result a = Result (Either String a)
  deriving (Eq, Show, Functor, App.Applicative, Monad)

instance Fail.MonadFail Result where
  fail = Result . Left

type PFT a = RegexContext TDFA.Regex RType a => RType -> RSource -> Result a

posix :: PFT a
posix x reg =
  let q :: Result TDFA.Regex
      q = makeRegexOptsM (defaultCompOpt { TDFA.caseSensitive = False}) defaultExecOpt reg
  in q >>= \ s -> return (match s x)

unN :: String -> String
unN ('\\':'n':xs) = '\n':unN xs
unN (x:xs)        = x:unN xs
unN []            = []

manual :: [String] -> IO ()
manual [sIn,rIn] = do
  let s :: RType
      r :: String
      s = fromString (unN sIn)
      r = (unN rIn)
  -- first match
  let r1 :: TDFA.Regex
      r1 = makeRegex r
  let b1u@(_,_b1s,_,_)=(match r1 s :: (RType,RType,RType,[RType]))
  putStrLn ("Searched text: "++show s)
  putStrLn ("Regex pattern: "++show r)
  print b1u
  -- multiple matches and counting
  let b1 = (match r1 s :: [MatchArray])
      c1 = (match r1 s :: Int)
  putStrLn $ "Count of matches = "++show c1
  putStrLn $ "Matches found = "++show (length b1)
  mapM_ (putStrLn . testOne') b1
manual _ = error "wrong arguments to regex-posix-unittest's manual function"

main :: IO ()
main = do
  putStr "Testing Text.Regex.TDFA version: "
  print TDFA.getVersion_Text_Regex_TDFA
  a <- getArgs
  if length a == 2
    then manual a
    else do
      putStrLn $ "Explanation and discussion of these tests on the wiki at http://www.haskell.org/haskellwiki/Regex_Posix including comparing results from different operating systems"
      putStrLn $ "Questions about this package to the author at email <TextRegexLazy@personal.mightyreason.com>"
      putStrLn $ "The type of both the pattern and test is " ++ show (typeOf (undefined :: RType))
      putStrLn $ "Without extactly two arguments:"
      putStrLn $ "    This program runs all test files listed in test/data-dir/test-manifest.txt"
      putStrLn $ "    Lines with negative number are expected to fail, others are expected to pass."
      putStrLn $ "With exactly two arguments:"
      putStrLn $ "    The first argument is the text to be searched."
      putStrLn $ "    The second argument is the regular expression pattern to search with."
      vals <- checkTests posix =<< readTestCases ("test" </> "cases")
      anchorAndBoundaryTests <- runAdditionalTests 
      if null (concatMap snd vals) && anchorAndBoundaryTests
        then do
          putStrLn "\nWow, all the tests passed!"
        else do
          putStrLn $ "\nBoo, tests failed!\n"++unlines (map show vals)
          exitFailure

{-
-- for TRE
posix x r = let q :: Posix.Regex
                q = makeRegexOpts (defaultCompOpt .|. Posix.compRightAssoc .|. Posix.compIgnoreCase) defaultExecOpt r
            in match q x

tdfa x r = let q :: TDFA.Wrap.Regex
               q = makeRegexOpts (defaultCompOpt { TDFA.Wrap.caseSensitive = False
                                                 , TDFA.Wrap.rightAssoc = True }) defaultExecOpt r
           in match q x

tdfa2 x r = let q :: TDFA2.Wrap.Regex
                q = makeRegexOpts (defaultCompOpt { TDFA2.Wrap.caseSensitive = False
                                                  , TDFA2.Wrap.rightAssoc = True }) defaultExecOpt r
            in match q x
-}
