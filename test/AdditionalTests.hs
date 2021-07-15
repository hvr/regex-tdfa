{-# OPTIONS_GHC -Wno-name-shadowing #-}
module AdditionalTests ( runAdditionalTests ) where

import Text.Regex.TDFA
import qualified Control.Monad.Writer.Strict as W
import qualified Control.Monad.Reader as R
import Control.Monad.Reader (lift)
import Data.Function
import AdditionalTests.Fencepost
import AdditionalTests.Generate
import Data.List.NonEmpty
import Data.Functor

data SyntaxOptions = NewSyntax
                   | OldSyntax
  deriving (Eq, Ord, Enum, Bounded, Show)

fromSyntaxOpt :: SyntaxOptions -> Bool
fromSyntaxOpt NewSyntax = True
fromSyntaxOpt OldSyntax = False

data LineOption = Multiline
                | SingleLine
  deriving (Eq, Ord, Enum, Bounded, Show)

fromLineOpt :: LineOption -> Bool
fromLineOpt Multiline = False
fromLineOpt SingleLine = True
-- TODO test character classes
data CharacterClasses = Alnum
                      | Digit
                      | Punct
                      | Alpha
                      | Graph
                      | Space
                      | Blank
                      | Lower
                      | Upper
                      | Control
                      | Print
                      | XDigit
                      | Word
  deriving (Eq, Ord, Enum, Bounded)
instance Show CharacterClasses where
  show Alnum = "alnum"
  show Digit = "digit"
  show Punct = "punct"
  show Alpha = "alpha"
  show Graph = "graph"
  show Space = "space"
  show Blank = "blank"
  show Lower = "lower"
  show Upper = "upper"
  show Control = "cntrl"
  show Print = "print"
  show XDigit = "xdigit"
  show Word = "word"

-- This test is a test for boundaries and anchors, and different configurations of the regex engine.
-- Since boundaries only interact with the concatenation regex operator, and union/closure is well
-- covered by existings tests, I ommitted them from my tests. When I did that, I realized since an
-- evaluator doesn't need to make desicsions (union) or backtrack (closure), you can match by doing
-- a simple forward search. So this test suite implements a very simple concatenation-only matcher
-- and compares it against the real one

-- R is for "Regex Character". It describes the set of characters that can occur in a regex in this
-- test suite

data RChar = BufferStartAnchor -- \`
           | BufferEndAnchor   -- \'
             -- \< matches the boundary when the character on the left is a word
             -- ".*\<fly" matches "buzzing fly" and "firefly"
           | WordOnRight       -- \<
             -- same as \< but flipped
           | WordOnLeft        -- \>
             -- \b matches when once character on the boundry is a word, but the other is not
             -- ".*\bfly" matches "buzzing fly", but NOT "firefly"
           | WordBoundary      -- \b
             -- \B is the negation of \b, if \b matches, \B does not, if \b does not match, \B does
           | NotWordBoundary   -- \B
           | LineStartAnchor   -- "^"
           | LineEndAnchor     -- "$"
           | RChar Char        -- c
           | Newline           -- \n
           | Wildcard          -- .
  deriving (Eq, Ord)

instance Show RChar where
  show BufferStartAnchor  = "\\`"
  show BufferEndAnchor    = "\\'"
  show WordOnRight        = "\\<"
  show WordOnLeft         = "\\>"
  show WordBoundary       = "\\b"
  show NotWordBoundary    = "\\B"
  show LineStartAnchor    = "^"
  show LineEndAnchor      = "$"
  show (RChar c)          = show c
  show Newline            = "\\n"
  show Wildcard           = "."

-- SChar stands for "String Character", it is the alphabet for the strings that are generated
-- in this test suite. "Sc" also stands for "String Character", the 'c' is lowercase to help
-- readability
data SChar = ScBacktick    -- `
           | ScQuote       -- '
           | ScAngleOpen   -- <
           | ScAngleClose  -- >
           | ScA           -- a
           | ScB           -- b
           | ScNewLine     -- \n
           | ScUpperB      -- B
  deriving (Eq, Ord, Enum, Bounded)

instance Show SChar where
  show ScBacktick = "`"
  show ScQuote = "'"
  show ScAngleOpen = "<"
  show ScAngleClose = ">"
  show ScA = "a"
  show ScB = "b"
  show ScNewLine = "\n"
  show ScUpperB = "B"

isWord :: SChar -> Bool
isWord ScA = True
isWord ScB = True
isWord ScUpperB = True
isWord _ = False
       -- Right now the tdfa regex engine throws an exception if you try to parse an empty regex.
       -- Online, there doesn't seem to be much agreement about what an empty regex means.
       -- The Posix regex specification just says that a regex can't be empty, javascript has the
       -- empty regex match everything, and to me it would make sense to match only the empty string.
       -- I sidestep the problem by never generating an empty regex in the test suite. 
data TestParams = TestParams { lineOpts :: LineOption
                             , syntax :: SyntaxOptions
                             , regexCase :: [RChar]
                             , strCase :: [SChar] }
instance Show TestParams where
  show (TestParams lo so r s) = concatMap show s ++ " =~ " ++ concatMap show r ++ " Line Mode = " ++ show lo ++ " Syntax = " ++ show so

data MatchStatus = SkipMatch -- Match, but don't move on to the next string character, but do move onto the next regex character
                 | CharMatch -- Match, move on to next string and regex character
                 | NoMatch -- Reject
{-
  Since the GNU extensions for matching the start and end of file in
  multiline mode are just infomal extensions, it is super ambiguous
  what even 'correct' means in that context. The behavior in grep
  doesn't match the behavior in sed. Perl has the same concept with
  '\A' and '\Z', but it again has different behavior. At this point I
  am going to write the test cases according to the current behavior,
  and then document that behavior.

  Since these are just GNU specific extensions, I discovered their
  behavior by poking around with grep and sed. For the purposes of boundaries,
  the start and end of the string is not a word.  
-}
matchSingleChar :: RChar -> FenceCase SChar -> TestM MatchStatus
matchSingleChar b c =
  do syntaxSetting <- syntaxOpt
     lineSetting <- multilineOpt
     multilineWarn lineSetting
     r <- convertSyntax syntaxSetting b
     case r of
       BufferStartAnchor ->
         case c of
           FenceStart c -> skipChar r c
           _ -> reject r (fenceVal c)
       BufferEndAnchor ->
         case c of
           FenceEnd c -> skipChar r c
           _ -> reject r (fenceVal c)
       WordOnRight ->
         case c of
           FenceEnd c -> reject r c
           _ -> skipIfWord r (fenceVal c)
       WordOnLeft ->
         case c of
           FenceStart c -> reject r c
           _ -> skipIfWord r (fenceVal c)
       WordBoundary ->
         case c of
           FenceGap c d -> skipIfWordBoundary r c d
           _ -> skipIfWord r (fenceVal c)
       NotWordBoundary ->
         case c of
           FenceGap c d -> skipIfNotWordBoundary r c d
           FenceStart c -> skipIfNotWord r c
           FenceEnd c -> skipIfNotWord r c
       LineStartAnchor ->
         case lineSetting of
           Multiline ->
             case c of
               FenceStart c -> skip r c
               FenceGap _ c -> skipIfNewline r c
               FenceEnd c -> reject r c
           SingleLine ->
             case c of
               FenceStart c -> skip r c
               _ -> reject r (fenceVal c)
       LineEndAnchor ->
         case lineSetting of
           Multiline ->
             case c of
               FenceStart c -> reject r c
               FenceEnd c -> skip r c
               FenceGap c _ -> skipIfNewline r c
           SingleLine ->
             case c of
               FenceEnd c -> skip r c
               _ -> reject r (fenceVal c)
       RChar r -> matchIfSameChar r (fenceVal c)
       Newline -> matchIfSameChar '\n' (fenceVal c)
       -- If a given regex engine matches '.' with ALL characters or just all non-newline
       -- characters varies wildly between engines.
       -- See: https://stackoverflow.com/a/45981809/3099751
       -- the best bet is to document our current behavior
       Wildcard ->
         case lineSetting of
           Multiline ->
             case fenceVal c of
               ScNewLine -> reject r ScNewLine
               c -> accept r c
           SingleLine -> accept r (fenceVal c)
  where
    accept r c = do
      matchMessage (show r) (show c)
      pure CharMatch
    skipChar r c = do
      matchMessage (show r) (show c)
      pure SkipMatch
    skipIfNewline r ScNewLine = skipChar r ScNewLine
    skipIfNewline r c = reject r c
    matchIfSameChar '`' ScBacktick = do
      matchMessage "`" "`"
      pure CharMatch
    matchIfSameChar '\'' ScQuote = do
      matchMessage "\'" "\'"
      pure CharMatch
    matchIfSameChar '<' ScAngleOpen = do
      matchMessage "<" "<"
      pure CharMatch
    matchIfSameChar '>' ScAngleClose = do
      matchMessage ">" ">"
      pure CharMatch
    matchIfSameChar 'a' ScA = do
      matchMessage "a" "a"
      pure CharMatch
    matchIfSameChar 'b' ScB = do
      matchMessage "b" "b"
      pure CharMatch
    matchIfSameChar '\n' ScNewLine = do
      matchMessage "\\n" "\\n"
      pure CharMatch
    matchIfSameChar 'B' ScUpperB = do
      matchMessage "B" "B"
      pure CharMatch
    matchIfSameChar r c = reject r c
    skipIfNotWord r c
      | isWord c = reject r c
      | otherwise = do
          matchMessage (show r) (show c)
          pure SkipMatch
    skipIfNotWordBoundary r c d
      | isWord c && isWord d = do
          tell (show c ++ " is a word character, and " ++ show d ++ " is a word character. So this is not a word boundary and matches " ++ show r ++ ".")
          pure SkipMatch
      | not (isWord c) && not (isWord d) = do
          tell (show c ++ " is not a word character, and " ++ show d ++ " is not a word character. So this is not a word boundary and matches " ++ show r ++ ".")
          pure SkipMatch
      | otherwise = do
          tell (show c ++ show d ++ " is a word boundary and does not match " ++ show r ++ ".")
          pure NoMatch
    skip r c = do
      matchMessage (show r) (show c)
      pure SkipMatch
    skipIfWordBoundary r c d
      | isWord c && not (isWord d) = do
          tell (show c ++ " is a word character, and " ++ show d ++ " is not a word character. So this isa word boundary and matches " ++ show r ++ ".")
          pure SkipMatch
      | not (isWord c) && isWord d = do
          tell (show c ++ " is not a word character, and " ++ show d ++ " is a word character. So this isa word boundary and matches " ++ show r ++ ".")
          pure SkipMatch
      | otherwise = do
          tell (show c ++ show d ++ " is not a word boundary and does not match " ++ show r ++ ".")
          pure NoMatch
    reject r c = do
      rejectMessage r c
      pure NoMatch
    skipIfWord r c
      | isWord c = skip r c
      | otherwise = reject r c
    convertSyntax :: SyntaxOptions -> RChar -> TestM RChar
    convertSyntax OldSyntax BufferStartAnchor = do
      oldSyntaxWarn BufferStartAnchor
      pure (RChar '`')
    convertSyntax OldSyntax BufferEndAnchor = do
      oldSyntaxWarn BufferEndAnchor
      pure (RChar '\'')
    convertSyntax OldSyntax WordOnRight = do
      oldSyntaxWarn WordOnRight
      pure (RChar '<')
    convertSyntax OldSyntax WordOnLeft = do
      oldSyntaxWarn WordOnLeft
      pure (RChar '>')
    convertSyntax OldSyntax WordBoundary = do
      oldSyntaxWarn WordBoundary
      pure (RChar 'b')
    convertSyntax OldSyntax NotWordBoundary = do
      oldSyntaxWarn NotWordBoundary
      pure (RChar 'B')
    convertSyntax _ b = pure b
    multilineOpt = asks lineOpts
    syntaxOpt = asks syntax
    oldSyntaxWarn :: RChar -> TestM ()
    oldSyntaxWarn c = tell (show c ++ " is not recognized with the old syntax and will be interpreted literally.")
    multilineWarn Multiline = tell "In multiline mode '.' does not match a newline. ^ and $ are both boundaries instead of anchors."
    multilineWarn SingleLine = tell "In singleine mode '.' does matches a newline."
    threePartMessage a b c = tell (show a ++ " " ++ show b ++ " " ++ show c ++ ".")
    matchMessage a b = threePartMessage a "matches" b
    rejectMessage a b = threePartMessage a "does not match" b

matchExactly :: [RChar] -> [SChar] -> TestM Bool
matchExactly [] _ = pure True
matchExactly _ [] = pure False
matchExactly (x:xs) [y] = do
  first <- matchSingleChar x (FenceStart y)
  case first of
    SkipMatch -> matchExactly xs [y]
    CharMatch -> matchExactlyEnd xs y
    NoMatch -> pure False
  where
    matchExactlyEnd [] _ = pure True
    matchExactlyEnd (x:xs) y = do
      first <- matchSingleChar x (FenceEnd y)
      case first of
        SkipMatch -> matchExactlyEnd xs y
        CharMatch -> case xs of
          [] -> pure True
          _ -> pure False
        NoMatch -> pure False
matchExactly (x:xs) (y:z:zs) = do
  first <- matchSingleChar x (FenceStart y)
  case first of
    SkipMatch -> matchExactly xs (y:z:zs)
    CharMatch -> matchInner xs y (z:zs)
    NoMatch -> pure False
  where
    matchInner [] _ _ = pure True
    matchInner (x:xs) y [] = do
      result <- matchSingleChar x (FenceEnd y)
      case result of
        SkipMatch -> matchInner xs y []
        CharMatch -> pure True
        NoMatch -> pure False
    matchInner (x:xs) y (z:zs) = do
      result <- matchSingleChar x (FenceGap y z)
      case result of
        SkipMatch -> matchInner (x:xs) y (z:zs)
        CharMatch -> matchInner (x:xs) z zs
        NoMatch -> pure False

testCaseMatch :: TestM Bool
testCaseMatch = do
  r <- asks regexCase
  s <- asks strCase
  matchAny r s where
    matchAny :: [RChar] -> [SChar] -> TestM Bool
    matchAny r s = unfoldr prefixes s & traverse (matchExactly r) <&> or where
      prefixes [] = ([], Nothing)
      prefixes (x:xs) = (x:xs, Just xs)


-- TODO test caseSensitive, rightAssoc, lastStartGreedy
allTestCases :: [TestParams]
allTestCases = TestParams <$> [Multiline, SingleLine] <*> [NewSyntax, OldSyntax] <*> rchars <*> scchars where
  rchars = allStrs [ BufferStartAnchor
                   , BufferEndAnchor
                   , WordOnRight
                   , WordOnLeft
                   , WordBoundary
                   , NotWordBoundary
                   , LineStartAnchor
                   , LineEndAnchor
                   , RChar 'a'
                   , RChar 'b'
                   , Newline
                   , Wildcard ] 1 3
  scchars = allStrs [ ScBacktick
                    , ScQuote
                    , ScAngleOpen
                    , ScAngleClose
                    , ScA
                    , ScB
                    , ScNewLine
                    , ScUpperB ] 0 3

mkRegex :: TestParams -> Regex
mkRegex regTestCase =
  makeRegexOpts
    CompOption { caseSensitive = True
               , multiline = fromLineOpt (lineOpts regTestCase)
               , rightAssoc = True
               , newSyntax = fromSyntaxOpt (syntax regTestCase)
               , lastStarGreedy = False }
    ExecOption { captureGroups = True }
    (concatMap show (regexCase regTestCase) :: String)

newtype TestM a = TestM (R.ReaderT TestParams (W.Writer [String]) a)

instance Functor TestM where
  fmap f (TestM r) = TestM (fmap f r)

instance Applicative TestM where
  pure = TestM . pure
  (<*>) (TestM f) (TestM a) = TestM (f <*> a)

instance Monad TestM where
  (>>=) (TestM aM) fM = TestM (aM >>= (\a -> let (TestM b) = fM a in b))

tell :: String -> TestM ()
tell s = TestM (lift (W.tell [s]))

asks :: (TestParams -> a) -> TestM a
asks f = TestM (R.asks f)

runTestM :: TestParams -> TestM a -> (a, String)
runTestM tp (TestM r) = let (a, log) = W.runWriter (R.runReaderT r tp)
                        in (a, unlines log)

evalTestCase :: TestParams -> (Bool, String)
evalTestCase tp = runTestM tp testCaseMatch

runTestCase :: TestParams -> IO Bool
runTestCase tp = let (expectedResult, log) = evalTestCase tp
                     r = mkRegex tp
                     s = foldMap show (strCase tp) :: String
                     actualResult = match r s :: Bool
                 in do putStrLn log
                       putStrLn ("The expected result is " ++ show expectedResult)
                       putStrLn ("The regex tdfa result is " ++ show actualResult)
                       if expectedResult == actualResult
                         then do putStrLn "The expected result matches the result from the regex engine. The test passes."
                                 pure True
                         else do putStrLn "The expected result does not match the result from the regex engine. The test fails."
                                 pure False
                                 

runAdditionalTests :: IO Bool
runAdditionalTests = do
  bs <- traverse runTestCase allTestCases
  pure (and bs)
