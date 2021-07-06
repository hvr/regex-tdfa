-- | Like Engine, but merely checks to see whether any match at all is found.
-- 
module Text.Regex.TDFA.NewDFA.Tester(matchTest) where

import qualified Data.IntMap.CharMap2 as CMap(findWithDefault)
import qualified Data.IntMap as IMap(null)
import qualified Data.IntSet as ISet(null)

import Data.Sequence(Seq)
import qualified Data.ByteString.Char8 as SBS(ByteString)
import qualified Data.ByteString.Lazy.Char8 as LBS(ByteString)
import qualified Data.Text as ST(Text)
import qualified Data.Text.Lazy as LT(Text)

import Text.Regex.Base()
import Text.Regex.TDFA.Common hiding (indent)
import Text.Regex.TDFA.NewDFA.Uncons (Uncons(uncons))
import Text.Regex.TDFA.NewDFA.MakeTest(test_singleline,test_multiline)

{-# SPECIALIZE matchTest :: Regex -> [] Char  -> Bool #-}
{-# SPECIALIZE matchTest :: Regex -> Seq Char -> Bool #-}
{-# SPECIALIZE matchTest :: Regex -> ST.Text  -> Bool #-}
{-# SPECIALIZE matchTest :: Regex -> LT.Text  -> Bool #-}
{-# SPECIALIZE matchTest :: Regex -> SBS.ByteString -> Bool #-}
{-# SPECIALIZE matchTest :: Regex -> LBS.ByteString -> Bool #-}
matchTest :: Uncons text => Regex -> text -> Bool
matchTest (Regex { regex_dfa = dfaIn
                 , regex_isFrontAnchored = ifa } )
          inputIn = ans where

  ans = case ifa of
          True -> single0 (d_dt dfaIn) inputIn
          False -> multi0 (d_dt dfaIn) inputIn

  multi0 (Testing' {dt_test=wt,dt_a=a,dt_b=b}) input =
    if test0 wt input
      then multi0 a input
      else multi0 b input
  multi0 (Simple' {dt_win=w,dt_trans=t, dt_other=o}) input
    | IMap.null w =
        case uncons input of
          Nothing -> False
          Just (c,input') ->
            case CMap.findWithDefault o c t of
              Transition {trans_many=DFA {d_dt=dt'}} -> multi dt' c input'
    | otherwise = True

  multi (Testing' {dt_test=wt,dt_a=a,dt_b=b}) prev input =
    if test wt prev input
      then multi a prev input
      else multi b prev input
  multi (Simple' {dt_win=w,dt_trans=t, dt_other=o}) _prev input
    | IMap.null w =
        case uncons input of
          Nothing -> False
          Just (c,input') ->
            case CMap.findWithDefault o c t of
              Transition {trans_many=DFA {d_dt=dt'}} -> multi dt' c input'
    | otherwise = True

  single0 (Testing' {dt_test=wt,dt_a=a,dt_b=b}) input =
    if testFA0 wt input
      then single0 a input
      else single0 b input
  single0 (Simple' {dt_win=w,dt_trans=t, dt_other=o}) input
    | IMap.null w =
        case uncons input of
             Nothing -> False
             Just (c,input') ->
               case CMap.findWithDefault o c t of
                 Transition {trans_single=DFA {d_id=did',d_dt=dt'}}
                   | ISet.null did' -> False
                   | otherwise -> single dt' c input'
    | otherwise = True

  single (Testing' {dt_test=wt,dt_a=a,dt_b=b}) prev input =
    if testFA wt prev input
      then single a prev input
      else single b prev input
  single (Simple' {dt_win=w,dt_trans=t, dt_other=o}) _prev input
    | IMap.null w =
        case uncons input of
             Nothing -> False
             Just (c,input') ->
               case CMap.findWithDefault o c t of
                 Transition {trans_single=DFA {d_id=did',d_dt=dt'}}
                   | ISet.null did' -> False
                   | otherwise -> single dt' c input'
    | otherwise = True

{-# INLINE testFA0 #-}
testFA0 :: Uncons text => WhichTest -> text -> Bool
testFA0 wt text = test_singleline wt 0 '\n' text

{-# INLINE testFA #-}
testFA :: Uncons text => WhichTest -> Char -> text -> Bool
testFA wt prev text = test_singleline wt 1 prev text

{-# INLINE test0 #-}
test0 :: Uncons text => WhichTest -> text -> Bool
test0 wt input = test_multiline wt 0 '\n' input

{-# INLINE test #-}
test :: Uncons text => WhichTest -> Char -> text -> Bool
test wt prev input = test_multiline wt 1 prev input
