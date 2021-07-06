-- | This is the non-capturing form of Text.Regex.TDFA.NewDFA.String
module Text.Regex.TDFA.NewDFA.Engine_NC_FA(execMatch) where

import Control.Monad(unless)
import Prelude hiding ((!!))

import Data.Array.MArray(MArray(..))
import Data.Array.Unsafe(unsafeFreeze)
import Data.Array.ST(STArray)
import qualified Data.IntMap.CharMap2 as CMap(findWithDefault)
import qualified Data.IntMap as IMap(null)
import qualified Data.IntSet as ISet(null)
import qualified Data.Array.MArray()
import Data.STRef(newSTRef,readSTRef,writeSTRef)
import qualified Control.Monad.ST.Strict as S(ST,runST)
import Data.Sequence(Seq)
import qualified Data.ByteString.Char8 as SBS(ByteString)
import qualified Data.ByteString.Lazy.Char8 as LBS(ByteString)
import qualified Data.Text as ST(Text)
import qualified Data.Text.Lazy as LT(Text)

import Text.Regex.Base(MatchArray,MatchOffset,MatchLength)
import Text.Regex.TDFA.Common hiding (indent)
import Text.Regex.TDFA.NewDFA.Uncons(Uncons(uncons))
import Text.Regex.TDFA.NewDFA.MakeTest(test_singleline)

--import Debug.Trace

-- trace :: String -> a -> a
-- trace _ a = a

{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> [] Char  -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> Seq Char -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> ST.Text  -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> LT.Text  -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> SBS.ByteString -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> LBS.ByteString -> [MatchArray] #-}
execMatch :: Uncons text => Regex -> Position -> Char -> text -> [MatchArray]
execMatch (Regex { regex_dfa = DFA {d_dt=dtIn} })
          offsetIn _prevIn inputIn = S.runST goNext where

  test wt off input = test_singleline wt off '\n' input

  goNext = {-# SCC "goNext" #-} do
    winQ <- newSTRef Nothing
    let next dt offset input = {-# SCC "goNext.next" #-}
          case dt of
            Testing' {dt_test=wt,dt_a=a,dt_b=b} ->
              if test wt offset input
                then next a offset input
                else next b offset input
            Simple' {dt_win=w,dt_trans=t, dt_other=o} -> do
              unless (IMap.null w) $
                writeSTRef winQ (Just offset)
              case uncons input of
                Nothing -> finalizeWinner
                Just (c,input') -> do
                  case CMap.findWithDefault o c t of
                    Transition {trans_single=DFA {d_id=did',d_dt=dt'}}
                      | ISet.null did' -> finalizeWinner
                      | otherwise ->
                          let offset' = succ offset
                          in seq offset' $ next dt' offset' input'

        finalizeWinner = do
          mWinner <- readSTRef winQ
          case mWinner of
            Nothing -> return []
            Just winner -> mapM (makeGroup offsetIn) [winner]

    next dtIn offsetIn inputIn

----

{- CONVERT WINNERS TO MATCHARRAY -}

makeGroup :: Position -> Position -> S.ST s MatchArray
makeGroup start stop = do
  ma <- newArray (0,0) (start,stop-start)  :: S.ST s (STArray s Int (MatchOffset,MatchLength))
  unsafeFreeze ma
