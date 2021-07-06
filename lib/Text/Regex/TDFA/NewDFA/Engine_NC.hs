-- | This is the non-capturing form of Text.Regex.TDFA.NewDFA.String
module Text.Regex.TDFA.NewDFA.Engine_NC(execMatch) where

import Control.Monad(when,join,filterM)
import Data.Array.Base(unsafeRead,unsafeWrite)
import Prelude hiding ((!!))

import Data.Array.MArray(MArray(..))
import Data.Array.Unsafe(unsafeFreeze)
import Data.Array.IArray(Ix)
import Data.Array.ST(STArray,STUArray)
import qualified Data.IntMap.CharMap2 as CMap(findWithDefault)
import qualified Data.IntMap as IMap(null,toList,keys,member)
import qualified Data.IntSet as ISet(toAscList)
import Data.STRef(STRef,newSTRef,readSTRef,writeSTRef)
import qualified Control.Monad.ST.Lazy as L(runST,strictToLazyST)
import qualified Control.Monad.ST.Strict as S(ST)
import Data.Sequence(Seq)
import qualified Data.ByteString.Char8 as SBS(ByteString)
import qualified Data.ByteString.Lazy.Char8 as LBS(ByteString)
import qualified Data.Text as ST(Text)
import qualified Data.Text.Lazy as LT(Text)

import Text.Regex.Base(MatchArray,MatchOffset,MatchLength)
import qualified Text.Regex.TDFA.IntArrTrieSet as Trie(lookupAsc)
import Text.Regex.TDFA.Common hiding (indent)
import Text.Regex.TDFA.NewDFA.Uncons(Uncons(uncons))
import Text.Regex.TDFA.NewDFA.MakeTest(test_singleline,test_multiline)

-- import Debug.Trace

-- trace :: String -> a -> a
-- trace _ a = a

err :: String -> a
err s = common_error "Text.Regex.TDFA.NewDFA.Engine_NC"  s

{-# INLINE (!!) #-}
(!!) :: (MArray a e (S.ST s),Ix i) => a i e -> Int -> S.ST s e
(!!) = unsafeRead
{-# INLINE set #-}
set :: (MArray a e (S.ST s),Ix i) => a i e -> Int -> e -> S.ST s ()
set = unsafeWrite

{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> [] Char  -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> Seq Char -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> ST.Text  -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> LT.Text  -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> SBS.ByteString -> [MatchArray] #-}
{-# SPECIALIZE execMatch :: Regex -> Position -> Char -> LBS.ByteString -> [MatchArray] #-}
execMatch :: Uncons text => Regex -> Position -> Char -> text -> [MatchArray]
execMatch (Regex { regex_dfa = (DFA {d_id=didIn,d_dt=dtIn})
                 , regex_init = startState
                 , regex_b_index = b_index
                 , regex_trie = trie
                 , regex_compOptions = CompOption { multiline = newline } } )
          offsetIn prevIn inputIn = L.runST runCaptureGroup where

  !test = mkTest newline         

  runCaptureGroup = {-# SCC "runCaptureGroup" #-} do
    obtainNext <- L.strictToLazyST constructNewEngine
    let loop = do vals <- L.strictToLazyST obtainNext
                  if null vals -- force vals before defining valsRest
                    then return []
                    else do valsRest <- loop
                            return (vals ++ valsRest)
    loop

  constructNewEngine :: S.ST s (S.ST s [MatchArray])
  constructNewEngine =  {-# SCC "constructNewEngine" #-} do
    storeNext <- newSTRef undefined
    writeSTRef storeNext (goNext storeNext)
    let obtainNext = join (readSTRef storeNext)
    return obtainNext

  goNext storeNext = {-# SCC "goNext" #-} do
    (SScratch s1In s2In winQ) <- newScratch b_index
    set s1In startState offsetIn
    writeSTRef storeNext (err "obtainNext called while goNext is running!")
    eliminatedStateFlag <- newSTRef False
    let next s1 s2 did dt offset prev input = {-# SCC "goNext.next" #-}
          case dt of
            Testing' {dt_test=wt,dt_a=a,dt_b=b} ->
              if test wt offset prev input
                then next s1 s2 did a offset prev input
                else next s1 s2 did b offset prev input
            Simple' {dt_win=w,dt_trans=t, dt_other=o}
              | IMap.null w ->
                  case uncons input of
                    Nothing -> finalizeWinners
                    Just (c,input') -> do
                      case CMap.findWithDefault o c t of
                        Transition {trans_many=DFA {d_id=did',d_dt=dt'},trans_how=dtrans} ->
                          findTrans s1 s2 did' dt' dtrans offset c input'
              | otherwise -> do
                  (did',dt') <- processWinner s1 did dt w offset
                  next' s1 s2 did' dt' offset prev input

        next' s1 s2 did dt offset prev input = {-# SCC "goNext'.next" #-}
          case dt of
            Testing' {dt_test=wt,dt_a=a,dt_b=b} ->
              if test wt offset prev input
                then next' s1 s2 did a offset prev input
                else next' s1 s2 did b offset prev input
            Simple' {dt_trans=t, dt_other=o} ->
              case uncons input of
                Nothing -> finalizeWinners
                Just (c,input') -> do
                  case CMap.findWithDefault o c t of
                    Transition {trans_many=DFA {d_id=did',d_dt=dt'},trans_how=dtrans} ->
                      findTrans s1 s2 did' dt' dtrans offset c input'

        findTrans s1 s2 did' dt' dtrans offset prev' input' =  {-# SCC "goNext.findTrans" #-} do
          --
          let findTransTo (destIndex,sources) = do
                val <- if IMap.null sources then return (succ offset)
                         else return . minimum =<< mapM (s1 !!) (IMap.keys sources)
                set s2 destIndex val
                return val
          earlyStart <- fmap minimum $ mapM findTransTo (IMap.toList dtrans)
          --
          earlyWin <- readSTRef (mq_earliest winQ)
          if earlyWin < earlyStart
            then do
              winnersR <- getMQ earlyStart winQ
              writeSTRef storeNext (next s2 s1 did' dt' (succ offset) prev' input')
              mapM wsToGroup (reverse winnersR)
            else do
              let offset' = succ offset in seq offset' $ next s2 s1 did' dt' offset' prev' input'

        processWinner s1 did dt w offset = {-# SCC "goNext.newWinnerThenProceed" #-} do
          let getStart (sourceIndex,_) = s1 !! sourceIndex
          vals <- mapM getStart (IMap.toList w)
          let low = minimum vals   -- perhaps a non-empty winner
              high = maximum vals  -- perhaps an empty winner
          if low < offset
            then do
              putMQ (WScratch low offset) winQ
              when (high==offset || IMap.member startState w) $
                putMQ (WScratch offset offset) winQ
              let keepState i1 = do
                    startsAt <- s1 !! i1
                    let keep = (startsAt <= low) || (offset <= startsAt)
                    if keep
                      then return True
                      else if i1 == startState
                             then {- check for additional empty winner -}
                                  set s1 i1 (succ offset) >> return True
                             else writeSTRef eliminatedStateFlag True >> return False
              states' <- filterM keepState (ISet.toAscList did)
              flag <- readSTRef eliminatedStateFlag
              if flag
                then do
                  writeSTRef eliminatedStateFlag False
                  let DFA {d_id=did',d_dt=dt'} = Trie.lookupAsc trie states'
                  return (did',dt')
                else do
                  return (did,dt)
            else do
               -- offset == low == minimum vals == maximum vals == high; vals == [offset]
               putMQ (WScratch offset offset) winQ
               return (did,dt)

        finalizeWinners = do
          winnersR <- readSTRef (mq_list winQ)
          resetMQ winQ
          writeSTRef storeNext (return [])
          mapM wsToGroup (reverse winnersR)

    -- goNext then ends with the next statement
    next s1In s2In didIn dtIn offsetIn prevIn inputIn

----

{-# INLINE mkTest #-}
mkTest :: Uncons text => Bool -> WhichTest -> Index -> Char -> text -> Bool
mkTest isMultiline = if isMultiline then test_multiline else test_singleline

----

{- MUTABLE WINNER QUEUE -}

data MQ s = MQ { mq_earliest :: !(STRef s Position)
               , mq_list :: !(STRef s [WScratch])
               }

newMQ :: S.ST s (MQ s)
newMQ = do
  earliest <- newSTRef maxBound
  list <- newSTRef []
  return (MQ earliest list)

resetMQ :: MQ s -> S.ST s ()
resetMQ (MQ {mq_earliest=earliest,mq_list=list}) = do
  writeSTRef earliest maxBound
  writeSTRef list []

putMQ :: WScratch -> MQ s -> S.ST s ()
putMQ ws@(WScratch {ws_start=start}) (MQ {mq_earliest=earliest,mq_list=list}) = do
  startE <- readSTRef earliest
  if start <= startE
    then writeSTRef earliest start >> writeSTRef list [ws]
    else do
      old <- readSTRef list
      let !rest = dropWhile (\ w -> start <= ws_start w) old 
          !new = ws : rest
      writeSTRef list new

getMQ :: Position -> MQ s -> S.ST s [WScratch]
getMQ pos (MQ {mq_earliest=earliest,mq_list=list}) = do
  old <- readSTRef list
  case span (\ w -> pos <= ws_start w) old of
    ([],ans) -> do
      writeSTRef earliest maxBound
      writeSTRef list []
      return ans
    (new,ans) -> do
      writeSTRef earliest (ws_start (last new))
      writeSTRef list new
      return ans

{- MUTABLE SCRATCH DATA STRUCTURES -}

data SScratch s = SScratch { _s_1 :: !(MScratch s)
                           , _s_2 :: !(MScratch s)
                           , _s_mq :: !(MQ s)
                           }
type MScratch s = STUArray s Index Position
data WScratch = WScratch {ws_start,_ws_stop :: !Position}
  deriving Show

{- DEBUGGING HELPERS -}
{- CREATING INITIAL MUTABLE SCRATCH DATA STRUCTURES -}

{-# INLINE newA #-}
newA :: (MArray (STUArray s) e (S.ST s)) => (Tag,Tag) -> e -> S.ST s (STUArray s Tag e)
newA b_tags initial = newArray b_tags initial

newScratch :: (Index,Index) -> S.ST s (SScratch s)
newScratch b_index = do
  s1 <- newMScratch b_index
  s2 <- newMScratch b_index
  winQ <- newMQ
  return (SScratch s1 s2 winQ)

newMScratch :: (Index,Index) -> S.ST s (MScratch s)
newMScratch b_index = newA b_index (-1)

{- CONVERT WINNERS TO MATCHARRAY -}

wsToGroup :: WScratch -> S.ST s MatchArray
wsToGroup (WScratch start stop) = do
  ma <- newArray (0,0) (start,stop-start)  :: S.ST s (STArray s Int (MatchOffset,MatchLength))
  unsafeFreeze ma

