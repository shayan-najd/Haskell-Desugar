module Language.Haskell.Exts.Unique  where

import Control.Monad.Trans  (lift)
import Control.Monad.State  (put,get,evalState,State(..))
import Control.Monad.Reader (ask,ReaderT(..))
import Control.Monad.Error  (throwError,ErrorT(..))

import Control.Applicative  ((<$>))

import Language.Haskell.Exts (Name)
 
type Unique a = ErrorT String (ReaderT String (State ([Name],Int))) a  

newVar :: Unique String
newVar = do 
  seed <- ask
  (ns,r) <- lift get 
  lift $ put $ (ns ,succ r)
  return $ seed ++ (Prelude.show r)

runUnique :: Unique a -> String -> Either String a
runUnique c seed =  evalState ((runReaderT $ runErrorT c) seed) ([], 0)

initUnique :: Unique ()
initUnique = lift $ put ([],0) 

error :: String -> Unique a
error = throwError

push :: [Name] -> Unique ()
push ns = do
  (_,r) <- lift get 
  lift $ put $ (ns ,r)

peak :: Unique [Name]  
peak = fst <$> lift get

pop :: Unique [Name]
pop = do 
      r <- peak
      push []
      return r
