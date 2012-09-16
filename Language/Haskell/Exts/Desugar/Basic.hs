module Language.Haskell.Exts.Desugar.Basic where

import qualified Prelude
import Language.Haskell.Exts
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Prelude (return,Integer,mapM,Bool(..),(++),($),String)


instance Desugar Integer where
  -- No desugaring
  desugar = return
  
instance Desugar QName   where
  -- No desugaring
  desugar = return

instance Desugar Name    where
  -- No desugaring
  desugar = return

instance Desugar SrcLoc  where
  -- No desugaring
  desugar = return

instance Desugar Literal where
  -- No desugaring
  desugar = return

instance Desugar a => 
         Desugar [a]     where
  -- No desugaring
  desugar = mapM desugar
  
  
isPVar (PVar _ ) = True
isPVar _         = False
 
isVar (Var _ )  = True
isVar _         = False

isUnit (Con (Special UnitCon)) = True
isUnit _                       = False 

isPatFun :: Decl -> Bool
isPatFun d = case d of 
  PatBind _ _ _ _ _ -> True 
  FunBind _ -> True
  _ -> False
  
isSig :: Decl -> Bool
isSig d = case d of
  TypeSig _ _ _ -> True
  _ -> False
  
newPrefix :: (String,String)
newPrefix = ("new",":$")

isPrefix  :: (String,String)
isPrefix  = ("is",":")

setPrefix :: (String,String)
setPrefix = ("set",":=")

addPrefixToQName :: (String, String) -> QName -> Unique QName
addPrefixToQName (namePrefix, symbolPrefix)  qName  = do 
  q <- desugar qName
  case q of  
    Qual m (Ident n)  -> 
      return $ Qual m (Ident  $ namePrefix   ++ n ) 
    Qual m (Symbol n) ->
      return $ Qual m (Symbol $ symbolPrefix ++ n ) 
    UnQual (Ident n)  -> 
      return $ UnQual (Ident  $ namePrefix   ++ n )
    UnQual (Symbol n) -> 
      return $ UnQual (Symbol $ symbolPrefix ++ n )
    _                 ->  
      error "Error in desugaring of QName!"  
 