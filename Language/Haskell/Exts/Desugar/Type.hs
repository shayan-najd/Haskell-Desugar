module Language.Haskell.Exts.Desugar.Type where

import qualified Prelude
import Language.Haskell.Exts
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Language.Haskell.Exts.Desugar.Basic

import Control.Applicative  ((<$>),(<*>))

import Data.Foldable        (foldl,foldr,foldl1,all,any)
import Data.Function        (($),(.),flip)
import Data.List            ((\\),length,union)
import Data.Maybe           (Maybe(..))
import Control.Monad        (return)

instance Desugar Kind    where  
  -- No desugaring
  desugar KindBang             = 
    return KindBang    
  -- No desugaring
  desugar (KindFn k1 k2)       =  
    KindFn $$ k1 ** k2
  -- No desugaring
  desugar (KindVar n)          =   
    KindVar $$ n
  -- HSE
  desugar (KindParen k)        = 
    desugar k 
   
instance Desugar Asst    where
  -- No desugaring
  desugar (ClassA qName ts)    =     
    ClassA $$ qName ** ts
  -- No desugaring
  desugar (EqualP t1 t2)       =
    EqualP $$ t1 ** t2     
  -- HSE
  desugar (InfixA t1 qName t2) = 
    desugar $ ClassA qName [t1,t2]  
  -- Not supported
  desugar (IParam iPName t)    =
    error "Not supported!"
    
instance Desugar TyVarBind where
  -- No desugaring 
  desugar (KindedVar n k) =
    KindedVar $$ n ** k
  -- No desugaring
  desugar (UnkindedVar n) =    
    UnkindedVar $$ n
    
instance Desugar Type where
  -- Not supported!
  desugar (TyForall (Just _) _ _)  =
    error "ExplicitForAlls is not supported!"
  
  -- desugar the components and then add the
  -- explicit foralls
  desugar (TyForall Nothing ctx ty) = 
    do
     t  <- desugarT ty
     c  <- desugar ctx
     tys <- peak
     return 
       $ TyForall 
       (Just $ UnkindedVar <$> (tyvars t \\ tys)) 
       c t
       
  -- desugar the components and then add the
  -- explicit foralls
  desugar ty  = do
    t <- desugarT ty
    tys <- peak
    return  
      $ TyForall 
      (Just $ UnkindedVar <$> (tyvars t \\ tys)) 
      [] t
  
desugarT (TyApp t1 t2)      = 
    TyApp <$> desugarT t1 <*> desugarT t2
desugarT (TyCon qName)      =  
    TyCon $$ qName
desugarT (TyVar  n)         = 
    TyVar $$ n
desugarT (TyKind t k)       = 
    TyKind <$> desugarT t ** k
desugarT (TyFun t1 t2)      =  
    desugarT $ TyInfix t1 (Special FunCon) t2
desugarT (TyTuple b ts)     = 
    desugarT $ foldl TyApp (TyCon $ Special $ TupleCon b $ length ts) ts
desugarT (TyList  t)        =  
    desugarT $ TyApp (TyCon $ Special ListCon) t 
desugarT (TyInfix t1 qn t2) = 
    desugarT $ TyApp (TyApp (TyCon qn) t1) t2  
desugarT ( TyParen t )      = 
    desugarT t      
    
tyvars :: Type -> [Name]
--tyvars (TyForall Nothing ctx t) = tyvars t --ambiguous types are not supported
tyvars (TyApp t1 t2) = (tyvars t1) `union`  (tyvars t2) 
tyvars (TyVar n) = [n]  
tyvars (TyCon _) = []                 
tyvars _ = Prelude.error "Not supported!"
    