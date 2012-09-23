{-# LANGUAGE FlexibleInstances #-} 
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

--NOT Supported: 
-- Arrows, Implicit Parameters, Template Haskell, Scoped Type Variables
-- XML,Regular, Generic Style, Mdo, Pragmas, Module,TransformListComp
-- FFI, GADTs, TypeFamilies, Fundeps, Datatype Contexts 

module Language.Haskell.Exts.Desugar.Declaration where

import qualified Prelude 
import Prelude              (Integer,Enum(..),Eq(..))

import Language.Haskell.Exts hiding (name)
import Language.Haskell.Exts.SrcLoc(noLoc)
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Language.Haskell.Exts.Desugar.Basic
import Language.Haskell.Exts.Desugar.Type ()
import Language.Haskell.Exts.Desugar.Pattern 
import Language.Haskell.Exts.Desugar.Conversion 
import Language.Haskell.Exts.Desugar.Expression ()
import Language.Haskell.Exts.Desugar.Record 
import Control.Monad        (mapM,sequence,Monad(..))

import Control.Applicative  ((<$>),(<*>))

import Data.Function        (($),(.))
import Data.Maybe           (Maybe(..))
import Data.List            ((++),notElem,length,partition
                            ,lookup,concat)

instance Desugar Decl where
  desugar (TypeDecl src name tvs t ) =  do
    push $ (\(UnkindedVar x)->x) <$> tvs
    d <- TypeDecl $$ src ** name ** tvs ** t
    _<-pop
    return d
    
  desugar (DataDecl src db ctx name tvs  qcds drs) = do
    push $ (\(UnkindedVar x)->x) <$> tvs
    d <- DataDecl $$ src ** db ** ctx ** name  ** tvs **  qcds ** drs
    _<-pop
    return d
    
  desugar (DerivDecl src ctx qName ts) =  
    DerivDecl $$ src ** ctx ** qName ** ts
  
  desugar (ClassDecl src ctx name tvs fundeps classDecls) = do
    push $ (\(UnkindedVar x)->x) <$> tvs
    cd' <- desugarDecls ((\(ClsDecl d)-> d) <$> classDecls)
    _<-pop
    ClassDecl $$ src ** ctx ** name ** tvs <*> return fundeps 
      <*> return (ClsDecl <$> cd')
    
  desugar (InstDecl src ctx qName ts instDecls) = do 
    id' <- desugarDecls ((\ (InsDecl d) -> d) <$> instDecls)
    InstDecl $$ src ** ctx ** qName <*> return ts 
      <*> return (InsDecl <$> id')
      
  desugar (PatBind src (PVar (Ident n)) (Just ty) 
             (UnGuardedRhs exp) (BDecls []))  
   = do
     -- having typevariables in the state desugar the type signature
     t@(TyForall (Just _) _ _)   <- desugar ty
     -- reset the state and store the old state
     tys <- pop 
     -- push ttys -- for scoped type variables
     -- desugar the subexpression
     e    <-  desugar exp
     -- set the state back to the way it was
     push tys       
     return $ PatBind  src   (PVar (Ident n)) (Just t)    
       (UnGuardedRhs e)  (BDecls [])
     
  
  desugar (PatBind src (PVar (Ident n)) Nothing 
           (UnGuardedRhs exp) (BDecls []))                 =
    (PatBind $$ src  ** (PVar (Ident n)) <*> 
     return Nothing <*>  
     (UnGuardedRhs $$ exp) <*> return
     (BDecls []))
     
  -- methods without body in class declarations    
  desugar (TypeSig      src names t)                       =
    TypeSig $$ src ** names ** t
      
  desugar (FunBind {})          = 
    error $ "Desugaring error: FunBind should already have"
    ++ " been desugared!"       
  desugar (PatBind {})          = 
    error "PatBind is in the wrong format!"
  desugar (TypeFamDecl {})      = error "Not supported!"
  desugar (GDataDecl {})        = error "Not supported!"
  desugar (DataFamDecl {})      = error "Not supported!"
  desugar (DataInsDecl {})      = error "Not supported!"
  desugar (TypeInsDecl {})      = error "Not supported!"
  desugar (GDataInsDecl {})     = error "Not supported!"
  desugar (DefaultDecl {})      = error "Not supported!" 
  desugar (SpliceDecl {})       = error "Not supported!"
  desugar (InfixDecl {})        = error "Not supported!"
  desugar (ForImp {})           = error "Not supported!"
  desugar (ForExp {})           = error "Not supported!"
  desugar (RulePragmaDecl {})   = error "Not supported!"
  desugar (DeprPragmaDecl {})   = error "Not supported!"
  desugar (WarnPragmaDecl {})   = error "Not supported!"
  desugar (InlineSig {})        = error "Not supported!"
  desugar (InlineConlikeSig {}) = error "Not supported!"
  desugar (SpecSig {})          = error "Not supported!"
  desugar (SpecInlineSig {})    = error "Not supported!"
  desugar (InstSig {})          = error "Not supported!"
  desugar (AnnPragma {})        = error "Not supported!"


---------------------------------------       
desugarDecls :: [Decl] -> Unique [Decl]   
desugarDecls decls =  do 
  gens <- sequence [generateRecordFuns d|d@(DataDecl{})<-decls]
  let 
    ds = decls ++ (concat gens)
    (fpbs,others) = partition isPatFun ds 
  pbs <- concat <$> mapM desugarPatFunBind fpbs
  let    
    (sgs,rest) = partition isSig others
    sigs = [ (n,t) | TypeSig _ ns t <- sgs, n <- ns ]
    -- attach signatures to their matching definitions
    explPBs =  
              [ PatBind src (PVar n) 
                (lookup n sigs) 
                r bs 
              | PatBind src (PVar n) _ r bs <- pbs]
    noBodySigs = 
      [TypeSig noLoc [n] t 
      |(n,t)<- sigs
      , notElem n [pn|PatBind _ (PVar pn) _ _ _ <- pbs] ]
    ds' = rest ++ noBodySigs ++explPBs         
  desugar ds' 

  
desugarPatFunBind :: Decl -> Unique [Decl]
-- 4.4.3.1
desugarPatFunBind (FunBind ms@((Match _ n ps _ _ _ ):_)) =  do
  names <- sequence [ Ident <$> newVar 
                    | _  <- [1..length ps]]
  concat <$> mapM desugarPatFunBind   
    [PatBind noLoc (PVar n) Nothing 
     (UnGuardedRhs (Lambda noLoc 
                    (PVar <$> names)  
                    (Case (Tuple ((Var . UnQual) <$> names)) 
                     (cMatchs ms))))
     (BDecls [])]
          
-- 4.4.3.2
desugarPatFunBind (PatBind src p m (GuardedRhss  grhss) bnds) =
  concat <$> mapM desugarPatFunBind 
  [PatBind src p m 
  (UnGuardedRhs 
   (Let bnds 
     (Case (Con (Special UnitCon)) 
      [Alt noLoc (PApp (Special UnitCon) []) 
       (GuardedAlts 
        (cGuardedRhs <$> grhss)
       )(BDecls [])]
     )
   ))
  (BDecls [])]        

-- Final State
desugarPatFunBind e@(PatBind _ (PVar (Ident _)) _ 
                     (UnGuardedRhs _) (BDecls [])) = 
    return  [e]

-- THIH 11.6.3 
desugarPatFunBind (PatBind _ p mt (UnGuardedRhs exp) (BDecls [])) = do
  seed <- newVar
  concat <$> mapM desugarPatFunBind   
    ((PatBind noLoc (PVar $ Ident $ seed) mt (UnGuardedRhs exp) (BDecls []))
     :
     ((\v ->
        (PatBind noLoc (PVar $ v) Nothing 
         (UnGuardedRhs 
          (Case (Var (UnQual (Ident $ seed))) 
           [Alt noLoc p (UnGuardedAlt (Var (UnQual v))) 
            (BDecls [])]) ) (BDecls []))) <$> (patVar p) 
     ))
desugarPatFunBind _ =     
  error "Absurd use of desugarPatFunBind"

instance Desugar Module where
  desugar (Module src n os mw me i ds) =  
    Module src n os mw me i <$> desugarDecls ds  

instance Desugar Binds where  
  desugar (BDecls ds) = do
     BDecls <$> desugarDecls ds
  desugar (IPBinds _) =  
    error "Not supported!"

instance Desugar BangType where
  desugar (BangedTy t)   = BangedTy   $$ t	
  desugar (UnBangedTy t) = UnBangedTy $$ t	  
  desugar (UnpackedTy t) = UnpackedTy $$ t  
  
instance Desugar DataOrNew where         
  desugar = return 
  

instance Desugar QualConDecl where
  desugar (QualConDecl src tvs ctx condecl) =
    QualConDecl $$ src ** tvs ** ctx ** condecl

instance Desugar ConDecl where
  desugar (ConDecl n bts)          = 
    ConDecl $$ n ** bts
  desugar (InfixConDecl bt1 n bt2) = desugar $ 
    ConDecl n [bt1,bt2]
  desugar (RecDecl n rs)           = desugar $
    ConDecl n [ bt | (ns,bt) <- rs, _ <- ns]
 
instance (Desugar a,Desugar b) => Desugar (a, b) where --deriving
  desugar (qName, tys) = do 
    q <- desugar qName
    ts <- desugar tys  
    return (q , ts)
