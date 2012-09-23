{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.Exts.Desugar.Conversion where

import qualified Prelude 
import Prelude              (Integer,Enum(..))
 
import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc(noLoc)
import Control.Applicative  ((<$>))

cMatchs :: [Match] -> [Alt]
cMatchs ms  = cMatch <$> ms 

cMatch :: Match -> Alt
cMatch (Match _ _ ps _ rhs bs) = 
  Alt noLoc (PTuple ps) (cRhs rhs) bs 

cRhs :: Rhs -> GuardedAlts  
cRhs (UnGuardedRhs exp) = 
  UnGuardedAlt exp
cRhs (GuardedRhss grhss) = 
  GuardedAlts (cGuardedRhs <$> grhss)
  
cGuardedRhs :: GuardedRhs -> GuardedAlt
cGuardedRhs (GuardedRhs _ stmts exp) = 
  GuardedAlt noLoc stmts exp        

      
desugarLambda2Alt :: Exp -> Alt
desugarLambda2Alt (Lambda _ [p] body) = 
  Alt noLoc p (UnGuardedAlt body) (BDecls [])
desugarLambda2Alt _ = Prelude.error "not lambda"  



{-
desugarPatBind2FunBind :: Decl -> Decl
desugarPatBind2FunBind 
  (PatBind _ (PVar v) _ (UnGuardedRhs e) (BDecls [])) =
    FunBind [Match noLoc v [] Nothing (UnGuardedRhs e) (BDecls [])]
--desugarPatBind2FunBind x = 
--  error "Desugaring error: patbind not in a correct format!"-}    

 

-- not implemented completely     
-- based on: "Bringing Back Monad Comprehensions" By Giorgidze et al
cQualStmt :: QualStmt -> Stmt 
cQualStmt (QualStmt (Qualifier e))       = 
      Qualifier (App (Var (UnQual (Ident "guard"))) e) 
cQualStmt (QualStmt g@(Generator _ _ _)) = 
      g  
cQualStmt (QualStmt l@(LetStmt _))       = 
      l 
cQualStmt _ = Prelude.error "not implemented completely"

{-           
demoteQualConDecl :: Name -> [Name]-> QualConDecl -> Exp
demoteQualConDecl d vars (QualConDecl _ [] [] cdecl) 
  = demoteConDecl d vars cdecl	

demoteConDecl :: Name -> [Name]-> ConDecl -> Exp
demoteConDecl d vars (ConDecl _ bts) 
  = App (App (Var (UnQual (Symbol "-->"))) 
         (foldl1  
          (\a e ->App (App (Var (UnQual (Symbol "-->"))) a) e)
          (demoteBangType <$> bts) )) 
         (foldl App  (Var $ UnQual d) ( (Var . UnQual)  <$> vars) ) 
demoteConDecl _ _ x = Prelude.error "Not supported!"
                     
demoteBangType :: BangType -> Exp
demoteBangType (BangedTy   t) = demoteType t
demoteBangType (UnBangedTy t) = demoteType t
demoteBangType (UnpackedTy t) = demoteType t

demoteDecl :: Decl -> Decl
demoteDecl (DataDecl _ _ [] dn tys qconds drs) =
  PatBind noLoc (PVar dn') Nothing 
  (UnGuardedRhs l) (BDecls [])
  where
    dn' = demoteName dn
    vars = (\(UnkindedVar n) -> n)  <$> tys
    pvars = PVar <$> vars
    l = Lambda noLoc  pvars $
         foldl1 (\a e ->App (App (Var (UnQual (Symbol "<+>"))) a) e)  
        ((demoteQualConDecl dn' vars ) <$> qconds)
--TODO: demote of other declarations

demoteCTX :: Context -> Exp           
demoteCTX []    = Var (UnQual (Ident "constraint"))
demoteCTX [asst] = demoteAsst asst
demoteCTX assts@(_:_) 
  = foldl1 
    (\a e -> App (App  (Var (UnQual (Symbol "<&>"))) a ) e)
    (demoteAsst <$> assts)              

demoteAsst :: Asst -> Exp
demoteAsst (ClassA qName ts) = foldl App   
                               (Var $ demoteQName qName) 
                               (demoteType <$> ts)
demote x = Prelude.error "Not supported!"  

demoteType :: Type -> Exp
demoteType (TyForall (Just bs) ctx ty) =
  Lambda noLoc 
  ( (\(UnkindedVar n) -> PVar n)  <$> bs)  
  (App (App (Var $ UnQual (Symbol "==>")) (demoteCTX ctx)) (demoteType ty))
demoteType (TyForall Nothing ctx ty) =  
  Prelude.error "Wrong format!"   
demoteType (TyApp t1 t2) = 
  App (demoteType t1) (demoteType t2)
demoteType (TyCon qName) =  
  Var $ demoteQName qName
demoteType (TyVar  n) =  
  Var $ UnQual n
    
 
demoteQName :: QName -> QName    
demoteQName (Qual m n) = Qual m $ demoteName n
demoteQName (UnQual n) = UnQual $ demoteName n
demoteQName (Special UnitCon) =  UnQual $ Ident "tUnit"              
demoteQName (Special ListCon) =  UnQual $ Ident "tList"                
demoteQName (Special FunCon)  =  UnQual $ Ident "-->"                
demoteQName (Special (TupleCon Boxed i)) =  UnQual $ Ident 
                                          $ "tTuple" ++ (Prelude.show i)    
 
demoteName :: Name -> Name
demoteName (Ident n) = Ident $ "t" ++ n
demoteName (Symbol n) = Ident $ ":" -}