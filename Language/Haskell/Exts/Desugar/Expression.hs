{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.Exts.Desugar.Expression where

import qualified Prelude 
import Prelude              (Integer,Enum(..))

--import Text.Show            (Show(..))

import Language.Haskell.Exts hiding (binds,name)
import Language.Haskell.Exts.SrcLoc(noLoc)
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Language.Haskell.Exts.Desugar.Basic
--import Language.Haskell.Exts.Desugar.Type
--import Language.Haskell.Exts.Desugar.Pattern
import Language.Haskell.Exts.Desugar.Case
import Language.Haskell.Exts.Desugar.Conversion
import {-# SOURCE #-} Language.Haskell.Exts.Desugar.Declaration ()
import Control.Monad        (mapM,sequence,Monad(..),(=<<))

import Control.Applicative  ((<$>),(<*>))

import Data.Foldable        (foldl,foldr,all,any)
import Data.Function        (($),(.),flip)
import Data.Bool            (Bool(..),not)
--import Data.String          (String(..))
import Data.Maybe           (Maybe(..))
import Data.Either          (Either(..))
import Data.List            ((++),length)


instance Desugar Exp where  
  -- 3.2
  -- no desugaring
  desugar (Var qName)   = 
    Var $$ qName
  
  -- 3.2
  -- no desugaring
  -- could be desugared to Var qname 
  desugar (Con qName) =   
    Con $$ qName  
  
  -- not 3.2
  -- no desugaring  
  -- could be considered as constant functions (Var)
  desugar (Lit l) =  
    Lit $$ l 
  
  -- 3.2
  -- no desugaring
  desugar (App e1 e2) = 
    App $$ e1 ** e2
  
  -- 3.3   
  -- HSE
  desugar (Lambda _ [] _) = 
    error "No header for the lambda expression!"
  desugar (Lambda src [p] body) 
    | not $ isPVar p = do
     name <- newVar
     desugar $
        Lambda src [PVar $ Ident name] 
         (Case (Var $ UnQual $ Ident name) 
          [Alt noLoc p (UnGuardedAlt body) (BDecls [])])
  desugar (Lambda src ps body) 
    | any (not . isPVar) ps = do
     names <- sequence [newVar| _ <-ps]
     desugar $
        Lambda src ((PVar . Ident) <$> names) 
         (Case (Tuple $ (Var . UnQual . Ident) <$> names) 
          [Alt noLoc (PTuple ps) (UnGuardedAlt body) (BDecls [])])
  desugar (Lambda src [p] body) = 
    Lambda $$ src ** [p] ** body
  desugar (Lambda src (p:ps) body) =
    Lambda $$ src  ** [p] ** (Lambda src ps body)
    
  -- 3.4  
  desugar (NegApp e) =
    desugar $ App (Var (UnQual (Ident "negate")))  e
  
  -- 3.4
  desugar (InfixApp exp1 (QVarOp qName) exp2) = 
    desugar $ App (App (Var qName) exp1) exp2
  
  -- 3.4  
  desugar (InfixApp exp1 (QConOp qName) exp2) =  
    desugar $ App (App (Con qName) exp1) exp2
  
  -- 3.5     
  desugar (LeftSection ex qOp) = do 
    n <- newVar
    desugar $ Lambda noLoc 
      [PVar $ Ident n] 
      (InfixApp ex qOp (Var $ UnQual $ Ident n))
  
  -- 3.5
  desugar  (RightSection qOp ex) = do
    n <- newVar
    desugar $ Lambda noLoc 
        [PVar $ Ident n] 
        (InfixApp (Var $ UnQual $ Ident n) qOp ex)
  
  -- 3.6
  desugar (If cond th el) = desugar $ 
    Case cond 
    [ Alt noLoc 
      (PApp (UnQual (Ident "True")) []) (UnGuardedAlt th) (BDecls [])
    ,Alt noLoc 
     (PApp (UnQual (Ident "False")) []) (UnGuardedAlt el) (BDecls [])]
  
  -- 3.7
  desugar (List es) = desugar $
    foldr (\e a -> App (App (Con $ Special Cons) e) a)
                  (Con (Special ListCon)) es
  
  -- not 3.8 
  -- HSE
  desugar (Tuple [])         = desugar $ Con (Special UnitCon)
  desugar (Tuple [e])        = desugar $ e
  desugar (Tuple exps@(_:_)) =
    desugar $ foldl App (Con $ Special $ TupleCon Boxed $ length exps) exps
  
  -- 3.9
  desugar (Paren ex) = 
    desugar $ ex
  
  -- 3.10
  desugar  (EnumFrom exp) =
    desugar $ App (Var (UnQual (Ident "enumFrom"))) exp
  
  -- 3.10
  desugar  (EnumFromTo ex1 ex2) = do
    desugar $ App (App (Var (UnQual (Ident "enumFromTo"))) ex1) ex2      
  
  -- 3.10
  desugar  (EnumFromThen ex1 ex2) = 
    desugar $ App (App (Var (UnQual (Ident "enumFromThen"))) ex1) ex2
  
  -- 3.10
  desugar   (EnumFromThenTo ex1 ex2 ex3) =
    desugar $  
      App (App (App (Var (UnQual (Ident "enumFromThen"))) ex1) ex2) ex3
  
  -- not 3.11
  -- Generalized to monad comprehensions  
  -- based on: "Comprehending Moands" By Walder   
  desugar (ListComp eexp qualStmts) =
       desugar $ 
       Do ( (cQualStmt <$> qualStmts) ++ 
            [(Qualifier (App (Var ((UnQual (Ident "return")))) eexp))])         
  
  -- 3.12
  -- let with empty binding is removed
  desugar (Let (BDecls []) ex) = 
    return ex 
  desugar (Let binds ex) = 
    Let $$ binds ** ex 

  -- 3.13 & 3.17.3   
  -- the optimization transformations (k .. r) are not implemented
  desugar (Case e altsi) = do 
    -- reduce patterns to:
    -- PApp, PVar, PLit, PAsPat, PWildCard, PIrrPat,   
    -- PNPlusk, PBangPat, PViewPat, PRecord 
    alts <- sequence $
            [Alt srcLoc $$ pat 
             <*> (return guardedAlts)
             <*> (return binds) 
            |Alt srcLoc pat guardedAlts binds <- altsi]
    let c = Case e alts       
    case e of 
   --------------------------
      {(Con (Special UnitCon)) -> 
          case alts of    
            {((Alt _ p galt _) 
              :(Alt _ PWildCard (UnGuardedAlt _) (BDecls []))
              :[]) -> case galt of
                {(UnGuardedAlt _ ) -> desugar =<< stepA c
                ;(GuardedAlts gss) -> case p of
                  {(PApp (Special UnitCon) []) -> case gss of
                      {[] -> error "Wrong HSE Tree!"
                      ;[GuardedAlt _ stmts _] -> case stmts of 
                        {[] -> error "Wrong HSE Tree!"
                        ;[Qualifier _]     -> desugar =<< stepV c
                        ;[LetStmt _]       -> desugar =<< stepU c
                        ;[Generator _ _ _] -> desugar =<< stepT c
                        ;(_:_)             -> desugar =<< stepS c }
                      ; _ -> desugar =<< stepA c }
                  ; _ -> desugar =<< stepA c }}
            ; _ -> desugar =<< stepA c }
      ; (Var _) -> case alts of
            { [] -> error "Wrong HSE Tree!"
            ;((Alt _ _ _ _)
              :[]) -> desugar =<< stepJ' c
            ;((Alt _ p galt decls) 
              :(Alt _ PWildCard (UnGuardedAlt _) (BDecls []))
              :[]) -> case galt of
              {(UnGuardedAlt _) -> case decls of
                  {BDecls [] -> case p of
                      {PVar    _       -> desugar =<< stepIJ     c
                      ;PIrrPat _       -> desugar =<< stepD      c
                      ;PAsPat _ _      -> desugar =<< stepE      c
                      ;PWildCard       -> desugar =<< stepF      c
                      ;PLit _          -> desugar =<< stepH      c
                      ;PBangPat _      -> desugar =<< stepT'     c
                      ;PViewPat _ _    -> desugar =<< stepV'     c
                      ;PNPlusK _ _     -> desugar =<< stepS'     c
                      ;PRec _ _        -> desugar =<< stepRecord c
                      ;PApp _ ps
                       | all isPVar ps -> stepFinal  c
                       | True          -> desugar =<< stepG      c
                      ;_ -> error "Not Supported in case!"}
                  ; _        -> desugar =<< stepBinding c} 
              ;(GuardedAlts _) -> desugar =<< stepC c}
            ; _ -> desugar =<< stepB c}
      ; _ -> desugar =<< stepA c}
   
  -- 3.14
  desugar (Do [])            = 
    error "Empty do block!"
  desugar (Do [Qualifier e]) = 
    return e
  desugar (Do [_])           = 
    error "The last statement in a 'do' block must be an expression!"
  desugar (Do ((Qualifier e):ss)) = 
    desugar $ InfixApp e (QVarOp (UnQual (Symbol ">>"))) (Do ss)
  desugar (Do ((Generator _ p e):stmts)) = do
    ok <- newVar
    desugar $ 
     Let 
      (BDecls 
       [FunBind [Match noLoc (Ident ok) 
                 [p] Nothing 
                 (UnGuardedRhs (Do stmts)) 
                 (BDecls [])
                ,Match noLoc (Ident ok) 
                 [PWildCard] Nothing 
                 (UnGuardedRhs (App (Var (UnQual (Ident "fail"))) 
                                (Lit (String "...")))) 
                 (BDecls [])]]) 
      (InfixApp e 
       (QVarOp (UnQual (Symbol ">>="))) 
       (Var (UnQual (Ident ok))))
  desugar (Do ((LetStmt bs):ss)) =   
    desugar $ Let bs (Do ss)
  desugar (Do ((RecStmt _) : (_ : _))) =
    error "not supported yet!" --ToDo
 
  -- not 3.15.2
  desugar (RecConstr qName fieldUpdates) = do
   qn <- addPrefixToQName newPrefix qName
   fu <- desugar fieldUpdates  
   desugar $ 
      RecUpdate (Var qn) fu 
    
  -- not 3.15.3
  desugar (RecUpdate eexp fieldUpdates) = do 
    fu <- desugar fieldUpdates
    es <- sequence  
          [do  
           {qn <- addPrefixToQName setPrefix  qName
           ;return $ App (Var qn) e}
          | FieldUpdate qName e  <- fu]
    desugar $ foldl (flip App) eexp es
   
  -- 3.16
  desugar (ExpTypeSig _ e t) = do
    v <- newVar 
    desugar $ 
     Let (BDecls [TypeSig noLoc [Ident v] t
                 ,PatBind noLoc (PVar (Ident v)) Nothing
                  (UnGuardedRhs e) (BDecls [])]) 
                  (Var (UnQual (Ident v)))
  
  -- HSE
  desugar (TupleSection mes) = do 
    eExps <- mapM (\m -> case m of {Nothing -> Left . Ident <$> newVar
                                   ;Just x  -> return $ Right x  }
                   ) mes
    desugar $ 
       Lambda noLoc [PVar n |Left n  <- eExps]
        (Tuple [ case x of   
                  Left n  -> Var $ UnQual n
                  Right e -> e 
               |x <- eExps])
 
  -- Not Supported 
  desugar (ParComp {}) =  error "Not supported!"
 {- 
  desugar (ParComp  eexp qualStmtss) =  error "Not supported!"
  let comps = [ ListComp 
                (Tuple [patToExp p| (Generator _ p _ ) <- qualStmts ]) 
                qualStmts 
              |  qualStmts <- qualStmtss
  let x = Generator noLoc (PTuple [PTuple  | <-]) 
      (foldl App (Var (UnQual $ Ident ("zip" ++ (show (length comps))))) comps )
       desugar (ListComp eexp x)  -}  

  desugar (MDo             {}) = error "Not supported!"
  desugar (IPVar           {}) = error "Not supported!"
  -- Template Haskell
  desugar (VarQuote        {}) = error "Not supported!"            
  desugar (TypQuote        {}) = error "Not supported!"            
  desugar (BracketExp      {}) = error "Not supported!"        
  desugar (SpliceExp       {}) = error "Not supported!"          
  desugar (QuasiQuote      {}) = error "Not supported!"  
  -- Hsx
  desugar (XTag            {}) = error "Not supported!"
  desugar (XETag           {}) = error "Not supported!"
  desugar (XPcdata         {}) = error "Not supported!"            
  desugar (XExpTag         {}) = error "Not supported!"               
  desugar (XChildTag       {}) = error "Not supported!"    
  -- Pragmas
  desugar (CorePragma      {}) = error "Not supported!"      
  desugar (SCCPragma       {}) = error "Not supported!"      
  desugar (GenPragma       {}) = error "Not supported!"
  -- Arrows
  desugar (Proc            {}) = error "Not supported!"   
  desugar (LeftArrApp      {}) = error "Not supported!"   
  desugar (RightArrApp     {}) = error "Not supported!"
  desugar (LeftArrHighApp  {}) = error "Not supported!"
  desugar (RightArrHighApp {}) = error "Not supported!"   


stepFinal :: Exp -> Unique Exp
stepFinal (Case v@(Var _) 
           ((Alt s1 p@(PApp _ ps) (UnGuardedAlt e ) 
             (BDecls [])) 
            :(Alt s2 PWildCard (UnGuardedAlt e') 
              (BDecls []))
            :[])) 
  | all isPVar ps
  =  Case v <$> 
     sequence 
     [Alt $$ s1 ** p         <*> (UnGuardedAlt $$ e) 
      <*> return (BDecls [])
     ,Alt $$ s2 ** PWildCard <*> (UnGuardedAlt $$ e') 
      <*> return (BDecls [])]  
stepFinal _ = error "not in the final state!"     
     
instance Desugar FieldUpdate where
  desugar (FieldUpdate qn e) = 
    FieldUpdate $$ qn ** e
  desugar (FieldPun n)       = 
    desugar $ FieldUpdate (UnQual n) (Var (UnQual n))
  desugar FieldWildcard      = 
    error "FieldWildcard is not supported!"