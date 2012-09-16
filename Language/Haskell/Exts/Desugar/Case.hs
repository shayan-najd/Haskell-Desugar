module Language.Haskell.Exts.Desugar.Case where

import qualified Prelude 
import Prelude              (Integer,Enum(..))

import Text.Show            (Show(..))

import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc(noLoc)
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Language.Haskell.Exts.Desugar.Basic
import Language.Haskell.Exts.Desugar.Type
import Language.Haskell.Exts.Desugar.Pattern
import Control.Monad        (mapM,sequence,Monad(..))

import Control.Applicative  ((<$>),(<*>))

import Data.Foldable        (foldl,foldr,foldl1,all,any)
import Data.Function        (($),(.),flip)
import Data.Tuple           (fst)
import Data.Int             (Int)
import Data.Bool            (Bool(..),not,(&&))
import Data.String          (String(..))
import Data.Maybe           (Maybe(..))
import Data.Either          (Either(..))
import Data.List            ((++),(\\),notElem,length,partition,filter
                            ,lookup,union,concat,zip,null)

import Debug.Trace          (trace)

 
-- 3.17.3.a
stepA :: Exp -> Unique Exp
stepA (Case e alts) = do
  v <- newVar
  return {- -} $ 
    App (Lambda noLoc [PVar $ Ident v]
         (Case (Var $ UnQual $ Ident v) alts))
    e

-- 3.17.3.b
stepB :: Exp -> Unique Exp  
stepB (Case v@(Var _) alts)  = do    
  return {- -} $ 
    foldr (\alt ex -> 
            Case v [alt
                   ,Alt noLoc PWildCard 
                    (UnGuardedAlt ex) (BDecls [])])
    (App (Var (UnQual (Ident "error"))) (Lit (String "No match")))
    alts
      
-- 3.17.3.c
stepC :: Exp -> Unique Exp
stepC (Case e@(Var _) 
       (  (Alt _ p         (GuardedAlts galts) decls      ) 
         :(Alt _ PWildCard (UnGuardedAlt e'  ) (BDecls []))
         :[])) = do   
  {
    y <- newVar
    ;let fld = foldr 
               ( \(GuardedAlt _ stmts e) ex -> 
                  Case (Con (Special UnitCon)) 
                  [(Alt noLoc (PApp (Special UnitCon) []) 
                    (GuardedAlts [GuardedAlt noLoc stmts e]) 
                    (BDecls [])) 
                  , (Alt noLoc PWildCard (UnGuardedAlt ex) 
                     (BDecls []))
                  ] 
               )   
               (Var $ UnQual $ Ident y) galts            
    ;return {- -} $ 
     Case e' 
     [Alt noLoc (PVar $ Ident y) 
      (UnGuardedAlt 
       (Case e 
        [Alt noLoc p (UnGuardedAlt 
                        (Let decls 
                         (fld)))(BDecls [])
        , Alt noLoc PWildCard 
          (UnGuardedAlt $ Var $ UnQual $ Ident  y) 
          (BDecls []) ])) (BDecls [])]} 

-- 3.17.3.g
-- simplifies application of constructor to patterns
-- check if the lazy semantics of newtype is held
stepG :: Exp -> Unique Exp
stepG (Case v@(Var _) 
       ((Alt s1 (PApp n ps) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt s2 PWildCard   (UnGuardedAlt e') 
          (BDecls []))
        :[]))  
  | any (not . isPVar) ps = do
    xs <- sequence [newVar|_ <-[1.. length ps]]
    let xps  = zip xs ps
        ealt = Alt noLoc PWildCard (UnGuardedAlt e') (BDecls [])
    return {- -} $ 
        Case v 
        [Alt noLoc (PApp n ((PVar . Ident) <$> xs)) 
         (UnGuardedAlt  $
          foldr (\ (x,p) r -> 
                  Case (Var $ UnQual $ Ident x) [
                    Alt noLoc p (UnGuardedAlt r) (BDecls []) 
                    ,ealt]
                )   e xps
         ) 
         (BDecls [])  
          , ealt]
      
-- 3.17.3.i & 3.17.3.j    
-- removes var pattern    
stepIJ :: Exp -> Unique Exp
stepIJ c@(Case v@(Var _) 
       ((Alt s1 (PVar n) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt s2 PWildCard   (UnGuardedAlt e') 
          (BDecls []))
        :[])) 
  = return {- -} $ 
    stepJ_ $ stepI_ c

-- 3.17.3.i
stepI :: Exp -> Unique Exp
stepI c@(Case v@(Var _) 
       ((Alt s1 (PVar n) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt s2 PWildCard   (UnGuardedAlt e') 
          (BDecls []))
        :[]))  
  = return {- -} $ 
  stepI_ c 
               

stepI_ :: Exp -> Exp
stepI_ (Case v@(Var _) 
       ((Alt s1 (PVar n) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt s2 PWildCard   (UnGuardedAlt e') 
          (BDecls []))
        :[]))  
  = Case v
    ( (Alt s1 (PVar n) (UnGuardedAlt e ) (BDecls []))
      : [])  


-- 3.17.3.j
stepJ :: Exp -> Unique Exp    
stepJ c@(Case v@(Var _) 
       ((Alt s1 (PVar n) (UnGuardedAlt e ) 
         (BDecls [])) 
        : []))  
  = return {- -} $ 
  stepJ_ c
    
stepJ_ :: Exp -> Exp    
stepJ_ (Case v@(Var _) 
        ((Alt s1 (PVar n) (UnGuardedAlt e ) 
          (BDecls [])) 
         : []))  
  = App (Lambda noLoc [PVar n] e) v


-- 3.17.3.d
-- removes Irrefutable pattern
stepD :: Exp -> Unique Exp
stepD (Case v@(Var _) 
       ((Alt _ (PIrrPat p) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt _ PWildCard   (UnGuardedAlt e') 
          (BDecls []))
        :[])) = let 
  vars = patVar p
  in
  return {- -} $ 
  (foldl App
   (Lambda noLoc (PVar <$> vars) e) 
   ((\n-> Case v [Alt noLoc p (UnGuardedAlt (Var (UnQual n)))
                  (BDecls [])
                 ,Alt noLoc PWildCard 
                  (UnGuardedAlt 
                   (App (Var (UnQual (Ident "error"))) 
                    (Lit (String "No match"))))
                  (BDecls [])
                 ] 
    ) <$> vars)
  )

-- 3.17.3.e
-- removes As pattern
stepE :: Exp -> Unique Exp  
stepE (Case v@(Var _) ( (Alt s1 (PAsPat n p) (UnGuardedAlt e ) 
                         (BDecls [])) 
                       :(Alt s2 PWildCard    (UnGuardedAlt e') 
                         (BDecls [])):[])) 
  = return {- -} $ 
    (Case v 
     ((Alt s1  p (UnGuardedAlt 
                  (App  (Lambda noLoc [PVar n] e) v)) 
       (BDecls [])) 
      :(Alt s2 PWildCard    (UnGuardedAlt e') 
        (BDecls []))
      :[]))
    
-- 3.17.3.f
-- removes _ pattern
stepF :: Exp -> Unique Exp    
stepF (Case v@(Var _) 
       ((Alt s1 PWildCard (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt s2 PWildCard (UnGuardedAlt e') 
          (BDecls []))
        :[]))      
  = return {- -} 
    e    

-- 3.17.3.h
-- removes literal pattern
stepH :: Exp -> Unique Exp    
stepH (Case v@(Var _) 
       ( (Alt s1 (PLit lit) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt s2 PWildCard  (UnGuardedAlt e') 
           (BDecls [])):[]))      
  = return {- -} $ 
    (If (App (App (Var (UnQual (Symbol "=="))) v) (Lit lit)) e e')

-- http://www.haskell.org/ghc/docs/latest/html/users_guide/bang-patterns.html
-- removes bang pattern
stepT' :: Exp -> Unique Exp    
stepT' (Case v@(Var _) 
        ((Alt s1 (PBangPat p) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt s2  PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]))      
  = return {- -} $  
    App ( App (Var (UnQual (Ident "seq"))) v )
    (Case v  (  (Alt s1  p (UnGuardedAlt e ) 
                 (BDecls [])) 
                :(Alt s2  PWildCard (UnGuardedAlt e') 
                  (BDecls []))
                :[]))      
    
-- 7.3.5
-- removes view patterns
stepV' :: Exp -> Unique Exp
stepV' (Case v@(Var _) 
        ((Alt s1 (PViewPat ex p) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt s2  PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]))      
  = return {- -} $ 
    (Case (App ex v) 
     ((Alt s1 p (UnGuardedAlt e ) 
       (BDecls [])) 
      :(Alt s2  PWildCard   (UnGuardedAlt e') 
        (BDecls []))
      :[]))  
    
-- 3.17.s Haskell 98 language report
-- removes nplusk pattern
stepS' :: Exp -> Unique Exp
stepS' (Case v@(Var _) 
        ((Alt s1 (PNPlusK n k) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt s2  PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]))      
  = return {- -} $  
    If 
    (App 
     (App (Var (UnQual (Symbol ">="))) (Var (UnQual n))) 
     (Lit  $ Int k ))
    (App 
     (Lambda noLoc [PVar n] e)
     (App 
      (App (Var (UnQual (Symbol "-"))) v) 
      (Lit (Int k))))    
    e'
-- 3.17.3.s
stepS :: Exp -> Unique Exp
stepS (Case v@(Con (Special UnitCon)) 
       ( (Alt s1 (PApp (Special UnitCon) []) 
          (GuardedAlts 
           [GuardedAlt _ (gs@(_:_)) e]) 
          (BDecls [])) 
         :(Alt s2 PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )  
  = return {- -} $ 
    foldr 
    (\g ex-> 
      (Case (Con (Special UnitCon)) 
       ((Alt noLoc (PApp (Special UnitCon) []) 
         (GuardedAlts [GuardedAlt noLoc [g] e]) 
         (BDecls [])) 
        : (Alt noLoc PWildCard (UnGuardedAlt ex) 
           (BDecls [])):[]))
    ) e' gs    

-- 3.17.3.t
stepT :: Exp -> Unique Exp
stepT (Case v@(Con (Special UnitCon)) 
       ( (Alt s1 (PApp (Special UnitCon) []) 
           (GuardedAlts 
           [GuardedAlt _ (gs@[Generator _ p e0]) e]) 
          (BDecls [])) 
         :(Alt s2 PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )
  = return {- -} $ 
    Case e0 
    [Alt noLoc p (UnGuardedAlt e) (BDecls [])
    ,Alt noLoc PWildCard (UnGuardedAlt e') (BDecls [])]

-- 3.17.3.u
stepU :: Exp -> Unique Exp
stepU (Case v@(Con (Special UnitCon)) 
       ( (Alt s1 (PApp (Special UnitCon) []) 
          (GuardedAlts 
           [GuardedAlt _ (gs@[LetStmt decls]) e]) 
          (BDecls [])) 
         :(Alt s2 PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )
  = return {- -} $ 
    Let decls e

-- 3.17.3.v
stepV :: Exp -> Unique Exp
stepV (Case v@(Con (Special UnitCon)) 
       ( (Alt s1 (PApp (Special UnitCon) []) 
             (GuardedAlts 
           [GuardedAlt _ (gs@[Qualifier e0]) e])
          (BDecls [])) 
         :(Alt s2 PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )
  = return {- -} $ 
  If e0 e e'

-- HSE 
-- it adds the default alt  
stepJ' :: Exp -> Unique Exp    
stepJ' (Case v@(Var _) (  
           (Alt s1 p (UnGuardedAlt e ) 
            (BDecls [])) 
           :[]))      
  = return {- -} $ 
    (Case v  
     ((Alt s1   p (UnGuardedAlt e ) 
       (BDecls [])) 
      :(Alt noLoc PWildCard   
        (UnGuardedAlt 
         (App (Var (UnQual (Ident "error"))) 
          (Lit (String "No match"))))
        (BDecls []))
      :[]))  
    
stepBinding :: Exp -> Unique Exp
stepBinding (Case v@(Var _) 
             ( (Alt s1 p         (UnGuardedAlt e ) 
                d@(BDecls bs)) 
              :(Alt s2 PWildCard (UnGuardedAlt e') 
                (BDecls []))
              :[])) 
  | not $ null bs     
  = return {- -} $  
    (Case v  
     ( (Alt s1 p         (UnGuardedAlt (Let d e)) 
       (BDecls [])) 
      :(Alt s2 PWildCard (UnGuardedAlt e'        ) 
        (BDecls []))
      :[]))

stepRecord :: Exp -> Unique Exp
stepRecord c@(Case (Var _) 
              ((Alt _ (PRec _ pfs) (UnGuardedAlt _) 
                (BDecls [])) 
               :(Alt _  PWildCard   (UnGuardedAlt _) 
                 (BDecls []))
               :[])) 
  = case pfs of 
  []    -> stepRecordN c
  _ : _ -> stepRecordC c  

stepRecordN :: Exp -> Unique Exp
stepRecordN  (Case v@(Var _) 
              ((Alt s1 (PRec n []) (UnGuardedAlt e ) 
                (BDecls [])) 
               :(Alt s2  PWildCard   (UnGuardedAlt e') 
                 (BDecls []))
               :[])) 
  =  do 
  pre <- addPrefixToQName isPrefix n
  x   <- newVar
  return {- -} $ 
    (Case v 
     ((Alt s1 (PVar $ Ident x) 
       (GuardedAlts [GuardedAlt s1 
                     [Qualifier (App (Var pre) (Var $ UnQual $ Ident x))] 
                     e] ) 
       (BDecls [])) 
      :(Alt s2  PWildCard   (UnGuardedAlt e') 
        (BDecls []))
      :[]))
   
stepRecordC :: Exp -> Unique Exp
stepRecordC  (Case v@(Var _) 
              ((Alt s1 (PRec n pfs@(_:_)) (UnGuardedAlt e ) 
                (BDecls [])) 
               :(Alt s2  PWildCard   (UnGuardedAlt e') 
                 (BDecls []))
               :[])) 
  = do 
  x    <- newVar
  dpfs <- sequence $ desugar <$> pfs
  return {- -} $ 
    (Case v 
     ((Alt s1 (PAsPat (Ident x) (PRec n [])) 
       (GuardedAlts [GuardedAlt s1 ((toStmt x) <$> dpfs) e] ) 
       (BDecls [])) 
      :(Alt s2  PWildCard   (UnGuardedAlt e') 
        (BDecls []))
      :[]))
    where
      toStmt :: String -> PatField  -> Stmt
      toStmt x (PFieldPat qn p) = Generator noLoc p (App (Var qn) 
                                                     (Var $ UnQual $ Ident x))


desugarPats :: Alt -> Unique Alt
desugarPats (Alt srcLoc pat guardedAlts binds)   
        = Alt srcLoc $$ pat <*> (return guardedAlts) <*> (return binds)