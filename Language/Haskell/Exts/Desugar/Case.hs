{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.Exts.Desugar.Case where

import qualified Prelude 
import Prelude              (Integer,Enum(..))
 
import Language.Haskell.Exts hiding (binds,alt)
import Language.Haskell.Exts.SrcLoc(noLoc)
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Language.Haskell.Exts.Desugar.Basic
import Language.Haskell.Exts.Desugar.Pattern
import Control.Monad        (sequence,Monad(..))

import Control.Applicative  ((<$>),(<*>))

import Data.Foldable        (foldl,foldr,any)
import Data.Function        (($),(.))
import Data.Bool            (not)
import Data.String          (String)
import Data.List            (length,zip,null)

 
-- 3.17.3.a
stepA :: Exp -> Unique Exp
stepA (Case e alts) = do
  v <- newVar
  return  $ 
    App (Lambda noLoc [PVar $ Ident v]
         (Case (Var $ UnQual $ Ident v) alts))
    e
stepA _ = error "Case expression is not in state A!"

-- 3.17.3.b
stepB :: Exp -> Unique Exp  
stepB (Case v@(Var _) alts)  = do    
  return  $ 
    foldr (\alt ex -> 
            Case v [alt
                   ,Alt noLoc PWildCard 
                    (UnGuardedAlt ex) (BDecls [])])
    (App (Var (UnQual (Ident "error"))) (Lit (String "No match")))
    alts
stepB _ = error "Case expression is not in state B!"      

-- 3.17.3.c
stepC :: Exp -> Unique Exp
stepC (Case v@(Var _) 
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
    ;return  $ 
     Case e' 
     [Alt noLoc (PVar $ Ident y) 
      (UnGuardedAlt 
       (Case v 
        [Alt noLoc p (UnGuardedAlt 
                        (Let decls 
                         (fld)))(BDecls [])
        , Alt noLoc PWildCard 
          (UnGuardedAlt $ Var $ UnQual $ Ident  y) 
          (BDecls []) ])) (BDecls [])]} 
stepC _ = error "Case expression is not in state C!"

-- 3.17.3.g
-- simplifies application of constructor to patterns
-- check if the lazy semantics of newtype is held
stepG :: Exp -> Unique Exp
stepG (Case v@(Var _) 
       ((Alt _ (PApp n ps) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt _ PWildCard   (UnGuardedAlt e') 
          (BDecls []))
        :[]))  
  | any (not . isPVar) ps = do
    xs <- sequence [newVar|_ <-[1.. length ps]]
    let xps  = zip xs ps
        ealt = Alt noLoc PWildCard (UnGuardedAlt e') (BDecls [])
    return  $ 
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
stepG _ = error "Case expression is not in state G!"        
      
-- 3.17.3.i & 3.17.3.j    
-- removes var pattern    
stepIJ :: Exp -> Unique Exp
stepIJ c@(Case (Var _) 
       ((Alt _ (PVar _) (UnGuardedAlt _ ) 
         (BDecls [])) 
        :(Alt _ PWildCard   (UnGuardedAlt _) 
          (BDecls []))
        :[])) 
  = return $ stepJ_ $ stepI_ c
stepIJ _ = error "Case expression is not in state IJ!"

-- 3.17.3.i
stepI :: Exp -> Unique Exp
stepI c@(Case (Var _) 
       ((Alt _ (PVar _) (UnGuardedAlt _ ) 
         (BDecls [])) 
        :(Alt _ PWildCard   (UnGuardedAlt _) 
          (BDecls []))
        :[]))  
  = return $ stepI_ c 
stepI _ = error "Case expression is not in state I!"                

stepI_ :: Exp -> Exp
stepI_ (Case v@(Var _) 
       ((Alt s1 (PVar n) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt _ PWildCard   (UnGuardedAlt _) 
          (BDecls []))
        :[]))  
  = Case v
    ( (Alt s1 (PVar n) (UnGuardedAlt e ) (BDecls []))
      : [])  
stepI_ _ = Prelude.error "Case expression is not in state I_!" 

-- 3.17.3.j
stepJ :: Exp -> Unique Exp    
stepJ c@(Case (Var _) 
       ((Alt _ (PVar _) (UnGuardedAlt _ ) 
         (BDecls [])) 
        : []))  
  = return  $ 
  stepJ_ c
stepJ _ = error "Case expression is not in state J!"    

stepJ_ :: Exp -> Exp    
stepJ_ (Case v@(Var _) 
        ((Alt _ (PVar n) (UnGuardedAlt e ) 
          (BDecls [])) 
         : []))  
  = App (Lambda noLoc [PVar n] e) v
stepJ_ _ = Prelude.error "Case expression is not in state J_!"    


-- 3.17.3.d
-- removes Irrefutable pattern
stepD :: Exp -> Unique Exp
stepD (Case v@(Var _) 
       ((Alt _ (PIrrPat p) (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt _ PWildCard   (UnGuardedAlt _) 
          (BDecls []))
        :[])) = let 
  vars = patVar p
  in
  return  $ 
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
stepD _ = error "Case expression is not in state D!"   

-- 3.17.3.e
-- removes As pattern
stepE :: Exp -> Unique Exp  
stepE (Case v@(Var _) ( (Alt s1 (PAsPat n p) (UnGuardedAlt e ) 
                         (BDecls [])) 
                       :(Alt s2 PWildCard    (UnGuardedAlt e') 
                         (BDecls [])):[])) 
  = return  $ 
    (Case v 
     ((Alt s1  p (UnGuardedAlt 
                  (App  (Lambda noLoc [PVar n] e) v)) 
       (BDecls [])) 
      :(Alt s2 PWildCard    (UnGuardedAlt e') 
        (BDecls []))
      :[]))
stepE _ = error "Case expression is not in state E!"   
    
-- 3.17.3.f
-- removes _ pattern
stepF :: Exp -> Unique Exp    
stepF (Case (Var _) 
       ((Alt _ PWildCard (UnGuardedAlt e ) 
         (BDecls [])) 
        :(Alt _ PWildCard (UnGuardedAlt _) 
          (BDecls []))
        :[]))      
  = return  
    e    
stepF _ = error "Case expression is not in state F!"       

-- 3.17.3.h
-- removes literal pattern
stepH :: Exp -> Unique Exp    
stepH (Case v@(Var _) 
       ( (Alt _ (PLit lit) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt _ PWildCard  (UnGuardedAlt e') 
           (BDecls [])):[]))      
  = return  $ 
    (If (App (App (Var (UnQual (Symbol "=="))) v) (Lit lit)) e e')
stepH _ = error "Case expression is not in state H!"       

-- http://www.haskell.org/ghc/docs/latest/html/users_guide/bang-patterns.html
-- removes bang pattern
stepT' :: Exp -> Unique Exp    
stepT' (Case v@(Var _) 
        ((Alt s1 (PBangPat p) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt s2  PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]))      
  = return  $  
    App ( App (Var (UnQual (Ident "seq"))) v )
    (Case v  (  (Alt s1  p (UnGuardedAlt e ) 
                 (BDecls [])) 
                :(Alt s2  PWildCard (UnGuardedAlt e') 
                  (BDecls []))
                :[]))      
stepT' _ = error "Case expression is not in state T'!"       

-- 7.3.5
-- removes view patterns
stepV' :: Exp -> Unique Exp
stepV' (Case v@(Var _) 
        ((Alt s1 (PViewPat ex p) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt s2  PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]))      
  = return  $ 
    (Case (App ex v) 
     ((Alt s1 p (UnGuardedAlt e ) 
       (BDecls [])) 
      :(Alt s2  PWildCard   (UnGuardedAlt e') 
        (BDecls []))
      :[]))  
stepV' _ = error "Case expression is not in state V'!"       

-- 3.17.s Haskell 98 language report
-- removes nplusk pattern
stepS' :: Exp -> Unique Exp
stepS' (Case v@(Var _) 
        ((Alt _ (PNPlusK n k) (UnGuardedAlt e ) 
          (BDecls [])) 
         :(Alt _  PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]))      
  = return  $  
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
stepS' _ = error "Case expression is not in state S'!"       

-- 3.17.3.s
stepS :: Exp -> Unique Exp
stepS (Case (Con (Special UnitCon)) 
       ( (Alt _ (PApp (Special UnitCon) []) 
          (GuardedAlts 
           [GuardedAlt _ (gs@(_:_)) e]) 
          (BDecls [])) 
         :(Alt _ PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )  
  = return  $ 
    foldr 
    (\g ex-> 
      (Case (Con (Special UnitCon)) 
       ((Alt noLoc (PApp (Special UnitCon) []) 
         (GuardedAlts [GuardedAlt noLoc [g] e]) 
         (BDecls [])) 
        : (Alt noLoc PWildCard (UnGuardedAlt ex) 
           (BDecls [])):[]))
    ) e' gs    
stepS _ = error "Case expression is not in state S!"   

-- 3.17.3.t
stepT :: Exp -> Unique Exp
stepT (Case (Con (Special UnitCon)) 
       ( (Alt _ (PApp (Special UnitCon) []) 
           (GuardedAlts 
           [GuardedAlt _ ([Generator _ p e0]) e]) 
          (BDecls [])) 
         :(Alt _ PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )
  = return  $ 
    Case e0 
    [Alt noLoc p (UnGuardedAlt e) (BDecls [])
    ,Alt noLoc PWildCard (UnGuardedAlt e') (BDecls [])]
stepT _ = error "Case expression is not in state T!"   

-- 3.17.3.u
stepU :: Exp -> Unique Exp
stepU (Case (Con (Special UnitCon)) 
       ( (Alt _ (PApp (Special UnitCon) []) 
          (GuardedAlts 
           [GuardedAlt _ ([LetStmt decls]) e]) 
          (BDecls [])) 
         :(Alt _ PWildCard   (UnGuardedAlt _) 
           (BDecls []))
         :[]
       )
      )
  = return  $ 
    Let decls e
stepU _ = error "Case expression is not in state U!"    

-- 3.17.3.v
stepV :: Exp -> Unique Exp
stepV (Case (Con (Special UnitCon)) 
       ( (Alt _ (PApp (Special UnitCon) []) 
             (GuardedAlts 
           [GuardedAlt _ ([Qualifier e0]) e])
          (BDecls [])) 
         :(Alt _ PWildCard   (UnGuardedAlt e') 
           (BDecls []))
         :[]
       )
      )
  = return  $ 
  If e0 e e'
stepV _ = error "Case expression is not in state V!"

-- HSE 
-- it adds the default alt  
stepJ' :: Exp -> Unique Exp    
stepJ' (Case v@(Var _) (alt:[]))      
  = return  $ 
    (Case v  
     (  alt 
      :(Alt noLoc PWildCard   
        (UnGuardedAlt 
         (App (Var (UnQual (Ident "error"))) 
          (Lit (String "No match"))))
        (BDecls []))
      :[]))  
stepJ' _ = error "Case expression is not in state J'!"    

stepBinding :: Exp -> Unique Exp
stepBinding (Case v@(Var _) 
             ( (Alt s1 p         (UnGuardedAlt e ) 
                d@(BDecls bs)) 
              :(Alt s2 PWildCard (UnGuardedAlt e') 
                (BDecls []))
              :[])) 
  | not $ null bs     
  = return  $  
    (Case v  
     ( (Alt s1 p         (UnGuardedAlt (Let d e)) 
       (BDecls [])) 
      :(Alt s2 PWildCard (UnGuardedAlt e'        ) 
        (BDecls []))
      :[]))
stepBinding _ = error "Case expression is not in state Binding!"    

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
stepRecord _ = error "Case expression is not in state Record!"

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
  return  $ 
    (Case v 
     ((Alt s1 (PVar $ Ident x) 
       (GuardedAlts [GuardedAlt s1 
                     [Qualifier (App (Var pre) (Var $ UnQual $ Ident x))] 
                     e] ) 
       (BDecls [])) 
      :(Alt s2  PWildCard   (UnGuardedAlt e') 
        (BDecls []))
      :[]))
stepRecordN _ = error "Case expression is not in state RecordN!"   

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
  return  $ 
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
      toStmt _  _ = Prelude.error "Should have been desugared!"
stepRecordC _ = error "Case expression is not in state RecordC!"   

desugarPats :: Alt -> Unique Alt
desugarPats (Alt srcLoc pat guardedAlts binds)   
        = Alt srcLoc $$ pat <*> (return guardedAlts) <*> (return binds)