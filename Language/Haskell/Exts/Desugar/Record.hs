{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.Exts.Desugar.Record where

import qualified Prelude 
import Prelude              (Integer,Enum(..),Eq(..),otherwise)

import Language.Haskell.Exts hiding(name)
import Language.Haskell.Exts.SrcLoc(noLoc)
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar.Basic
 
import Control.Monad        (sequence,Monad(..))

import Control.Applicative  ((<$>))

import Data.Foldable        (foldl)
import Data.Function        (($))
import Data.Int             (Int)
import Data.String          (String)
import Data.Maybe           (Maybe(..))
import Data.List            ((++),notElem,length,concat,nub)


-- Generates the following functions for each data declaration 
-- 1.Getter 2.Setter 3.Is 4.New  
generateRecordFuns :: Decl -> Unique [Decl]   
generateRecordFuns (DataDecl _ _ [] 
                    _ _ qualConDecls _) = 
  let
    -- collect 1.name of the constructor 2.labels 3.arity
    cons = [case cDecl of
            ConDecl name ts         -> (name,[],length ts)
            InfixConDecl _ name _ -> (name,[],2)
            RecDecl name nts        -> 
              let nns = [n|(ns,_) <- nts,n <- ns]
              in (name,nns,length nns)
           |QualConDecl _ _ _ cDecl <- qualConDecls]	  
    ls = nub [ l | (_,lcs,_) <- cons , l<-lcs]     
    cs = [ (c,ar) | (c,_,ar) <- cons]     
  in 
   do
     dgs  <- sequence [genGet l cons | l <- ls]
     dss  <- sequence [genSet l cons | l <- ls]
     dis  <- sequence [genIs  c ar   | (c,ar) <- cs]  
     dns  <- sequence [genNew c ar   | (c,ar) <- cs]  
     return $ dgs++dss++dis++dns
generateRecordFuns _ = error "absurd use!"   

-- Generates a getter function for the given label, e.g.,
-- having "data X = X1 {l1:: Int,l2::String} | X2 {l1::Int}" it generates: 
-- > getl1 = \r -> case r of 
-- > {X1 x0 _ -> x0
-- > ;X2 x0   -> x0
-- > ; _  -> error ...}     
genGet :: Name -> [(Name,[Name],Int)] -> Unique Decl
genGet l cons = do
  r <- newVar
  alts' <-sequence $ genGet_ l <$> cons 
  let alts = concat alts'
  return $ 
    PatBind noLoc (PVar l) Nothing 
    (UnGuardedRhs 
     (Lambda noLoc [PVar $ Ident r] 
      (Case (Var $ UnQual $ Ident r)
       (alts 
        ++
        [Alt noLoc PWildCard
         (UnGuardedAlt 
          (App (Var (UnQual (Ident "error"))) (Lit (String "Label is not defined!"))))
         (BDecls [])]))))
    (BDecls [])
  
genGet_ :: Name -> (Name,[Name],Int) -> Unique [Alt]
genGet_ l (c,ns,_)
     | l `notElem` ns = return []
     | otherwise      = do
       x <- newVar
       let vs  =
             [if (l == n) 
              then Just x 
              else Nothing 
             | n <- ns]                 
       return $ 
         [Alt noLoc 
          (PApp (UnQual c) 
           [case v of  
               Just x0  -> PVar $ Ident x0 
               Nothing -> PWildCard
           | v <- vs]) 
          (UnGuardedAlt 
           (Var $ UnQual $ Ident x)) 
          (BDecls [])]
       
         
-- Generates a setter function for the given label, e.g.,
-- having "data X = X1 {l1:: Int,l2::String} | X2 {l1::Int}" it generates: 
-- > setl1 = \e -> \r -> case r of 
-- > {X1 _ x0 -> X1 e x0
-- > ;X2 _    -> X2 e
-- > ; _  -> error ...}   
genSet :: Name -> [(Name,[Name],Int)] -> Unique Decl
genSet l cons = do
  e <- newVar
  r <- newVar
  (UnQual n') <- addPrefixToQName setPrefix (UnQual l)
  alts' <-sequence $ genSet_ l e <$> cons 
  let alts = concat alts'
  return $ 
    PatBind noLoc (PVar n') Nothing 
    (UnGuardedRhs 
     (Lambda noLoc [PVar $ Ident e] (
         Lambda noLoc [PVar $ Ident r] 
         (Case (Var $ UnQual $ Ident r)
          (alts 
           ++
           [Alt noLoc PWildCard
            (UnGuardedAlt 
             (App (Var (UnQual (Ident "error"))) 
              (Lit (String "Label is not defined! "))))
            (BDecls [])])))))
    (BDecls [])
 
genSet_ :: Name -> String -> (Name,[Name],Int) -> Unique [Alt]
genSet_ l e (c,ns,_)
     | l `notElem` ns = return []
     | otherwise      = do
     vs <- sequence [if (l == n) 
                     then return Nothing 
                     else (Just <$> newVar) 
                    | n <- ns]                 
     return $ 
       [Alt noLoc 
        (PApp (UnQual c) 
         [case v of  
             Just x  -> PVar $ Ident x 
             Nothing -> PWildCard
         | v <- vs]) 
        (UnGuardedAlt 
         (foldl App (Con (UnQual c)) 
          [case v of
              Just x  -> Var $ UnQual $ Ident x
              Nothing -> Var $ UnQual $ Ident e
          | v <- vs])) 
        (BDecls [])]
  
-- Generates a function to match a constructor, e.g.,
-- having "data X = X Int" it generates "isX = \x -> case x of 
-- {X _ -> True;_ -> False}"
genIs  :: Name -> Int -> Unique Decl
genIs n l = do
 (UnQual n') <- addPrefixToQName isPrefix (UnQual n)
 v <- newVar
 return $ PatBind noLoc (PVar n') (Nothing) 
   (UnGuardedRhs 
    (Lambda noLoc [PVar $ Ident v]
     (Case (Var $ UnQual $ Ident v)
      [Alt noLoc (PApp (UnQual n) [PWildCard|_ <-[1..l]]) 
       (UnGuardedAlt (Con (UnQual (Ident "True"))))(BDecls [])
      ,Alt noLoc PWildCard
       (UnGuardedAlt (Con (UnQual (Ident "False"))))(BDecls [])
      ])))
   (BDecls [])

-- Generates a function that instantiates every filed of a constructor
-- with undefined, e.g., having "data X = X Int" it generates "newX = X undefined"
genNew  :: Name -> Int -> Unique Decl
genNew n l = do
 (UnQual n') <- addPrefixToQName newPrefix (UnQual n)
 return $ PatBind noLoc (PVar n') (Nothing) 
   (UnGuardedRhs 
    (foldl App (Con (UnQual n))  
     [Var $ UnQual $ Ident "undefined"|_ <- [1..l]]  
    )
   )
   (BDecls [])
