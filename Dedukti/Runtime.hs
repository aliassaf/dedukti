-- Copyright © 2009 CNRS - École Polytechnique - INRIA
--
-- Permission to use, copy, modify, and distribute this file for any
-- purpose with or without fee is hereby granted, provided that the above
-- copyright notice and this permission notice appear in all copies.
--
-- THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
-- WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
-- MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
-- ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
-- WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
-- ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
-- OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

-- | All generated Haskell files import this module. The data type
-- declarations are given here, along with the conversion relation and type
-- inference function.

module Dedukti.Runtime
    ( Code(..), Term(..), ap
    , convertible
    , bbox, sbox, obj
    , start, stop
    , checkDeclaration
    , checkRule) where

import qualified Data.ByteString.Char8 as B
import Control.Exception
import Text.Show.Functions ()
import Data.Typeable hiding (typeOf)
import Prelude hiding (pi, catch)
import Data.Time.Clock
import Text.PrettyPrint.Leijen
import System.Exit
import System.Posix.Process (exitImmediately)


-- Exceptions

data SortError = SortError
    deriving (Show, Typeable)

data TypeError = TypeError
    deriving (Show, Typeable)

data RuleError = RuleError Doc Doc
    deriving (Show, Typeable)

instance Exception SortError
instance Exception TypeError
instance Exception RuleError

-- Convertible and static terms.

data Code = Var !Int
          | Con !B.ByteString
          | Lam !(Code -> Code)
          | Pi  Code !(Code -> Code)
          | App Code Code
          | Type
          | Kind
            deriving (Eq, Show)

data Term = TLam !Term !(Term -> Term)
          | TPi  !Term !(Term -> Term)
          | TApp !Term !Term
          | TType
          | Box Code Code
          | UBox Term Code
            deriving Show

instance Eq (Code -> Code)

ap :: Code -> Code -> Code
ap (Lam f) t = f t
ap t1 t2 = App t1 t2

obj :: Term -> Code
obj (Box _ obj) = obj

convertible :: Int -> Code -> Code -> Bool
convertible n (Var x) (Var x') = x == x'
convertible n (Con c) (Con c') = c == c'
convertible n (Lam t) (Lam t') =
    convertible (n + 1) (t (Var n)) (t' (Var n))
convertible n (Pi ty1 ty2) (Pi ty3 ty4) =
    convertible n ty1 ty3 && convertible (n + 1) (ty2 (Var n)) (ty4 (Var n))
convertible n (App t1 t2) (App t3 t4) =
    convertible n t1 t3 && convertible n t2 t4
convertible n Type Type = True
convertible n Kind Kind = True
convertible n _ _ = False

-- | A box in which we didn't put anything.
emptyBox = Box undefined undefined

bbox, sbox :: Term -> Code -> Code -> Term

-- | A big box holds terms of sort Type or Kind
bbox = box [Type, Kind]

-- | A small box holds terms of sort Type.
sbox = box [Type]

box sorts ty ty_code obj_code
    | typeOf 0 ty `elem` sorts = Box ty_code obj_code
    | otherwise = throw SortError

typeOf :: Int -> Term -> Code
typeOf n (Box ty _) = ty
typeOf n (TLam (Box Type a) f) = Pi a (\x -> typeOf n (f (Box a x)))
typeOf n (TPi (Box Type a) f) = typeOf (n + 1) (f (Box a (Var n)))
typeOf n (TApp t1 (Box ty2 t2))
    | Pi tya f <- typeOf n t1, convertible n tya ty2 = f t2
typeOf n (TApp t1 (UBox tty2 t2))
    | Pi tya f <- typeOf n t1, ty2 <- typeOf n tty2,
      convertible n tya ty2 = f t2
typeOf n TType = Kind
typeOf n t = throw TypeError

checkDeclaration :: String -> Term -> IO ()
checkDeclaration x t = catch (evaluate t >> putStrLn ("Checked " ++ x ++ ".")) handler
    where handler (SomeException e) = do
            putStrLn $ "Error during checking of " ++ x ++ "."
            throw e

checkRule :: Term -> Term -> Term
checkRule lhs rhs | convertible 0 (typeOf 0 lhs) (typeOf 0 rhs) = emptyBox
                  | otherwise = throw $ RuleError (pretty (typeOf 0 lhs)) (pretty (typeOf 0 rhs))

start :: IO UTCTime
start = do
  putStrLn "Start."
  getCurrentTime


stop :: UTCTime -> IO ()
stop t = do
  t' <- getCurrentTime
  let total = diffUTCTime t' t
  putStrLn $ "Stop. Runtime: " ++ show total
  -- Use Posix exitImmediately rather than System.Exit to really exit GHCi.
  exitImmediately ExitSuccess

-- Pretty printing.

instance Pretty Code where
  pretty = p 0 where
    p n (Var x) = text (show x)
    p n (Con c) = text (show c)
    p n (Lam f) = parens (int n <+> text "=>" <+> p (n + 1) (f (Var n)))
    p n (Pi ty1 ty2) = parens (int n <+> colon <+> p n ty1 <+> text "->" <+> p (n + 1) (ty2 (Var n)))
    p n (App t1 t2) = parens (p n t1 <+> p n t2)
    p n Type = text "Type"
    p n Kind = text "Kind"
