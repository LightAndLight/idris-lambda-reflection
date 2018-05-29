module Main

import Data.Fin
import Data.Vect
import Data.HVect
import Data.String
import Text.Parser
import Pruviloj.Derive.DecEq

%default total

%language ElabReflection

data Ty = TyBool | TyInt | TyArr Ty Ty

Quotable Ty TT where
  quotedTy = `(Ty)

  quote TyBool = `(TyBool)
  quote TyInt = `(TyInt)
  quote (TyArr a b) = `(TyArr ~(quote a) ~(quote b))

{-
Pruviloj's deriving is currently broken so we have to write it by hand

decTyEq : (xs, ys : Ty) -> Dec (xs = ys)
%runElab (deriveDecEq `{decTyEq})
-}
Uninhabited (TyBool = TyInt) where
  uninhabited Refl impossible

Uninhabited (TyBool = TyArr a b) where
  uninhabited Refl impossible

Uninhabited (TyInt = TyBool) where
  uninhabited Refl impossible

Uninhabited (TyInt = TyArr a b) where
  uninhabited Refl impossible

Uninhabited (TyArr a b = TyBool) where
  uninhabited Refl impossible

Uninhabited (TyArr a b = TyInt) where
  uninhabited Refl impossible

decTyEq : (xs, ys : Ty) -> Dec (xs = ys)
decTyEq TyBool TyBool = Yes Refl
decTyEq TyBool TyInt = No absurd
decTyEq TyBool (TyArr _ _) = No absurd
decTyEq TyInt TyInt = Yes Refl
decTyEq TyInt TyBool = No absurd
decTyEq TyInt (TyArr _ _) = No absurd
decTyEq (TyArr a b) (TyArr a' b') =
  case decTyEq a a' of
    Yes Refl =>
      case decTyEq b b' of
        Yes Refl => Yes Refl
        No contra' => No $ \Refl => contra' Refl
    No contra => No $ \contra' => case contra' of Refl => contra Refl
decTyEq (TyArr _ _) TyBool = No absurd
decTyEq (TyArr _ _) TyInt = No absurd


data Lambda : {n : Nat} -> Vect n Ty -> Ty -> Type where
  TmVar
     : {n : Nat}
    -> {v : Vect n Ty}
    -> (ix : Fin n)
    -> Lambda {n} v (index ix v)
  TmAbs
     : {ty, ty' : Ty}
    -> {n : Nat}
    -> {v : Vect n Ty}
    -> Lambda {n=S n} (ty :: v) ty'
    -> Lambda {n} v (TyArr ty ty')
  TmApp
     : {ty, ty' : Ty}
    -> {n : Nat}
    -> {v : Vect n Ty}
    -> Lambda {n} v (TyArr ty ty')
    -> Lambda {n} v ty
    -> Lambda {n} v ty'
  TmInt
     : {n : Nat}
    -> {v : Vect n Ty}
    -> Int
    -> Lambda {n} v TyInt
  TmBool
    : {n : Nat}
    -> {v : Vect n Ty}
    -> Bool
    -> Lambda {n} v TyBool

example_1 : Lambda [] (TyArr TyInt TyInt)
example_1 = TmAbs (TmVar 0)

reflectTy : Ty -> Type
reflectTy TyBool = Bool
reflectTy TyInt = Int
reflectTy (TyArr t1 t2) = reflectTy t1 -> reflectTy t2

map_dist
   : {n : Nat}
  -> (ix : Fin n)
  -> (f : a -> b)
  -> (v : Vect n a)
  -> index ix (map f v) = f (index ix v)
map_dist FZ f  [] impossible
map_dist (FS _) f  [] impossible
map_dist FZ f  (x :: xs) = Refl
map_dist (FS ix') f (x :: xs) = map_dist ix' f xs

reflectLambda : {ty : Ty} -> Lambda [] ty -> reflectTy ty
reflectLambda (TmVar FZ) impossible
reflectLambda (TmVar (FS _)) impossible
reflectLambda e = reflectLambda_inner [] e
  where
    reflectLambda_inner
       : {ty : Ty}
      -> {n : Nat}
      -> {v : Vect n Ty}
      -> HVect (map reflectTy v)
      -> Lambda v ty
      -> reflectTy ty
    reflectLambda_inner {v} vars (TmVar ix) =
      rewrite
        sym (map_dist ix reflectTy v)
      in
        index ix vars
    reflectLambda_inner vars (TmAbs e) =
      \var => reflectLambda_inner (var :: vars) e
    reflectLambda_inner vars (TmApp f x) =
      reflectLambda_inner vars f (reflectLambda_inner vars x)
    reflectLambda_inner vars (TmInt i) = i
    reflectLambda_inner vars (TmBool b) = b

example_2 : Int -> Int
example_2 = reflectLambda example_1

data Lambda' : Type where
  TmVar' : String -> Lambda'
  TmAbs' : String -> Ty -> Lambda' -> Lambda'
  TmApp' : Lambda' -> Lambda' -> Lambda'
  TmInt' : Int -> Lambda'
  TmBool' : Bool -> Lambda'

Quotable Bool TT where
  quotedTy = `(Bool)

  quote True = `(True)
  quote False = `(False)

Quotable Bool Raw where
  quotedTy = `(Bool)

  quote True = `(True)
  quote False = `(False)

Quotable Lambda' TT where
  quotedTy = `(Lambda')

  quote (TmVar' s) = `(TmVar' ~(quote s))
  quote (TmAbs' a b c) = `(TmAbs' ~(quote a) ~(quote b) ~(quote c))
  quote (TmApp' a b) = `(TmApp' ~(quote a) ~(quote b))
  quote (TmInt' i) = `(TmInt' ~(quote i))
  quote (TmBool' b) = `(TmBool' ~(quote b))

char : Char -> Grammar Char True Char
char c = terminal (\a => if a == c then Just a else Nothing)

digit : Grammar Char True Char
digit = terminal (\a => if isDigit a then Just a else Nothing)

fromMaybe : Maybe a -> Grammar Char False a
fromMaybe res =
  case res of
    Nothing => fail "not a natural number"
    Just a => pure a

nat : Grammar Char True Nat
nat = map (parsePositive . pack) (some digit) >>= fromMaybe

int : Grammar Char True Int
int = map (parseInteger . pack) (some digit) >>= fromMaybe

symbol : Char -> List Char -> Grammar Char True (List Char)
symbol c [] = do
  c' <- char c
  pure [c]
symbol c (d :: ds) = do
  c' <- char c
  rest <- symbol d ds
  pure (c' :: rest)

letter : Grammar Char True Char
letter = terminal (\a => if isLower a then Just a else Nothing)

mutual
  tyAtom : Grammar Char True Ty
  tyAtom =
    (do
       symbol 'b' (unpack "ool")
       pure TyBool) <|>
    (do
       symbol 'i' (unpack "nt")
       pure TyInt) <|>
    (do
       char '('
       t <- ty
       char ')'
       pure t)

  ty : Grammar Char True Ty
  ty = do
    t <- tyAtom
    ts <- many (char '-' *> char '>' *> tyAtom)
    pure (foldr TyArr t ts)

grammar : Grammar Char True Lambda'
grammar = grammar'
  where
    mutual
      atom : Grammar Char True Lambda'
      atom =
        TmVar' . pack <$> some letter <|>
        const (TmBool' True) <$> symbol 't' (unpack "rue") <|>
        const (TmBool' False) <$> symbol 'f' (unpack "alse") <|>
        TmInt' <$> int <|>
        do
          const () <$> char '('
          g <- grammar'
          const () <$> char ')'
          pure g

      app : Grammar Char True Lambda'
      app = do
        a <- atom
        as <- many (some (char ' ') *> atom)
        pure (foldl TmApp' a as)

      grammar' : Grammar Char True Lambda'
      grammar' =
        (do
           char '\\'
           n <- some letter
           many (char ' ')
           char ':'
           many (char ' ')
           t <- ty
           char '.' *> many (char ' ')
           e <- grammar'
           pure (TmAbs' (pack n) t e)) <|>
        app

parseLambda : String -> Maybe Lambda'
parseLambda input =
  case parse grammar (unpack input) of
    Left _ => Nothing
    Right (a, _) => Just a

lookupVect : {n : Nat} -> String -> Vect n (String, a) -> Maybe a
lookupVect s [] = Nothing
lookupVect s ((s', x) :: xs) =
  if s == s' then Just x else lookupVect s xs

typecheck : Lambda' -> Maybe (ty : Ty ** Lambda [] ty)
typecheck (TmVar' _) = Nothing
typecheck e = typecheck_inner [] [] e
  where
    typecheck_inner
       : {n : Nat}
      -> (ixs : List (String, Fin n))
      -> (v : Vect n Ty)
      -> Lambda'
      -> Maybe (ty : Ty ** Lambda v ty)
    typecheck_inner ixs v (TmVar' n) = do
      ix <- lookup n ixs
      let ty = index ix v
      pure (ty ** TmVar ix)
    typecheck_inner ixs v (TmAbs' n ty e) = do
      (e_ty ** e') <-
        typecheck_inner
          ((n, 0) :: map (\(a, b) => (a, FS b)) ixs)
          (ty :: v)
          e
      pure (TyArr ty e_ty ** TmAbs e')
    typecheck_inner ixs v (TmApp' f x) = do
      (f_ty ** f') <- typecheck_inner ixs v f
      (x_ty ** x') <- typecheck_inner ixs v x
      case f_ty of
        TyArr from to =>
          case decTyEq from x_ty of
            Yes Refl => Just (_ ** TmApp f' x')
            No _ => Nothing
        _ => Nothing
    typecheck_inner ixs v (TmBool' b) = Just (TyBool ** TmBool b)
    typecheck_inner ixs v (TmInt' i) = Just (TyInt ** TmInt i)

ofType : String -> (ty : Ty) -> Maybe (reflectTy ty)
ofType str ty =
  map reflectLambda $ do
    l <- parseLambda str
    (ty' ** l') <- typecheck l
    case decTyEq ty ty' of
      Yes Refl => Just l'
      No _ => Nothing

example_3 : Maybe (Int -> Int -> Int)
example_3 = ofType "\\x : int. \\y : int. x" (TyArr TyInt (TyArr TyInt TyInt))

main : IO ()
main =
  case example_3 of
    Just f => print $ f 1 3
    Nothing => print 2

{-
Elaborator reflection

fromTT : TT -> Elab Ty
fromTT tt =
  case tt of
    `(~a -> ~b) => TyArr <$> fromTT a <*> fromTT b
    `(Int) => pure TyInt
    `(Bool) => pure TyBool
    _ => fail [TextPart "Cannot convert", TermPart tt, TextPart "to", TermPart `(Ty)]

reflect : String -> Elab ()
reflect str = do
  l <-
    maybe
      (fail [TextPart "error parsing", TermPart (quote str)])
      pure
      (parseLambda str)
  (ty ** l') <-
    maybe
      (fail [TextPart "type error in", TermPart (quote l)])
      pure
      (typecheck l)
  (_, goalTy) <- getGoal
  ty' <- fromTT goalTy
  case decTyEq ty ty' of
    No _ =>
      fail
        [ TextPart "mismatch between goal type"
        , TermPart (quote ty')
        , TextPart "and actual type"
        , TermPart (quote ty)
        ]
    Yes prf => do
      [hole_0, hole_2] <- getHoles
        | otherwise => fail [TextPart "incorrect number of holes"]
      focus hole_2
      reflect_inner {ty} hole_2 [] [] l'
where
  reflect_inner
     : {ty : Ty}
    -> TTName
    -> (ns : Vect n TTName)
    -> (v : Vect n Ty)
    -> Lambda v ty -> Elab ()
  reflect_inner hole ns v (TmVar ix) = fill $ Var (index ix ns)
  reflect_inner hole ns v (TmApp f x) = debug {a=()}
  reflect_inner hole ns v (TmAbs {ty} e) = debug {a=()}
  reflect_inner hole ns v (TmInt i) = fill (quote i)
  reflect_inner hole ns v (TmBool b) = fill (quote b)

test : Int -> Int
test = %runElab (reflect "\\x : int. x")
-}