# Reflecting simply typed lambda calculus into Idris
--------------------------------------------------

## Runtime Reflection

Culminates in this definition:

```idris
example_3 : Maybe (Int -> Int -> Int)
example_3 = ofType "\\x : int. \\y : int. x" (TyArr TyInt (TyArr TyInt TyInt))
```

which evaluates to `Just (\a, b => a)`

It says "This string should express a lambda calculus term of type `Int -> Int -> Int`".
If the term fails to parse or typecheck, `ofType` will return `Nothing`.

## Compile Time Reflection

Using elaborator reflection, we can parse and typecheck the string at compile
time, and build up the corresponding Idris syntax tree. If the Idris function
has a type that doesn't match the lambda expression, or the expression fails
to parse, then an error will be reported.

```idris
test1 : (Int -> Int) -> Int -> Int
test1 = %runElab (reflect "\\f : int -> int. \\x : int. f x")

test2 : Int -> Int
test2 = %runElab (reflect "\\x : int. x")

test3 : Int -> Bool
test3 = %runElab (reflect "\\x : int. true")

test4 : Bool
test4 = %runElab (reflect "(\\x : bool. x) true")
```
