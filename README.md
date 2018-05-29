# Reflecting simply typed lambda calculus into Idris
--------------------------------------------------

Culminates in this definition:

```idris
example_3 : Maybe (Int -> Int -> Int)
example_3 = ofType "\\x : int. \\y : int. x" (TyArr TyInt (TyArr TyInt TyInt))
```

which evaluates to `Just (\a, b => a)`

It says "This string should express a lambda calculus term of type `Int -> Int -> Int`".
If the term fails to parse or typecheck, `ofType` will return `Nothing`.

## Future Work

Use elaborator reflection to write and compile:

```idris
elabLC : String -> Elab ()
elabLC = ...

example_4 : Int -> Int -> Int
example_4 = %runElab (elabLC "\\x : int. \\y : int. x")
```

We should be able use the goal type to guide a compile-time implementation of the function,
and provide nice error messages if things go wrong at any stage.
