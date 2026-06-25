{-# OPTIONS --type-in-type #-}

module AnIntroductionToIntuitionisticMathematics where

{-

Intuitionistic Mathematics in Agda:

Intuitionistic Mathematics is a form of constructive mathematics, built on top of intuitionistic logic.

In intuitionistic logic, terminating programs and their types are understood as proofs and propositions respectively.

With enough work, we can formalize any mathematics as code which can be verified mechanically by running a type checker.

This introduction uses an intuitionistic proof assistant and functional programming language called Agda.

If you wish to fill in the exercises, install `agda` and the text editor `emacs`, and run `agda --emacs-mode setup`.

Agda was designed around its powerful interactive editing with emacs, so use another editor at your own discretion.

Other editors with decent support include vscode and neovim, but key combos may vary from the emacs ones taught here.

I personally was shocked to find out that emacs is a normal text editor which could be used without prior experience.

Open this file in emacs and load it into Agda by pressing "C-c C-l", which is emacs-speak for key combo "Ctrl-c Ctrl-l".

If you set everything up correctly, you should now see an empty informational window, and code should be colored:

-}

AxiomOfChoice = {A B : Set} -> ((A -> B) -> A) -> A

{-

A note on logical consistency:

At the top of the file we have enabled an option, "--type-in-type", which makes Agda logically inconsistent.

This means that by abusing something called Girard's Paradox we can technically prove anything, even false propositions.

The advantage of this is that it eliminates a form of bureaucracy known as "universe levels" which can be very annoying.

Additionally, the paradox is quite difficult to take advantage of intentionally, let alone unintentionally.

So, for the sake of learning, rather than rigorous formal verification, this is an appropriate sacrifice to make.

If you have a problem with this, feel free to try to take advantage of Girard's Paradox in the space provided below:

-}



{-

Part 1. Pure Functional Programming

Pure Functional Programming involves programming with functions that do not mutate shared state or have side effects.

This lets use equational reasoning to prove properties about our programs, without having to keep track of shared state.

In Agda, functions are not just pure, they also are total, meaning they always terminate given a valid input.

In Part 2, this very clean and mathematical foundation will enable us to write proofs about our Agda code, *in Agda*.

Chapter 1. Booleans

The booleans are a `Set` containing two elements, `true`, and `false`, and in Agda this can be declared as follows:

-}

data Bool : Set where
  false : Bool
  true : Bool

{-

We can now declare functions between booleans, such as the negation function:

-}

not : Bool -> Bool

{-

This is called a type signature and it states that `not` is a function with a boolean input and a boolean output.

Agda checks that this type signature is respected by the definition of `not`:

-}

not false = true
not true = false

{-

Notice how in Agda we omit the parentheses found in math and most programming languages (e.g. `not(false) = true`).

To define functions accepting multiple input parameters in Agda, we generally use a trick called "Currying".

Agda has no built in notion of pairs or cartesian products, and functions have exactly one input and one output.

So, in place of the "uncurried" function type `A × B -> C`, we can the "curried" function type `A -> (B -> C)`.

Rather than accepting two inputs at once, we accept the first input and return a function accepting the second input.

Consequently we don't write function application like `f(x, y)`, but rather like `f(x)(y)`, or in Agda just `f x y`:

-}

and : Bool -> Bool -> Bool
and false false = false
and false true = true
and true false = true
and true true = true

{-

The above definitions use pattern matching to map every possible pair of inputs to an output.

However we can also bind parameters to variables which match any input:

-}

or : Bool -> Bool -> Bool
or true x = true
or false x = x

{-

Despite looking like equalities, cases are tried top to bottom, with the first match succeeding.

If a later case overlaps with an earlier case, then the equational syntax can be misleading:

-}

xor : Bool -> Bool -> Bool
xor true true = false
xor true false = true
xor false true = true
xor false x = false

{-

The last case gives the impression that `xor false x` is always equal to `false`, for any `x`.

However, it overlaps with the previous case, and only matches if the `xor false true` case doesn't match.

Agda's syntax highlighting colors this case to indicate that it overlaps with previous cases and is not a true equality.

Naturally, functions may be defined in terms of other functions:

-}

implies : Bool -> Bool -> Bool
implies l r = or r (not l) -- (l ⇒ r) == r ∨ ¬l

{-

Notice how function application associates to the left, so `or r (not l)` is the same as as `or(r)(not(l))`.

Like any programming language, Agda supports comments which are ignored by the typechecker and have no effect on code.

This is a block comment, delimited by `{-` and `-}`, however we can also write single line comments starting with `--`.

It can be useful to comment out code which we don't want Agda to load, e.g. because it has an error:

-}

-- Bad-xor : Bool -> Bool -> Bool
-- Bad-xor false x = x

{-

By selecting lines of code and hitting "M-;" (emacs for "alt+semicolon"), you can easily comment them out or back in.

Try temporarily commenting Bad-xor back in and reloading with C-c C-l to see what kind of error you get.

Agda allows us to use almost any characters we want as part of a name, including `-` and `'`.

One character with a special meaning in a name, however, is underscore, which is used for so called mixfix syntax.

Each underscore in a name indicates where a parameter belongs syntactically:

-}

_&&_ : Bool -> Bool -> Bool
l && r = and l r

{-

This defines a synonym for `and` called `_&&_`, where `l && r` carries the same meaning as `_&&_ l r`.

We could have just as well written "_&&_ l r = and l r" for the definition, there is absolutely no difference.

While underscores can have quite a few meanings in Agda which we will cover later, one of them is to discard an input:

-}

nand : Bool -> Bool -> Bool
nand true x = not x
nand false _ = true

{-

It wouldn't have hurt to name the second input parameter `x` again, but the `_` explicitly doesn't bring it into scope.

Another cool thing we can do in Agda is pass functions as inputs to functions:

-}

alwaysReturnsTrue : (Bool -> Bool) -> Bool
alwaysReturnsTrue f = f false && f true

{-

Exercises:

If you uncomment the following exercise and reload, the question mark should turn into a "hole" which looks like {! !}.

-}

-- A synonym for `or`
-- _||_ : Bool -> Bool -> Bool
-- x || y = ?

{-

Holes represent a missing part of a program that you plan to complete later, and can be filled in interactively.

A hole can be filled in by writing something in it, and pressing C-c C-Space to type check and enter it in.

Any error in an Agda file typically renders its editor support useless, making holes crucial to keeping code well-typed.

Hole-based editing will form the basis for interactive programming and theorem proving in Agda.

Use these exercises to experiment and get used to Agda's unusual "curried" syntax:

-}

-- and3 : Bool -> Bool -> Bool -> Bool
-- and3 x y z = ?

-- A synonym for `implies`, but missing a definition
-- _=>_ Bool -> Bool -> Bool

-- A synonym for `xor`, but missing a type signature
-- x ^^ y = ?

-- Define boolean equality, aka biimplication, as the symbol _<=>_

-- Returns true if the provided function returns false regardless of what input it is given
-- alwaysReturnsFalse : (Bool -> Bool) -> Bool
-- alwaysReturnsFalse f = ?

{-

Tips and Tricks:

Make sure to always reload after making changes outside of a hole, otherwise Agda won't know about them.

If you rename a parameter variable and try to use it to fill in a hole without reloading, Agda wont recognize it.

To test your code, you can normalize an expression within a hole by entering the key combo C-c C-n.

To create a throw-away hole for such purposes you can use an anonymous, unnamed definition like "_ = ?".

Try uncommenting the following line, placing your cursor in the hole, and normalizing the contained expression:

-}

-- _ = {! true && false !}

{-

Use holes and C-c C-n liberally to test your code while commenting them out to avoid polluting the informational window.

Challenge Exercises:

-}

-- While there are two distinct `Bool`s, there are four distinct `Bool -> Bool`s

-- Pick some way to order the `Bool -> Bool`s 1st through 4th and fill in the following definitions
-- firstBoolToBool : Bool -> Bool
-- firstBoolToBool x = ?
-- secondBoolToBool : Bool -> Bool
-- secondBoolToBool x = ?
-- thirdBoolToBool : Bool -> Bool
-- thirdBoolToBool x = ?
-- fourthBoolToBool : Bool -> Bool
-- fourthBoolToBool x = ?

-- Compares two `Bool -> Bool`s for equality
-- _equalsBoolToBool_ : (Bool -> Bool) -> (Bool -> Bool) -> Bool
-- f equalsBoolToBool g = ?

-- An increment function which wraps around from fourth to first
-- nextBoolToBool : (Bool -> Bool) -> Bool -> Bool
-- nextBoolToBool f = ?

-- Similarly, an addition function which wraps around from fourth to first
-- addBoolToBool : (Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool
-- addBoolToBool f g = ?

{-

Chapter 2. Natural Numbers

The booleans were defined by the unique ways they can be constructed, namely by the "constructors" `true` and `false`.

The Set of natural numbers are defined by the element `zero`, and the successor function `suc n` aka "n + 1":

-}

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-

This works because for every natural number, there is *exactly* one way to write it in terms of its constructors:

-}

one : Nat
one = suc zero -- 0 + 1

two : Nat
two = suc (suc zero) -- 0 + 1 + 1

three : Nat
three = suc (suc (suc zero)) -- 0 + 1 + 1 + 1

{-

We could even port this into a typical imperative language like:
  interface Nat {};
  class zero extends Nat {};
  class suc extends Nat { Nat n; };
  ...
  Nat three = new suc(n = new suc(n = new suc(n = zero())))

This singly-linked-list representation of the natural numbers is obviously quite bloated and inefficient for most tasks.

However, as we will see soon, it excels at justifying the termination of recursive functions accepting natural numbers.

Just like with the booleans, we can pattern match on natural numbers by handling both their `zero` and `suc` cases:

-}

-- A "fake" predecessor function, which stops decrementing inputs at zero so that we don't have to deal with integers
pred : Nat -> Nat
pred zero = zero -- pred(0) = 0
pred (suc n) = n -- pred(n + 1) = n

{-

When we handle the `suc` case, we are handed the input to which it was applied, which happens to be the input minus one.

We can also nest patterns, e.g. by matching again against the natural number we are handed in the `suc` case:

-}

isTwo : Nat -> Bool
isTwo (suc (suc zero)) = true
isTwo other = false

isGreaterThanTwo : Nat -> Bool
isGreaterThanTwo (suc (suc (suc _))) = true
isGreaterThanTwo other = false

{-

As mentioned previously, we can also define functions recursively:

-}

isEven : Nat -> Bool
isEven zero = true -- zero is even
isEven (suc n) = not (isEven n) -- n+1 is even <=> n is not even

-- Again, a "fake" halving function, which rounds up so we don't have to deal with fractions
halfOf : Nat -> Nat
halfOf zero = zero -- 0 / 2 = 0
halfOf (suc zero) = suc zero -- 1 / 2 = 1
halfOf (suc (suc n)) = suc (halfOf n) -- (n + 2) / 2 = 1 + n / 2

{-

The recursive calls are clearly safe since `n` is literally a smaller piece of data than `suc n` or `suc (suc n)`.

If recursive calls only are made on structurally smaller pieces of data, then the function must terminate eventually.

This is in contrast to the following definition, which is not a total function, and results in a termination error:

-}

-- bad-isEven : Nat -> Bool
-- bad-isEven zero = true
-- bad-isEven n = not (bad-isEven (suc n))

{-

Here, not only is the input parameter not shrinking with each recursive call, it is growing, leading to non-termination.

However, a function being total is no guarantee that the termination checker will be able to see that it is total.

For example, we can't use a function which makes its input smaller, such as `pred`, in place of pattern matching:

-}

-- isEven' : Nat -> Bool
-- isEven' zero = true
-- isEven' n = isEven' (pred n)

{-

While the above definition of isEven' is equivalent to the original isEven, Agda cannot see that it terminates.

This may sound like a serious limitation, but in practice it can be worked around with a variety of tricks.

For example, say we want to compute the minimum number of bits required to represent a natural number in binary.

We can do so by observing how often we must halve a number (rounded up) before it reaches 1:
  binLength(0) = 1
  binLength(1) = 1
  binLength(n) = 1 + (binLength(n / 2))

However we cannot halve a number by pattern matching, since halving is an operation which itself requires recursion:

-}

-- Bad-binLength : Nat -> Nat
-- Bad-binLength zero = one
-- Bad-binLength (suc zero) = one
-- Bad-binLength n = suc (Bad-binLength (halfOf n))

{-

So, to guarantee termination, we can use a helper function which recurses over a sufficiently large dummy parameter:

-}

binLength-helper : Nat -> Nat -> Nat
binLength-helper dummy zero = one -- binLength(0) = 1
binLength-helper dummy (suc zero) = one -- binLength(1) = 1
binLength-helper (suc dummy) n = suc (binLength-helper dummy (halfOf n)) -- binLength(n) = 1 + (binLength(n / 2))
binLength-helper zero n = zero -- This case should never be reached and is only here to reassure the termination checker

binLength : Nat -> Nat
binLength n = binLength-helper n n

{-

The dummy parameter can be thought of as "recursion fuel", and is irrelevant to the computation if it is large enough.

While it is good to be aware of this admittedly quite ugly trick, the reader will not be expected to use it.

Most definitions, and any (non-challenge) exercise in this tutorial, can be completed elegantly with regular recursion:

-}

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

{-

Finally, we will note that this incredibly inefficient representation of natural numbers can be remedied in Agda:

-}

-- Allows natural numbers to be stored compactly in memory, and also written efficiently as in the following definitions
{-# BUILTIN NATURAL Nat #-}

four : Nat
four = 4

five : Nat
five = 5

isThree : Nat -> Bool
isThree 3 = true
isThree _ = false

-- Allows plus to be executed efficiently, e.g. so following hole's contents can be normalized without Agda hanging
{-# BUILTIN NATPLUS _+_ #-}

-- _ = {! 200000000000000000 + 300000000000000000 !}

{-

Exercises:

Agda will help you interactively perform pattern matching on a variable of your choice with the case-split command.

Try uncommenting the following line, reloading, placing your cursor in the hole, and pressing C-c C-c:

-}

-- isOdd : Nat -> Bool
-- isOdd n = {! n !}

{-

Use Agda's interactive editing to fill in the following definitions:

-}

-- Multiplication
-- _*_ : Nat -> Nat -> Nat
-- n * m = ?

-- Equality
-- _equalsNat_ : Nat -> Nat -> Bool
-- n equalsNat m = ?

-- Less-than
-- _<_ : Nat -> Nat -> Bool
-- n < m = ?

-- Minimum
-- _min_ : Nat -> Nat -> Nat
-- n min m = ?

-- Maximum
-- _max_ : Nat -> Nat -> Nat
-- n max m = ?

-- A "fake" minus function which stops at zero rather than returning a negative integer
-- _-_ : Nat -> Nat -> Nat
-- n - m = ?

-- Define the factorial function

-- Sum of the first n outputs of a function
-- sum : (Nat -> Nat) -> Nat -> Nat
-- sum f n = ?

-- Product of the first n outputs of a function
-- product : (Nat -> Nat) -> Nat -> Nat
-- product f n = ?

-- After correctly filling in and testing the above defintions, comment in the following BUILTIN-pragmas.
-- Note that BUILTIN-pragmas verify your definitions on a best-effort basis and may fail even for a correct definition.
-- {-# BUILTIN NATTIMES _*_ #-}
-- {-# BUILTIN NATMINUS _-_ #-}
-- {-# BUILTIN NATEQUALS _equalsNat_ #-}
-- {-# BUILTIN NATLESS _<_ #-}

{-

Tips and Tricks:

Use C-c C-f and C-c C-b to jump to the next or previous holes respectively, speeding up your interactive editing.

Challenge Exercises:

-}

-- We can think of a `Nat -> A` as an infinite sequence of `A`s.
-- Therefore, we can think of a `Nat -> Nat -> Bool` as an infinite sequence of infinite sequences of bools.
-- Prove informally that there exists no `Nat -> Nat -> Bool` which enumerates every `Nat -> Bool`.
-- For any `Nat -> Nat -> Bool`, construct a counterexample `Nat -> Bool` which it does not return for any input `Nat`:
-- infinite-sequences-are-enumerable-counterexample : (Nat -> Nat -> Bool) -> Nat -> Bool
-- infinite-sequences-are-enumerable-counterexample f n = ?

-- Try defining some variant of the division and modulo operations that passes the termination checker.
-- Beware: this may be harder than it sounds.

{-

Chapter 3. Parametric Polymorphism

So far we have worked with a number of Sets, such as Nat, Bool, as well as many function-Sets.

Some functions, however, can be defined for any Set, as is the case with the identity function:

-}

idForBool : Bool -> Bool
idForBool x = x

idForNat : Nat -> Nat
idForNat x = x

idForBoolToBool : (Bool -> Bool) -> Bool -> Bool
idForBoolToBool x = x

{-

In such a situation, we can accept a named parameter in Set, and define the rest of the type in terms of that parameter:

-}

idFor : (A : Set) -> A -> A
idFor A x = x

idForBool' : Bool -> Bool
idForBool' x = idFor Bool x

idForNat' : Nat -> Nat
idForNat' x = idFor Nat x

{-

We also could have written out the above definitions like e.g. `idForBool' x = idFor Bool x`.

In most languages, type parameters are special, whereas in Agda, they are just regular parameters of type Set.

In fact, you can name any parameter in a type signature, just like we previously named the Set parameter `A`:

-}

triple : (x : Nat) -> Nat
triple zero = zero
triple (suc x) = suc (suc (suc (triple x)))

{-

Here we have brought the first parameter into scope in the type signature rather than just in the definition.

The `x` in the definition is entirely independent from (and in fact not even equal to) the `x` in the type signature.

Naming the first input `x` in the type signature here accomplished nothing, since we only used it in the definition.

On the other hand, `A` was only useful to name in the type signature of `idFor`, and didn't get used in the definition.

Not only was this Set parameter not useful at the definition, but it could have been inferred at the call site:

-}

idForBool'' : Bool -> Bool
idForBool'' x = idFor _ x

idForNat'' : Nat -> Nat
idForNat'' x = idFor _ x

{-

In Agda, underscore may be used to infer an unambiguous input to a function based on surrounding type constraints.

This usage of underscore is distinct from yet aesthetically complementary to how it can be used to hide parameters:

-}

idFor' : (A : Set) -> A -> A
idFor' _ x = x

{-

In simple cases with an unambiguous solution, Agda will almost always be able to infer the correct type.

For this reason, Agda has a special syntax for implicit parameters, which are hidden and inferred by default:

-}


id : {A : Set} -> A -> A
id x = x

idForBool''' : Bool -> Bool
idForBool''' x = id x

idForNat''' : Nat -> Nat
idForNat''' x = id x

{-

The difference between regular and implicit parameters is purely syntactical.

Just as you can opt in to inference with underscore, you can explicitly pass an implicit parameter with curly braces:

-}

idForBool'''' : Bool -> Bool
idForBool'''' x = id {Bool} x

idForNat'''' : Nat -> Nat
idForNat'''' x = id {Nat} x

{-

One thing worth noting about Sets is that they are not data, and you cannot pattern match on them:

-}

-- Bad-idFor : (A : Set) -> A -> A
-- Bad-idFor Nat x = suc x
-- Bad-idFor Bool x = not x
-- Bad-idFor Other x = x

{-

If you comment in the above definition, Agda treats Nat and Bool (and Other) as fresh variable names, not patterns.

These variable names shadow the previously defined Nat and Bool, and are the same as the `A` from the type signature.

Since `suc` and `not` only work on a `Nat` or `Bool` respectively, and not with any arbitrary Set, you get a type error.

On top of this restriction, we also may not pattern match on a parameter without knowing its actual datatype:

-}


-- Bad-id : {A : Set} -> A -> A
-- Bad-id true = false
-- Bad-id false = true
-- Bad-id other = other

{-

These two restrictions more or less sum up what it means for polymorphic functions to be "parametric".

Parametricity guarantees, for instance, that the identity function is the only function of type `{A : Set} -> A -> A`.

Paremetrically polymorphic functions cannot have differing behavior depending on the concrete type they are used with.

One useful application of this is to encode datatypes like Nat and Bool *as* parametrically polymorphic function types:

-}

-- A type alias, to avoid repeatedly writing out the somewhat long-winded type `{A : Set} → A → A → A`
Bool' : Set
Bool' = {A : Set} → A → A → A

false' : Bool'
false' x y = x

true' : Bool'
true' x y = y

not' : Bool' -> Bool'
not' f x y = f y x

{-

Indeed, there really only are two ways to produce an `A` given two `A`s, if you know nothing more about `A`.

With a slightly cleverer polymorphic function type, we can also encode the natural numbers using parametricity:

-}

Nat' : Set
Nat' = {A : Set} → (A → A) → A → A

zero' : Nat'
zero' f x = x

one' : Nat'
one' f x = f x

two' : Nat'
two' f x = f (f x)

three' : Nat'
three' f x = f (f (f x))

{-

Exercises:

-- todo: C-c C-, and C-c C-.

-}

-- and' : Bool' -> Bool' -> Bool'

-- suc' : Nat' -> Nat'
-- suc' = ?

-- BoolToBool' aka if_then_else_
-- Bool'ToBool

-- NatToNat'
-- Nat'ToNat
