-- This option technically makes Agda logically inconsistent, in exchange for a greatly improved learning experience
{-# OPTIONS --type-in-type #-}

module AnIntroductionToIntuitionisticMathematics where

{-

Preface.

Intuitionistic Mathematics may be used to construct formal proofs which are well defined mathematical objects.

Such proofs may be seen simply as programs, and propositions accordingly as properties or types of said programs.

With enough work, we can formalize all of mathematics as typed code which can be formally verified by a type checker.

This interactive tutorial and exercise-book uses an intuitionistic proof assistant and programming language called Agda.

To fill in the exercises you must install `agda` and `emacs`, and run `agda --emacs-mode setup` before starting emacs.

Open this file in emacs and load it into Agda by pressing "C-c C-l", which refers to the key combo "Ctrl-c Ctrl-l".

If everything is set up correctly, you should now see an (empty) informational window, and code should be colored.

In emacs you can zoom in and out with "C-x C-+" (Ctrl-x Ctrl-plus) and "C-x C--" (Ctrl-x Ctrl-minus) respectively.

You can cancel most key combos and commands in emacs with "C-g" (Ctrl-g), or otherwise by hitting escape three times.

Part 1. Pure Functional Programming

A "pure" function always produces one and the same output for a given input, without causing side effects.

Pure functions have a mathematical flavor, since we can use equational reasoning to prove properties about them.

In Agda, functions are required not just to be pure but also "total", meaning they may not fail or loop indefinitely.

This is not to say that we cannot write, say, imperative functions, just that we must model them with pure functions.

In Part 2, this very clean and mathematical foundation will enable us to write proofs about our Agda code, *in Agda*.

Chapter 1. Booleans

The booleans are a `Set` containing two elements, `true`, and `false`, and in Agda this can be declared as follows:

-}

data Bool : Set where
  false : Bool
  true : Bool

{-

"X : Y" means "X is of type Y", so we have effectively declared "Bool is a Set, false is a Bool, and true is a Bool".

We can now declare the existence of functions between booleans, such as the negation function:

-}

not : Bool -> Bool

{-

This is called a type signature and it states that `not` is a function with a boolean input and a boolean output.

Agda checks that this type signature is respected by the definition of `not`, which we can give as follows:

-}

not false = true
not true = false

{-

`not` applied to an input of `false` results in it returning an output of `true`, and vice versa.

Agda lets us leave out the parentheses used in most programming languages and mathematics (as in "not(false) = true").

To define functions accepting multiple input parameters in Agda, we use a trick called "Currying".

Rather than accepting two inputs at once, we can accept one input, and then output a function accepting another input.

So instead of the "uncurried" function type `(A, B) -> C`, we use the "curried" function type `A -> (B -> C)`.

Consequently we don't write function application like `f(x, y)`, but rather like `f(x)(y)`, or in Agda just `f x y`.

Notably, the function arrow is right-associative, meaning `A -> (B -> C)` can be written simply as `A -> B -> C`.

One such function with two inputs and one output is the boolean `and` operation:

-}

and : Bool -> Bool -> Bool
and false false = false
and false true = false
and true false = false
and true true = true

{-

The definitions of `not` and `and` use so-called "pattern matching" to map every possible set of inputs to an output.

However we can also bind input parameters to variables, which match any input and can be used to define an output:

-}

or : Bool -> Bool -> Bool
or false x = x
or true x = true

{-

Despite looking like equalities, cases are technically tried from top to bottom, with only the first match succeeding.

If a later case overlaps with an earlier case, then the equational syntax can be misleading:

-}

xor : Bool -> Bool -> Bool
xor true true = false
xor true false = true
xor false true = true
xor false x = false

{-

The last case gives the impression that `xor false x` is always equal to `false`, for any `x`.

However, it overlaps with the previous case, and therefore only holds if the inputs do not match `false true`.

Agda's syntax highlighting colors this case to indicate that it overlaps with previous cases and is not a true equality.

Naturally, functions may also be defined in terms of other previously defined functions:

-}

implies : Bool -> Bool -> Bool
implies l r = or r (not l) -- "l implies r" is equivalent to "r or not l"

{-

Function application is left-associative, so `or r (not l)` is parsed as `or(r)(not(l))`, not as `or(r(not(l)))`.

The parentheses used here are critical, as `or r not l` would be parsed as `or(r)(not)(l)`.

Try deleting these parentheses, reloading with C-c C-l, and making sense of the error message you get.

Be sure to undo these changes and reload again to get rid of the error message.

Like any programming language, Agda supports comments, which are ignored by the typechecker and have no effect on code.

Block comments are delimited by `{-` and `-}`, and single-line comments begin with `--`.

It can be useful to comment out code which we don't want Agda to load, e.g. because it has an error:

-}

-- bad-xor : Bool -> Bool -> Bool
-- bad-xor false x = x

{-

By selecting lines of code and hitting "C-x C-;" (Ctrl-x Ctrl-semicolon), you can easily comment them out or back in.

Try temporarily commenting bad-xor back in and reloading with C-c C-l to see what kind of error you get.

Note that Agda lets us to use nearly any character as part of a name, including `-`, `'`, and even unicode characters.

One character with a special meaning in a name, however, is underscore, which is used for so-called "mixfix" syntax.

Each underscore in the name of a function indicates where an input parameter belongs syntactically:

-}

_&&_ : Bool -> Bool -> Bool
l && r = and l r

{-

This defines a synonym for `and` called `_&&_`, where `l && r` carries the same exact meaning as `_&&_ l r`.

We could have just as well written "_&&_ l r = and l r" for the definition, as there is absolutely no difference.

Note that the whitespace between each symbol is mandatory, and "l&&r" would be parsed as a singular, unrelated symbol.

Another useful thing we can do in Agda is define "higher order functions" which accept other functions as inputs:

-}

-- Tells you whether the provided function outputs true for any input
always-outputs-true : (Bool -> Bool) -> Bool
always-outputs-true f = f false && f true

{-

Notice that we need to wrap the `Bool -> Bool` argument in parentheses, since `->` is not left-associative.

Not only are functions treated as first class values in Agda, but types are as well, allowing us to define type aliases:

-}

BoolToBool : Set
BoolToBool = Bool -> Bool

always-outputs-false : BoolToBool -> Bool
always-outputs-false f = not (f false) && not (f true)

{-

BoolToBool is a regular definition, but it has the type Set, and can be used anywhere where a Set can be used.

When used in a type signature, Agda will happily substitute in the definition of BoolToBool before type checking.

Exercises:

If you uncomment the following exercise and reload, the question mark should turn into a "hole" which looks like { }0.

-}

-- Ex1.1: Define a synonym for `or`

-- _||_ : Bool -> Bool -> Bool
-- x || y = ?

{-

Holes represent a missing part of a program that you plan to complete later, and can be filled in interactively.

Write an expression in this hole and press C-c C-Space to ask Agda to type check it, and if successful, fill it in.

Any error in an Agda file typically renders its editor support useless, so holes are crucial to keeping code well-typed.

Another useful trick is to fill a hole with an expression containing yet more holes.

We can do this by simply writing an expression containing question marks, and hitting C-c C-Space.

Try this by uncommenting the following definition, reloading, writing "not ?" in the hole, and hitting C-c C-Space:

-}

-- Ex1.2: Define the nand operation

-- nand : Bool -> Bool -> Bool
-- nand x y = ?

{-

Note that you must reload with C-c C-l after making changes outside of a hole, otherwise Agda won't know about them.

If you rename an input variable and try to use it to fill in a hole without reloading, Agda wont recognize it.

This tutorial contains an excess of exercises, so complete whatever interests you before moving on to the next chapter.

If you get stuck on or lose interest in an exercise, it is best to just skip it so you may come back to it later.

-}

-- Ex1.3: `and` for 3 inputs

-- and3 : Bool -> Bool -> Bool -> Bool
-- and3 x y z = ?

-- Ex1.4: Define a synonym for `implies`

-- _=>_ : Bool -> Bool -> Bool

-- Ex1.5: Define a synonym for `xor`

-- x ^^ y = ?

-- Ex1.6: Define boolean equality, aka biimplication, as the symbol _<=>_

-- Ex1.7: Define the following higher order functions

-- A function which tells you whether the provided function always outputs the same input it is given

-- is-the-identity-function : (Bool -> Bool) -> Bool
-- is-the-identity-function f = ?

-- Define a function which tells you whether its input is the `not` function

-- Ex1.8: Define all four distinct functions of type `Bool -> Bool`

-- BoolToBoolA : BoolToBool
-- BoolToBoolA x = ?

-- BoolToBoolB : BoolToBool
-- BoolToBoolB x = ?

-- BoolToBoolC : BoolToBool
-- BoolToBoolC x = ?

-- BoolToBoolD : BoolToBool
-- BoolToBoolD x = ?

-- Ex1.9: Compare two `Bool -> Bool`s for equality

-- _=[BoolToBool]=_ : BoolToBool -> BoolToBool -> Bool
-- f =[BoolToBool]= g = ?

-- Ex1.10: Extending the booleans with uncertainty

-- We can define an extension of the booleans with a third "unknown" value
data MaybeBool : Set where
  mfalse : MaybeBool
  mtrue : MaybeBool
  munknown : MaybeBool

-- Complete the following definitions which should properly propogate the unknown-ness of *relevant* inputs to outputs

-- mnot : MaybeBool -> MaybeBool
-- mnot x = ?

-- mand : MaybeBool -> MaybeBool -> MaybeBool
-- mand x y = ?

-- mor : MaybeBool -> MaybeBool -> MaybeBool
-- mor x y = ?

-- BoolFunc-to-MaybeBoolFunc : (Bool -> Bool) -> MaybeBool -> MaybeBool
-- BoolFunc-to-MaybeBoolFunc f x = ?

{-

Tips and Tricks:

To test your code, you can normalize an expression within a hole by entering the key combo C-c C-n.

To create a throw-away hole for such purposes you can use an anonymous, unnamed definition like "_ = ?".

Try uncommenting the following line, placing your cursor in the hole, and normalizing the contained expression:

-}

-- _ = {! true && false !}

{-

Use holes and C-c C-n to test your code while commenting them out as needed to avoid polluting the informational window.

In emacs, "C-x 2" will split the current window horizontally into two windows and "C-x 3" will split it vertically.

"C-x 0" can then be used to delete a window, and "C-x C-1" can be used to delete all windows except the current one.

While working on a definition, it can often help split the window in order to reference another part of the file.

Challenge Exercises:

Beware: challenge exercises can be very time consuming

-}

-- Ce1.1: Properties of binary relations

-- A binary relation `r : A -> A -> Bool` can be classified by a number of properties such as being:
-- functional when, for any `x` `y` and `z`, `(r x y && r x z) => (y == z)`
-- injective when, for any `x` `y` and `z`, `(r x z && r y z) => (x == y)`
-- total when, for any `x`, there exists a `y` such that `r x y`

-- We can define a binary relation over functions between booleans as:
BoolToBoolRel : Set
BoolToBoolRel = BoolToBool -> BoolToBool -> Bool

-- Complete the following definitions

-- is-BoolToBoolRel-functional : BoolToBoolRel -> Bool
-- is-BoolToBoolRel-functional r = ?

-- is-BoolToBoolRel-injective : BoolToBoolRel -> Bool
-- is-BoolToBoolRel-injective r = ?

-- is-BoolToBoolRel-total : BoolToBoolRel -> Bool
-- is-BoolToBoolRel-total r = ?

-- Under the assumption that the provided binary relation is functional and total, turn it into a function
-- total-functional-BoolToBoolRel-to-function : BoolToBoolRel -> BoolToBool -> BoolToBool
-- total-functional-BoolToBoolRel-to-function r f x = ?

-- Ce1.2: Modeling bounded number types

-- Just as there are 4 different `Bool -> Bool`s, there are 16 different `Bool -> Bool -> Bool`s.
-- Furthermore, there are a whopping 256 different `Bool -> Bool -> Bool -> Bool`s.
-- By assigning a number to each distinct function of such a type, we can treat these types like bounded number types:

-- (A "UIntN" refers to an unsigned integer with N bits, and can represent 2^N distinct numbers)
UInt1 : Set
UInt1 = Bool
UInt2 : Set
UInt2 = Bool -> Bool
UInt4 : Set
UInt4 = Bool -> Bool -> Bool
UInt8 : Set
UInt8 = Bool -> Bool -> Bool -> Bool

-- Find some such set of assignments with which you can define the following operations.

-- bitwiseNotUInt8 : UInt8 -> UInt8
-- bitwiseNotUInt8 f x y z = ?

-- bitwiseAndUInt8 : UInt8 -> UInt8 -> UInt8
-- bitwiseAndUInt8 f g x y z = ?

-- Hint: to define an operation over UInt8, it may help to first define it over UInt1, UInt2, and UInt4.

-- addUInt8 : UInt8 -> UInt8 -> UInt8
-- addUInt8 f g x y z = ?

-- multiplyUInt4 : UInt4 -> UInt4 -> UInt8
-- multiplyUInt4 f g x y z = ?

-- Ce1.3: Counting boolean function types

-- How many different `(Bool -> Bool) -> Bool -> Bool`s are there?
-- How many different `((Bool -> Bool) -> Bool) -> Bool`s are there?

{-

Chapter 2. Natural Numbers

The booleans were defined by the unique ways they can be constructed, namely by the "constructors" `true` and `false`.

The Set of natural numbers can be defined by the element `zero`, and the successor function `suc(n)` i.e. "n + 1":

-}

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-

This works because for every natural number, there is exactly one way to write it in terms of these constructors:

-}

one : Nat
one = suc zero -- 0 + 1

two : Nat
two = suc (suc zero) -- 0 + 1 + 1

three : Nat
three = suc (suc (suc zero)) -- 0 + 1 + 1 + 1

{-

We could port this definition of Nat into a typical imperative programming language like:
  interface Nat {};
  class zero extends Nat {};
  class suc extends Nat { Nat n; };
  ...
  Nat three = new suc(n = new suc(n = new suc(n = new zero())))

This singly-linked-list representation of the natural numbers is obviously quite bloated and inefficient for most tasks.

However, as we will see soon, it excels at justifying the existence of recursive functions accepting natural numbers.

Just like with the booleans, we can pattern match on natural numbers by handling both of the `zero` and `suc` cases:

-}

-- Subtracts one from the input
pred : Nat -> Nat
pred zero = zero -- pred(0) = 0
pred (suc n) = n -- pred(n + 1) = n

{-

When handling the `suc` case, we are handed the value to which the suc function was applied, namely the input minus one.

We can also nest patterns, e.g. by pattern matching again against the natural number we are handed in the `suc` case:

-}

is-two : Nat -> Bool
is-two (suc (suc zero)) = true -- is-two(0 + 1 + 1) = true
is-two other = false -- is-two(other) = false

isGreaterThan-two : Nat -> Bool
isGreaterThan-two (suc (suc (suc n))) = true -- isGreaterThan-two(n + 1 + 1 + 1) = true
isGreaterThan-two other = false -- isGreaterThan-two(other) = true

{-

As mentioned previously, we can also define functions recursively:

-}

isEven : Nat -> Bool
isEven zero = true -- zero is even
isEven (suc n) = not (isEven n) -- n+1 is even <=> n is not even

-- Halves the input and rounds it up
halfOf : Nat -> Nat
halfOf zero = zero -- ceil(0 / 2) = 0
halfOf (suc zero) = suc zero -- ceil(1 / 2) = 1
halfOf (suc (suc n)) = suc (halfOf n) -- ceil((n + 2) / 2) = 1 + ceil(n / 2)

{-

It is important that we use recursion in a safe manner to avoid defining non-total "functions" which may loop forever.

The recursive calls here are clearly safe since `n` is literally a smaller piece of data than `suc n` or `suc (suc n)`.

If recursive calls only are made on "structurally" smaller pieces of data, then the function must terminate eventually.

This is in contrast to the following definition, which is not a total function and results in a termination error:

-}

-- bad-isEven : Nat -> Bool
-- bad-isEven zero = true
-- bad-isEven n = not (bad-isEven (suc n))

{-

Here, not only is the input parameter not shrinking with each recursive call, it is growing, leading to non-termination.

A function being total, however, is no guarantee that the termination checker will be able to see that it is total.

To keep Agda's termination checking reliable, this structural shrinking needs to be obvious at the syntax level.

For example, we can't use another function which makes its input smaller, such as `pred`, in place of pattern matching:

-}

-- isEven' : Nat -> Bool
-- isEven' zero = true
-- isEven' n = isEven' (pred n)

{-

Even though the above definition of isEven' is equivalent to the original isEven, Agda cannot see that it terminates.

This limitation may sound problematic, but in practice it can be worked around with a variety of tricks.

For example, say we want to compute the minimum number of bits required to represent a natural number in binary.

We can do so by observing how often we must halve a number (rounded up) before it reaches 1:
  binLength(0) = 1
  binLength(1) = 1
  binLength(n) = 1 + binLength(ceil(n / 2))

However we cannot halve a number by pattern matching, and Agda cannot see that the following definition terminates:

-}

-- bad-binLength : Nat -> Nat
-- bad-binLength zero = one
-- bad-binLength (suc zero) = one
-- bad-binLength n = suc (bad-binLength (halfOf n))

{-

Proving that halfOf always shrinks its input is non-trivial, so Agda does not even bother trying to do so.

The simplest workaround is to use a helper function which recurses over a sufficiently large dummy parameter:

-}

binLength-helper : Nat -> Nat -> Nat
binLength-helper dummy zero = one -- binLength(0) = 1
binLength-helper dummy (suc zero) = one -- binLength(1) = 1
binLength-helper (suc dummy) n = suc (binLength-helper dummy (halfOf n)) -- binLength(n) = 1 + (binLength(n / 2))
binLength-helper zero n = zero -- This case cannot be reached and is only here to reassure the termination checker

binLength : Nat -> Nat
binLength n = binLength-helper n n

{-

The dummy parameter can be thought of as "recursion fuel", and is irrelevant to the computation if it is large enough.

While it is good to be aware of this admittedly quite ugly trick, the reader will not be expected to use it.

Most definitions, and any (non-challenge) exercise in this tutorial, can be completed elegantly with regular recursion:

-}

_+_ : Nat -> Nat -> Nat
zero + m = m -- 0 + m = m
suc n + m = suc (n + m) -- (1 + n) + m = 1 + (n + m)

{-

Again, notice how the first input, which we are recursing over, *visibly* shrinks from `suc n` to `n`.

While this is great if we are concerned about mathematical validity of our definitions, it is terrible for performance.

The amount of space required to write or store a natural number is proportional to the very same natural number.

An unsurprising consequence of this is that many useful operations on natural numbers tend to run in linear time.

To remedy this, Agda allows us to mark certain definitions with `BUILTIN` pragmas:

-}

-- Ask Agda to represent values of our `Nat` type efficiently
{-# BUILTIN NATURAL Nat #-}

-- Ask Agda to compute addition over `Nat`s with efficiently
{-# BUILTIN NATPLUS _+_ #-}

{-

Agda is smart enough to recognize that our `Nat` is a natural number, and that our `_+_` is a valid addition operation.

Thanks to `BUILTIN NATURAL`, we now can write `Nat`s with numeric literals:

-}

four : Nat
four = 4

five : Nat
five = 5

is-three : Nat -> Bool
is-three 3 = true
is-three n = false


{-

We also can now add large numbers without causing Agda to hang:

-}

-- Try uncommenting the following hole and normalizing the contents with C-c C-n

-- _ = {! 200000000000000000 + 300000000000000000 !}

{-

Exercises:

Agda will help you interactively perform pattern matching on a variable of your choice with the case-split command.

Uncomment the following definition, reload, write "n" in the hole, and press C-c C-c with your cursor still in the hole:

-}

-- Ex2.1: Interactive pattern matching

-- isOdd : Nat -> Bool
-- isOdd n = ?

{-

Be sure to take full advantage of Agda's interactive editing when completing exercises.

-}

-- Ex2.2: Arithmetic

-- Multiplication
-- _*_ : Nat -> Nat -> Nat
-- n * m = ?

-- Exponentiation
-- Typically, 0^0 is left undefined, but for our purposes we can say 0^0 = 1
-- _^_ : Nat -> Nat -> Nat
-- n ^ m = ?

-- Ex2.3: Comparison operations

-- Equality for natural numbers
-- _=[Nat]=_ : Nat -> Nat -> Bool
-- n =[Nat]= m = ?

-- Less-than
-- _<_ : Nat -> Nat -> Bool
-- n < m = ?

-- Ex2.4: min and max

-- Minimum
-- _min_ : Nat -> Nat -> Nat
-- n min m = ?

-- Maximum
-- _max_ : Nat -> Nat -> Nat
-- n max m = ?

-- Ex2.5: "Monus"

-- A "fake" minus function (sometimes called monus) which stops at zero rather than returning a negative integer
-- _-_ : Nat -> Nat -> Nat
-- n - m = ?

-- Ex2.6: Define the factorial function

-- Ex2.7: Iterated addition and multiplication

-- Sum of the first n outputs of a function
-- sum : (Nat -> Nat) -> Nat -> Nat
-- sum f n = ?

-- Product of the first n outputs of a function
-- product : (Nat -> Nat) -> Nat -> Nat
-- product f n = ?

-- Ex2.8: Enabling BUILTINs

-- After correctly filling in and testing the above definitions, comment in the following BUILTIN-pragmas
-- Note that BUILTIN-pragmas verify your definitions on a best-effort basis and may fail even for a correct definition
-- {-# BUILTIN NATTIMES _*_ #-}
-- {-# BUILTIN NATMINUS _-_ #-}
-- {-# BUILTIN NATEQUALS _=[Nat]=_ #-}
-- {-# BUILTIN NATLESS _<_ #-}

-- Ex2.9: Integers

-- Once we have defined the natural numbers, it is easy to define the integers in terms of them
-- The data type `Int` must provide constructors for mapping natural numbers to both positive and negative integers
-- However we must take care to avoid creating distinct ways to construct the same integer, such as "0" and "-0":
data Int : Set where
  -- Maps a natural number `n` to the integer `n` (which is greater than or equal to zero)
  int : Nat -> Int
  -- Maps a natural number `n` to the integer `-1 - n` (which is strictly less than zero)
  -[1+ _] : Nat -> Int

-- _=[Int]=_ : Int -> Int -> Bool
-- n =[Int]= m = ?

-- _z+_ : Int -> Int -> Int
-- x z+ y = ?

-- _z-_ : Int -> Int -> Int
-- n z- m = ?

-- _z*_ : Int -> Int -> Int
-- x z* y = ?

-- _z<_ : Int -> Int -> Bool
-- n z< m = ?

-- _zmin_ : Int -> Int -> Int
-- n zmin m = ?

-- _zmax_ : Int -> Int -> Int
-- n zmax m = ?

-- Ex2.10: Fractions

-- We can define a weak form of the rational numbers as follows:
data Fraction : Set where
  _/_ : Int -> Int -> Fraction

-- The main issue with this definition is that there are many different ways to write the same rational number
-- Define an equality comparison operation which disregards this and treats e.g. `4 / 2` and `2 / 1` as equivalent

-- _=[Fraction]=_ : Fraction -> Fraction -> Bool
-- n =[Fraction]= m = ?

-- Define operations which respect this equivalence

-- _f+_ : Fraction -> Fraction -> Fraction
-- x f+ y = ?

-- _f-_ : Fraction -> Fraction -> Fraction
-- n f- m = ?

-- _f*_ : Fraction -> Fraction -> Fraction
-- x f* y = ?

-- _f<_ : Fraction -> Fraction -> Bool
-- n f< m = ?

-- _fmin_ : Fraction -> Fraction -> Fraction
-- n fmin m = ?

-- _fmax_ : Fraction -> Fraction -> Fraction
-- n fmax m = ?

{-

Tips and Tricks:

Don't be afraid to define your own helper functions, just be sure to name them like "...-helper" to avoid name clashes.

Use "C-c C-f" and "C-c C-b" to jump to the next or previous hole respectively, speeding up your interactive editing.

Agda lets us control the order of operations, which is left up to the reader if they desire to do so.

An operator may be defined as infixl(eft-associative) or infixr(ight-associative) and can be given a precedence:

-}

-- `a && b || c => d => e` = `((a && b) || c) => (d => e)`
-- infixl 4 _||_
-- infixl 5 _&&_
-- infixr 3 _=>_

-- `a * b + c ^ d ^ e` = (a * b) + (c ^ (d ^ e))
-- infixl 4 _+_
-- infixl 5 _*_
-- infixr 6 _^_

{-

If you chose not to uncomment and/or create such declarations, you must use parentheses to avoid ambiguity.

Challenge Exercises:

-}

-- Ce2.1: Infinite sequences

-- We can think of a `Nat -> A` as an infinite sequence of `A`s
-- Therefore, we can think of a `Nat -> Nat -> Bool` as an infinite sequence of infinite sequences of booleans
-- Prove informally that there exists no `Nat -> Nat -> Bool` which enumerates every `Nat -> Bool`
-- For any `Nat -> Nat -> Bool`, construct a counterexample `Nat -> Bool` which it does not output for any input `Nat`
-- infinite-sequences-are-enumerable-counterexample : (Nat -> Nat -> Bool) -> Nat -> Bool
-- infinite-sequences-are-enumerable-counterexample f n = ?

-- Similarly, we can think of a `Nat -> Nat -> Nat` as an infinite sequence of infinite sequences of natural numbers
-- Define a function which flattens such an infinite two-dimensional array into a single infinite sequence
-- Any number which occurs in the provided infinite array *must* occur eventually in the resulting sequence
-- flatten-sequence : (Nat -> Nat -> Nat) -> Nat -> Nat
-- flatten-sequence f n = ?

-- Construct an infinite sequence of fractions which converges to the square root of 2
-- converges-to-sqrt-2 : Nat -> Fraction
-- converges-to-sqrt-2 n = ?

-- Ce2.2: Division and modulus

-- Define division and modulus operations for the natural numbers
-- To avoid having to define division/modulus by zero, we implicitly add one to the input for the denominator

-- _/[1+_] : Nat -> Nat -> Nat
-- n /[1+ m ] = ?

-- _%[1+_] : Nat -> Nat -> Nat
-- n %[1+ m ] = ?

-- Define a function which enumerates the prime numbers
-- primes : Nat -> Nat
-- primes n = ?

{-

Chapter 3. Parametric Polymorphism

So far we have worked with a number of Sets, such as Nat, Bool, as well as many function-Sets over Nat and Bool.

Some functions, however, can be defined for any Set, as is the case with the identity function:

-}

id-for-Bool : Bool -> Bool
id-for-Bool x = x

id-for-Nat : Nat -> Nat
id-for-Nat x = x

id-for-BoolToBool : (Bool -> Bool) -> Bool -> Bool
id-for-BoolToBool x = x

{-

To avoid duplicating such a definition for every type we wish to use it with, we can define polymorphic functions.

In Agda, polymorhpic functions are simply functions accepting an input of type Set which is given a name in its type:

-}

id-for : (A : Set) -> A -> A
id-for A x = x

id-for-Bool' : Bool -> Bool
id-for-Bool' = id-for Bool

id-for-Nat' : Nat -> Nat
id-for-Nat' = id-for Nat

{-

Most languages have special syntax for type parameters, but in Agda, types are just values, and Set is a type of types.

In fact, you can technically name any parameter in a type signature like we previously named the Set parameter `A`:

-}

triple : (x : Nat) -> Nat
triple zero = zero
triple (suc x) = suc (suc (suc (triple x)))

{-

Here we have brought the first parameter into scope in the type signature rather than just in the definition.

The `x` in the type signature is entirely independent from (and in fact not even equal to) the `x` in the definition.

Besides perhaps making a point, this accomplished nothing, since we did not refer to `x` in the remainder of the type.

On the other hand, `A` was only useful to name in the type signature of `idFor`, and didn't get used in the definition.

To make it explicit that a parameter is not used at a definition, we can discard it with an underscore pattern:

-}

id-for' : (A : Set) -> A -> A
id-for' _ x = x

{-

This is generally more useful for longer definitions, where a reader cannot easily see if a parameter is used.

However, to complement this syntax, an underscore can be used when calling a function to ask Agda to infer an input:

-}

id-for-Bool'' : Bool -> Bool
id-for-Bool'' = id-for _

id-for-Nat'' : Nat -> Nat
id-for-Nat'' = id-for _

{-

In simple cases like this with an unambiguous solution, Agda will almost always be able to infer the correct type.

For this reason, Agda has a special syntax for "implicit parameters", which are hidden and inferred by default:

-}


id : {A : Set} -> A -> A
id x = x

id-for-Bool''' : Bool -> Bool
id-for-Bool''' = id

id-for-Nat''' : Nat -> Nat
id-for-Nat''' = id

{-

There is no difference between regular and implicit parameters beyond the convenience of the syntax.

Just as you can opt in to inference with underscore, you can apply implicit parameters explicitly with curly braces:

-}

id-for-Bool'''' : Bool -> Bool
id-for-Bool'''' = id {Bool}

id-for-Nat'''' : Nat -> Nat
id-for-Nat'''' = id {Nat}

id' : {A : Set} -> A -> A
id' {A} = id-for A

{-

In general we will prefer the implicit syntax for polymorphic Set parameters, as they can almost always be inferred.

Polymorphism over Sets is incredibly useful for defining a wide range of generic functions:

-}

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

applyNTimes : {A : Set} -> Nat -> (A -> A) -> A -> A
applyNTimes zero f x = x
applyNTimes (suc n) f x = f (applyNTimes n f x)

{-

Multiple named parameters of the same type can be abbreviated, e.g. if we wish to abstract over multiple types:

-}

-- Instead of "compose : {A : Set} -> {B : Set} -> {C : Set} -> (B -> C) -> (A -> B) -> A -> C", we can just write:
compose : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
compose f g x = f (g x)

lift : {A B C D : Set} -> (B -> C -> D) -> (A -> B) -> (A -> C) -> A -> D
lift op f g x = op (f x) (g x)

{-

While polymorphism is incredibly useful, it has some (rightful) limitations in Agda.

For one, while Sets may be treated as values, they are not data, and you cannot pattern match on them:

-}

-- bad-id-for : (A : Set) -> A -> A
-- bad-id-for Nat x = suc x
-- bad-id-for Bool x = not x
-- bad-id-for Other x = x

{-

On top of this restriction, we also may not pattern match on a parameter without knowing its exact datatype:

-}

-- bad-id : {A : Set} -> A -> A
-- bad-id true = false
-- bad-id false = true
-- bad-id other = other

{-

These two restrictions more or less sum up what it means for polymorphic functions to be "parametric".

Parametrically polymorphic functions cannot have differing behavior depending on the concrete type they are used with.

This guarantees, for instance, that the identity function is the only function of type `{A : Set} -> A -> A`.

One clever use case of parametricity is to encode datatypes like Nat and Bool *as* polymorphic function types:

-}

-- Here we define a type alias, to avoid having to repeatedly write the polymorphic type `{X : Set} -> X -> X -> X`
CBool : Set
CBool = {X : Set} -> X -> X -> X

cfalse : CBool
cfalse x y = x

ctrue : CBool
ctrue x y = y

cnot : CBool -> CBool
cnot f x y = f y x

{-

Indeed, there really only are two ways to produce an `X` given two `X`s, if you know nothing more about `X`.

Take a moment to convince yourself of this correspondence and that e.g. `cnot cfalse` is equivalent to `ctrue`.

With a slightly cleverer polymorphic function type, we can also encode the natural numbers using parametricity:

-}

CNat : Set
CNat = {X : Set} -> (X -> X) -> X -> X

czero : CNat
czero f x = x

cone : CNat
cone f x = f x

ctwo : CNat
ctwo f x = f (f x)

cthree : CNat
cthree f x = f (f (f x))

{-

The only thing such a function can do is apply the `X -> X` a natural number of times to the `X`.

This mirrors how, to construct a Nat, we must apply `suc : Nat -> Nat` some natural number of times to `zero : Nat`.

Such encodings of data as functions are also known as church encodings after Alonzo Church.

Church encodings can be used as a basis to define any computation purely in terms of polymorphic functions.

Exercises:

When working with type aliases like CBool and CNat, keeping track of the types of input parameters can be tricky.

Luckily, Agda provides us with the hole-command "C-c C-," which displays exactly this contextual information.

Furthermore, if you type an expression into a hole, "C-c C-." displays its inferred type in addition to the context.

We can also prefix either of these commands with "C-u C-u" to force Agda to normalize any type aliases.

For example, if "C-c C-." displays "CBool" then "C-u C-u C-c C-." should display "{X : Set} -> X -> X -> X".

Make sure to try these commands out while working on the following exercises:

-}

-- Ex3.1: Define the following polymorphic functions

-- apply : {A B : Set} -> (A -> B) -> A -> B
-- apply f x = ?

-- k : {A B : Set} -> A -> B -> A
-- k x y = ?

-- s : {A B C : Set} -> (A -> B -> C) -> (A -> B) -> A -> C
-- s x y z = ?

-- owl : {A B : Set} -> ((A -> B) -> A) -> (A -> B) -> B
-- owl f g = ?

-- Ex3.2: Define these functions over church encodings without using any regular, non-church-encoded definitions

-- csuc : CNat -> CNat
-- csuc n f x = ?

-- cand : CBool -> CBool -> CBool
-- cand f g x y = ?

-- cor : CBool -> CBool -> CBool
-- cor f g x y = ?

-- cisEven : CNat -> CBool
-- cisEven f x y = ?

-- Ex3.3: Define conversion functions between datatypes and their parametric/church encodings

-- Bool-to-CBool : Bool -> CBool
-- Bool-to-CBool b x y = ?

-- CBool-to-Bool : CBool -> Bool
-- CBool-to-Bool f = ?

-- Nat-to-CNat : Nat -> CNat
-- Nat-to-CNat n f x = ?

-- CNat-to-Nat : CNat -> Nat
-- CNat-to-Nat f = ?

-- What previously defined functions accomplish exactly the same thing as Bool-to-CBool and Nat-to-CNat?

-- Ex3.4: Fill in the missing types

-- flip : {A B C : Set} -> (A -> ? -> C) -> B -> ? -> C
-- flip f x y = f y x

-- on : {A B C : Set} -> (? -> ? -> ?) -> (A -> B) -> A -> A -> C
-- on op f x y = op (f x) (f y)

-- isOne : Nat -> Bool
-- isOne = compose {?} {?} {?} isTwo suc

-- warbler : ?
-- warbler f x = f x x

-- Find any type for this definition which does not result in an error:
-- apply-to-self : ?
-- apply-to-self f = f f

-- Ex3.5: Arithmetic with church naturals

-- The church encoding of the natural numbers notably allows us to write the following astonishing definitions:

_c+_ : CNat -> CNat -> CNat
(n c+ m) f x = n f (m f x)

_c*_ : CNat -> CNat -> CNat
(n c* m) f x = n (m f) x

_c^_ : CNat -> CNat -> CNat
(n c^ m) f x = m n f x

-- Take a moment to consider why each of these works
-- Also, 0^0 is normally left undefined, but what does `czero c^ czero` equal?
-- When you think you have the answer, try normalizing the following expression:
-- _ = {! CNat-to-Nat (czero c^ czero)  !}

-- Ex3.6: Pointfree style

-- "Eta equality" tells us that we can simplify the definition "f(x) = g(x)" down to "f = g"
-- Consequently, we can often avoid introducing parameters and use previously defined higher order functions instead
-- Complete the following definitions by returning a function as output rather than introducing further parameters

-- todo: more exercises here

-- _c^'_ : CNat -> CNat -> CNat
-- n c^' m = m ?

-- _c*'_ : CNat -> CNat -> CNat
-- n c*' m = compose ? ?

-- _c+'_ : CNat -> CNat -> CNat
-- n c+' m = lift ? ? ?

-- Ex3.7: Church encoded integers and fractions

-- Define `CInt`, a church encoding of `Int` in terms of `CNat`, as well as conversion functions to and from Int

-- CInt : Set
-- CInt = {X : Set} -> ?

-- Int-to-CInt : Int -> CInt
-- Int-to-CInt = ?

-- CInt-to-Int : CInt -> Int
-- CInt-to-Int = ?

-- Similarly, define `CFraction`, in terms of `CInt`, along with conversion functions

-- CFraction : Set
-- CFraction = {X : Set} -> ?

-- Fraction-to-CFraction : Fraction -> CFraction
-- Fraction-to-CFraction = ?

-- CFraction-to-Fraction : CFraction -> Fraction
-- CFraction-to-Fraction = ?

-- Ex1.8: Powersets

-- We can think of `A -> Bool`s as constructive representations of subsets `A`
-- Each `A -> Bool` is a predicate which tells you if a given `A` is contained by the respective subset
-- Therefore `A -> Bool` itself is the Set of all subsets of (aka the "powerset" of) the Set `A`
-- This can be formalized with a parameterized type alias, which in Agda is just a regular function of type `Set -> Set`
Powerset : Set -> Set
Powerset A = A -> Bool

-- Define the empty (sub-)set which contains no elements
-- emptyset : {A : Set} -> Powerset A
-- emptyset x = ?

-- Define the union of two (sub-)sets containing all elements which either of them contains
-- union : {A : Set} -> Powerset A -> Powerset A -> Powerset A
-- union f g x = ?

-- Define the intersection of two (sub-)sets containing all elements which both of them contain
-- intersection : {A : Set} -> Powerset A -> Powerset A -> Powerset A
-- intersection f g x = ?

-- Define the difference of two (sub-)sets containing all elements contained by the former but not the latter
-- difference : {A : Set} -> Powerset A -> Powerset A -> Powerset A
-- difference f g x = ?

-- Ex3.9: Infinite sequences

-- We can think of a `Nat -> A` as an infinite sequence or stream of `A`s
-- This can similarly be formalzied with a parameterized type alias:

Stream : Set -> Set
Stream A = Nat -> A

-- Returns the first element of a stream
-- head : {A : Set} -> Stream A -> A
-- head f = ?

-- Returns all but the first element of a stream
-- tail : {A : Set} -> Stream A -> Stream A
-- tail f = ?

-- Chops off the first n elements of a stream
-- drop : {A : Set} -> Nat -> Stream A -> Stream A
-- drop n f = ?

-- Repeats a value infinitely
-- repeat : {A : Set} -> A -> Stream A
-- repeat x = ?

-- Applies a function to each element of a stream
-- map-Stream : {A B : Set} -> (A -> B) -> Stream A -> Stream B
-- map-Stream f g = ?

-- Zips two streams together with an operation
-- zipWith : {A B C : Set} -> (A -> B -> C) -> Stream A -> Stream B -> Stream C
-- zipWith op f g = ?

{-

Tips and Tricks:

You can jump to a definition under the cursor with "M-." and jump back when you are done with "M-,".

In emacs, "M-<key>" means "alt-<key>", or "option-<key>" on mac.

As previously mentioned, holes can be filled in with solutions containing more holes.

For example, you could start to fill in the following definition by writing `op ? ? ?` and pressing C-c C-Space.

However, you could also just write `op` into it, and hit C-c C-r to "refine" the solution:

-}

-- Ex3.10: Refine

-- lift3 : {A B C D E : Set} -> (B -> C -> D -> E) -> (A -> B) -> (A -> C) -> (A -> D) -> A -> E
-- lift3 op f g h x = ?

{-

Challenge Exercises:

-}


-- Ce3.1: Complete an insanely polymorphic definition

-- insanity : {X Y : Set} -> ({A B : Set} -> (({C : Set} -> A -> C) -> B) -> (A -> B) -> B) -> ((X -> Y) -> X) -> X
-- insanity f g = ?

-- Ce3.2: Define a minus function for the natural numbers using only church encoded definitions

-- _c-_ : CNat -> CNat -> CNat
-- (n c- m) f x = ?

-- Ce3.3: Complete the given definitions using only s and k, without introducing any parameters

-- The previously defined `s` and `k` functions, also called "combinators", together are turing complete
-- With enough work, any polymorphic function can be written without introducing parameters, purely in terms of s and k
-- It may be helpful to define and use helper functions using only s and k, and substitute them in afterwards
-- Note that you may need to explicitly provide a few implicit type parameters where Agda cannot infer them

-- flip-k' : {A B : Set} -> A -> B -> B
-- flip-k' {A} {B} = ?

-- compose' : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
-- compose' {A} {B} {C} = ?

-- owl' : {A B : Set} -> ((A -> B) -> A) -> (A -> B) -> B
-- owl' {A} {B} = ?

-- cthree' : CNat
-- cthree' {A} = ?

{-

Chapter 4. Algebraic Datatypes

When we think of types formally as sets of values, the number of distinct values of a type becomes very apparent.

This number is referred to as the cardinality of a set or type, and is not necessarily always a finite number.

For example, while Bool has a cardinality of 2, Nat has an infinite cardinality as there are infinitely many Nats.

It is very easy to define a type with any finite cardinality we desire:

-}

data Zero : Set where

data One : Set where
  1/One : One

-- This is effectively equivalent to our definition of Bool
data Two : Set where
  1/Two : Two
  2/Two : Two

data Three : Set where
  1/Three : Three
  2/Three : Three
  3/Three : Three

{-

Once we start thinking of types as "number-like" things, we might wonder if we can add or multiply types.

A programming language with "Algebraic Datatypes" simply provides us with a convenient way to do exactly this.

In fact, most languages already make it easy to define products, even if the numeric correspondence is not obvious.

Two types X and Y can be "multiplied" with a "Pair<X, Y>" type, which is just a struct containing both an X and a Y.

In Agda, we can define e.g. the product of Two and Three as follows:

-}

data Six : Set where
  sixFromTwoAndThree : Two -> Three -> Six

1/Six : Six
1/Six = sixFromTwoAndThree 1/Two 1/Three

2/Six : Six
2/Six = sixFromTwoAndThree 1/Two 2/Three

3/Six : Six
3/Six = sixFromTwoAndThree 1/Two 3/Three

4/Six : Six
4/Six = sixFromTwoAndThree 2/Two 1/Three

5/Six : Six
5/Six = sixFromTwoAndThree 2/Two 2/Three

6/Six : Six
6/Six = sixFromTwoAndThree 2/Two 3/Three

{-

Such a pair type is the cartesian product of its components, whose cardinalities are combined by multiplication.

This is no different from the more typical `struct Six { Two x; Three y; };` we would write in an imperative language.

While not as common in other languages, sums can also be encoded as variant/enum types, aka disjoint unions:

-}

data Five : Set where
  fiveFromTwo : Two -> Five
  fiveFromThree : Three -> Five

1/Five : Five
1/Five = fiveFromTwo 1/Two

2/Five : Five
2/Five = fiveFromTwo 2/Two

3/Five : Five
3/Five = fiveFromThree 1/Three

4/Five : Five
4/Five = fiveFromThree 2/Three

5/Five : Five
5/Five = fiveFromThree 3/Three

{-

Since this variant type contains either a Two, or a Three, but never both, it has exactly 2 + 3 distinct values.

One way to hack this into a typical imperative language is by using inheritance, e.g.
  interface Five {};
  class FiveFromTwo extends Five { Two x; };
  class FiveFromThree extends Five { Three x; };

Many languages provide variants (sums) and tuples (products) in the form of a library type with type parameters.

In Agda, as with every other type we have seen until now, we can define these generic types ourselves:

-}

-- 2-ary tuple, a "product" of its two type arguments:
data Pair : Set -> Set -> Set where
  pair : {A B : Set} -> A -> B -> Pair A B

-- 2-ary variant, a "sum" of its two type arguments
data Either : Set -> Set -> Set where
  left : {A B : Set} -> A -> Either A B
  right : {A B : Set} -> B -> Either A B

{-

Observe how Pair and Either are both functions accepting two Sets and returning a Set.

This matches up exactly with how _+_ and _*_ are functions accepting two Nats and returning a Nat.

If x and y are Nats, then `_+_ x y` is a Nat, and likewise if A and B are Sets, then `Either A B` is a Set.

If we wish, we can use these generic types instead of defining a whole new datatype like we did for Five and Six.

We can demonstrate that these two approaches are the same by constructing a bijection using pattern matching:

-}

-- A bijection between the types `Either Two Three` and `Five`

EitherTwoThree-to-Five : Either Two Three -> Five
EitherTwoThree-to-Five (left x) = fiveFromTwo x
EitherTwoThree-to-Five (right x) = fiveFromThree x

Five-to-EitherTwoThree : Five -> Either Two Three
Five-to-EitherTwoThree (fiveFromTwo x) = left x
Five-to-EitherTwoThree (fiveFromThree x) = right x

-- A bijection between the types `Pair Two Three` and `Six`

PairTwoThree-to-Six : Pair Two Three -> Six
PairTwoThree-to-Six (pair x y) = sixFromTwoAndThree x y

Six-to-PairTwoThree : Six -> Pair Two Three
Six-to-PairTwoThree (sixFromTwoAndThree x y) = pair x y

{-

A bijection between two sets is an exhaustive one-to-one mapping between their elements.

As we do not yet possess the power of theorem proving, it is up to the reader to verify that these are true bijections.

For product types, we can also define accessor functions, which are often referred to as projections:

-}

fst : {A B : Set} -> Pair A B -> A
fst (pair x y) = x

snd : {A B : Set} -> Pair A B -> B
snd (pair x y) = y

{-

For sum types however, we notably can't define accessors like this which are total, since we must handle all cases:

-}

-- getLeft : {A B : Set} -> Either A B -> A
-- getLeft (left x) = x
-- getLeft (right x) = ?

-- getRight : {A B : Set} -> Either A B -> B
-- getRight (left x) = ?
-- getRight (right x) = x

{-

To do so, we would need some notion of partiality or optionality, which brings us to our next polymorphic datatype:

-}

data Maybe : Set -> Set where
  nothing : {A : Set} -> Maybe A
  just : {A : Set} -> A -> Maybe A

{-

The Maybe type lets us express failure in a mathematically pure manner, without crashing or throwing any exceptions:

-}

-- A partial predecessor function over the natural numbers which does not wrongly output zero given an input of zero
pred-partial : Nat -> Maybe Nat
pred-partial zero = nothing
pred-partial (suc n) = just n

getLeft-partial : {A B : Set} -> Either A B -> Maybe A
getLeft-partial (left x) = just x
getLeft-partial (right _) = nothing

getRight-partial : {A B : Set} -> Either A B -> Maybe B
getRight-partial (left _) = nothing
getRight-partial (right x) = just x

{-

We can formalize this notion of a partial function with the following parameterized type alias:

-}

_-/>_ : Set -> Set -> Set
A -/> B = A -> Maybe B

{-

In imperative languages, we can effectively compose two partial functions by calling one after another.

When either of them fails by crashing or throwing an exception, the resulting "composed" function fails as well.

In Agda, we can explicitly define this kind of composition for our notion of partial functions:

-}

compose-partial : {A B C : Set} -> (B -/> C) -> (A -/> B) -> A -/> C
compose-partial {_} {B} {C} f g x = h (g x)
  where
    h : Maybe B -> Maybe C
    h nothing = nothing
    h (just y) = f y

{-

Here we define a local helper function in a "where" clause in order to pattern match on the intermediate result `g x`.

This helper function has access to exactly the variables which are in scope at the body of `compose-partial`.

To write its type, it was therefore necessary to bring the implicit type parameters `B` and `C` into scope.

Last but not least, lets look at an Algebraic Datatype which is used everywhere in computer science:

-}

data List : Set -> Set where
  nil : {A : Set} -> List A
  cons : {A : Set} -> A -> List A -> List A

{-

This "singly-linked" definition of a list is very similar to our definition of the natural numbers.

"nil" represents an empty list, like zero, and "cons" prepends a single element onto the front of the list, like suc:

-}

List-from-one-to-five : List Nat
List-from-one-to-five = cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))) -- that is, `[1, 2, 3, 4, 5]`

{-

Just as with the natural numbers, we can define operations on lists using recursion:

-}

length : {A : Set} -> List A -> Nat
length nil = zero
length (cons x xs) = suc (length xs)

{-

Agda can see that this function will always terminate since we recurse on the structurally smaller `xs` in `cons x xs`.

This is the same as how we justified recursing on the `n` in `suc n` with the natural numbers.

Concatenation can also be defined recursively, in a manner that strongly resembles addition on the natural numbers:

-}

_++_ : {A : Set} -> List A -> List A -> List A
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

{-

All of the types we have defined can be thought of "algebraically" in terms of their cardinalities, e.g.
  Bool = 1 + 1
    false^   ^true
  Nat = 1 + Nat
    zero^   ^suc
  Maybe A = 1 + A
     nothing^   ^just
  Either A B = A + B
           left^   ^right
  Pair A B = A * B
         mkPair^
  List A = 1 + A * List A
        nil^     ^cons

Notice how Nat, which has an infinite cardinality, is defined by being equal to itself plus one.

Furthermore, if datatypes may be thought of as sums and products, a function set may be thought of as an exponentiation.

Given the sets N and M with cardinalities n and m, the function set N -> M has a cardinality of m to the power of n.

Consider for example how many different functions there are with the following type:

-}

-- x : Three -> Two
-- x 1/Three = ?
-- x 2/Three = ?
-- x 3/Three = ?

{-

Indeed there are 2^3 or 2 * 2 * 2 different ways to fill this in, just as there are for a `Pair Two (Pair Two Two)`.

Exercises:

-}

-- We can informally demonstrate algebraic laws by defining bijections involving algebraic data types.

-- Ex4.1: Complete the given definitions which demonstrate the algebraic law of commutativity for sum and product types

-- a * b = b * a
-- swapPair : {A B : Set} -> Pair A B -> Pair B A
-- swapPair x = ?

-- a + b = b + a
-- swapEither : {A B : Set} -> Either A B -> Either B A
-- swapEither x = ?

-- Ex4.2: Complete the given definitions which demonstrate the algebraic law "c^(a * b) = (c^b)^a"

-- curry : {A B C : Set} -> (Pair A B -> C) -> A -> B -> C
-- curry f x y = ?

-- uncurry : {A B C : Set} -> (A -> B -> C) -> Pair A B -> C
-- uncurry f x = ?

-- Ex4.3: Complete the given definitions which demonstrate the algebraic law "c^a * c^b = c^(a + b)"

-- either : {A B C : Set} -> Pair (A -> C) (B -> C) -> Either A B -> C
-- either x y = ?

-- uneither : {A B C : Set} -> (Either A B -> C) -> Pair (A -> C) (B -> C)
-- uneither f = ? -- Hint: it may help to use a "where" clause

-- Ex4.4: Complete the given definitions which should demonstrate the algebraic law "a * (b + c) = a * b + a * c"

-- distribute : ?
-- distribute = ?

-- undistribute : ?
-- undistribute = ?

-- Ex4.5: Complete the given definitions which would almost appear to demonstrate an invalid algebraic law

-- Consider what this law would be, and how its invalidity will inevitably be reflected in any solution

-- split : {A B C : Set} -> Either A (Pair B C) -> Pair (Either A B) (Either A C)
-- split = ?

-- unsplit : {A B C : Set} -> Pair (Either A B) (Either A C) -> Either A (Pair B C)
-- unsplit = ?

-- Ex4.6: Define the following functions involving Maybe and List

-- A partial minus function for natural numbers, which fails rather than returning zero in place of a negative number
-- minus-partial : Nat -> Nat -> Maybe Nat
-- minus-partial n m = ?

-- Take the first Maybe which contains a value
-- _orElse_ : Maybe A -> Maybe A -> Maybe A
-- x orElse y = ?

-- Get the nth element of a list
-- index : Nat -> List A -> Maybe A
-- index n xs = ?

-- Map an operation over every element in a list
-- map : {A B : Set} -> (A -> B) -> List A -> List B
-- map f xs = ?

-- Flatten a list of lists into one long list
-- flatten : {A : Set} -> List (List A) -> List A
-- flatten xs = ?

-- todo: there must be more interesting exercises than these

-- Ex4.7: Lifting boolean equalities

-- We can define the type of equality comparison operations as follows:
BEQ : Set -> Set
BEQ A = A -> A -> Bool

-- Define operations to lift equality comparisons over types A and B into equality comparisons for generic types

-- Pair-eq : {A B : Set} -> BEQ A -> BEQ B -> BEQ (Pair A B)
-- Pair-eq a-eq b-eq x y = ?

-- Either-eq : {A B : Set} -> BEQ A -> BEQ B -> BEQ (Either A B)
-- Either-eq a-eq b-eq x y = ?

-- Maybe-eq : {A : Set} -> BEQ A -> BEQ (Maybe A)
-- Maybe-eq a-eq x y = ?

-- List-eq : {A : Set} -> BEQ A -> BEQ (List A)
-- List-eq a-eq x y = ?

-- Ex4.8: Church encoded sums and products

-- Traditionally, we define multiplication by repeated addition, and exponentiation by repeated multiplication
-- Yet bizarrely, parametric polymorphism lets us define both addition and multiplication in terms of exponentiation:

CPair : Set -> Set -> Set
CPair A B = {X : Set} -> (A -> B -> X) -> X

CEither : Set -> Set -> Set
CEither A B = {X : Set} -> (A -> X) -> (B -> X) -> X

-- Define conversion functions to and from these parametric encodings:

-- Pair-to-CPair : {A B : Set} -> Pair A B -> CPair A B
-- Pair-to-CPair x f = ?

-- CPair-to-Pair : {A B : Set} -> CPair A B -> Pair A B
-- CPair-to-Pair f = ?

-- Either-to-CEither : {A B : Set} -> Either A B -> CEither A B
-- Either-to-CEither x f g = ?

-- CEither-to-Either : {A B : Set} -> CEither A B -> Either A B
-- CEither-to-Either f = ?

-- Ex4.9: Church encoded Maybe and List

-- CMaybe : Set -> Set
-- CMaybe A = ?

-- Maybe-to-CMaybe : {A : Set} -> Maybe A -> CMaybe A
-- Maybe-to-CMaybe x = ?

-- CMaybe-to-Maybe : {A : Set} -> CMaybe A -> Maybe A
-- CMaybe-to-Maybe f = ?

-- CList : Set -> Set
-- CList A = ?

-- List-to-CList : {A : Set} -> List A -> CList A
-- List-to-CList x = ?

-- CList-to-List : {A : Set} -> CList A -> List A
-- CList-to-List f = ?

-- Ex4.10: todo: state monad?

{-

Tips and Tricks:

Right clicking on a hole will list all of Agda's hole-commands, including many which we have not yet covered.

Emacs also has a toolbar by default, and the "Agda" dropdown lists other non-hole commands.

The toolbar can be used to discover most basic emacs functionality and corresponding key combos.

Alternatively, "C-h m" will list all key combos, and pressing "?" after starting a key combo will list completions.

If you enjoy working with key combos to edit and navigate more efficiently, try the emacs tutorial with "C-h t".

Challenges Exercises:

-}

-- Ce4.1: subsequences

-- Compute a list of all subsequences of the provided list
-- subsequences : {A : Set} -> List A -> List (List A)
-- subsequences xs = ?

-- Ce4.2: sorting

-- Sort a list by the given less-than relation
-- sortBy : {A : Set} -> (A -> A -> Bool) -> List A -> List A
-- sortBy _isLessThan_ xs = ?

{-

Part 2. Constructive Theorem Proving

In classical logic, which is what most people are familiar with from math class, propositions are booleans.

That is, every proposition in classical mathematics is assumed to either have a proof, or not have a proof.

This is reflected by the boolean Law of the Excluded Middle (often written as "LEM"), which says "forall p, p or not p".

LEM lets us prove the existence of functions whose outputs depend on the truth of any arbitrarily complex proposition.

This abstract notion of proof disregards whether such a function can be "constructed" in a turing-complete language.

However, proofs which simply avoid using LEM represent specific functions that serve as evidence of a proposition.

Intuitionistic logic simply drops LEM as an axiom, which instead must be explicitly assumed where it is needed.

This results in a strictly more expressive logic, where proofs may have specific meanings and can be treated as values.

So whereas classical logic is a logic of abstract truth, intuitionistic logic is a logic of constructible evidence.

Chapter 5. Intuitionistic Propositions

By now we have technically already proven quite a few propositions, though they have all been extremely boring.

Specifically, by constructing a value of a type, we prove the nonemptyness of the Set which that type represents:

-}

Nat-is-nonempty : Nat
Nat-is-nonempty = zero

Nat-is-nonempty' : Nat
Nat-is-nonempty' = suc zero

Nat-is-nonempty'' : Nat
Nat-is-nonempty'' = suc (suc zero)

{-

The above definitions can all be understood as proofs that Nat is "inhabited", even if this is very obvious anyway.

In intuitionistic mathematics, these "inhabitants" are considered distinct proofs or reasons that Nat is a nonempty Set.

An intuitionist might interpret `Nat` itself as this proposition, and say it has a countably infinite number of proofs.

Similarly, `One` was defined as a Set with exactly one element, and can be interpreted as a trivially true proposition:

-}

One-is-nonempty : One
One-is-nonempty = 1/One

{-

Treating types as propositions becomes significantly more interesting once we consider Sets with no elements:

-}

-- Zero-is-nonempty : Zero
-- Zero-is-nonempty = ?

{-

`Zero` was previously defined to be an empty set, and can be understood as a trivially false proposition.

While it may be obvious that there is no way to fill in this definition, it would be nice to actually disprove `Zero`.

One way to demonstrate that a proposition is false is by showing that it can be used to prove any other proposition:

-}

-- For any proposition X, absurd takes a proof of Zero as input and returns a proof of X as output
absurd : {X : Set} -> Zero -> X
-- With a trivially empty type like `Zero`, we can do this by pattern matching on all zero of its constructor cases:
absurd ()

{-

The `()` is called a refutation pattern, and states that we do not need to give an output as there can be no input.

There is always exactly one function from the empty set to any other set, namely one mapping all zero inputs to outputs.

Evidence of Zero simply cannot exist, since it would let us summon evidence of any other proposition, which is absurd.

At this point, one might notice that function sets correspond exactly to implications when interpreted as propositions:

-}

true-implies-true : One -> One
true-implies-true 1/One = 1/One

false-implies-true : Zero -> One
false-implies-true ()

true-implying-false-is-absurd : {X : Set} -> (One -> Zero) -> X
true-implying-false-is-absurd one-to-zero = absurd (one-to-zero 1/One)

false-implies-false : Zero -> Zero
false-implies-false ()

{-

A function of type `A -> B` allows us to turn evidence of `A` into evidence of `B`.

Therefore, `A -> B` is an inhabited Set if `A` being an inhabited Set *implies* that `B` is an inhabited Set.

Furthermore, polymorphism over Sets, looked at through this propositional lens, is just universal quantification.

That is to say, for example, that the type of `absurd` quite literally states that "forall x, false implies x".

With the same trick, the products and sums we defined over types can be interpreted as "and"s and "or"s respectively:

-}

-- `n times m is nonzero` if and only if `n is nonzero *and* m is nonzero`
-- Therefore `Pair N M` is inhabited if and only if `N` is inhabited *and* `M` is inhabited

true-and-true : Pair One One
true-and-true = pair 1/One 1/One

false-and-true-is-absurd : {X : Set} -> Pair Zero One -> X
false-and-true-is-absurd (pair () x)

true-and-false-is-absurd : {X : Set} -> Pair One Zero -> X
true-and-false-is-absurd (pair x ())

false-and-false-is-absurd : {X : Set} -> Pair Zero Zero -> X
false-and-false-is-absurd (pair () ())

-- `n plus m is nonzero` if and only if `n is nonzero *or* m is nonzero`
-- Therefore `Either N M` is inhabited if and only if `N` is inhabited *or* `M` is inhabited

true-or-true : Either One One
true-or-true = left 1/One -- Note that this is only one of two distinct proofs of this proposition

false-or-true : Either One Zero
false-or-true = left 1/One

true-or-false : Either Zero One
true-or-false = right 1/One

false-or-false-is-absurd : {X : Set} -> Either Zero Zero -> X
false-or-false-is-absurd (left ())
false-or-false-is-absurd (right ())

{-

The ability to prove any proposition given a false proposition, as in `absurd`, is known as the principle of explosion:

-}

IsFalse : Set -> Set
IsFalse A = {X : Set} -> A -> X -- `A` can "explode" into any other proposition `X`

Zero-IsFalse : IsFalse Zero
Zero-IsFalse {X} z = absurd {X} z

{-

A consequence of this principle is that one false proposition is just as useful as any other false proposition:

-}

False-propositions-imply-each-other : {A B : Set} -> IsFalse A -> IsFalse B -> Pair (A -> B) (B -> A)
False-propositions-imply-each-other {A} {B} a-is-false b-is-false = pair a-to-b b-to-a
  where
    a-to-b : A -> B
    a-to-b a = a-is-false {B} a
    b-to-a : B -> A
    b-to-a b = b-is-false {A} b

{-

To disprove an assumption, it therefore suffices to prove any proposition for which we have proven explosion, like Zero:

-}

false-or-false-is-false : Either Zero Zero -> Zero
false-or-false-is-false (left ())
false-or-false-is-false (right ())

true-and-false-is-false : Pair One Zero -> Zero
true-and-false-is-false (pair _ ())

{-

Picking a default false proposition to use instead of using the principle of explosion is generally more convenient.

Aside from the type being more concise, this lets us write many disproofs more directly, without refutation patterns:

-}

false-or-false-is-false' : Either Zero Zero -> Zero
false-or-false-is-false' (left x) = x
false-or-false-is-false' (right y) = y

true-and-false-is-false' : Pair One Zero -> Zero
true-and-false-is-false' x = snd x

{-

Just as one could define `not : Bool -> Bool` as `not x = x => false`, we can define negation over types like:

-}

Not : Set -> Set
Not A = A -> Zero

{-

Disproofs or negations are not only interesting to construct, they can also be useful to have as an assumption.

Previously we observed that we cannot always extract an element from an Either, since we must always handle both cases.

However, if we have proof that a particular case of an Either is not even possible, then we can refuse to handle it:

-}

getLeftAndRefuteRight : {A B : Set} -> Not B -> Either A B -> A
getLeftAndRefuteRight not-b (left a) = a
getLeftAndRefuteRight not-b (right b) = absurd (not-b b) -- Note how Agda infers the type parameter `A` for absurd

{-

This function is a proof that "not b implies ((a or b) implies a)", or equivalently that "not b and (a or b) imply a".

At this point, we are more than ready to formulate the law of the excluded middle:

-}

LEM : Set
LEM = {A : Set} -> Either A (Not A)

{-

LEM quite literally states that for any proposition A, either A, or not A.

While this is obvious classically, where propositions are just booleans, it is not at all obvious intuitionistically:

-}

-- proof-of-LEM : LEM
-- proof-of-LEM {A} = ?

{-

An attempt to fill this definition will quickly make it clear that we have no basis upon which to compute an answer.

Even if you could somehow inspect the concrete definition of A, you would at best be up against the halting problem.

This is not to say, however, that LEM is false intuitionistically, as disproving it is similarly impossible:

-}

-- disproof-of-LEM : Not LEM
-- disproof-of-LEM lem = ?

{-

Consequently, we can safely port any classical proposition into Agda by simply adding the assumption "LEM -> ...".

Another law which is valid classically but not intuitionistically is the principle of double negation elimination:

-}

DNE : Set
DNE = {A : Set} -> Not (Not A) -> A

-- proof-of-DNE : DNE
-- proof-of-DNE {A} = ?

-- disproof-of-DNE : Not DNE
-- disproof-of-DNE dne = ?

{-

A function outputting an empty type does not need to define any output, it only needs to refute its input.

So, if all you have is a function of type `Not (Not A)`, or `(A -> Zero) -> Zero`, it is impossible to *produce* an A.

That is, impossible unless you can magically summon a proof or disproof out of nowhere, as is possible with LEM:

-}

LEM-to-DNE : LEM -> DNE -- written out this reads: ({A : Set} -> Either A (Not A)) -> {A : Set} -> Not (Not A) -> A
LEM-to-DNE lem {A} not-not-a = h (lem {A})
  where
    h : Either A (Not A) -> A
    h (left a) = a
    h (right not-a) = absurd (not-not-a not-a)

{-

LEM-to-DNE assumes `lem : LEM` and the inputs of DNE, `{A : Set}` and `Not (Not A)`, to prove the output of DNE, `A`.

To do this we invoke lem with the type `A` to prove `Either A (Not A)` (note that lem itself is a polymorphic function).

Since we assumed `Not (Not A)` (i.e. the input `not-not-a`), we know that lem will output `left`, with a proof of A.

If lem were to output `right` with a proof of `Not A`, then this would contradict our assumption of `Not (Not A)`.

By pattern matching on the output of lem with `h`, we can extract a proof of `A`, and refute the possibility of `Not A`.

In fact, the helper function `h` serves the same exact purpose as the previously defined function getLeftAndRefuteRight:

-}

LEM-to-DNE' : LEM -> DNE
LEM-to-DNE' lem {A} not-not-a = getLeftAndRefuteRight not-not-a (lem {A})

{-

Notice how the lack of computational feasibility is cleanly carried over from one classical law to the other.

Exercises:

While working on these exercises, consider how your solutions can be read as logical proofs.

Keep an eye out for opportunities to write proofs in terms of previously completed proofs.

-}

-- Ex5.1: Prove the following lemmas involving negations

-- a-to-not-not-a : {A : Set} -> A -> Not (Not A)
-- a-to-not-not-a a not-a = ?

-- not-not-a-to-not-a-implies-a : {A : Set} -> Not (Not A) -> Not A -> A
-- not-not-a-to-not-a-implies-a not-not-a not-a = ?

-- dne-for-negations : {A : Set} -> Not (Not (Not A)) -> Not A
-- dne-for-negations not-not-not-a a = ?

-- Ex5.2: Prove the following lemmas involving negations and disjunctions

-- a-or-b-to-not-a-implies-b : {A B : Set} -> Either A B -> Not A -> B
-- a-or-b-to-not-a-implies-b a-or-b not-a = ?

-- not-a-implies-b-to-not-not-a-or-b : {A B : Set} -> (Not A -> B) -> Not (Not (Either A B))
-- not-a-implies-b-to-not-not-a-or-b not-a-implies-b not-a-or-b = ?

-- Ex5.3: Prove the following lemmas involving assumptions which are universally quantified (aka polymorphic functions)

-- not-forall-a,b-a-or-b-implies-a : Not ({A B : Set} -> Either A B -> A)
-- not-forall-a,b-a-or-b-implies-a forall-a,b-a-or-b-implies-a = ?

-- not-forall-a,b-a-implies-a-and-b : Not ({A B : Set} -> A -> Pair A B)
-- not-forall-a,b-a-implies-a-and-b forall-a,b-a-implies-a-and-b = ?

-- classically-not-a-implies-b-to-a-or-b : {A B : Set} -> LEM -> (Not A -> B) -> Either A B
-- classically-not-a-implies-b-to-a-or-b lem not-a-implies-b = ?

-- Ex5.4: Prove the following lemmas involving assumptions which are only valid classically

-- not-not-a-or-b-to-a-or-b-is-classical : ({A B : Set} -> Not (Not (Either A B)) -> Either A B) -> DNE
-- not-not-a-or-b-to-a-or-b-is-classical not-not-a-or-b-to-a-or-b = ?

-- not-a-implies-b-to-a-or-b-is-classical : ({A B : Set} -> (Not A -> B) -> Either A B) -> DNE
-- not-a-implies-b-to-a-or-b-is-classical = ?

-- Ex5.5: Define the parametric encodings of Zero and One

-- CZero : Set
-- CZero = {X : Set} -> ?

-- COne : Set
-- COne = {X : Set} -> ?

-- Ex5.6: Define the following variant of propositional `or` such that the following definitions can be filled in

-- Par : Set -> Set -> Set
-- Par A B = Pair (? -> A) (? -> B)

-- either-to-par : {A B : Set} -> Either A B -> Par A B
-- either-to-par either-a-b = ?

-- par-to-not-not-either : {A B : Set} -> Par A B -> Not (Not (Either A B))
-- par-to-not-not-either par-a-b = ?

-- par-lem-to-dne : ({A : Set} -> Par A (Not A)) -> DNE
-- par-lem-to-dne par-lem = ?

-- Ex5.7: Fill in the missing types to show how proofs about implications de-generalize into proofs about negations

-- What logical law does the type of `id` correspond to?

-- not-false : Not Zero
-- not-false = id {?}

-- What logical law does the type of `compose` correspond to?

-- not-b-to-a-implies-b-to-not-a : {A B : Set} -> Not B -> (A -> B) -> Not A
-- not-b-to-a-implies-b-to-not-a {A} {B} = compose {?} {?} {?}

-- Ex5.8: Find the exercises from chapter 3 which de-generalize into the following lemmas and use them as solutions

-- false-to-not-a : {A : Set} -> Zero -> Not A
-- false-to-not-a = ?

-- not-a-to-not-a : {A : Set} -> Not A -> Not A
-- not-a-to-not-a = ?

-- a-implies-not-a-to-not-a : {A : Set} -> (A -> Not A) -> Not A
-- a-implies-not-a-to-not-a = ?

-- a-implies-not-b-to-b-implies-not-a : {A : Set} -> (A -> Not B) -> B -> Not A
-- a-implies-not-b-to-b-implies-not-a = ?

-- not-a-implies-a-to-not-not-a : {A : Set} -> (Not A -> A) -> Not (Not A)
-- not-a-implies-a-to-not-not-a = ?

-- Ex5.9: Find the exercises from chapter 4 which de-generalize into the following lemmas and use them as solutions

-- a-implies-b-to-not-a-and-b : {A B : Set} -> (A -> Not B) -> Not (Pair A B)
-- a-implies-b-to-not-a-and-b = ?

-- not-a-and-not-b-to-not-a-or-b : {A B : Set} -> Pair (Not A) (Not B) -> Not (Either A B)
-- not-a-and-not-b-to-not-a-or-b = ?

-- not-a-and-b-to-a-implies-b : {A B : Set} -> Not (Pair A B) -> A -> Not B
-- not-a-and-b-to-a-implies-b = ?

-- not-a-or-b-to-not-a-and-not-b : {A B : Set} -> Not (Either A B) -> Pair (Not A) (Not B)
-- not-a-or-b-to-not-a-and-not-b = ?

-- Ex5.10: Reconciling algebraic and logical interpretations of types

-- We have seen that some logical laws involving `Zero`/`Not` are de-generalizations of corresponding algebraic laws
-- What are some logical laws involving `Zero`/`Not` which do *not* correspond like this to any algebraic law?
-- Why are these laws not necessarily inconsistent with our algebraic interpretation of types?

{-

Tips and Tricks:

In Emacs, you can search forwards and backwards for text with C-s and C-r respectively.

After finding an initial match, pressing C-s and C-r again will take you to any next and previous matches respectively.

You can use this to jump to specific exercises, since they are all labeled like "Ex<chapter>.<number>".

Challenge Exercises:

-}

-- Ce5.1: Double negation elimination implies the law of the excluded middle

-- DNE-to-LEM : DNE -> LEM
-- DNE-to-LEM dne {A} = ?

-- Ce5.2: The principle of double negation shift

-- It is easy to move a double negation from the outside to the inside of a universal quantification
-- However, going in the opposite direction is not so easy and is known as a double negation shift:
DNS : Set
DNS = {P : Set -> Set} -> ({X : Set} -> Not (Not (P X))) -> Not (Not ({X : Set} -> P X))

-- DNS is an example of a classical principle which is weaker than LEM
-- Show that it is equivalent to the double negation of LEM

-- not-not-lem-to-dns : Not (Not LEM) -> DNS
-- not-not-lem-to-dns not-not-lem forall-x-not-not-p-of-x not-forall-x-p-of-x = ?

-- dns-to-not-not-lem : DNS -> Not (Not LEM)
-- dns-to-not-not-lem dns not-lem = ?

{-

Chapter 6. Dependent Types

It is very convenient in Agda that types are treated just like values, allowing us to define type aliases as functions:

-}

_<->_ : Set -> Set -> Set
A <-> B = Pair (A -> B) (B -> A)

{-

This definition of propositional bi-implication perfectly mirrors the following definition of boolean bi-implication:

-}

-- _<=>_ : Bool -> Bool -> Bool
-- a <=> b = (a => b) && (b => a)

{-

While this is neat, it is only the first step toward a language feature which is orders of magnitude more powerful.

A language with "Dependent Types" allows us to fluidly bridge the gap between values and types:

-}

-- `Vec` is a list type parameterized by (or "dependent" on) a length, so `Vec n A` is a list of exactly `n` `A`s.
Vec : Nat -> Set -> Set
Vec zero A = One
Vec (suc n) A = Pair A (Vec n A)

{-

`Vec` is just a function which computes a type from a value, and mirrors the following definition of exponentiation:

-}

-- _^_ : Nat -> Nat -> Nat
-- a ^ zero = one
-- a ^ (suc n) = a * (a ^ n)

{-

Functions from values to types may be used like type aliases and will be normalized during type checking:

-}

-- This should look very similar to List-from-one-to-five from Chapter 4.
Vec-from-one-to-five : Vec 5 Nat
Vec-from-one-to-five = pair 1 (pair 2 (pair 3 (pair 4 (pair 5 1/One))))

-- Use "C-c C-n" in the following hole to see the fully written out type of Vec-from-one-to-five
-- _ = {! Vec 5 Nat  !}

-- The following two variants will not type check:

-- Bad-Vec-from-one-to-five : Vec 6 Nat
-- Bad-Vec-from-one-to-five = pair 1 (pair 2 (pair 3 (pair 4 (pair 5 1/One))))

-- Bad-Vec-from-one-to-five : Vec 4 Nat
-- Bad-Vec-from-one-to-five = pair 1 (pair 2 (pair 3 (pair 4 (pair 5 1/One))))

{-

The ability to compute types from constant values is not particularly rare in modern programming languages.

Dependently typed programming languages stand out by letting us describe types in terms of *variable* input values.

We have arguably already been doing this with types which are dependent on variable inputs of type Set.

However, if we can compute Sets from values of type Nat, then can name Nat inputs and use them in the remaining type:

-}

prepend-to-Vec : {A : Set} {n : Nat} -> Vec n A -> A -> Vec (suc n) A
prepend-to-Vec xs x = pair x xs

-- Use "C-c C-." to display the inferred type of the given expression
-- Vec-from-zero-to-five = {! prepend-to-Vec Vec-from-one-to-five 0  !}

{-

When prepending an element to a tuple of length `n`, the resulting tuple should of course have a length of `n + 1`.

While it may seem intuitive that the type of `prepend-to-Vec` is correct, it is not obvious that it should type check.

In particular, the type checker must take into account the "definitional" equality `Vec (suc n) A = Pair A (Vec n A)`.

During type checking, Agda will aggressively apply definitional equalities to reduce types wherever possible.

While checking prepend-to-Vec, Agda reduces its type to `{n : Nat} {A : Set} -> Vec n A -> A -> Pair A (Vec n A)`.

More complex definitions operating on dependent types often involve so-called "dependent pattern matching":

-}

concat-Vecs : {A : Set} {n m : Nat} -> Vec n A -> Vec m A -> Vec (n + m) A
concat-Vecs {_} {zero} {_} 1/One ys = ys
concat-Vecs {_} {suc n'} {_} (pair x xs) ys = pair x (concat-Vecs xs ys)

{-

When pattern matching on an input which the output type depends on, Agda's type checker will refine the output type:

  In the `n = zero` case, the remaining type is `{m : Nat} {A : Set} -> Vec zero A -> Vec m A -> Vec (zero + m) A`.

  Since we defined `zero + m = m`, Agda can reduce this down to `{m : Nat} {A : Set} -> One -> Vec m A -> Vec m A`.

  After this reduction it becomes entirely trivial for Agda to see that `concat-Vecs ... ys = ys` should type check.

  In the `n = suc n'` case, we get `{m : Nat} {A : Set} -> Vec (suc n') A -> Vec m A -> Vec (suc n' + m) A`.

  Here Agda uses the definitional equalities `suc n + m = suc (n + m)` and `Vec (suc n) A = Pair A (Vec n A)`.

  The fully reduced type is then `{m : Nat} {A : Set} -> Pair A (Vec n' A) -> Vec m A -> Pair A (Vec (n' + m) A)`.

  The recursive usage of `concat-Vecs` then operates on a `Vec n' A` and `Vec m' A` producing a `Vec (n' + m) A`.

  Finally, `pair` is applied to an `A` and a `Vec (n' + m) A`, producing the required `Pair A (Vec (n' + m) A)`.

Many programming languages allow for similar code which works for a finite number of inputs known all at compiletime.

Such a language is only able to reduce types individually for each set of concrete, compiletime-constant inputs.

Agda does not impose this restriction, and instead uses equational reasoning to check types containing variable inputs.

While this is much more powerful, computing with variables is entirely non-trivial, unlike computing with constants.

If we so much as flip the `n + m` around to `m + n`, Agda suddenly fails to reduce `m + zero` and `m + (suc n')`:

-}

-- concat-Vecs' : {A : Set} {n m : Nat} -> Vec n A -> Vec m A -> Vec (m + n) A
-- concat-Vecs' {_} {zero} {_} 1/One ys = ys
-- concat-Vecs' {_} {suc n'} {_} (pair x xs) ys = pair x (concat-Vecs' xs ys)

{-

While the reader may find it obvious that `m + zero = m` and `m + (suc n') = suc (m + n')`, Agda's typechecker does not.

Agda only knows the two definitional equalities we gave for `_+_`, and will only use these during type checking.

So while Agda sees that `ys` is of type `Vec m A`, it cannot see that this is the same as `Vec (m + zero) A`.

Similarly, `pair x (concat-Vecs' xs ys)` is of type `Pair A (Vec (m + n') A)`, not the required `Vec (m + suc n') A`.

Luckily, dependent types and pattern matching also enable us to formulate and prove such equalities separately.

After proving an equality, we will be able to apply it explicitly to perform any necessary substitutions.

Using our propositional interpretation of types, we can define equalities of natural numbers as a dependent type:

-}

Nat-Id : Nat -> Nat -> Set
Nat-Id zero zero = One
Nat-Id (suc n) (suc m) = Nat-Id n m
Nat-Id zero (suc _) = Zero
Nat-Id (suc _) zero = Zero

{-

Nat-Id is the identity relation for `Nat`s, where a value of type `Nat-Id n m` is a proof that n and m are identical.

Again, this definition mirrors the following definition of boolean equality over the natural numbers:

-}

-- _==_ : Nat -> Nat -> Bool
-- zero == zero = true
-- (suc n) == (suc m) = n == m
-- zero == (suc _) = false
-- (suc _) == zero = false

{-

Indeed, `Nat-Id n m` is an inhabited Set (`One`) when n and m are equal, and is an uninhabited Set (`Zero`) otherwise:

-}

two-is-equal-to-two : Nat-Id 2 2
two-is-equal-to-two = 1/One

two-is-not-equal-to-three : Not (Nat-Id 2 3)
two-is-not-equal-to-three = id {Zero}

{-

Here, Agda has no problem reducing `Nat-Id 2 2` and `Nat-Id 2 3` down to `One` and `Zero` respectively.

As with `Vec 5 Nat`, this reduction is trivial since it only involves constants, but we can also work with variables:

-}

-- forall Nats n and m, n = m implies n + 1 = m + 1
n-equals-m-implies-n+1-equals-m+1 : {n m : Nat} -> Nat-Id n m -> Nat-Id (suc n) (suc m)
n-equals-m-implies-n+1-equals-m+1 n-eq-m = n-eq-m

{-

As with `prepend-to-Vec`, Agda is willing to apply definitional equalities even in the presence of variables.

  Here, Agda takes advantage of the fact that `Nat-Id` was defined such that `Nat-Id (suc n) (suc m) = Nat-Id n m`.

  The reduced type of this definition is then `{n m : Nat} -> Nat-Id n m -> Nat-Id n m`, which can be easily checked.

Previously we observed how Agda cannot see that `n + zero` is equal to `n`, however now we can simply prove this:

-}

n+0-equals-n : (n : Nat) -> Nat-Id (n + zero) n
n+0-equals-n zero = 1/One
n+0-equals-n (suc n') = n+0-equals-n n'

{-

As with `concat-Vecs`, here we are again taking advantage of dependent pattern matching:

  In the `n = zero` case, the remaining type `Nat-Id (zero + zero) zero` has no variables and simply reduces to `One`.

  In the `n = suc n'` case, the remaining type `Nat-Id (suc n' + zero) (suc n')` reduces in a two steps:

  First the `suc n' + zero` reduces to `suc (n' + zero)`, resulting in the type `Nat-Id (suc (n' + zero)) (suc n')`.

  This then reduces to `Nat-Id (n' + zero) n'` via the definitional equality `Nat-Id (suc n) (suc m) = Nat-Id n m`.

  This type is exactly the same as the original type we wanted to prove, but with `n` aka `suc n'` replaced by `n'`

  So, since `n'` is structurally smaller than `n`, we can complete the proof recursively with `n+0-equals-n n'`.

While this is cool and all, it is important that we can actually *use* our equality proofs to perform substitutions.

Given an equality `n = m`, substitution should let us turn any value or proof of type `P(n)` into one of type `P(m)`.

This means we need to quantify over dependent types (or, less generally, logical predicates) `P` of type `Nat -> Set`.

For instance when `P x = Vec x A`, an equality `Nat-id n m` should allow us to turn a `Vec n A` into a `Vec m A`.

Similarly when `P x = Nat-Id x a`, then this should allow us to assume `Nat-Id n a` in order to prove `Nat-Id m a`.

Critically though, if n and m are truly equal, then this must work for any given dependent type or logical predicate P:

-}

Nat-subst : (P : Nat -> Set) (n m : Nat) -> Nat-Id n m -> P n -> P m
Nat-subst P zero zero n-eq-m p-n = p-n
Nat-subst P (suc n') (suc m') n-eq-m p-n = recursive-case P' p-n
  where
    recursive-case : (Q : Nat -> Set) -> Q n' -> Q m'
    recursive-case Q = Nat-subst Q n' m' n-eq-m
    P' : Nat -> Set
    P' x = P (suc x)

{-

The particularly tricky type of `Nat-subst` is accompanied by a similarly tricky proof:

  The first case is trivial, as `P n` and `P m` both become `P zero`, so we just have to prove `P zero -> P zero`.

  However in the second case we need to somehow prove `P (suc n') -> P (suc m')` given a proof of `Nat-Id n' m'`.

  We can perform recursion with the structurally smaller `n'` and `m'` yielding a `(Q : Nat -> Set) -> Q n' -> Q m'`.

  Note how we carefully switch to the name `Q` in a where clause to avoid confusingly talking about two different `P`s.

  The `Q` input in the recursive case can be any predicate, so we may define it in terms of the `P` input we are handed.

  By using `P'` where `P' x = P (suc x)`, we get a proof of `P' n' -> P' m'` or equivalently `P (suc n') -> P (suc m')`.

Since `Nat-subst` assumes `Nat-Id n m`, Agda lets us omit the remaining two cases where n and m are trivially unequal:

-}

-- Nat-subst zero (suc _) () P
-- Nat-subst (suc _) zero () P

-- Or alternatively:

-- Nat-subst zero (suc _) n-eq-m P = absurd n-eq-m
-- Nat-subst (suc _) zero n-eq-m P = absurd n-eq-m

{-

Both of these cases can be defined by showing the `Nat-Id n m` input to be absurd, since it simply reduces to `Zero`.

Agda infers these cases for us automatically since they both can be completed with no more than a refutation pattern.

Finally, lets see substitution in action:

-}

cast-Vec : {A : Set} {n m : Nat} -> Nat-Id n m -> Vec n A -> Vec m A
cast-Vec {A} {n} {m} n-eq-m vec = Nat-subst P n m n-eq-m vec
  where
    P : Nat -> Set
    P x = Vec x A

cast-Nat-Id : {a n m : Nat} -> Nat-Id n m -> Nat-Id n a -> Nat-Id m a
cast-Nat-Id {a} {n} {m} n-eq-m m-eq-a = Nat-subst P n m n-eq-m m-eq-a
  where
    P : Nat -> Set
    P x = Nat-Id x a

{-

Notably, `Nat-subst _ _ _ _ p-n` always returns the same `p-n` it is given, so `cast-Vec` does not modify its input.

`cast-Vec` can be used to turn e.g. a `Vec (n + m) A` into an equivalent `Vec (m + n)` given a proof of `n + m = m + n`.

This will be left as an exercise for the reader.

Exercises:

When writing proofs in Agda, the type checker can do a lot of the work for us by applying definitional equalities.

While completing these exercises, make sure to understand exactly which definitional equalities you are relying on.

As previously mentioned, prefixing a command like "C-c C-." with "C-u C-u" will fully normalize any displayed types.

To force Agda to explicitly avoid any normalization whatsoever, a command can similarly be prefixed with a single "C-u".

-}

-- Ex6.1: Prove the following lemmas about your chapter 1 solutions

Is-true : Bool -> Set
Is-true false = Zero
Is-true true = One

-- or<->|| : (x y : Bool) -> Is-true (or x y) <-> Is-true (x || y)
-- or<->|| x y = ?

-- not-and<->nand : (x y : Bool) -> Is-true (not (and x y)) <-> Is-true (nand x y)
-- not-and<->nand x y = ?

-- and-and<->and3 : (x y z : Bool) -> Is-true (and x (and y z)) <-> Is-true (and3 x y z)
-- and-and<->and3 x y z = ?

-- Formulate and prove that implies is the same as _=>_

-- Formulate and prove that xor is the same as _^^_

-- Formulate the law of the excluded middle in terms of boolean operations and show that it always Is-true

-- Ex6.2: Formalize our interpretation of various types as particular propositions

-- One~true : One <-> Is-true true
-- One~true = ?

-- Zero~false : Zero <-> Is-true false
-- Zero~false = ?

-- Pair~and : (x y : Bool) -> Pair (Is-true x) (Is-true y) <-> Is-true (x && y)
-- Pair~and x y = ?

-- Either~or : (x y : Bool) -> Either (Is-true x) (Is-true y) <-> Is-true (x || y)
-- Either~or x y = ?

-- ->~implication : (x y : Bool) -> (Is-true x -> Is-true y) <-> Is-true (x => y)
-- ->~implication x y = ?

-- <->~biimplication : (x y : Bool) -> (Is-true x <-> Is-true y) <-> Is-true (x <=> y)
-- <->~biimplication x y = ?

-- Ex6.3: Formalize a notion of propositional equality for the booleans

-- Bool-Id : Bool -> Bool -> Set
-- Bool-Id x y = ?

-- Bool-Id-subst : (P : Bool -> Set) (x y : Bool) -> Bool-Id x y -> P x -> P y
-- Bool-Id-subst P x y x-eq-y p-x = ?

-- Prove the following lemmas by substitution

-- always-true-lemma-1 : (f : Bool -> Bool) -> Bool-Id (f false) (f true) -> Is-true (f false) -> Is-true (f true)
-- always-true-lemma-1 f f-false-eq-f-true f-false-Is-true = ?

-- always-true-lemma-2 : (f : Bool -> Bool) (x : Bool) -> Bool-Id true (f false) -> Bool-Id true (f true) -> Is-true (f x)
-- always-true-lemma-2 f x true-eq-f-false true-eq-f-true = ?

-- Prove the following lemmas with multiple consecutive substitutions
-- Consider the exact sequence of equality substitutions you intend to apply
-- One effective strategy is to write out the individual steps as separate helper definitions and then compose them

-- always-true-lemma-3 : (f : Bool -> Bool) -> Bool-Id true (f false) -> Bool-Id true (f true)
--                    -> Is-true (f false && f true)
-- always-true-lemma-3 f true-eq-f-false true-eq-f-true = ?

-- Bool-identity-lemma : (f : Bool -> Bool) -> Bool-Id false (f false) -> Bool-Id true (f true)
--                    -> Is-true (is-the-identity-function f)
-- Bool-identity-lemma f p = ?

-- Ex6.4: Induction over the booleans

-- The induction principle for booleans captures how we typically prove theorems about them
-- More generally it captures how we construct values of types dependent on boolean values

-- Bool-induction : (P : Bool -> Set) -> P false -> P true -> (a : Bool) -> P a
-- Bool-induction P p-false p-true a = ?

-- Choose an appropriate predicate to prove the following lemma by induction

-- not-[x-and-not-x]-Is-true : (x : Bool) -> Is-true (not (x && not x))
-- not-[x-and-not-x]-Is-true x = Bool-induction P ? ? x
--   where
--     P : Bool -> Set
--     P y = ?

-- Prove the following lemma once in terms of the previous lemma, and once in terms of Bool-induction
-- Observe how in both cases we are effectively performing dependent pattern matching on the result of an expression

-- not-[f-x-and-not-f-x]-Is-true : (f : Bool -> Bool) (x : Bool) -> Is-true (not (f x && not (f x)))
-- not-[f-x-and-not-f-x]-Is-true f x = ?

-- not-[f-x-and-not-f-x]-Is-true' : (f : Bool -> Bool) (x : Bool) -> Is-true (not (f x && not (f x)))
-- not-[f-x-and-not-f-x]-Is-true' f x = ?

-- Use induction to prove the following theorem about one of your chapter 1 solutions

-- BoolToBool-equality-lemma : (f g : Bool -> Bool) -> Bool-Id (f false) (g false) -> Bool-Id (f true) (g true)
--                          -> Is-true (f =[BoolToBool]= g)
-- BoolToBool-equality-lemma = ?

-- Ex6.5: Induction over the naturals

-- todo:

-- If P(0) and forall n, P(n) implies P(n + 1) then forall m, P(m)
-- Nat-induction : (P : Nat -> Set) -> P zero -> ((n : Nat) -> P n -> P (suc n)) -> (m : Nat) -> P m
-- Nat-induction P base-case step-case m = ?

-- Previously, we proved `n + zero = n` by recursion, however recursion with dependent types is really just induction.
-- Now prove this lemma directly with Nat-induction:

-- n+0-equals-n' : (n : Nat) -> Nat-Id (n + zero) n
-- n+0-equals-n' n = ?

-- Nat-Id-symmetry : (n m : Nat) -> Nat-Id n m -> Nat-Id m n
-- Nat-Id-symmetry = ?

-- n+m-equals-m+n : (n m : Nat) -> Nat-Id (n + m) (m + n)
-- n+m-equals-m+n = ?

Is-Even : Nat -> Set
Is-Even zero = One
Is-Even (suc n) = Not (Is-Even n)

-- Ex6.6: Prove the following lemmas about your chapter 2 solutions

-- todo:

-- Remember that nothing will stop you from using the same name for two unequal values in a type and in a definition.
-- In fact, when case-splitting with "C-c C-c", even Agda will not make any effort to avoid such ambiguities.
-- Take care to name your variables appropriately to avoid confusion when looking at Agda's informational window.

-- _ : (n m : Nat) -> (Nat-Id n m <-> Is-true (n =[Nat]= m))
-- _ = ?

-- Ex6.7: Formalize our algebraic interpretation of types

-- todo:

-- Ex6.8: something about counter examples to universally quantified predicates

-- todo:

-- pred-is-a-lie : Not ((n : Nat) -> Nat-Id n (suc (pred n)))
-- pred-is-a-lie f = ?

-- Ex6.9: induction and equality for other datatypes

-- todo:

-- Ex6.10: proofs about Ch4 exercises

{-

Tips and Tricks:

Agda's type system is so powerful that it can sometimes be difficult to understand why a definition type checks.

This can be problematic, as understanding why a proof type checks is key to actually understanding the proof.

One way to combat this is to explicitly annotate expressions with types like `id {ExpectedType} expr`:

-}

vec-from-3-to-5 = id {Vec 3 Nat} (pair 3 (pair 4 (pair 5 1/One)))

{-

If we are not quite sure about a type, we can place a hole and ask Agda to solve for it with "C-c C-s":

-}

-- vec-from-3-to-5' = id {?} (pair 3 (pair 4 (pair 5 1/One)))

{-

Feel free to insert such type annotations anywhere, even outside of exercises, to make proofs more understandable.

Using the identity function for annotations is a cute trick, but we might prefer to use a more purposeful syntax:

-}

-- Declare "a as A" to be syntactic sugar for "id {A} a" and be left-associative, so `a as X as Y` == `(a as X) as Y`

-- infixl 10 id
-- syntax id {A} a = a as A

-- Now we can annotate terms more nicely:

-- vec-from-3-to-5'' = pair 3 (pair 4 (pair 5 1/One)) as Vec 3 Nat as Pair Nat (Pair Nat (Pair Nat One))

{-

Place this syntax declaration at the earliest point in this file (after the definition of id) where you wish to use it.

Challenge Exercises:

-}

-- todo: 

Is-inhabitance-predicate : (Set -> Bool) -> Set
Is-inhabitance-predicate p = (A : Set) -> Is-true (p A) <-> A

inhabitance-predicates-imply-lem : (p : Set -> Bool) -> Is-inhabitance-predicate p -> LEM
inhabitance-predicates-imply-lem p p-is-ip {A} = ?

Tuple : List Set -> Set
Tuple types = ?

LeibnitzEquality : {A : Set} -> A -> A -> Set
LeibnitzEquality {A} x y = (P : A -> Set) -> P x -> P y

-- LeibnitzEquality<->Bool-Id : (x y : Bool) -> LeibnitzEquality x y <-> Bool-Id x y
-- LeibnitzEquality<->Bool-Id x y = ?

-- LeibnitzEquality<->Nat-Id : (x y : Nat) -> LeibnitzEquality x y <-> Nat-Id x y
-- LeibnitzEquality<->Nat-Id x y = ?

-- Leibnitz-reflexivity
-- Leibnitz-symmetry
-- Leibnitz-transitivity
-- Leibnitz-congruence

-- Prove that _=[Fraction]=_ is an equivalence relation
-- Prove that it is the right equivalence relation
-- Prove that it cannot have a general substitution principle

-- prove correctness about various challenge exercises from previous chapters

{-

todo:

-}


data Sigma : (A : Set) -> (P : A -> Set) -> Set where
  sigma : {A : Set} {P : A -> Set} -> (a : A) -> P a -> Sigma A P

data Pi : (A : Set) -> (P : A -> Set) -> Set where
  pi : {A : Set} {P : A -> Set} -> ((a : A) -> P a) -> Pi A P
