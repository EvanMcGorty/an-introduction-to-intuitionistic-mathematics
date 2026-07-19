-- This option technically makes Agda logically inconsistent, in exchange for a greatly improved learning experience.
{-# OPTIONS --type-in-type #-}

module AnIntroductionToIntuitionisticMathematics where

{-

Preface.

Intuitionistic mathematics is a form of constructive mathematics which is built on top of intuitionistic logic.

In intuitionistic logic, proofs may be understood as programs, and propositions may be understood as types of programs.

We can formalize all(?) of mathematics as well-typed code which can be verified mechanically by running a type checker.

This interactive tutorial uses an intuitionistic proof assistant and functional programming language called Agda.

If you wish to fill in the exercises, install `agda` and the text editor `emacs`, and run `agda --emacs-mode setup`.

Agda was designed around its powerful interactive editing with emacs, so use another editor at your own discretion.

Open this file in emacs and load it into Agda by pressing "C-c C-l", which is emacs-speak for key combo "Ctrl-c Ctrl-l".

If you set everything up correctly, you should now see an empty informational window, and code should be colored.

In emacs you can zoom in and out with "C-x C-+" (Ctrl-x Ctrl-plus) and "C-x C--" (Ctrl-x Ctrl-minus) respectively.

Part 1. Pure Functional Programming

A "pure" function is one which always produces one and the same output for a given input, without causing side effects.

Pure functions have a mathematical flavor, and make it easy to use equational reasoning to prove properties about them.

In Agda, functions are required not just to be pure but also "total", meaning they may not fail or loop indefinitely.

This is not to say that we cannot write e.g. imperative functions, just that we must model them with pure functions.

In Part 2, this very clean and mathematical foundation will enable us to write proofs about our Agda code, *in Agda*.

Chapter 1. Booleans

The booleans are a `Set` containing two elements, `true`, and `false`, and in Agda this can be declared as follows:

-}

data Bool : Set where
  false : Bool
  true : Bool

{-

We can now declare the existence of functions between booleans, such as the negation function:

-}

not : Bool -> Bool

{-

This is called a type signature and it states that `not` is a function with a boolean input and a boolean output.

Agda checks that this type signature is respected by the definition of `not`, which we can construct as follows:

-}

not false = true
not true = false

{-

Notice how in Agda we leave out the parentheses found in math and most programming languages (e.g. `not(false) = true`).

To define functions accepting multiple input parameters in Agda, we use a trick called "Currying".

Rather than accepting e.g. two inputs at once, we accept one input, and return a function accepting the another input.

So instead of the "uncurried" function type `(A, B) -> C`, we use the "curried" function type `A -> (B -> C)`.

Consequently we don't write function application like `f(x, y)`, but rather like `f(x)(y)`, or in Agda just `f x y`.

Notably, the function arrow associates to the right, meaning that `A -> B -> C` is parsed as  `A -> (B -> C)`.

One such function with two inputs and one output is the boolean `and` operation:

-}

and : Bool -> Bool -> Bool
and false false = false
and false true = true
and true false = true
and true true = true

{-

The definitions of `not` and `and` used so-called "pattern matching" to map every possible set of inputs to an output.

However we can also bind input parameters to variables, which match any input, and can be used to define the output:

-}

or : Bool -> Bool -> Bool
or true x = true
or false x = x

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

However, it overlaps with the previous case, and therefore only holds if the inputs are not `false true`.

Agda's syntax highlighting colors this case to indicate that it overlaps with previous cases and is not a true equality.

Naturally, functions may also be defined in terms of other functions:

-}

implies : Bool -> Bool -> Bool
implies l r = or r (not l) -- I.e. "l implies r" is equivalent to "r or not l"

{-

Notice how function application associates to the left, so `or r (not l)` is the same as as `or(r)(not(l))`.

The use of parenthesis here is critical, as `or r not l` would have wrongly been interpreted as `or(r)(not)(l)`.

Try deleting these parentheses, reloading with C-c C-l, and making sense of the error message you get.

In emacs, you can undo these changes with C-/, at which point you should reload again to get rid of the error message.

Like any programming language, Agda supports comments which are ignored by the typechecker and have no effect on code.

Block comments are delimited by `{-` and `-}`, single-line comments begin with `--`.

It can be useful to comment out code which we don't want Agda to load, e.g. because it has an error:

-}

-- bad-xor : Bool -> Bool -> Bool
-- bad-xor false x = x

{-

By selecting lines of code and hitting "M-;" (emacs for "alt+semicolon"), you can easily comment them out or back in.

Try temporarily commenting bad-xor back in and reloading with C-c C-l to see what kind of error you get.

Agda allows us to use nearly any character we desire as part of a name, including `-`, `'`, and even unicode characters.

One character with a special meaning in a name, however, is underscore, which is used for so-called "mixfix" syntax.

Each underscore in the name of a function indicates where a parameter belongs syntactically:

-}

_&&_ : Bool -> Bool -> Bool
l && r = and l r

{-

This defines a synonym for `and` called `_&&_`, where `l && r` carries the same meaning as `_&&_ l r`.

We could have just as well written "_&&_ l r = and l r" for the definition, as there is absolutely no difference.

Note that the whitespace between each symbol is mandatory, and "l&&r" would be parsed as a singular, unrelated symbol.

Another cool thing we can do in Agda is define "higher order functions" which accept other functions as inputs:

-}

-- Tells you whether the provided function outputs true for any input
always-outputs-true : (Bool -> Bool) -> Bool
always-outputs-true f = f false && f true

{-

Notice that we need to wrap the `Bool -> Bool` argument in parentheses, since `->` does not associate to the left.

Exercises:

If you uncomment the following exercise and reload, the question mark should turn into a "hole" which looks like {! !}.

-}

-- A synonym for `or` (note: this line is an actual comment. Do not uncomment this as it is not valid Agda code)
-- _||_ : Bool -> Bool -> Bool
-- x || y = ?

{-

Holes represent a missing part of a program that you plan to complete later, and can be filled in interactively.

Write an expression in this hole and press C-c C-Space to ask Agda to type check it, and if successful, fill it in.

Any error in an Agda file typically renders its editor support useless, so holes are crucial to keeping code well-typed.

Another useful trick is to fill a hole with an expression containing yet more holes.

We can do this by simply writing an expression containing question marks, and hitting C-c C-Space.

Uncomment the following definition, reload, and try hitting C-c C-Space with your cursor placed in the hole:

-}

-- nand : Bool -> Bool -> Bool
-- nand x y = {! not ? !}

{-

It is crucial to learn to work with holes, which become extremely useful when writing more complex programs and proofs.

Complete as few or as many of the remaining exercises as you see fit:

-}

-- 3-ary and
-- and3 : Bool -> Bool -> Bool -> Bool
-- and3 x y z = ?

-- A synonym for `implies`, but missing a definition
-- _=>_ Bool -> Bool -> Bool

-- A synonym for `xor`, but missing a type signature
-- x ^^ y = ?

-- Define boolean equality, aka biimplication, as the symbol _<=>_

-- Tells you whether the provided function returns false regardless of what input it is given
-- always-outputs-false : (Bool -> Bool) -> Bool
-- always-outputs-false f = ?

-- Define a function which tells you whether its input (which is itself a function) is the `not` function

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
-- _=[BoolToBool]=_ : (Bool -> Bool) -> (Bool -> Bool) -> Bool
-- f =[BoolToBool]= g = ?

-- An increment function which wraps around from fourth to first
-- nextBoolToBool : (Bool -> Bool) -> Bool -> Bool
-- nextBoolToBool f = ?

-- Similarly, an addition function which wraps around from fourth to first
-- addBoolToBool : (Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool
-- addBoolToBool f g = ?

{-

Tips and Tricks:

Always reload with C-c C-l after making changes outside of a hole, otherwise Agda won't know about them.

If you rename a parameter variable and try to use it to fill in a hole without reloading, Agda wont recognize it.

To test your code, you can normalize an expression within a hole by entering the key combo C-c C-n.

To create a throw-away hole for such purposes you can use an anonymous, unnamed definition like "_ = ?".

Try uncommenting the following line, placing your cursor in the hole, and normalizing the contained expression:

-}

-- _ = {! true && false !}

{-

Use holes and C-c C-n liberally to test your code while commenting them out to avoid polluting the informational window.

Challenge Exercises:

(Note: these exercises can be very difficult and are best avoided by readers who are pressed for time)

Just as there are 4 different `Bool -> Bool`s, there are 16 different `Bool -> Bool -> Bool`s.

Furthermore, there are a whopping 256 different `Bool -> Bool -> Bool -> Bool`s.

By mapping each distinct function of such a type to a number, we can treat these types like size-bounded number types.

Find some such mapping with which you can define the following operations.

-}

-- A "UInt<n>" refers to an unsigned integer with "n" bits, and can represent the first 2^n natural numbers

-- bitwiseNotUInt8 : (Bool -> Bool -> Bool -> Bool) -> Bool -> Bool -> Bool -> Bool
-- bitwiseNotUInt8 f x y z = ?

-- bitwiseAndUInt8 : (Bool -> Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool -> Bool) -> Bool -> Bool -> Bool -> Bool
-- bitwiseAndUInt8 f g x y z = ?

-- Hint: to define an operation over UInt8, it may help to first define it over UInt1, UInt2, and UInt4.

-- addUInt8 : (Bool -> Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool -> Bool) -> Bool -> Bool -> Bool -> Bool
-- addUInt8 f g x y z = ?

-- multiplyUInt4 : (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool -> Bool)
-- multiplyUInt4 f g x y z = ?

-- How many different `((Bool -> Bool) -> Bool) -> Bool`s are there?

{-

Chapter 2. Natural Numbers

The booleans were defined by the unique ways they can be constructed, namely by the "constructors" `true` and `false`.

The Set of natural numbers are defined by the element `zero`, and the successor function `suc(n)` aka "n + 1":

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

We could even port this into a typical imperative language like:
  interface Nat {};
  class zero extends Nat {};
  class suc extends Nat { Nat n; };
  ...
  Nat three = new suc(n = new suc(n = new suc(n = zero())))

This singly-linked-list representation of the natural numbers is obviously quite bloated and inefficient for most tasks.

However, as we will see soon, it excels at justifying the existence of recursive functions accepting natural numbers.

Just like with the booleans, we can pattern match on natural numbers by handling both of the `zero` and `suc` cases:

-}

-- A "fake" predecessor function, which stops decrementing inputs at zero, since we have not yet defined the integers
pred : Nat -> Nat
pred zero = zero -- pred(0) = 0
pred (suc n) = n -- pred(n + 1) = n

{-

When handling the `suc` case, we are handed the input to which the suc function was applied, namely the input minus one.

We can also nest patterns, e.g. by pattern matching again against the natural number we are handed in the `suc` case:

-}

is-two : Nat -> Bool
is-two (suc (suc zero)) = true
is-two other = false

isGreaterThan-two : Nat -> Bool
isGreaterThan-two (suc (suc (suc n))) = true
isGreaterThan-two other = false

{-

As mentioned previously, we can also define functions recursively:

-}

isEven : Nat -> Bool
isEven zero = true -- zero is even
isEven (suc n) = not (isEven n) -- n+1 is even <=> n is not even

-- Again, a "fake" halving function, which rounds up so we have not yet defined fractions
halfOf : Nat -> Nat
halfOf zero = zero -- 0 / 2 = 0
halfOf (suc zero) = suc zero -- 1 / 2 = 1
halfOf (suc (suc n)) = suc (halfOf n) -- (n + 2) / 2 = 1 + n / 2

{-

The recursive calls are clearly safe since `n` is literally a smaller piece of data than `suc n` or `suc (suc n)`.

If recursive calls only are made on structurally smaller pieces of data, then the function must terminate eventually.

This is in contrast to the following definition, which is not a total function, as it results in a termination error:

-}

-- bad-isEven : Nat -> Bool
-- bad-isEven zero = true
-- bad-isEven n = not (bad-isEven (suc n))

{-

Here, not only is the input parameter not shrinking with each recursive call, it is growing, leading to non-termination.

A function being total, however, is no guarantee that the termination checker will be able to see that it is total.

To keep Agda's termination checking reliable, this structural shrinking needs to be obvious at a syntactical level.

For example, we can't use another function which makes its input smaller, such as `pred`, in place of pattern matching:

-}

-- isEven' : Nat -> Bool
-- isEven' zero = true
-- isEven' n = isEven' (pred n)

{-

Even though the above definition of isEven' is equivalent to the original isEven, Agda cannot see that it terminates.

This may sound like a serious limitation, but in practice it can be worked around with a variety of tricks.

For example, say we want to compute the minimum number of bits required to represent a natural number in binary.

We can do so by observing how often we must halve a number (rounded up) before it reaches 1:
  binLength(0) = 1
  binLength(1) = 1
  binLength(n) = 1 + (binLength(n / 2))

However we cannot halve a number by pattern matching, and Agda cannot see that the following definition terminates:

-}

-- bad-binLength : Nat -> Nat
-- bad-binLength zero = one
-- bad-binLength (suc zero) = one
-- bad-binLength n = suc (bad-binLength (halfOf n))

{-

The simplest way to define this is to use a helper function which recurses over a sufficiently large dummy parameter:

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
isThree n = false

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

-- Exponentiation
-- Typically, 0^0 is left undefined, but for our purposes we can say 0^0 = 1
-- _^_ : Nat -> Nat -> Nat
-- n ^ m = ?

-- Equality
-- _=[Nat]=_ : Nat -> Nat -> Bool
-- n =[Nat]= m = ?

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

-- After correctly filling in and testing the above definitions, comment in the following BUILTIN-pragmas.
-- Note that BUILTIN-pragmas verify your definitions on a best-effort basis and may fail even for a correct definition.
-- {-# BUILTIN NATTIMES _*_ #-}
-- {-# BUILTIN NATMINUS _-_ #-}
-- {-# BUILTIN NATEQUALS _=[Nat]=_ #-}
-- {-# BUILTIN NATLESS _<_ #-}

{-

Tips and Tricks:

Don't be afraid to define your own helper functions, just be sure to name them like "...-helper" to avoid name clashes.

Use "C-c C-f" and "C-c C-b" to jump to the next or previous holes respectively, speeding up your interactive editing.

In emacs, "C-x 2" will split your screen horizontally into two windows, and "C-x 0" will get rid of the current window.

Challenge Exercises:

-}

-- We can think of a `Nat -> A` as an infinite sequence of `A`s.
-- Therefore, we can think of a `Nat -> Nat -> Bool` as an infinite sequence of infinite sequences of booleans.
-- Prove informally that there exists no `Nat -> Nat -> Bool` which enumerates every `Nat -> Bool`.
-- For any `Nat -> Nat -> Bool`, construct a counterexample `Nat -> Bool` which it does not output for any input `Nat`:
-- infinite-sequences-are-enumerable-counterexample : (Nat -> Nat -> Bool) -> Nat -> Bool
-- infinite-sequences-are-enumerable-counterexample f n = ?

-- Similarly, we can think of a `Nat -> Nat -> Nat` as an infinite sequence of infinite sequences of natural numbers.
-- Define a function which flattens such an infinite two-dimensional array into a single infinite sequence.
-- Any number which occurs in the provided infinite array *must* occur eventually in the resulting sequence:
-- flatten-sequence : (Nat -> Nat -> Nat) -> Nat -> Nat
-- flatten-sequence f n = ?

-- Define some variant of the division and modulo operations that pass the termination checker.

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

In Agda, polymorhpic functions are simply functions accepting an input of type Set, which is given a name in its type:

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

The `x` in the definition is entirely independent from (and in fact not even equal to) the `x` in the type signature.

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

The difference between regular and implicit parameters is purely syntactical.

Just as you can opt in to inference with underscore, you can apply implicit parameters explicitly with curly braces:

-}

id-for-Bool'''' : Bool -> Bool
id-for-Bool'''' = id {Bool}

id-for-Nat'''' : Nat -> Nat
id-for-Nat'''' = id {Nat}

id' : {A : Set} -> A -> A
id' {A} = id-for A

{-

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

While polymorphism is incredibly useful, it has some (rightful) limitations.

For one, Sets may be treated as values, but they are not data, and you cannot pattern match on them:

-}

-- bad-id-for : (A : Set) -> A -> A
-- bad-id-for Nat x = suc x
-- bad-id-for Bool x = not x
-- bad-id-for Other x = x

{-

If you comment in the above definition, Agda treats Nat and Bool (and Other) as fresh variable names, not patterns.

These variable names shadow the previously defined Nat and Bool, and are the same as the `A` from the type signature.

Since `suc` and `not` only work on a `Nat` or `Bool` respectively, and not with any arbitrary `A`, we get a type error.

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

One useful application of parametricity is to encode datatypes like Nat and Bool *as* polymorphic function types:

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

Exercises:

When working with type aliases like CBool and CNat, keeping track of the types of input parameters can be tricky.

Luckily, Agda provides us with the hole-command "C-c C-," which displays exactly this contextual information.

Furthermore, if you type an expression into a hole, "C-c C-." displays its inferred type in addition to the context.

We can also prefix either of these commands with "C-u C-u" to force Agda to normalize any type aliases.

For example, if "C-c C-." displays "CBool" then "C-u C-u C-c C-." should display "{X : Set} -> X -> X -> X".

Try these commands out on the following exercises:

-}

-- Define the following polymorphic functions:

-- apply : {A B : Set} -> (A -> B) -> A -> B
-- apply f x = ?

-- k : {A B : Set} -> A -> B -> A
-- k x y = ?

-- s : {A B C : Set} -> (A -> B -> C) -> (A -> B) -> A -> C
-- s x y z = ?

-- owl : {A B : Set} -> ((A -> B) -> A) -> (A -> B) -> B
-- owl f g = ?

-- Define these functions over church encodings without using any regular, non-church-encoded definitions:

-- csuc : CNat -> CNat
-- csuc n f x = ?

-- cand : CBool -> CBool -> CBool
-- cand f g x y = ?

-- cor : CBool -> CBool -> CBool
-- cor f g x y = ?

-- cisEven : CNat -> CBool
-- cisEven f x y = ?

-- Define conversion functions between datatypes and their parametric/church encodings:

-- Bool-to-CBool : Bool -> CBool
-- Bool-to-CBool b x y = ?

-- CBool-to-Bool : CBool -> Bool
-- CBool-to-Bool f = ?

-- Nat-to-CNat : Nat -> CNat
-- Nat-to-CNat n f x = ?

-- CNat-to-Nat : CNat -> Nat
-- CNat-to-Nat f = ?

-- What previously defined functions accomplish exactly the same thing as Bool-to-CBool and Nat-to-CNat?

-- Fill in the missing types:

-- flip : {A B C : Set} -> (A -> ? -> C) -> B -> ? -> C
-- flip f x y = f y x

-- on : {A B C : Set} -> (? -> ? -> ?) -> (A -> B) -> A -> A -> C
-- on op f x y = op (f x) (f y)

-- isOne : Nat -> Bool
-- isOne = compose {?} {?} {?} isTwo suc

-- warbler : ?
-- warbler f x = f x x

-- The church encoding of the natural numbers notably allows us to write the following astonishing definitions:

_c+_ : CNat -> CNat -> CNat
(n c+ m) f x = n f (m f x)

_c*_ : CNat -> CNat -> CNat
(n c* m) f x = n (m f) x

_c^_ : CNat -> CNat -> CNat
(n c^ m) f x = m n f x

-- Take some time to consider why each of these works.
-- Also, 0^0 is normally left undefined, but what does `czero c^ czero` equal?
-- When you think you have the answer, try normalizing the following expression:
-- _ = {! CNat-to-Nat (czero c^ czero)  !}

-- We don't always need to introduce all parameters in order to define a function
-- Instead we can simply provide a function as output which itself awaits more parameters as input:

-- _c^'_ : CNat -> CNat -> CNat
-- n c^' m = m ?

-- _c*'_ : CNat -> CNat -> CNat
-- n c*' m = compose ? ?

-- _c+'_ : CNat -> CNat -> CNat
-- n c+' m = lift ? ? ?

{-

Tips and Tricks:

As previously mentioned, holes can be filled in with solutions containing more holes.

For example, you could start to fill in the following definition by writing `op ? ? ?` and pressing C-c C-Space.

However, you could also just write `op` into it, and hit C-c C-r to "refine" the solution.

-}

-- lift3 : {A B C D E : Set} -> (B -> C -> D -> E) -> (A -> B) -> (A -> C) -> (A -> D) -> A -> E
-- lift3 op f g h x = {! op !}

{-

Challenge Exercises:

-}

-- Find some type for this definition which does not result in an error:
-- apply-to-self : ?
-- apply-to-self f = f f

-- The previously defined `s` and `k` functions, also called "combinators", together are turing complete
-- With enough work, any higher-order function can be written without introducing parameters, purely in terms of s and k
-- Define the following functions using only s and k, without introducing any parameters (aside from type parameters)
-- It may be helpful to define and use helper functions using only s and k, and substitute them in afterwards
-- Note that Agda tries to infer all type parameters, even if they are irrelevant, which can lead to constraint errors
-- You therefore may need to explicitly supply implicit type parameters to get Agda to stop complaining

-- warbler' : {A B : Set} -> (A -> A -> B) -> A -> B
-- warbler' {A} {B} = ?

-- compose' : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
-- compose' {A} {B} {C} = ?

-- owl' : {A B : Set} -> ((A -> B) -> A) -> (A -> B) -> B
-- owl' {A} {B} = ?

{-

Chapter 4. Algebraic Datatypes

When defining types formally as Sets of values, the number of distinct values inhabiting a type becomes very apparent.

This number, which does not always have to be finite, is referred to as the cardinality of a type/set.

Just as Bool has a cardinality of 2, it is easy to define a type with any finite cardinality we desire:

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

A programming language with Algebraic Datatypes simply provides us with a convenient way to do exactly this.

In fact, most languages already make it easy to define products, even if the numeric correspondence is not obvious.

Two types X and Y can be "multiplied" with a "Pair<X, Y>" type, which is just a struct containing both an X and a Y.

In Agda, we can define e.g. the product of Two and Three as follows:

-}

data Six : Set where
  mkSix : Two -> Three -> Six

1/Six : Six
1/Six = mkSix 1/Two 1/Three

2/Six : Six
2/Six = mkSix 1/Two 2/Three

3/Six : Six
3/Six = mkSix 1/Two 3/Three

4/Six : Six
4/Six = mkSix 2/Two 1/Three

5/Six : Six
5/Six = mkSix 2/Two 2/Three

6/Six : Six
6/Six = mkSix 2/Two 3/Three

{-

A pair like this is the cartesian product of its components, whose cardinalities are combined by multiplication.

This is no different from the more typical `struct Six { Two x; Three y; };` we would write in an imperative language.

While not as common in other languages, sums can also be encoded as variant/enum types, aka disjoint unions:

-}

data Five : Set where
  mkFiveFromTwo : Two -> Five
  mkFiveFromThree : Three -> Five

1/Five : Five
1/Five = mkFiveFromTwo 1/Two

2/Five : Five
2/Five = mkFiveFromTwo 2/Two

3/Five : Five
3/Five = mkFiveFromThree 1/Three

4/Five : Five
4/Five = mkFiveFromThree 2/Three

5/Five : Five
5/Five = mkFiveFromThree 3/Three

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
  mkPair : {A B : Set} -> A -> B -> Pair A B

-- 2-ary variant, a "sum" of its two type arguments
data Either : Set -> Set -> Set where
  left : {A B : Set} -> A -> Either A B
  right : {A B : Set} -> B -> Either A B

{-

Observe how Pair and Either are both functions accepting two Sets and returning a Set.

This matches up exactly with how _+_ and _*_ are functions accepting two Nats and returning a Nat.

If x and y are Nats, then `_+_ x y` is a Nat, and likewise if A and B are Sets, then `Either A B` is a Set.

If we wish, we can use these polymorphic types instead of defining a whole new datatype like we did for Five and Six.

We can demonstrate that these two approaches are the same by constructing a bijection using pattern matching:

-}

-- A bijection between the types `Either Two Three` and `Five`

EitherTwoThree-to-Five : Either Two Three -> Five
EitherTwoThree-to-Five (left x) = mkFiveFromTwo x
EitherTwoThree-to-Five (right x) = mkFiveFromThree x

Five-to-EitherTwoThree : Five -> Either Two Three
Five-to-EitherTwoThree (mkFiveFromTwo x) = left x
Five-to-EitherTwoThree (mkFiveFromThree x) = right x

-- A bijection between the types `Pair Two Three` and `Six`

PairTwoThree-to-Six : Pair Two Three -> Six
PairTwoThree-to-Six (mkPair x y) = mkSix x y

Six-to-PairTwoThree : Six -> Pair Two Three
Six-to-PairTwoThree (mkSix x y) = mkPair x y

{-

As we do not yet possess the power of theorem proving, it is up to the reader to verify that these are true bijections.

For product types, we can also define accessor functions, which are often referred to as projections:

-}

fst : {A B : Set} -> Pair A B -> A
fst (mkPair x y) = x

snd : {A B : Set} -> Pair A B -> B
snd (mkPair x y) = y

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

-- A partial predecessor function, which does not wrongly output zero given an input of zero
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

oneToFive : List Nat
oneToFive = cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))) -- that is, `[1, 2, 3, 4, 5]`

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

Notice how Nat, which has an infinite number of elements, embodies the idea that infinity equals infinity plus one.

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

-- Complete the following definitions which demonstrate the algebraic law of commutativity for sums and products

-- a * b = b * a
-- swapPair : {A B : Set} -> Pair A B -> Pair B A
-- swapPair x = ?

-- a + b = b + a
-- swapEither : {A B : Set} -> Either A B -> Either B A
-- swapEither x = ?

-- Complete the following definitions which demonstrate the algebraic law "c^(a * b) = (c^b)^a"

-- curry : {A B C : Set} -> (Pair A B -> C) -> A -> B -> C
-- curry f x y = ?

-- uncurry : {A B C : Set} -> (A -> B -> C) -> Pair A B -> C
-- uncurry f x = ?

-- Complete the following definitions which demonstrate the algebraic law "c^a * c^b = c^(a + b)"

-- either : {A B C : Set} -> Pair (A -> C) (B -> C) -> Either A B -> C
-- either x y = ?

-- uneither : {A B C : Set} -> (Either A B -> C) -> Pair (A -> C) (B -> C)
-- uneither f = ? -- Hint: it may help to use a "where" clause

-- Complete the following definitions which should demonstrate the algebraic law "a * (b + c) = a * b + a * c"

-- distribute : ?
-- distribute = ?

-- undistribute : ?
-- undistribute = ?

-- Define the following functions which use Maybe and List

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

-- Turn a list of pairs into two lists
-- unzip : {A B : Set} -> List (Pair A B) -> Pair (List A) (List B)
-- unzip xs = ?

-- Traditionally, we define multiplication as a repeated addition, and exponentiation as a repeated multiplication.
-- Yet bizarrely, parametric polymorphism lets us to define both addition and multiplication in terms of exponentiation:

CPair : Set -> Set -> Set
CPair A B = {X : Set} -> (A -> B -> X) -> X

CEither : Set -> Set -> Set
CEither A B = {X : Set} -> (A -> X) -> (B -> X) -> X

-- Pair-to-CPair : {A B : Set} -> Pair A B -> CPair A B
-- Pair-to-CPair x f = ?

-- CPair-to-Pair : {A B : Set} -> CPair A B -> Pair A B
-- CPair-to-Pair f = ?

-- Either-to-CEither : {A B : Set} -> Either A B -> CEither A B
-- Either-to-CEither x f g = ?

-- CEither-to-Either : {A B : Set} -> CEither A B -> Either A B
-- CEither-to-Either f = ?

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

-- Pick out some previous exercises and complete them again with their church encoded equivalents

{-

Tips and Tricks:

Right clicking on a hole will list all of Agda's hole-commands, including many which we have not yet covered.

Emacs also has a toolbar by default, and the "Agda" dropdown lists other non-hole commands.

The toolbar can be used to discover most basic emacs functionality and corresponding key combos.

If you enjoy working with key combos to edit and navigate more efficiently, try the emacs tutorial with "C-h t".

Challenges Exercises:

-}

-- Compute all prime numbers up until the provided number
-- primesUntil : Nat -> List Nat
-- primesUntil n = ?

-- Compute a list of all subsequences of the provided list
-- subsequences : {A : Set} -> List A -> List (List A)
-- subsequences xs = ?

-- Sort the given list by the given less-than relation
-- sortBy : {A : Set} -> (A -> A -> Bool) -> List A -> List A
-- sortBy _isLessThan_ xs = ?


{-

Part 2. Constructive Theorem Proving

In classical logic, which is what most people are familiar with from math class, propositions are booleans.

That is, every proposition in classical mathematics is assumed to either have a proof, or not have a proof.

This is reflected by the boolean Law of the Excluded Middle (often called LEM), which says "forall p, p or not p".

LEM lets us prove the existence of functions whose outputs depend on the truth of any arbitrarily complex proposition.

This abstract notion of proof disregards whether such a function can be "constructed" in a turing-complete language.

However, proofs which simply avoid using LEM represent specific functions that serve as evidence of a proposition.

Intuitionistic logic does not have LEM as an axiom, which must instead be explicitly assumed where it is needed.

This results in a strictly more expressive logic, where proofs may have specific meanings and can be treated as values.

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

While it may be obvious that there is no way to fill in this definition, it would be nice to actually disprove Zero.

One way to demonstrate that a proposition is false is by showing that it can be used to prove any other proposition:

-}

-- For any proposition X, absurd takes a proof of Zero as input and returns a proof of X as output
absurd : {X : Set} -> Zero -> X

{-

With a trivially empty type like Zero, we can prove this by pattern matching on "all" zero of its constructor cases:

-}

absurd ()

{-

The `()` is called a refutation pattern, and states that we do not need to give an output as there can be no input.

There is always exactly one function from the empty set to any other set, namely one mapping all zero inputs to outputs.

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

A function in `A -> B` requires a proof of `A` as input and produces a proof of `B` as output.

Therefore, `A -> B` is a nonempty Set when the `A` being a nonempty Set *implies* that `B` is a nonempty Set.

Furthermore, polymorphism over Sets, looked at through this propositional lens, is just universal quantification.

That is to say, for example, that the type of `absurd` quite literally states that "forall x, false implies x".

With the same trick, products and sums as defined previously over types de-generalize to "and"s and "or"s respectively:

-}

-- `n * m is nonzero` if and only if `n is nonzero and m is nonzero`
-- Therefore `Pair N M` is inhabited if and only if `N` is inhabited *and* `M` is inhabited

true-and-true : Pair One One
true-and-true = mkPair 1/One 1/One

false-and-true-is-absurd : {X : Set} -> Pair Zero One -> X
false-and-true-is-absurd (mkPair () x)

true-and-false-is-absurd : {X : Set} -> Pair One Zero -> X
true-and-false-is-absurd (mkPair x ())

false-and-false-is-absurd : {X : Set} -> Pair Zero Zero -> X
false-and-false-is-absurd (mkPair () ())

-- `n + m is nonzero` if and only if `n is nonzero or m is nonzero`
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

False-propositions-imply-each-other : {A B : Set} -> IsFalse A -> IsFalse B -> A -> B
False-propositions-imply-each-other a-is-false _ a = a-is-false a

{-

To disprove an assumption, it therefore suffices to prove any proposition for which we have proven explosion, like Zero:

-}

false-or-false-is-false : Either Zero Zero -> Zero
false-or-false-is-false (left ())
false-or-false-is-false (right ())

{-

Picking a default false proposition to use instead of using the principle of explosion is generally more convenient.

Aside from the type being more concise, this lets us write many disproofs more directly, without refutation patterns:

-}

true-and-false-is-false : Pair One Zero -> Zero
true-and-false-is-false x = snd x

{-

Just as one can define the function `not : Bool -> Bool` as `not x = x => false`, we can define negation over types as:

-}

Not : Set -> Set
Not A = A -> Zero

{-

Disproofs or negations are not only interesting to construct, and can also be useful to have, e.g. as an assumption.

Previously we observed that we cannot always extract an element from an Either, since we must always handle both cases.

However, if have proof that a particular case of an Either is not even possible, then we can refuse to handle it:

-}

getLeftAndRefuteRight : {A B : Set} -> Not B -> Either A B -> A
getLeftAndRefuteRight not-b (left a) = a
getLeftAndRefuteRight not-b (right b) = absurd (not-b b)

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

An attempt to fill this definition quickly makes it clear that we have no basis upon which to compute an answer.

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

LEM-to-DNE : LEM -> DNE
LEM-to-DNE lem {A} not-not-a = h (lem {A})
  where
    h : Either A (Not A) -> A
    h (left a) = a
    h (right not-a) = absurd (not-not-a not-a)

{-

Here, we first invoke LEM with `A` to prove `Either A (Not A)`.

Since DNE assumes `Not (Not A)`, we know that LEM will output `left`, with a proof of A.

If LEM were to output `right` with a proof of `Not A`, then this would contradict our assumption of `Not (Not A)`.

By pattern matching on the output of LEM with `h`, we can extract the proof of A, and refute the possibility of `Not A`.

In fact, the helper function `h` serves the same exact purpose as the previously defined function getLeftAndRefuteRight:

-}

LEM-to-DNE' : LEM -> DNE
LEM-to-DNE' lem {A} not-not-a = getLeftAndRefuteRight not-not-a (lem {A})

{-

Notice how the lack of computational feasibility is cleanly carried over from one classical law to the other.

Exercises:

todo:
  Prove that there is no total function "Either A B -> A" or "A -> Pair A B"
  CZero and COne
  peirces law aka callcc (or maybe save this for later)
  (¬X → X) ≅ ¬¬X
  _<->_

-}

-- What definitions from Chapter 3 can be understood as corresponding to laws of logical implication?
-- How can we interpret the various algebraic laws from Chapter 4 as logical laws?
-- What logical laws involving `Zero` cannot be mapped to corresponding algebraic laws?
-- Why are these laws not problematic alongside our algebraic interpretation of types?


{-

Tips and Tricks:

Don't be afraid to create a throwaway hole to normalize some type aliases

-}

{-

Challenge Exercises:

-}

-- DNE-to-LEM : DNE -> LEM
-- DNE-to-LEM dne {A} = ?

{-

Chapter 6. Dependent Types

-}
