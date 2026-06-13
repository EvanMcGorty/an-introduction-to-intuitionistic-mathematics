{-# OPTIONS --type-in-type #-}

module AnIntroductionToIntuitionisticMathematics where

{-

Intuitionistic Logic is a particular kind of constructive logic in which terminating programs and computable functions are interpreted as proofs of their types, which are interpreted as propositions.

With enough work, intuitionistic logic can be used to formalize more or less any arbitrary mathematics in the form of typed programs which can be formally verified mechanically by running a type-checker.

This introduction uses an intuitionistic proof assistant and functional programming language called Agda.

If you wish to fill in the exercises, you will need to install `agda` and `emacs`, and run `agda --emacs-mode setup`.

Then, open this file in emacs and hit "C-c C-l", which in emacs means the key combo "Ctrl-c Ctrl-l", to load the file into Agda and provide syntax coloring in Agda code in this file.

Use an alternative text editor at your own discretion as the key combinations tend to vary and the integration likely will not be as good as in emacs, which Agda's interactive editing is designed around.

Index:
Part 1. Pure Functional Programming
  Chapter 1. Booleans
  Chapter 2. Natural Numbers
  Chapter 3. Parametric Polymorphism
  Chapter 4. Algebraic Datatypes
  Chapter 5. Typeclasses
Part 2. Constructive Theorem Proving
  Chapter 6. Propositions
  Chapter 7. Dependent types
  Chapter 8. Induction
  Chapter 9. Generalized Algebraic Datatypes
  Chapter 10. Equality
Part ?
  Classical Logic
  The Axiom of Choice
  Function Extensionality
  Markovs principle
  Anti-Classical Logic
  Girards paradox
  Equivalence Relations
  Well Founded Recursion
  Category Theory

Before we begin, let us note that we will be using the option "--type-in-type" which makes Agda logically inconsistent, meaning that we can technically prove anything, and in return eliminates a form of beaurocracy known as "universe levels" which are an absolute pain in the ass to work with.

However, this technical inconsistency (known as Girards paradox) is quite hard to take advantage of intentionally, let alone accidentally, making it an appropriate sacrifice for introductory content.

-}


{-

Part 1. Pure Functional Programming

Pure Functional Programming involves programming with functions that do not mutate shared state or have side effects.

This lets use equational reasoning to prove properties about our programs, without having to keep track of shared state.

In Agda, not only are functions always pure, they also are always total, i.e. they always terminate for all valid inputs.

in Part 2, this foundation will allow us to write proofs about our Agda code, *in Agda*.

Chapter 1. Booleans

The booleans are a `Set` containing two elements, `true`, and `false`, and in Agda this can be defined as follows:

-}

data Bool : Set where
  false : Bool
  true : Bool

{-

We can now declare functions between booleans, such as the negation function:

-}

not : Bool -> Bool

{-

This is called a type signature and states that `not` is a function which takes a boolean as input and returns a boolean as output, but we also must define it:

-}

not false = true
not true = false

{-

Agda leaves out the parentheses typically used in math and other programming languages, where we might rather have written `not(false) = true` and `not(true) = false`.

If wish to have a function accepting multiple inputs, we use "Currying", meaning we accept just one parameter, and return yet another function accepting any remaining parameters.

So instead of the typical function type `(A, B) -> C`, we rather use `A -> (B -> C)`, which can equivalently just be written as `A -> B -> C`.

This also means that instead of applying such a function like `f(a, b)`, we instead apply it like `(f(a))(b)`, which in Agda is simply written as `f a b`:

-}

and : Bool -> Bool -> Bool
and false false = false
and false true = true
and true false = true
and true true = true

{-

The above definitions use pattern matching to assign an output to each possible set inputs, but we can also define functions using variable parameters which match all possible inputs:

-}

or : Bool -> Bool -> Bool
or true x = true
or false x = x

{-

It is worth noting that cases of a definition may overlap and are not necessarily absolute equalities, as each case is tried in order, from top to bottom:

-}

xor : Bool -> Bool -> Bool
xor true true = false
xor true false = true
xor false true = true
xor false x = false

{-

The last case gives the impression that `xor false x` is always equal to `false`, for any `x`, but in reality this equality only holds if none of the previous cases match the inputs, which is even indicated by Agda's syntax coloring.

Naturally, we may also define functions in terms of other functions:

-}

implies : Bool -> Bool -> Bool
implies l r = or (not l) r -- (l ⇒ r) = (¬l ∨ r)

{-

The above `--` marks the beginning of a single-line comment in Agda (as opposed to the multiline comments containing most explanations in this file).

It can be useful to comment out code which we don't want Agda to load, e.g. because it has an error:

-}

-- Bad-xor : Bool -> Bool -> Bool
-- Bad-xor false x = x

{-

Lines of code can be easily commented out or back in by selecting them and entering "M-;", which in emacs means hitting semicolon while holding Alt (or Option on MacOS)

If you try uncommenting this definition of `Bad-xor`, Agda will complain that it is not an exhaustive definition, since it does not define what `Bad-xor` true false` or `Bad-xor` true true` should be equal to.

In a typical programming language, this might simply result in a runtime crash, but Agda requires all definitions to be mathematically pure, total functions which always construct a valid output for any set of valid inputs.

Agda also supports so-called "mixfix" syntax for function application, whereby underscores in an identifier are placeholders for where their parameters belong syntactically:

-}

_&&_ : Bool -> Bool -> Bool
l && r = and l r

{-

This defines a synonym for `and` called `_&&_`, where `l && r` is syntactic sugar for `_&&_ l r`.

We could have just as well written "_&&_ l r = and l r".

One other cool thing we can do in Agda is pass functions as inputs to functions:

-}

alwaysReturnsTrue : (Bool -> Bool) -> Bool
alwaysReturnsTrue f = f false && f true

{-

Exercises:

If you uncomment the following definitions and reload the file into Agda with C-c C-l, the question marks should turn into "holes" which look like {! !} and represent a missing part of a program.

After writing something in a hole and making sure your cursor is inside of it, you can hit C-c C-Space to interactively fill in the hole if what you wrote is well formed typed correctly, and report an error otherwise.

Beware: if you make any changes outside of a hole, then Agda and its interactive editing commands (such as C-c C-Space) will be unaware of these changes until you reload the file with C-c C-l.

-}

-- A synonym for `or`
-- _||_ : Bool -> Bool -> Bool
-- x || y = ?

-- A synonym for `implies`, but missing a definition
-- _=>_ Bool -> Bool -> Bool

-- A synonym for `xor`, but missing a type signature
-- x ^^ y = ?

-- Define boolean equality, aka biimplication, as the symbol _<=>_

-- Returns true if the provided function returns false regardless of the input
-- alwaysReturnsFalse : (Bool -> Bool) -> Bool
-- alwaysReturnsFalse f = ?

{-

Tips and Tricks:

To test your code, you can normalize an expression within a hole by entering the key combo C-c C-n.

To create a throw-away hole for such purposes you can use an anonymous, unnamed definition like "_ = ?".

Try uncommenting the following line, placing your cursor in the hole, and normalizing the contained expression:

-}

-- _ = {! true && false !}

{-

Make sure to delete or comment out any holes you don't plan on filling in as they will clutter the informational window.

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
-- compareBoolToBool : (Bool -> Bool) -> (Bool -> Bool) -> Bool
-- compareBoolToBool f g = ?

-- An increment function which wraps around from fourth to first
-- nextBoolToBool : (Bool -> Bool) -> Bool -> Bool
-- nextBoolToBool f = ?

{-

Chapter 2. Natural Numbers

The natural numbers are a Set containing the element `zero`, and for any natural number `n`, a successor natural number (i.e. n + 1).

-}

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-

In a typical programming language, this would be like defining the natural numbers as an interface with two classes extending it:
  interface Nat {};
  class zero extends Nat {};
  class succ extends Nat { Nat n; };

To write the number n, we simply apply the successor function to zero n times:

-}

one : Nat
one = succ (zero)

two : Nat
two = succ (succ zero)

three : Nat
three = succ (succ (succ zero))

{-

This singly-linked-list representation of the natural numbers is obviously not very efficient or compact, but it excels at justifying the termination of recursive pattern-matching functions over natural numbers:

-}

isEven : Nat -> Bool
isEven zero = true -- zero is not an even number
isEven (succ n) = not (isEven n) -- n+1 is even <=> n is not even

{-

When we handle the successor case, we are handed the predecessor of the provided natural number.

Because it is syntactically clear that `n` is literally a smaller piece of data than `(succ n)`, the recursive call to isEven is safe.

This is in contrast to the following definition, which is not a total function, and results in a termination error:

-}

-- Bad-isEven : Nat -> Bool
-- Bad-isEven zero = true
-- Bad-isEven n = Bad-isEven (succ n)

{-

Even total, terminating functions can result in such an error if it is not syntactically obvious that recursive calls are only made with smaller inputs:

-}

pred : Nat -> Nat
pred zero = zero
pred (succ n) = n

-- isEven' : Nat -> Bool
-- isEven' zero = true
-- isEven' n = isEven' (pred n)

{-

isEven' has the exact same behavior as isEven, but Agda does not automatically perform the necessary case analysis to see that `pred n` produces a smaller value than `n`.

Nonetheless, so called "structural recursion" is more than enough to define any computable function.

-}

_+_ : Nat -> Nat -> Nat
zero + m = m
succ n + m = succ (n + m)

{-

Also, note that we can nest patterns:

-}

isTwo : Nat -> Bool
isTwo (succ (succ zero)) = true
isTwo other = false

isGreaterThanTwo : Nat -> Bool
isGreaterThanTwo (succ (succ (succ n))) = true
isGreaterThanTwo other = false

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
-- compareNat : Nat -> Nat -> Bool
-- compareNat n m = ?

-- Less-than
-- _<_ : Nat -> Nat -> Bool
-- n < m = ?

-- Minimum
-- _min_ : Nat -> Nat -> Nat
-- n min m = ?

-- Maximum
-- _max_ : Nat -> Nat -> Nat
-- n max m = ?

-- Define the factorial function

-- Sums up the first n outputs of the given function f
-- prefixSum : (Nat -> Nat) -> Nat -> Nat
-- prefixSum f n = ?

{-

Tips and Tricks:

Use C-c C-f and C-c C-b can to jump to the next and previous holes respectively, speeding up your interactive editing.

Challenge Exercises:

-}

-- We can think of a `Nat -> A` as an infinite sequence of `A`s.
-- Therefore, we can think of a `Nat -> Nat -> Bool` as an infinite sequence of infinite binary sequences.
-- Prove informally that there exists no `Nat -> Nat -> Bool` which enumerates every `Nat -> Bool`.
-- Define a function which produces a counterexample `Nat -> Bool` that a given `Nat -> Nat -> Bool` does not output for any input:
-- infinite-sequences-are-enumerable-counterexample : (Nat -> Nat -> Bool) -> Nat -> Bool
-- infinite-sequences-are-enumerable-counterexample f n = ?

-- Try defining some variant of the division and modulo operations that passes the termination checker.
-- Beware: this is a lot harder than it sounds.

{-

Chapter 3. Parametric Polymorphism

So far we have worked with a number of Sets, such as Nat, Bool, as well as many function-Sets.

Some functions, however, work with any Set, as is the case with the identity function:

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
idForBool' = idFor Bool

idForNat' : Nat -> Nat
idForNat' = idFor Nat

{-

In most languages, type parameters are special, whereas in Agda, they are just regular parameters.

In fact, you can name any parameter in a type like we named the Set parameter `A`, it just wouldn't accomplish anything:

-}

not' : (x : Bool) -> Bool
not' = not

{-

Naming `x` in the type signature doesn't accomplish anything, since we only use it in the definition.

On the other hand, `A` was only useful to name in the type signature of `idFor`, and didn't get used in the definition.

Not only was this Set parameter not useful at the definition, but it could have been inferred at the call site.

We can write an underscore to ask Agdas constraint solver to fill in the gap:

-}

idForBool'' : Bool -> Bool
idForBool'' = idFor _

idForNat'' : Nat -> Nat
idForNat'' = idFor _

{-

Similarly, we can use an underscore when introducing a variable to make it immediately clear that we don't need it:

-}

idFor' : (A : Set) -> A -> A
idFor' _ x = x

{-

However, in simple cases like this, Agda will almost always be able to infer the correct type.

For this reason, Agda has a special syntax for implicit parameters, which are hidden and inferred by default:

-}


id : {A : Set} -> A -> A
id x = x

idForBool''' : Bool -> Bool
idForBool''' = id

idForNat''' : Nat -> Nat
idForNat''' = id

{-

The difference between regular and implicit parameters is purely syntactical.

Just as you can opt in to inference with underscore, you can also explicitly specify the type in curly braces:

-}

idForBool'''' : Bool -> Bool
idForBool'''' = id {Bool}

idForNat'''' : Nat -> Nat
idForNat'''' = id {Nat}

{-

One thing worth noting about Sets is that they are not data, and you cannot pattern match on them:

-}

-- Bad-idFor : (A : Set) -> A -> A
-- Bad-idFor Nat x = succ x
-- Bad-idFor Bool x = not x
-- Bad-idFor Other x = x

{-

If you comment in the above definition, Agda treats Nat and Bool (and Other) as fresh variable names, not patterns.

These variable names shadow the previously defined Nat and Bool, and are the same as the `A` from the type signature.

Since `succ` and `not` only work on a Nat or Bool respectively, and not with any arbitrary Set, you get a type error.

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

One useful application of this is to encode datatypes like Nat and Bool *as* parametrically polymorphic functions:

-}

-- A type alias, to avoid repeatedly writing out the somewhat long-winded type `{A : Set} → A → A → A`
BoolChurch : Set
BoolChurch = {A : Set} → A → A → A

falseChurch : BoolChurch
falseChurch x y = x

trueChurch : BoolChurch
trueChurch x y = y

notChurch : BoolChurch -> BoolChurch
notChurch f x y = f y x

{-

There are really only two ways to produce an `A` given two `A`s, if you know nothing more about `A`.

This is called a church encoding, after Alonzo Church, and it is also possible to church encode the natural numbers:

-}

NatChurch : Set
NatChurch = {A : Set} → (A → A) → A → A

zeroChurch : NatChurch
zeroChurch f x = x

oneChurch : NatChurch
oneChurch f x = f x

twoChurch : NatChurch
twoChurch f x = f (f x)

threeChurch : NatChurch
threeChurch f x = f (f (f x))

{-

Exercises:

-}
