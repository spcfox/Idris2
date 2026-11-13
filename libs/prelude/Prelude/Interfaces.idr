module Prelude.Interfaces

import Builtin
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num

%default total

-------------
-- ALGEBRA --
-------------

||| Sets equipped with a single binary operation that is associative.  Must
||| satisfy the following laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
public export
interface Semigroup (## ty : Type) where
  constructor MkSemigroup
  (<+>) : ty -> ty -> ty

||| Sets equipped with a single binary operation that is associative, along with
||| a neutral element for that binary operation.  Must satisfy the following
||| laws:
|||
||| + Associativity of `<+>`:
|||     forall a b c, a <+> (b <+> c) == (a <+> b) <+> c
||| + Neutral for `<+>`:
|||     forall a, a <+> neutral == a
|||     forall a, neutral <+> a == a
public export
interface Semigroup ty => Monoid (## ty : Type) where
  constructor MkMonoid
  neutral : ty

public export
Semigroup () where
  _ <+> _ = ()

public export
Monoid () where
  neutral = ()

public export
{## a, b : _} -> Semigroup a => Semigroup b => Semigroup (a, b) where
  (x, y) <+> (v, w) = (x <+> v, y <+> w)

public export
{## a, b : _} -> Monoid a => Monoid b => Monoid (a, b) where
  neutral = (neutral, neutral)

public export
Semigroup Ordering where
  LT <+> _ = LT
  GT <+> _ = GT
  EQ <+> o =  o

public export
Monoid Ordering where
  neutral = EQ

public export
{## a, b : _} -> Semigroup b => Semigroup (a -> b) where
  (f <+> g) x = f x <+> g x

public export
{## a, b : _} -> Monoid b => Monoid (a -> b) where
  neutral _ = neutral

---------------------------------------------------------
-- FUNCTOR, BIFUNCTOR, APPLICATIVE, ALTERNATIVE, MONAD --
---------------------------------------------------------

||| Functors allow a uniform action over a parameterised type.
||| @ f a parameterised type
public export
interface Functor (## f : (## _ : Type) -> Type) where
  constructor MkFunctor
  ||| Apply a function across everything of type 'a' in a parameterised type
  ||| @ f the parameterised type
  ||| @ func the function to apply
  map : {## a, b : _} -> (func : a -> b) -> f a -> f b

||| An infix alias for `map`, applying a function across everything of type 'a'
||| in a parameterised type.
||| @ f the parameterised type
||| @ func the function to apply
%inline %tcinline public export
(<$>) : {## f, a, b : _} -> Functor f => (func : a -> b) -> f a -> f b
(<$>) func x = map func x

||| Flipped version of `<$>`, an infix alias for `map`, applying a function across
||| everything of type 'a' in a parameterised type.
||| @ f the parameterised type
||| @ func the function to apply
%inline %tcinline public export
(<&>) : {## f, a, b : _} -> Functor f => f a -> (func : a -> b) -> f b
(<&>) x func = map func x

||| Run something for effects, replacing the return value with a given parameter.
%inline %tcinline public export
(<$) : {## f, a, b : _} -> Functor f => b -> f a -> f b
(<$) b = map (const b)

||| Flipped version of `<$`.
%inline %tcinline public export
($>) : {## f, a, b : _} -> Functor f => f a -> b -> f b
($>) fa b = map (const b) fa

||| Run something for effects, throwing away the return value.
%inline %tcinline public export
ignore : {## f, a : _} -> Functor f => f a -> f ()
ignore = map (const ())

-- TODO: Fix it
-- namespace Functor
--   ||| Composition of functors is a functor.
--   public export
--   [Compose] {## f, g : _} -> (l : Functor f) => (r : Functor g) => Functor (f . g) where
--     map = map . map

||| Bifunctors
||| @f The action of the Bifunctor on pairs of objects
||| A minimal definition includes either `bimap` or both `mapFst` and `mapSnd`.
public export
interface Bifunctor (## f : (## _ : Type) -> (## _ : Type) -> Type) where
  constructor MkBifunctor
  ||| The action of the Bifunctor on pairs of morphisms
  |||
  ||| ````idris example
  ||| bimap (\x => x + 1) reverse (1, "hello") == (2, "olleh")
  ||| ````
  |||
  total
  bimap : {## a, b, c, d : _} -> (a -> c) -> (b -> d) -> f a b -> f c d
  bimap f g = mapFst f . mapSnd g

  ||| The action of the Bifunctor on morphisms pertaining to the first object
  |||
  ||| ````idris example
  ||| mapFst (\x => x + 1) (1, "hello") == (2, "hello")
  ||| ````
  |||
  total
  mapFst : {## a, b, c : _} -> (a -> c) -> f a b -> f c b
  mapFst f = bimap f id

  ||| The action of the Bifunctor on morphisms pertaining to the second object
  |||
  ||| ````idris example
  ||| mapSnd reverse (1, "hello") == (1, "olleh")
  ||| ````
  |||
  total
  mapSnd : {## a, b, d : _} -> (b -> d) -> f a b -> f a d
  mapSnd = bimap id

public export %tcinline
mapHom : {## f, a, b : _} -> Bifunctor f => (a -> b) -> f a a -> f b b
mapHom f = bimap f f

-- TODO: Fix it
-- namespace Bifunctor

--   ||| Composition of a bifunctor and a functor is a bifunctor.
--   public export %inline
--   [Compose] {## f, g : _} -> (l : Functor f) => (r : Bifunctor g) => Bifunctor (f .: g) where
--     bimap = map .: bimap
--     mapFst = map . mapFst
--     mapSnd = map . mapSnd

public export
interface Functor f => Applicative (## f : (## _ : Type) -> Type) where
  constructor MkApplicative
  pure : {## a : _} -> a -> f a
  (<*>) :  {## a, b : _} -> f (a -> b) -> f a -> f b

public export %tcinline
(<*) : {## f, a, b : _} -> Applicative f => f a -> f b -> f a
a <* b = map const a <*> b

public export %tcinline
(*>) : {## f, a, b : _} -> Applicative f => f a -> f b -> f b
a *> b = map (const id) a <*> b

%allow_overloads pure
%allow_overloads (<*)
%allow_overloads (*>)

-- namespace Applicative
--   ||| Composition of applicative functors is an applicative functor.
--   public export
--   [Compose] {## f, g : _} -> (l : Applicative f) => (r : Applicative g) => Applicative (f . g)
--     using Functor.Compose where
--       pure = pure . pure
--       fun <*> x = [| fun <*> x |]

||| An alternative functor has a notion of disjunction.
||| @f is the underlying applicative functor
||| We expect (f a, empty, (<|>)) to be a type family of monoids.
public export
interface Applicative f => Alternative (## f : (## _ : Type) -> Type) where
  constructor MkAlternative
  empty : {## a : _} -> f a
  (<|>) : {## a : _} -> f a -> Lazy (f a) -> f a

||| Monad
||| @m The underlying functor
||| A minimal definition includes either `(>>=)` or `join`.
public export
interface Applicative m => Monad (## m : (## _ : Type) -> Type) where
  constructor MkMonad
  ||| Also called `bind`.
  total
  (>>=) : {## a, b : _} -> m a -> (a -> m b) -> m b

  ||| Also called `flatten` or mu.
  total
  join : {## a : _} -> m (m a) -> m a

  -- default implementations
  (>>=) x f = join (f <$> x)
  join x = x >>= id

%allow_overloads (>>=)

||| Right-to-left monadic bind, flipped version of `>>=`.
%inline %tcinline public export
(=<<) : {## m, a, b : _} -> Monad m => (a -> m b) -> m a -> m b
(=<<) = flip (>>=)

||| Sequencing of effectful composition
%inline %tcinline public export
(>>) : {## m, a, b : _} -> Monad m => m () -> Lazy (m b) -> m b
a >> b = a >>= \_ => b

||| Left-to-right Kleisli composition of monads.
public export %tcinline
(>=>) : {## m, a, b, c : _} -> Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g = \x => f x >>= g

||| Right-to-left Kleisli composition of monads, flipped version of `>=>`.
public export %tcinline
(<=<) : {## m, a, b, c : _} -> Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

||| `guard a` is `pure ()` if `a` is `True` and `empty` if `a` is `False`.
public export
guard : {## f : _} -> Alternative f => Bool -> f ()
guard x = if x then pure () else empty

||| Conditionally execute an applicative expression when the boolean is true.
public export
when : {## f : _} -> Applicative f => Bool -> Lazy (f ()) -> f ()
when True f = f
when False f = pure ()

||| Execute an applicative expression unless the boolean is true.
%inline %tcinline public export
unless : {## f : _} -> Applicative f => Bool -> Lazy (f ()) -> f ()
unless = when . not

---------------------------
-- FOLDABLE, TRAVERSABLE --
---------------------------

||| The `Foldable` interface describes how you can iterate over the elements in
||| a parameterised type and combine the elements together, using a provided
||| function, into a single result.
||| @ t The type of the 'Foldable' parameterised type.
||| A minimal definition includes `foldr`
public export
interface Foldable (## t : (## _ : Type) -> Type) where
  constructor MkFoldable
  ||| Successively combine the elements in a parameterised type using the
  ||| provided function, starting with the element that is in the final position
  ||| i.e. the right-most position.
  ||| @ func  The function used to 'fold' an element into the accumulated result
  ||| @ init  The starting value the results are being combined into
  ||| @ input The parameterised type
  foldr : {## elem, acc : _} -> (func : elem -> acc -> acc) -> (init : acc) -> (input : t elem) -> acc

  ||| The same as `foldr` but begins the folding from the element at the initial
  ||| position in the data structure i.e. the left-most position.
  ||| @ func  The function used to 'fold' an element into the accumulated result
  ||| @ init  The starting value the results are being combined into
  ||| @ input The parameterised type
  foldl : {## acc, elem : _} -> (func : acc -> elem -> acc) -> (init : acc) -> (input : t elem) -> acc
  foldl f z t = foldr (flip (.) . flip f) id t z

  ||| Test whether the structure is empty.
  ||| @ acc The accumulator value which is specified to be lazy
  null : {## elem : _} -> t elem -> Bool
  null xs = foldr {acc = Lazy Bool} (\ _,_ => False) True xs

  ||| Similar to `foldl`, but uses a function wrapping its result in a `Monad`.
  ||| Consequently, the final value is wrapped in the same `Monad`.
  foldlM : {## m, elem, acc : _} -> Monad m => (funcM : acc -> elem -> m acc) -> (init : acc) -> (input : t elem) -> m acc
  foldlM fm a0 = foldl (\ma, b => ma >>= flip fm b) (pure a0)

  ||| Produce a list of the elements contained in the parametrised type.
  toList : {## elem : _} -> t elem -> List elem
  toList = foldr (::) []

  ||| Maps each element to a value and combine them.
  ||| For performance reasons, this should wherever
  ||| be implemented with tail recursion.
  ||| @ f The function to apply to each element.
  foldMap : {## a, m : _} -> Monoid m => (f : a -> m) -> t a -> m
  foldMap f = foldr ((<+>) . f) neutral

||| Combine each element of a structure into a monoid.
%inline %tcinline public export
concat : {## a, t : _} -> Monoid a => Foldable t => t a -> a
concat = foldMap id

||| Combine into a monoid the collective results of applying a function to each
||| element of a structure.
%inline %tcinline public export
concatMap : {## a, m, t : _} -> Monoid m => Foldable t => (a -> m) -> t a -> m
concatMap = foldMap

namespace Bool.Lazy
  namespace Semigroup
    public export
    [Any] Semigroup (Lazy Bool) where
      x <+> y = force x || y

    public export
    [All] Semigroup (Lazy Bool) where
      x <+> y = force x && y

  namespace Monoid
    public export
    [Any] Monoid (Lazy Bool) using Semigroup.Any where
      neutral = delay False

    public export
    [All] Monoid (Lazy Bool) using Semigroup.All where
      neutral = delay True

||| The conjunction of all elements of a structure containing lazy boolean
||| values.  `and` short-circuits from left to right, evaluating until either an
||| element is `False` or no elements remain.
public export %tcinline
and : {## t : _} -> Foldable t => t (Lazy Bool) -> Bool
and = force . concat @{All}

||| The disjunction of all elements of a structure containing lazy boolean
||| values.  `or` short-circuits from left to right, evaluating either until an
||| element is `True` or no elements remain.
public export %tcinline
or : {## t : _} -> Foldable t => t (Lazy Bool) -> Bool
or = force . concat @{Any}

namespace Bool
  namespace Semigroup
    public export
    [Any] Semigroup Bool where
      x <+> y = x || delay y

    public export
    [All] Semigroup Bool where
      x <+> y = x && delay y

  namespace Monoid
    public export
    [Any] Monoid Bool using Bool.Semigroup.Any where
      neutral = False

    public export
    [All] Monoid Bool using Bool.Semigroup.All where
      neutral = True

||| The disjunction of the collective results of applying a predicate to all
||| elements of a structure.  `any` short-circuits from left to right.
%inline %tcinline public export
any : {## t, a : _} -> Foldable t => (a -> Bool) -> t a -> Bool
any = foldMap @{%search} @{Any}

||| The conjunction of the collective results of applying a predicate to all
||| elements of a structure.  `all` short-circuits from left to right.
%inline %tcinline public export
all : {## t, a : _} -> Foldable t => (a -> Bool) -> t a -> Bool
all = foldMap @{%search} @{All}

namespace Num
  namespace Semigroup
    public export
    [Additive] {## a : _} -> Num a => Semigroup a where
      (<+>) = (+)

    public export
    [Multiplicative] {## a : _} -> Num a => Semigroup a where
      (<+>) = (*)

  namespace Monoid
    public export
    [Additive] {## a : _} -> Num a => Monoid a using Semigroup.Additive where
      neutral = 0

    public export
    [Multiplicative] {## a : _} -> Num a => Monoid a using Semigroup.Multiplicative where
      neutral = 1

||| Add together all the elements of a structure.
public export %tcinline
sum : {## t, a : _} -> Num a => Foldable t => t a -> a
sum = concat @{Additive}

||| Add together all the elements of a structure.
||| Same as `sum` but tail recursive.
export %tcinline
sum' : {## t, a : _} -> Num a => Foldable t => t a -> a
sum' = sum

||| Multiply together all elements of a structure.
public export %tcinline
product : {## t, a : _} -> Num a => Foldable t => t a -> a
product = concat @{Multiplicative}

||| Multiply together all elements of a structure.
||| Same as `product` but tail recursive.
export %tcinline
product' : {## t, a : _} -> Num a => Foldable t => t a -> a
product' = product

||| Map each element of a structure to a computation, evaluate those
||| computations and discard the results.
public export %tcinline
traverse_ : {## f, t, a, b : _} -> Applicative f => Foldable t => (a -> f b) -> t a -> f ()
traverse_ f = foldr ((*>) . f) (pure ())

||| Evaluate each computation in a structure and discard the results.
public export %tcinline
sequence_ : {## f, t, a : _} -> Applicative f => Foldable t => t (f a) -> f ()
sequence_ = foldr (*>) (pure ())

||| Like `traverse_` but with the arguments flipped.
public export %tcinline
for_ : {## f, t, a, b : _} -> Applicative f => Foldable t => t a -> (a -> f b) -> f ()
for_ = flip traverse_

public export
[SemigroupApplicative] {## f, a : _} -> Applicative f => Semigroup a => Semigroup (f a) where
  x <+> y = [| x <+> y |]

public export
[MonoidApplicative] {## f, a : _} -> Applicative f => Monoid a => Monoid (f a) using SemigroupApplicative where
  neutral = pure neutral

namespace Lazy
  public export
  [SemigroupAlternative] {## f, a : _} -> Alternative f => Semigroup (Lazy (f a)) where
    x <+> y = force x <|> y

  public export
  [MonoidAlternative] {## f, a : _} -> Alternative f => Monoid (Lazy (f a)) using Lazy.SemigroupAlternative where
    neutral = delay empty

public export
[SemigroupAlternative] {## f, a : _} -> Alternative f => Semigroup (f a) where
  x <+> y = x <|> delay y

public export
[MonoidAlternative] {## f, a : _} -> Alternative f => Monoid (f a) using Interfaces.SemigroupAlternative where
  neutral = empty

||| Fold using Alternative.
|||
||| If you have a left-biased alternative operator `<|>`, then `choice` performs
||| left-biased choice from a list of alternatives, which means that it
||| evaluates to the left-most non-`empty` alternative.
|||
||| If the list is empty, or all values in it are `empty`, then it evaluates to
||| `empty`.
|||
||| Example:
|||
||| ```
||| -- given a parser expression like:
||| expr = literal <|> keyword <|> funcall
|||
||| -- choice lets you write this as:
||| expr = choice [literal, keyword, funcall]
||| ```
|||
||| Note: In Haskell, `choice` is called `asum`.
%inline %tcinline public export
choice : {## f, t, a : _} -> Alternative f => Foldable t => t (Lazy (f a)) -> f a
choice = force . concat @{Lazy.MonoidAlternative}

||| A fused version of `choice` and `map`.
%inline %tcinline public export
choiceMap : {## f, t, a : _} -> Alternative f => Foldable t => (a -> f b) -> t a -> f b
choiceMap = foldMap @{%search} @{MonoidAlternative}

-- TODO: Fix it
-- namespace Foldable
--   ||| Composition of foldables is foldable.
--   public export %tcinline
--   [Compose] {## t, f : _} -> (l : Foldable t) => (r : Foldable f) => Foldable (t . f) where
--     foldr = foldr . flip . foldr
--     foldl = foldl . foldl
--     null tf = null tf || all null tf
--     foldMap = foldMap . foldMap

||| `Bifoldable` identifies foldable structures with two different varieties
||| of elements (as opposed to `Foldable`, which has one variety of element).
||| Common examples are `Either` and `Pair`.
||| A minimal definition includes `bifoldr`
public export
interface Bifoldable (## p : (## _ : Type) -> (## _ : Type) -> Type) where
  constructor MkBifoldable
  bifoldr : {## a, b, acc : _} -> (a -> acc -> acc) -> (b -> acc -> acc) -> acc -> p a b -> acc

  bifoldl :  {## a, b, acc : _} -> (acc -> a -> acc) -> (acc -> b -> acc) -> acc -> p a b -> acc
  bifoldl f g z t = bifoldr (flip (.) . flip f) (flip (.) . flip g) id t z

  binull : {## a, b: _} -> p a b -> Bool
  binull t = bifoldr {acc = Lazy Bool} (\ _,_ => False) (\ _,_ => False) True t

||| Analogous to `foldMap` but for `Bifoldable` structures
public export %tcinline
bifoldMap : {## acc, p, a, b : _} -> Monoid acc => Bifoldable p => (a -> acc) -> (b -> acc) -> p a b -> acc
bifoldMap f g = bifoldr ((<+>) . f) ((<+>) . g) neutral

||| Like Bifunctor's `mapFst` but for `Bifoldable` structures
public export %tcinline
bifoldMapFst : {## acc, p, a, b : _} -> Monoid acc => Bifoldable p => (a -> acc) -> p a b -> acc
bifoldMapFst f = bifoldMap f (const neutral)

-- TODO: Fix it
-- namespace Bifoldable

--   ||| Composition of a bifoldable and a foldable is bifoldable.
--   public export %tcinline
--   [Compose] {## f, p : _} -> (l : Foldable f) => (r : Bifoldable p) => Bifoldable (f .: p) where
--     bifoldr = foldr .: flip .: bifoldr
--     bifoldl = foldl .: bifoldl
--     binull fp = null fp || all binull fp

public export
interface (Functor t, Foldable t) => Traversable (## t : (## _ : Type) -> Type) where
  constructor MkTraversable
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  traverse : {## f, a, b : _} -> Applicative f => (a -> f b) -> t a -> f (t b)

||| Evaluate each computation in a structure and collect the results.
public export %tcinline
sequence : {## f, t, a : _} -> Applicative f => Traversable t => t (f a) -> f (t a)
sequence = traverse id

||| Like `traverse` but with the arguments flipped.
%inline %tcinline public export
for : {## f, t, a, b : _} -> Applicative f => Traversable t => t a -> (a -> f b) -> f (t b)
for = flip traverse

public export
interface (Bifunctor p, Bifoldable p) => Bitraversable (## p : (## _ : Type) -> (## _ : Type) -> Type) where
  constructor MkBitraversable
  ||| Map each element of a structure to a computation, evaluate those
  ||| computations and combine the results.
  bitraverse : {## f, a, b, c, d : _} -> Applicative f => (a -> f c) -> (b -> f d) -> p a b -> f (p c d)

||| Evaluate each computation in a structure and collect the results.
public export %tcinline
bisequence : {## f, p, a, b : _} -> Applicative f => Bitraversable p => p (f a) (f b) -> f (p a b)
bisequence = bitraverse id id

||| Like `bitraverse` but with the arguments flipped.
public export %tcinline
bifor :  {## f, p, a, b, c, d : _}
      -> Applicative f => Bitraversable p
      => p a b
      -> (a -> f c)
      -> (b -> f d)
      -> f (p c d)
bifor t f g = bitraverse f g t

-- TODO: fix it
-- namespace Traversable
--   ||| Composition of traversables is traversable.
--   public export %tcinline
--   [Compose] {## t, f : _} -> (l : Traversable t) => (r : Traversable f) => Traversable (t . f)
--     using Foldable.Compose Functor.Compose where
--       traverse = traverse . traverse

-- TODO: fix it
-- namespace Bitraversable
--   ||| Composition of a bitraversable and a traversable is bitraversable.
--   public export %tcinline
--   [Compose] {## t, p : _} -> (l : Traversable t) => (r : Bitraversable p) => Bitraversable (t .: p)
--     using Bifoldable.Compose Bifunctor.Compose where
--       bitraverse = traverse .: bitraverse

-- TODO: fix it
-- namespace Monad
--   ||| Composition of a traversable monad and a monad is a monad.
--   public export %tcinline
--   [Compose] {## m, t : _} -> (l : Monad m) => (r : Monad t) => (tr : Traversable t) => Monad (m . t)
--     using Applicative.Compose where
--       a >>= f = a >>= map join . traverse f
