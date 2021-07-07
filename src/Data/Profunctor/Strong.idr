module Data.Profunctor.Strong

import Control.Category
import Data.Profunctor.Interface

infixr 3 ***, &&&

||| The `Strong` interface extends `Profunctor` with combinators for working with
||| product types.
|||
||| `first` and `second` lift values in a `Profunctor` to act on the first and
||| second components of a `Pair`, respectively.
|||
||| If we specialize the profunctor p to the function arrow, we get the following type
||| signatures, which may look a bit more familiar:
|||
||| ```
||| first :  (input -> output) -> (input, a) -> (output, a)
||| second : (input -> output) -> (a, input) -> (a, output)
||| ```
||| So, when the `profunctor` is `Function` application (represented by `Morphism`),
||| `first` essentially applies your function
||| to the first element of a `Tuple`, and `second` applies it to
||| the second element (same as `map` would do).
public export
interface Profunctor p => Strong p where
  first  : p a b -> p (a,c) (b,c)
  second : p a b -> p (c,a) (c,b)

||| Compose a value acting on a `Pair` from two values, each acting on one of
||| the components of the `Pair`.
|||
||| Specializing `(***)` to function application would look like this:
||| ```
||| (***) : (a -> b) -> (c -> d) -> (a, c) -> (b, d)
||| ```
||| We take two functions, `f` and `g`, and we transform
||| them into a single function which
||| takes a `Pair` and maps `f` over the first element
||| and `g` over the second.
public export
(***) : Category p => Strong p => p a b -> p c d -> p (a, c) (b, d)
l *** r = first l . second r

||| Compose a value which introduces a `Pair` from two values,
||| each introducing one side of the `Pair`.
|||
||| This combinator is useful when assembling values from smaller components,
||| because it provides a way to support two different types of output.
|||
||| Specializing `(&&&)` to function application would look like this:
||| ```
||| (&&&) : (a -> b) -> (a -> c) -> (a -> (b, c))
||| ```
||| We take two functions, `f` and `g`, with the same parameter
||| type and we transform them into a
||| single function which takes one parameter and
||| returns a `Pair` of the results of running
||| `f` and `g` on the parameter, respectively.
||| This allows us to run two parallel computations
||| on the same input and return both results in a `Pair`.
public export
(&&&) : Category p => Strong p => p a b -> p a c -> p a (b, c)
l &&& r = clmap dup (l *** r)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Strong Morphism where
  first  (Mor f) = Mor $ mapFst f
  second (Mor f) = Mor $ mapSnd f

public export
Functor m => Strong (Kleislimorphism m) where
  first  (Kleisli f) = Kleisli \(a,c) => (,c) <$> f a
  second (Kleisli f) = Kleisli \(c,a) => (c,) <$> f a

public export
Strong (Forget r) where
  first  (MkForget f) = MkForget \(a,_) => f a
  second (MkForget f) = MkForget \(_,a) => f a
