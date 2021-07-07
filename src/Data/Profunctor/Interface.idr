module Data.Profunctor.Interface

import Control.Category
import public Control.Applicative.Const
import public Control.Monad.Identity
import public Data.Morphisms

--------------------------------------------------------------------------------
--          Forget
--------------------------------------------------------------------------------

public export
record Forget (r : Type) (a : Type) (b : Type) where
  constructor MkForget
  fun : a -> Maybe r

public export
Functor (Forget r a) where
  map _ (MkForget fun) = MkForget fun

--------------------------------------------------------------------------------
--          Profunctor
--------------------------------------------------------------------------------

||| A `Profunctor` is a `Functor` from the pair category `(Type^op, Type)`
||| to `Type`.
|||
||| In other words, a `Profunctor` is a type constructor of two type
||| arguments, which is contravariant in its first argument and covariant
||| in its second argument.
|||
||| The `dimap` function can be used to map functions over both arguments
||| simultaneously.
|||
||| A straightforward example of a profunctor is the function arrow `(->)`
||| (represented by `Morphism`).
|||
||| Laws:
|||
||| - Identity: `dimap identity identity = identity`
||| - Composition: `dimap f1 g1 <<< dimap f2 g2 = dimap (f1 >>> f2) (g1 <<< g2)`
public export
interface (forall a . Functor (p a)) => Profunctor (0 p : Type -> Type -> Type) where
  dimap : (i2 -> i1) -> (o1 -> o2) -> p i1 o1 -> p i2 o2

||| Map a function over the (contravariant) first type argument only.
public export
clmap : Profunctor p => (i2 -> i1) -> p i1 o -> p i2 o
clmap f = dimap f id

||| Map a function over the (covariant) second type argument only.
public export
rmap : Profunctor p => (o1 -> o2) -> p i o1 -> p i o2
rmap = dimap id

||| Lift a pure function into any `Profunctor` which is also a `Category`.
public export
arr : Category p => Profunctor p => (a -> b) -> p a b
arr f = rmap f id

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Profunctor Morphism where
  dimap f g (Mor fun) = Mor $ g . fun . f

public export
Profunctor (Forget r) where
  dimap f _ (MkForget fun) = MkForget (fun . f)

public export
Functor m => Profunctor (Kleislimorphism m) where
  dimap f g (Kleisli fun) = Kleisli (map g . fun . f)
