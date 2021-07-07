module Data.Profunctor

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

public export
interface (forall a . Functor (p a)) => Profunctor (0 p : Type -> Type -> Type) where
  dimap : (i2 -> i1) -> (o1 -> o2) -> p i1 o1 -> p i2 o2

  lmap : (i2 -> i1) -> p i1 o -> p i2 o
  lmap f = dimap f id

  rmap : (o1 -> o2) -> p i o1 -> p i o2
  rmap = dimap id

public export
Profunctor Morphism where
  dimap f g (Mor fun) = Mor $ g . fun . f

public export
Profunctor (Forget r) where
  dimap f _ (MkForget fun) = MkForget (fun . f)

public export
Functor m => Profunctor (Kleislimorphism m) where
  dimap f g (Kleisli fun) = Kleisli (map g . fun . f)

--------------------------------------------------------------------------------
--          Strong
--------------------------------------------------------------------------------

public export
interface Profunctor p => Strong p where
  first  : p a b -> p (a,c) (b,c)
  second : p a b -> p (c,a) (c,b)

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

--------------------------------------------------------------------------------
--          Choice
--------------------------------------------------------------------------------

public export
interface Profunctor p => Choice p where
  left  : p a b -> p (Either a c) (Either b c)
  right : p a b -> p (Either c a) (Either c b)

public export
Choice Morphism where
  left  (Mor f) = Mor $ mapFst f
  right (Mor f) = Mor $ mapSnd f

public export
Applicative m => Choice (Kleislimorphism m) where
  left  (Kleisli f) = Kleisli $ bitraverse f pure
  right (Kleisli f) = Kleisli $ bitraverse pure f

public export
Choice (Forget r) where
  left  (MkForget f) = MkForget $ either f (const Nothing)
  right (MkForget f) = MkForget $ either (const Nothing) f
