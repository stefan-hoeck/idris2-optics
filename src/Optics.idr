module Optics

import Control.Applicative.Const
import Control.Monad.Identity
import Data.List1
import Data.Morphisms

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

--------------------------------------------------------------------------------
--          Optics
--------------------------------------------------------------------------------

Optic : (p : Type -> Type -> Type) -> (a,b,s,t : Type) -> Type
Optic p a b s t = p a b -> p s t

AGetter : (a,b,s,t : Type) -> Type
AGetter a = Optic (Kleislimorphism $ Const a) a

ASetter : (a,b,s,t : Type) -> Type
ASetter = Optic Morphism

public export
Iso : (a,b,s,t : Type) -> Type
Iso a b s t = {p : _} -> Profunctor p => p a b -> p s t

iso : (s -> a) -> (b -> t) -> Iso a b s t
iso f g = dimap {p} f g

public export
Lens : (a,b,s,t : Type) -> Type
Lens a b s t = {p : _} -> Strong p => p a b -> p s t

lens : (s -> a) -> (s -> b -> t) -> Lens a b s t
lens f g = dimap f' (uncurry g) . second
  where f' : s -> (s,a)
        f' s = (s, f s)

fst : Lens a b (a,c) (b,c)
fst = lens fst \(_,c),b => (b,c)

snd : Lens a b (c,a) (c,b)
snd = lens snd \(c,_),b => (c,b)

view : AGetter a b s t -> s -> a
view f = runConst . applyKleisli (f $ Kleisli MkConst)

over : ASetter a b s t -> (a -> b) -> s -> t
over f g = applyMor (f $ Mor g)

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

cons : Iso (a,List a) (b,List b) (List1 a) (List1 b)
cons = iso (\(h ::: t) => (h,t)) (\(h,t) => h ::: t)

uncons : Iso (List1 a) (List1 b) (a,List a) (b,List b)
uncons = iso (\(h,t) => h ::: t) (\(h ::: t) => (h,t))

headUpper : List1 Char -> List1 Char
headUpper = over (cons . fst) toUpper
