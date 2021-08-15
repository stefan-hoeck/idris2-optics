module Optics

import Data.Profunctor
import Data.List1

--------------------------------------------------------------------------------
--          Optics
--------------------------------------------------------------------------------

Optic : (p : Type -> Type -> Type) -> (a,b,s,t : Type) -> Type
Optic p a b s t = p a b -> p s t

AGetter : (a,b,s,t : Type) -> Type
AGetter a = Optic (Kleislimorphism $ Const a) a

ASetter : (a,b,s,t : Type) -> Type
ASetter = Optic Morphism

iso : Profunctor p => (s -> a) -> (b -> t) -> Optic p a b s t
iso = dimap 

lens : Strong p => (s -> a) -> (s -> b -> t) -> Optic p a b s t
lens f g = dimap f' (uncurry g) . second
  where f' : s -> (s,a)
        f' s = (s, f s)

fst : Strong p => Optic p a b (a,c) (b,c)
fst = lens fst $ \(_,c),b => (b,c)

snd : Strong p => Optic p a b (c,a) (c,b)
snd = lens snd $ \(c,_),b => (c,b)

view : AGetter a b s t -> s -> a
view f = runConst . applyKleisli (f $ Kleisli MkConst)

over : ASetter a b s t -> (a -> b) -> s -> t
over f g = applyMor (f $ Mor g)

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

cons : Profunctor p => Optic p (a,List a) (b,List b) (List1 a) (List1 b)
cons = iso (\(h ::: t) => (h,t)) (\(h,t) => h ::: t)

uncons : Profunctor p => Optic p (List1 a) (List1 b) (a,List a) (b,List b)
uncons = iso (\(h,t) => h ::: t) (\(h ::: t) => (h,t))

headUpper : List1 Char -> List1 Char
headUpper = over (cons . fst) toUpper
