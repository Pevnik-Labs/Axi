// TODO: finish, update to new typeclass syntax/semantics.

class Functor (F : Type -> Type) where
  fmap : forall A B, (A -> B) -> F A -> F B

class LawfulFunctor (F : Type -> Type) <= Functor F where
  fmap-id : forall A, fmap id === id
  fmap-comp : forall A B C (f : A -> B) (g : B -> C), fmap (comp f g) === comp (fmap f) (fmap g)

instance Functor List where
  fmap (f : A -> B) : List A -> List B
  | nil => nil
  | cons h t => cons (f h) (fmap f t)

instance LawfulFunctor List where
  theorem fmap-id :
    forall {A}, fmap id === id
  proof
    pick-any A
    funext l
    proving fmap id l === l
    induction l with
    | nil =>
      chaining
        === fmap id nil
        === nil
    | cons h (t & ind IH) =>
      chaining
        === fmap id (cons h t)
        === cons (id h) (fmap id t)
        === cons h (fmap id t)
        === cons h t                 by rewrite IH
  qed

  theorem fmap-comp :
    forall {A B C} (f : A -> B) (g : B -> C),
      fmap (comp f g) === comp (fmap f) (fmap g)
  proof
    pick-any A B C f g
    funext l
    proving fmap (comp f g) l === fmap g (fmap f l)
    induction l with
    | nil =>
      chaining
        === fmap (comp f g) nil
        === nil
        === fmap g (fmap f nil)
    | cons h (t & ind IH) =>
      chaining
        === fmap (comp f g) (cons h t)
        === cons (g (f h)) (fmap (comp f g) t)
        === cons (g (f h)) (fmap g (fmap f t))  by rewrite IH
        === fmap g (fmap f (cons h t))
  qed
