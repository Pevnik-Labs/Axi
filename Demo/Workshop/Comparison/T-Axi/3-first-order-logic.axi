
type N


declaration P Q : N -> Prop
declaration R : N -> N -> Prop


// forall x : N, P x
// exists x : N, Q x /\ R x x


theorem rename-forall :
  (forall x : N, P x) --> (forall y : N, P y)
proof
  assume allp
  pick-any y : N
  instantiate allp with y
qed

theorem irrefl-trans-asym :
  (forall x : N, ~ R x x) -->
  (forall x y z : N, R x y --> R y z --> R x z) -->
    forall x y : N, R x y --> ~ R y x
proof
  assume irrefl trans
  pick-any a b
  assume rab rba
  apply (instantiate irrefl with a)
  apply (instantiate trans with a b a)
  . assumption
  . assumption
qed

theorem rename-exists :
  (exists x : N, P x) --> (exists y : N, P y)
proof
  assume ex
  pick-witness a pa for ex
  witness a
  assumption
qed

theorem rename-exists-pattern :
  (exists x : N, P x) --> (exists y : N, P y)
proof
  assume (witness a such-that pa)
  witness a
  assumption
qed


pq (x : N) : Prop =
  P x /\ Q x

declaration f : N -> N

ff (x : N) : N =
  f (f x)