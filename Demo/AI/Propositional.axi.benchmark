// Propositional logic benchmark for AIs.

// claude-3.7-sonnet-thinking: one shot.
theorem dn-intro :
  P --> ~ ~ P

// default/4o(?) one shot.
// DeepSeek V3 one-shot.
theorem iff-not-nand :
  ~ (P <--> Q) --> ~ P \/ ~ Q

// 4o one shot.
// DeepSeek V3 two shot.
theorem and-or-distrib :
  P /\ (Q \/ R) <--> (P /\ Q) \/ (P /\ R)

// 4o one shot, but with a more complicated proof.
// DeepSeek V3 two shot.
theorem de-morgan :
  ~ (P /\ Q) --> ~ P \/ ~ Q

// 4o two shot.
// DeepSeek V3 one-shot.
theorem de-morgan-conv :
  ~ P \/ ~ Q --> ~ (P /\ Q)

// DeepSeek V3 two shot.
theorem de-morgan-and :
  ~ (P \/ Q) <--> ~ P /\ ~ Q

theorem impl-and-distrib :
  (P --> Q /\ R) <--> (P --> Q) /\ (P --> R)

theorem impl-or-distrib :
  ((P \/ Q) --> R) <--> (P --> R) /\ (Q --> R)

// Very hard.
theorem iff-not-conv :
  (~ P <--> ~ Q) --> (P <--> Q)