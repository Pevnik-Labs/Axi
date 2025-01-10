| Description                | Schematic         | Naturalistic  | Slides                |
| Assumption (P)             | P                 | P             | P                     |
| True introduction          | true-intro        | true          | true                  |
| False elimination          | false-elim        | exfalso       | exfalso               |
| Implication introduction   | impl-intro P in e | assume P in e | assume P in e         |
| Implication elimination    | impl-elim e1 e2   |               | modus-ponens e1 e2    |
| Negation introduction      | not-intro P in e  |               | suppose-absurd P in e |
| Negation elimination       | not-elim e1 e2    |               | absurd e1 e2          |
| Conjunction introduction   | and-intro e1 e2   | both          | both e1 e2            |
| Conjunction elimination-l  | and-elim-l e      |               | left-and e            |
| Conjunction elimination-r  | and-elim-r e      |               | right-and e           |
| Biconditional introduction | iff-intro e1 e2   | equivalence   | equivalence e1 e2     |
| Biconditiona elimination-l | iff-elim-l e      |               | left-iff e            |
| Biconditiona elimination-r | iff-elim-r e      |               | right-iff             |
| Disjunction introduction-l | or-intro-l e      | left e        | left-either Q e       |
| Disjunction introduction-r | or-intro-r e      | right e       | right-either P e      |
| Disjunction elimination    | or-elim e1 e2 e3  | case e1 e2 e3 | constructive-dilemma  |
| Double negation            | double-negation e | double-negation e | double-negation e |