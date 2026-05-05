Require Import SMTCoq.SMTCoq.
Local Open Scope Z_scope.
Require Import ZArith.


Goal forall
    (x y: Z)
    (f: Z -> Z),
    (* x = y + 1 -> *) f y = f (x - 1).
Proof.
  Fail smt. Fail abduce_changeName2 2.

Abort.
