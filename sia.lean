prelude
import init.algebra.field
import init.algebra.order
import init.logic
universe u


variable {R : Type u}
variable [ring R]

definition D (a : R): Prop := a * a = 0
definition z_mul_z_eq_z : D (0 : R) := ring.mul_zero 0
def derivative_test (d : R) (pf : D d) (f : (Pi r : R, D r -> R)) (a : R) : Prop := f d pf = f 0 z_mul_z_eq_z + a * d

-- Smooth Infinitesimal Analysis
class sia R extends field R, strict_order R :=
-- Axiom 1 (field R)
-- Axiom 2 (strict_order R); we can't just use ordered_field due to antisymmetric ≤
(zero_lt_one :            0 < 1)
(add_lt_add_left :        forall a b : R, a < b → forall c : R, c + a < c + b)
(mul_lt_mul_of_pos_left : forall a b c : R, a < b → 0 < c → c * a < c * b)
(neq_distinguishable :    forall a b : R, a ≠ b → a < b ∨ b < a)
-- Axiom 3
(exists_unique_sqrt :     forall a : R, ∃! b, b * b = a)
-- Axiom 4
(kock_lawvere : forall f: (Pi r:R, D r -> R), forall d:R, Pi pf: D d, exists_unique (derivative_test d pf f))
