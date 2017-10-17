prelude
import init.algebra.field
import init.logic
import init.core
import .order
universe u

notation `exists!` binders `, ` r:(scoped P, exists_unique P) := r


variable {R : Type u}
variable [ring R]

@[reducible]
definition microneighborhood (around : R) : Type u := { r: R // r * r = around }

@[reducible]
def Delta : Type u := microneighborhood (0 : R)
@[reducible]
instance : has_zero Delta := (| { val := (0 : R), property := ring.mul_zero (0 : R) } |)

-- Smooth Infinitesimal Analysis
class sia R extends field R, strict_order R :=
-- Axiom 1 (field R)
-- Axiom 2 (strict_order R); we can't just use ordered_field due to antisymmetric ≤
(zero_lt_one :            0 < 1)
(add_lt_add_left :        forall a b : R, a < b -> forall c : R, c + a < c + b)
(mul_lt_mul_of_pos_left : forall a b c : R, a < b -> 0 < c -> c * a < c * b)
-- Axiom 3
(exists_unique_sqrt :     forall a : R, exists! b, b * b = a)
-- Axiom 4 : principle of microaffineness
(kock_lawvere :           forall f: Delta -> R, exists! a: R, forall d: Delta, f d = f 0 + a * d.val)
