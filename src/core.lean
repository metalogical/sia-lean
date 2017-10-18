prelude
import init.algebra.field
import init.logic
import init.core
import .order
universe u

notation `exists!` binders `, ` r:(scoped P, exists_unique P) := r


variable {R : Type u}

section -- microneighborhoods
    variable [ring R]

    @[reducible]
    definition microneighborhood (around : R) : Type u := { r: R // r * r = around }

    @[reducible]
    def Delta : Type u := microneighborhood (0 : R)

    @[reducible]
    instance : has_zero Delta := (| { val := (0 : R), property := ring.mul_zero (0 : R) } |)
end

-- Smooth Infinitesimal Analysis
class sia R extends field R, strict_order R :=
    (zero_lt_one :            (0: R) < (1: R))
    (add_lt_add_left :        forall {a b : R}, a < b -> forall c : R, c + a < c + b)
    (mul_lt_mul_of_pos_left : forall {a b c : R}, a < b -> 0 < c -> c * a < c * b)
    (exists_unique_sqrt :     forall a : { r: R // r > 0 }, exists! b, b * b = a.val)
    (kock_lawvere :           forall f: Delta -> R, exists! a: R, forall d: Delta, f d = f 0 + a * d.val)

section -- intervals
    variable [sia R]

    definition open_interval (a: R) (b: R) : Type u := { r: R // a < r /\ r < b }
    definition closed_interval (a: R) (b: R) : Type u := { r: R // a <= r /\ r <= b }

    notation `int[` a `,` b `]` := open_interval a b
    notation `int(` a `,` b `(` := closed_interval a b
end
