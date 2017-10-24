prelude
import init.algebra.field
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
class sia R extends field R, has_lt R, has_le R :=
    (lt_irrefl : forall a : R, not (a < a))
    (lt_trans  : forall {a b c : R}, a < b -> b < c -> a < c)
    (le_def    : forall {a b : R}, a <= b <-> not (b < a))
    (ne_lt     : forall {a b : R}, ne a b -> a < b \/ b < a)

    (zero_one_far       : forall a: R, 0 < a \/ a < 1)
    (lt_add_left        : forall {a b : R}, a < b -> forall c : R, c + a < c + b)
    (lt_mul_pos_left    : forall {a b c : R}, a < b -> 0 < c -> c * a < c * b)
    (exists_unique_sqrt : forall a : { r: R // r > 0 }, exists! b, b * b = a.val)
    (kock_lawvere       : forall f: Delta -> R, exists! a: R, forall d: Delta, f d = f 0 + a * d.val)
attribute [trans] sia.lt_trans -- allow use of transitivity in calc proofs

section -- intervals
    variable [sia R]

    definition open_interval (a: R) (b: R) : Type u := { r: R // a < r /\ r < b }
    definition closed_interval (a: R) (b: R) : Type u := { r: R // a <= r /\ r <= b }

    notation `[` a `...` b `]` := open_interval a b
    notation `[[` a `...` b `]]` := closed_interval a b
end

section
    variable [sia R]

    -- non-unicode notation for inverse
    @[simp, reducible]
    def inv : R -> R := has_inv.inv
end
