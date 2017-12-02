universe u

notation `exists!` binders `, ` r:(scoped P, exists_unique P) := r

variable {R : Type u}

section -- define Delta in terms of ring to avoid circularity in the definition of sia
    variable [ring R]

    @[reducible]
    private def Delta : set R := fun r, r * r = 0

    @[reducible]
    private def zero_Delta : has_zero (subtype Delta) := { zero := { val := (0 : R), property := ring.mul_zero (0 : R) } }
end

-- Smooth Infinitesimal Analysis
class sia R extends field R, has_lt R :=
    (lt_irrefl : forall a : R, not (a < a))
    (lt_trans  : forall {a b c : R}, a < b -> b < c -> a < c)
    (ne_lt     : forall {a b : R}, ne a b -> a < b \/ b < a)

    (zero_one_far       : forall a: R, 0 < a \/ a < 1)
    (lt_add_left        : forall {a b : R}, a < b -> forall c : R, c + a < c + b)
    (lt_mul_pos_left    : forall {a b c : R}, 0 < c -> a < b -> c * a < c * b)
    (exists_unique_sqrt : forall a : { r: R // r > 0 }, exists! b, b * b = a.val)
    (kock_lawvere       : forall f: subtype Delta -> R, exists! a: R, forall d: subtype Delta, f d = f zero_Delta.zero + a * d.val)

attribute [trans] sia.lt_trans -- allow use of transitivity in calc proofs

instance sia_has_le [sia R] : has_le R := {
    le := fun x, fun y, not (y < x)
}
attribute [reducible] has_le.le

namespace sia -- intervals
    variable [sia R]

    @[reducible]
    def microstable (A : set R) : Prop := forall a : subtype A, forall d : subtype Delta, set.mem (a.val + d.val) A

    definition open_interval (a: R) (b: R) : set R := fun r: R, a < r /\ r < b
    definition closed_interval (a: R) (b: R) : set R := fun r: R, a <= r /\ r <= b

    notation `[` a `...` b `]` := open_interval a b
    notation `[[` a `...` b `]]` := closed_interval a b
end sia

namespace sia
    -- export Delta in terms of sia; type parameter R is explicit because Lean cannot typically infer it
    @[reducible] def Delta (R: Type u) [sia R] := fun r : R, r * r = 0
    instance {R : Type u} [sia R] : has_zero (subtype (Delta R)) := (| { val := (0 : R), property := ring.mul_zero (0 : R) } |)
end sia
