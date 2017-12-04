import .ordered_field
import .util

universe u
variable {R : Type u}

section -- define Delta in terms of ring to avoid circularity in the definition of sia
    variable [ring R]

    @[reducible]
    private def Delta : set R := fun r, r * r = 0

    @[reducible]
    private def zero_Delta : has_zero (subtype Delta) := { zero := { val := (0 : R), property := ring.mul_zero (0 : R) } }
end

-- Smooth Infinitesimal Analysis
class sia R extends st_ordered_field R :=
    (exists_unique_sqrt : forall a : { r: R // r > 0 }, exists! b, b * b = a.val) -- we have at least the real numbers (? is this equivalent to LUB)
    (kock_lawvere       : forall f: subtype Delta -> R, exists! a: R, forall d: subtype Delta, f d = f zero_Delta.zero + a * d.val)

namespace sia -- intervals
    variable [sia R]

    @[reducible]
    def microstable (A : set R) : Prop := forall a : subtype A, forall d : subtype Delta, set.mem (a.val + d.val) A
end sia

namespace sia
    -- export Delta in terms of sia; type parameter R is explicit because Lean cannot typically infer it
    @[reducible] def Delta (R: Type u) [sia R] := fun r : R, r * r = 0
    instance {R : Type u} [sia R] : has_zero (subtype (Delta R)) := (| { val := (0 : R), property := ring.mul_zero (0 : R) } |)
end sia
