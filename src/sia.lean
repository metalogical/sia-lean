import .ordered_field
import .util

universe u
variable {R : Type u}

section -- define Delta in terms of ring to avoid circularity in the definition of sia
    variable [ring R]

    @[reducible] private def DeltaT := { x:R // x * x = 0 }
    @[reducible] private def zDeltaT : DeltaT := { val := (0 : R), property := ring.mul_zero (0 : R) }
end

-- Smooth Infinitesimal Analysis
class sia R extends st_ordered_field R :=
    (exists_unique_sqrt : forall a : { r: R // r > 0 }, exists! b, b * b = a.val) -- we have at least the real numbers (? is this equivalent to LUB)
    (kock_lawvere       : forall f: DeltaT -> R, exists! a: R, forall d: DeltaT, f d = f zDeltaT + a * d.val)

namespace sia -- intervals
    variable [sia R]

    @[reducible]
    def microstable (A : set R) : Prop := forall a : subtype A, forall d : DeltaT, set.mem (a.val + d.val) A
end sia

namespace sia
    -- export Delta in terms of sia; type parameter R is explicit because Lean cannot typically infer it
    @[reducible] def Delta (R: Type u) [sia R] := fun r : R, r * r = 0
    @[reducible] def DeltaT (R: Type u) [sia R] := subtype (Delta R)
    instance {R : Type u} [sia R] : has_zero (DeltaT R) := (| zDeltaT |)
end sia
