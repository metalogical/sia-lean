import init.algebra.ring
import .core

variable (R : Type)
variable [sia R]

theorem microcancellation : forall a b: R, (forall d: Delta, a * d.val = b * d.val) -> a = b :=
    take a b,
    assume ea_eq_eb : forall d: Delta, a * d.val = b * d.val,
    let f (d : Delta) : R := a * d.val in 
    begin
        apply (unique_of_exists_unique (sia.kock_lawvere f)),
        show forall d, f d = a * 0 + a * d.val,
            simp,
        show forall d, f d = a * 0 + b * d.val,
            simp,
            show forall d, f d = b * d.val,
            intro d,
            apply eq.trans (ea_eq_eb d),
            reflexivity,
    end
