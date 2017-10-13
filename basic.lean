import init.algebra.ring
import .sia

variable (R : Type)
variable [sia R]

theorem microcancellation : forall a b: R, forall d: Delta, a * d.val = b * d.val -> a = b :=
    take a b,
    take d,
    assume ea_eq_eb : a * d.val = b * d.val,
    let f (d : Delta) : R := a * d.val in 
    begin
        apply (unique_of_exists_unique (sia.kock_lawvere f d)),
        show f d = a * 0 + a * d.val,
            simp,
        show f d = a * 0 + b * d.val,
            simp,
            show f d = b * d.val,
            apply eq.trans ea_eq_eb,
            reflexivity,
    end
