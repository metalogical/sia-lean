import init.algebra.ring
import init.algebra.group
import .core

variable (R : Type)
variable [sia R]

theorem microcancellation : forall a b: R, (forall d: Delta, a * d.val = b * d.val) -> a = b :=
    assume a b,
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

theorem microaffinity : forall f: R -> R, forall x: R, exists! a: R, forall d: Delta, f (x + d.val) = f x + a * d.val :=
    assume f: R -> R,
    assume x: R,
    let g (d: Delta) : R := f (x + d.val) in
    have nice: f x = g 0, from eq.symm (eq.subst (add_group.add_zero x) (eq.refl _)),
    begin
        show exists! a: R, forall d: Delta, g d = f x + a * d.val,
        rewrite nice,
        apply sia.kock_lawvere,
    end
