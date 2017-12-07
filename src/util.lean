universe u

notation `exists!` binders `, ` r:(scoped P, exists_unique P) := r
infix ` != `:50 := ne

namespace set -- set extensionality
    variable {R : Type u}

    @[reducible]
    def eq (A : set R) (B : set R) := forall x : R, set.mem x A <-> set.mem x B

    theorem ext {A : set R} {B : set R} (a_eq_b : eq A B) : A = B := funext (fun x, propext (a_eq_b x))
end set
