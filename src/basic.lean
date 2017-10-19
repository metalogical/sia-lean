import .core

variable {R : Type}
variable [sia R]

section -- useful lemmas
    variable [sia R]

    lemma sia.zero_lt_one : (0: R) < (1: R) :=
        have almost: 0 < (0: R) \/ (0: R) < 1, from sia.zero_one_far (0: R),
        have left: 0 < (0: R) -> (0: R) < 1, from
            assume bad,
            absurd bad (strict_order.lt_irrefl (0: R)),
        have right: (0: R) < 1 -> (0: R) < 1, from fun x, x,
        or.elim almost left right

    lemma neg_flips_order : forall {a b : R}, a < b -> -b < -a :=
        assume a b,
        assume lt: a < b,
        calc
            -b  = -b + 0        : by rw add_zero
            ... = -b + (-a + a) : by rw add_left_neg
            ... = (-b + -a) + a : by rw add_assoc
            ... < (-b + -a) + b : sia.add_lt_add_left lt _
            ... = (-a + -b) + b : congr_arg (fun x, x + b) (add_comm _ _)
            ... = -a + (-b + b) : by rw add_assoc
            ... = -a + 0        : by rw add_left_neg
            ... = -a            : by rw add_zero
end

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
