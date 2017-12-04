import .sia

namespace sia
section
    parameters {R : Type} [sia R]
    variables {a b c : R}

    @[reducible] private def Delta := Delta R
    @[reducible] private def DeltaT := subtype Delta

    theorem microaffinity : forall f: R -> R, forall x: R, exists! a: R, forall d: DeltaT, f (x + d.val) = f x + a * d.val :=
        assume f: R -> R,
        assume x: R,
        let g (d: DeltaT) : R := f (x + d.val) in
        have nice: f x = g 0, from eq.symm (eq.subst (add_group.add_zero x) (eq.refl _)),
        by {rewrite nice, apply kock_lawvere}

    theorem delta_near_zero : forall d: DeltaT, 0 <= d.val /\ d.val <= 0 :=
        assume d,
        have left: not (d.val < 0), from
            assume bad,
            have 0 < -d.val, by {rw <-neg_zero, apply st_ordered_field.lt_neg_flip bad},
            have 0 < d.val * d.val, by {rw <-neg_mul_neg, rw <-mul_zero, apply st_ordered_field.lt_mul_pos_left this, assumption},
            absurd d.property (ne.symm (st_order.lt_ne this)),
        have right: not (0 < d.val), from
            assume bad,
            have 0 < d.val * d.val, by {rw <-mul_zero, apply st_ordered_field.lt_mul_pos_left bad bad},
            absurd d.property (ne.symm (st_order.lt_ne this)),
        and.intro left right

    section -- Theorem 1.1
        theorem delta_in_zero_interval : set.subset Delta [[(0: R) ... 0]] :=
            assume a,
            assume a_in_Delta,
            delta_near_zero { val := a, property := a_in_Delta }

        @[reducible]
        def degenerate (S : set R) : Prop := forall x y : subtype S, x.val = y.val

        theorem delta_nondegenerate : not (degenerate Delta) :=
            assume deg,
            have d_eq_zero: forall y: DeltaT, (0: R) = y.val, from deg 0,
            let f := fun r: R, r in
            have bad: exists! a: R, forall d: DeltaT, 0 + d.val = 0 + a * d.val, from microaffinity f 0,
            have pf_zero: forall d: DeltaT, 0 + d.val = 0 + 0 * d.val, from
                assume d,
                calc
                    0 + d.val = d.val + 0 * d.val : by simp
                    ...       = 0 + 0 * d.val     : by rw d_eq_zero d,
            have pf_one: forall d: DeltaT, 0 + d.val = 0 + 1 * d.val, by simp,
            have (0: R) = 1, from unique_of_exists_unique bad pf_zero pf_one,
            absurd this (st_order.lt_ne (st_ordered_field.lt_zero_one R))

        theorem delta_indistinguishable_zero : forall d: DeltaT, not (not (d.val = 0)) :=
            assume d,
            assume bad: d.val != 0,
            have d.val < 0 \/ 0 < d.val, from st_order.ne_lt bad,
            have left: not (d.val < 0), from and.elim_left (delta_near_zero d),
            have right: not (0 < d.val), from and.elim_right (delta_near_zero d),
            or.elim this left right

        theorem not_lem_eq_delta_zero : not (forall d: DeltaT, d.val = 0 \/ d.val != 0) :=
            assume bad,
            have forall d: DeltaT, d.val = 0, from
                assume d,
                or.resolve_right (bad d) (delta_indistinguishable_zero d),
            have forall x y: DeltaT, x.val = y.val, from
                assume x y,
                eq.trans (this x) (eq.symm (this y)),
            delta_nondegenerate this

        theorem microcancellation : forall {a b: R}, (forall d: DeltaT, a * d.val = b * d.val) -> a = b :=
            assume a b,
            assume ea_eq_eb : forall d: DeltaT, a * d.val = b * d.val,
            let f (d : DeltaT) : R := a * d.val in 
            begin
                apply (unique_of_exists_unique (kock_lawvere f)),
                show forall d, f d = a * 0 + a * d.val,
                    simp,
                show forall d, f d = a * 0 + b * d.val,
                    simp,
                    show forall d, f d = b * d.val,
                    intro d,
                    apply eq.trans (ea_eq_eb d),
                    reflexivity,
            end
    end
end
end sia
