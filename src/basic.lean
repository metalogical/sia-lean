import .core

variable {R : Type}
variable [sia R]

section -- useful lemmas about orders
    variables {a b c : R}

    lemma sia.lt_zero_one : (0: R) < (1: R) :=
        have almost: 0 < (0: R) \/ (0: R) < 1, from sia.zero_one_far (0: R),
        have left: 0 < (0: R) -> (0: R) < 1, from
            assume bad,
            absurd bad (sia.lt_irrefl (0: R)),
        have right: (0: R) < 1 -> (0: R) < 1, from fun x, x,
        or.elim almost left right

    lemma sia.lt_neg_flip : a < b -> -b < -a :=
        assume lt: a < b,
        calc
            -b  = -b + 0        : by rw add_zero
            ... = -b + (-a + a) : by rw add_left_neg
            ... = (-b + -a) + a : by rw add_assoc
            ... < (-b + -a) + b : sia.lt_add_left lt _
            ... = (-a + -b) + b : congr_arg (fun x, x + b) (add_comm _ _)
            ... = -a + (-b + b) : by rw add_assoc
            ... = -a + 0        : by rw add_left_neg
            ... = -a            : by rw add_zero

    lemma sia.lt_ne : forall {a b : R}, a < b -> ne a b :=
        assume a b,
        assume a_lt_b,
        assume bad_a_eq_b: a = b,
        sia.lt_irrefl a (calc
            a   < b : a_lt_b
            ... = a : by rw bad_a_eq_b
        )

    lemma sia.lt_far : forall {a b: R}, a < b -> forall x: R, a < x \/ x < b := -- Bell 1.2
        assume a b,
        assume a_lt_b,
        assume x,

        -- shift x by [a ... b] -> [0 ... 1]
        let delta: R := b - a in
        let y: R := (x - a) / delta in

        have delta_pos : 0 < b - a, from (calc
            0   = -a + a : by rw add_left_neg
            ... < -a + b : sia.lt_add_left a_lt_b _
            ... =  b - a : by rw [add_comm, sub_eq_add_neg]
        ),
        have delta_ne_zero : ne (b - a) 0, from ne.symm (sia.lt_ne delta_pos),

        have almost: 0 < y \/ y < 1, from sia.zero_one_far y,
        have left: 0 < y -> a < x \/ x < b, from
            assume y_pos : 0 < y,
            or.intro_left _ (calc -- show a < x
                a   = a + delta * 0               : by rw [mul_zero, add_zero a]
                ... < a + delta * y               : sia.lt_add_left (sia.lt_mul_pos_left y_pos delta_pos) _
                ... = a + (x - a) / delta * delta : by rw mul_comm
                ... = a + (x - a)                 : by rw div_mul_cancel _ delta_ne_zero
                ... = x                           : by rw [add_comm, sub_add_cancel]
            ),
        have right: y < 1 -> a < x \/ x < b, from
            assume y_lt_one: y < 1,
            or.intro_right _ (calc -- show x < b
                x   = (x - a) + a   : by rw sub_add_cancel
                ... = a + delta * y : by rw [mul_comm, add_comm, div_mul_cancel _ delta_ne_zero]
                ... < a + delta * 1 : sia.lt_add_left (sia.lt_mul_pos_left y_lt_one delta_pos) _
                ... = a + b - a     : by rw [mul_one, add_sub_assoc]
                ... = b             : by rw [sub_eq_add_neg, add_comm, neg_add_cancel_left]
            ),
        or.elim almost left right

    lemma sia.one_div_pos_of_pos : forall {c : R}, 0 < c -> 0 < 1 / c :=
        assume c,
        assume c_pos,

        have c_ne_zero : ne c 0, from ne.symm (sia.lt_ne c_pos),
        have ne (1 / c) 0, from one_div_ne_zero c_ne_zero,
        have disj: 1 / c < 0 \/ 0 < 1 / c, from sia.ne_lt this,

        have left: 1 / c < 0 -> 0 < 1 / c, from
            assume one_div_c_neg,
            have (1: R) < 1, from (calc
                1   = c * (1 / c) : by rw mul_div_cancel' _ c_ne_zero
                ... < c * 0       : sia.lt_mul_pos_left one_div_c_neg c_pos
                ... = 0           : mul_zero _
                ... < (1: R)      : sia.lt_zero_one
            ),
            absurd this (sia.lt_irrefl 1),
        or.elim disj left (fun x, x)

    section -- Bell 1.4
        lemma sia.le_refl : a <= a := by simp [sia.lt_irrefl, sia.le_def]

        @[trans]
        lemma sia.le_trans : a <= b -> b <= c -> a <= c := begin
            simp [sia.le_def] at *,
            exact
                assume a_le_b b_le_c,
                assume bad_c_lt_a,
                have bad_or: c < b \/ b < a, from (sia.lt_far bad_c_lt_a b),
                or.elim bad_or b_le_c a_le_b
        end

        lemma sia.le_add_left : a <= b -> c + a <= c + b := begin
            simp [sia.le_def] at *,
            exact
                assume a_le_b,
                assume almost_bad,
                have bad: b < a, from calc
                    b   = -c + (b + c) : by simp
                    ... < -c + (a + c) : sia.lt_add_left almost_bad (-c)
                    ... = a            : by simp,
                a_le_b bad
        end

        lemma sia.le_zero_one : (0: R) <= 1 :=
            have almost: not ((1: R) < 0), from
                assume bad : (1: R) < 0,
                sia.lt_irrefl (0 : R) (sia.lt_trans sia.lt_zero_one bad),
            iff.elim_right (sia.le_def R) almost

        lemma sia.le_mul_pos_left : a <= b -> 0 <= c -> c * a <= c * b := begin
            simp [sia.le_def] at *,
            exact
                assume a_le_b,
                assume zero_le_c,
                assume bc_lt_ac,

                have c_ne_zero: ne c 0, from
                    assume bad: c = 0,
                    have b * c = a * c, by simp [bad, mul_zero],
                    absurd this (sia.lt_ne bc_lt_ac),
                have c < 0 \/ 0 < c, from sia.ne_lt c_ne_zero,

                have right : not (0 < c), from
                    assume c_pos,
                    have b < a, from (calc
                        b   = (1 / c) * c * b   : by rw [one_div_mul_cancel c_ne_zero, one_mul]
                        ... = (1 / c) * (b * c) : by simp [mul_comm, mul_assoc]
                        ... < (1 / c) * (a * c) : sia.lt_mul_pos_left bc_lt_ac (sia.one_div_pos_of_pos c_pos)
                        ... = (1 / c) * c * a   : by simp [mul_comm, mul_assoc]
                        ... = a                 : by rw [one_div_mul_cancel c_ne_zero, one_mul]
                    ),
                    a_le_b this,
                or.elim this zero_le_c right
        end
    end
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
