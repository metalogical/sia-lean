import .core

variable {R : Type}
variable [sia R]

namespace sia
    variables {a b c : R}

    -- Lemmas regarding <

    lemma lt_zero_one : (0: R) < (1: R) :=
        have almost: 0 < (0: R) \/ (0: R) < 1, from zero_one_far (0: R),
        have left: 0 < (0: R) -> (0: R) < 1, from
            assume bad,
            absurd bad (lt_irrefl (0: R)),
        have right: (0: R) < 1 -> (0: R) < 1, from fun x, x,
        or.elim almost left right

    lemma lt_neg_flip : a < b -> -b < -a :=
        assume lt: a < b,
        calc
            -b  = -b + 0        : by rw add_zero
            ... = -b + (-a + a) : by rw add_left_neg
            ... = (-b + -a) + a : by rw add_assoc
            ... < (-b + -a) + b : lt_add_left lt _
            ... = (-a + -b) + b : congr_arg (fun x, x + b) (add_comm _ _)
            ... = -a + (-b + b) : by rw add_assoc
            ... = -a + 0        : by rw add_left_neg
            ... = -a            : by rw add_zero

    lemma lt_ne : forall {a b : R}, a < b -> ne a b :=
        assume a b,
        assume a_lt_b,
        assume bad_a_eq_b: a = b,
        lt_irrefl a (calc
            a   < b : a_lt_b
            ... = a : by rw bad_a_eq_b
        )

    lemma lt_far : forall {a b: R}, a < b -> forall x: R, a < x \/ x < b := -- Bell 1.2
        assume a b,
        assume a_lt_b,
        assume x,

        -- shift x by [a ... b] -> [0 ... 1]
        let delta: R := b - a in
        let y: R := (x - a) / delta in

        have delta_pos : 0 < b - a, from (calc
            0   = -a + a : by rw add_left_neg
            ... < -a + b : lt_add_left a_lt_b _
            ... =  b - a : by rw [add_comm, sub_eq_add_neg]
        ),
        have delta_ne_zero : ne (b - a) 0, from ne.symm (lt_ne delta_pos),

        have almost: 0 < y \/ y < 1, from zero_one_far y,
        have left: 0 < y -> a < x \/ x < b, from
            assume y_pos : 0 < y,
            or.intro_left _ (calc -- show a < x
                a   = a + delta * 0               : by rw [mul_zero, add_zero a]
                ... < a + delta * y               : lt_add_left (lt_mul_pos_left delta_pos y_pos) _
                ... = a + (x - a) / delta * delta : by rw mul_comm
                ... = a + (x - a)                 : by rw div_mul_cancel _ delta_ne_zero
                ... = x                           : by rw [add_comm, sub_add_cancel]
            ),
        have right: y < 1 -> a < x \/ x < b, from
            assume y_lt_one: y < 1,
            or.intro_right _ (calc -- show x < b
                x   = (x - a) + a   : by rw sub_add_cancel
                ... = a + delta * y : by rw [mul_comm, add_comm, div_mul_cancel _ delta_ne_zero]
                ... < a + delta * 1 : lt_add_left (lt_mul_pos_left delta_pos y_lt_one) _
                ... = a + b - a     : by rw [mul_one, add_sub_assoc]
                ... = b             : by rw [sub_eq_add_neg, add_comm, neg_add_cancel_left]
            ),
        or.elim almost left right

    lemma one_div_pos_of_pos : forall {c : R}, 0 < c -> 0 < 1 / c :=
        assume c,
        assume c_pos,

        have c_ne_zero : ne c 0, from ne.symm (lt_ne c_pos),
        have ne (1 / c) 0, from one_div_ne_zero c_ne_zero,
        have disj: 1 / c < 0 \/ 0 < 1 / c, from ne_lt this,

        have left: 1 / c < 0 -> 0 < 1 / c, from
            assume one_div_c_neg,
            have (1: R) < 1, from (calc
                1   = c * (1 / c) : by rw mul_div_cancel' _ c_ne_zero
                ... < c * 0       : lt_mul_pos_left c_pos one_div_c_neg
                ... = 0           : mul_zero _
                ... < (1: R)      : lt_zero_one
            ),
            absurd this (lt_irrefl 1),
        or.elim disj left (fun x, x)

    -- Lemmas regarding ≤

    lemma le_refl : a <= a := lt_irrefl a

    @[trans]
    lemma le_trans : a <= b -> b <= c -> a <= c :=
        assume a_le_b b_le_c,
        assume bad_c_lt_a,
        have bad_or: c < b \/ b < a, from (lt_far bad_c_lt_a b),
        or.elim bad_or b_le_c a_le_b

    lemma le_add_left : a <= b -> c + a <= c + b :=
        assume a_le_b,
        assume almost_bad,
        have bad: b < a, from calc
            b   = -c + (c + b) : by simp
            ... < -c + (c + a) : lt_add_left almost_bad (-c)
            ... = a            : by simp,
        a_le_b bad

    lemma le_zero_one : (0: R) <= 1 :=
        assume bad : (1: R) < 0,
        lt_irrefl (0 : R) (lt_trans lt_zero_one bad)

    lemma le_mul_pos_left : a <= b -> 0 <= c -> c * a <= c * b :=
        assume a_le_b,
        assume zero_le_c,
        assume bc_lt_ac,

        have c_ne_zero: ne c 0, from
            assume bad: c = 0,
            have c * b = c * a, by simp [bad, mul_zero],
            absurd this (lt_ne bc_lt_ac),
        have c < 0 \/ 0 < c, from ne_lt c_ne_zero,

        have right : not (0 < c), from
            assume c_pos,
            have b < a, from (calc
                b   = (1 / c) * c * b   : by rw [one_div_mul_cancel c_ne_zero, one_mul]
                ... = (1 / c) * (c * b) : by simp [mul_assoc]
                ... < (1 / c) * (c * a) : lt_mul_pos_left (one_div_pos_of_pos c_pos) bc_lt_ac
                ... = (1 / c) * c * a   : by simp [mul_assoc]
                ... = a                 : by rw [one_div_mul_cancel c_ne_zero, one_mul]
            ),
            a_le_b this,
        or.elim this zero_le_c right

    lemma le_neg_flip : a <= b -> -b <= -a :=
        assume a_le_b,
        assume neg_a_lt_neg_b,
        have b < a, from (calc
            b   = -(-b) : by rw neg_neg
            ... < -(-a) : lt_neg_flip neg_a_lt_neg_b
            ... = a     : by rw neg_neg
        ),
        absurd this a_le_b

    @[trans]
    lemma le_lt_trans : a <= b -> b < c -> a < c :=
        assume le,
        assume lt,
        have ne a c, from
            assume bad,
            have b < a, by {rw bad, assumption},
            le this,
        have a < c \/ c < a, from ne_lt this,
        have right_bad : not (c < a), from
            assume bad,
            have b < a, from lt_trans lt bad,
            le this,
        or.resolve_right this right_bad

    @[trans]
    lemma lt_le_trans : a < b -> b <= c -> a < c :=
        assume lt,
        assume le,
        have ne a c, from
            assume bad,
            have c < b, by {rw <-bad, assumption},
            le this,
        have a < c \/ c < a, from ne_lt this,
        have right_bad : not (c < a), from
            assume bad,
            have c < b, from lt_trans bad lt,
            le this,
        or.resolve_right this right_bad

    -- General Theorems

    theorem microcancellation : forall a b: R, (forall d: subtype Delta, a * d.val = b * d.val) -> a = b :=
        assume a b,
        assume ea_eq_eb : forall d: subtype Delta, a * d.val = b * d.val,
        let f (d : subtype Delta) : R := a * d.val in 
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

    theorem microaffinity : forall f: R -> R, forall x: R, exists! a: R, forall d: subtype Delta, f (x + d.val) = f x + a * d.val :=
        assume f: R -> R,
        assume x: R,
        let g (d: subtype Delta) : R := f (x + d.val) in
        have nice: f x = g 0, from eq.symm (eq.subst (add_group.add_zero x) (eq.refl _)),
        begin
            show exists! a: R, forall d: subtype Delta, g d = f x + a * d.val,
            rewrite nice,
            apply kock_lawvere,
        end

    section -- Theorem 1.1
    end
end sia
