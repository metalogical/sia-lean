universe u
variable {R : Type u}

class st_order R extends has_lt R := -- strict total order
    (lt_irrefl : forall a : R, not (a < a))
    (lt_trans  : forall {a b c : R}, a < b -> b < c -> a < c)
    (ne_lt     : forall {a b : R}, ne a b -> a < b \/ b < a)
    -- Bell 1.2, but we use it as an axiom for better structure
    (lt_far    : forall {a b : R}, a < b -> forall c : R, a < c \/ c < b)
attribute [trans] st_order.lt_trans -- allow use of transitivity in calc proofs

-- ordered field
class st_ordered_field R extends field R, st_order R :=
    (lt_zero_one        : (0: R) < 1)
    (lt_add_left        : forall {a b : R}, a < b -> forall c : R, c + a < c + b)
    (lt_mul_pos_left    : forall {a b c : R}, 0 < c -> a < b -> c * a < c * b)

-- lemmas & theorems regarding ordering
namespace st_order
    variable [st_order R]
    variables {a b c : R}

    -- intervals
    definition lt_interval [has_lt R] (a: R) (b: R) : set R := fun r: R, a < r /\ r < b
    definition le_interval [has_le R] (a: R) (b: R) : set R := fun r: R, a <= r /\ r <= b
    notation `[` a `...` b `]` := lt_interval a b
    notation `[[` a `...` b `]]` := le_interval a b

    -- non-strict total order
    instance has_le : has_le R := {
        le := fun x, fun y, not (y < x)
    }
    attribute [reducible] has_le.le

    lemma lt_ne : a < b -> ne a b :=
        assume a_lt_b,
        assume bad_a_eq_b: a = b,
        st_order.lt_irrefl a (calc
            a   < b : a_lt_b
            ... = a : by rw bad_a_eq_b
        )

    lemma le_refl : a <= a := lt_irrefl a

    @[trans]
    lemma le_trans : a <= b -> b <= c -> a <= c :=
        assume a_le_b b_le_c,
        assume bad_c_lt_a,
        have bad_or: c < b \/ b < a, from (st_order.lt_far bad_c_lt_a b),
        or.elim bad_or b_le_c a_le_b

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
end st_order

namespace st_ordered_field
    variable [st_ordered_field R]
    variables {a b c : R}

    lemma zero_one_far : 0 < a \/ a < 1 := st_order.lt_far (lt_zero_one R) a

    lemma lt_neg_flip : a < b -> -b < -a :=
        assume lt: a < b,
        calc
            -b  = -b + (-a + a) : by simp
            ... = (-b + -a) + a : by rw add_assoc
            ... < (-b + -a) + b : lt_add_left lt _
            ... = -a            : by simp

    lemma one_div_pos_of_pos : 0 < c -> 0 < 1 / c :=
        assume c_pos,
        have c_ne_zero : ne c 0, from ne.symm (st_order.lt_ne c_pos),
        have ne (1 / c) 0, from one_div_ne_zero c_ne_zero,
        have disj: 1 / c < 0 \/ 0 < 1 / c, from st_order.ne_lt this,
        have left: 1 / c < 0 -> 0 < 1 / c, from
            assume one_div_c_neg,
            have (1: R) < 1, from (calc
                1   = c * (1 / c) : by rw mul_div_cancel' _ c_ne_zero
                ... < c * 0       : lt_mul_pos_left c_pos one_div_c_neg
                ... = 0           : mul_zero _
                ... < (1: R)      : (lt_zero_one R)
            ),
            absurd this (st_order.lt_irrefl 1),
        or.elim disj left (fun x, x)

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
        st_order.lt_irrefl 0 (calc
            0   < 1 : lt_zero_one R
            ... < 0 : bad
        )

    lemma le_mul_pos_left : a <= b -> 0 <= c -> c * a <= c * b :=
        assume a_le_b,
        assume zero_le_c,
        assume bc_lt_ac,

        have c_ne_zero: ne c 0, from
            assume bad: c = 0,
            have c * b = c * a, by simp [bad, mul_zero],
            absurd this (st_order.lt_ne bc_lt_ac),
        have c < 0 \/ 0 < c, from st_order.ne_lt c_ne_zero,

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
end st_ordered_field
