import .core
import .basic

variable {R : Type}
variable [sia R]


section -- 1.1
    variable (a: R)

    example : 0 < a -> ne 0 a :=
        assume a_pos,
        assume a_zero_bad: 0 = a,
        sia.lt_irrefl (0: R) (calc
            0   < a : a_pos
            ... = 0 : by rw a_zero_bad
        )

    example : 0 < a <-> -a < 0 :=
        have forwards : 0 < a -> -a < 0, from (
            assume a_pos,
            calc
                -a  < -0 : sia.lt_neg_flip a_pos
                ... = 0  : neg_zero
        ),
        have backwards : -a < 0 -> 0 < a, from (
            assume neg_a_neg,
            calc
                0   = -0    : by rw neg_zero
                ... < -(-a) : sia.lt_neg_flip neg_a_neg
                ... = a     : by rw neg_neg
        ),
        iff.intro forwards backwards

    example : 0 < (1: R) + 1 := calc
        0   < 1           : sia.lt_zero_one
        ... = 1 + 0       : eq.symm (add_zero 1)
        ... < (1 + 1 : R) : sia.lt_add_left sia.lt_zero_one 1

     example : a < 0 \/ 0 < a -> 0 < a * a :=
         assume either_lt_0_a,
         have left: a < 0 -> 0 < a * a, from (
            assume a_neg,
            have neg_a_pos: 0 < -a, from (calc
                0   = -0 : by rw neg_zero
                ... < -a : sia.lt_neg_flip a_neg
            ), calc
                0   = -a * 0     : by rw mul_zero
                ... < -a * -a    : sia.lt_mul_pos_left neg_a_pos neg_a_pos
                ... = a * a      : by rw neg_mul_neg
         ),
         have right: 0 < a -> 0 < a * a, from (
             assume a_pos,
             calc
                 0   = a * 0 : by rw (mul_zero a)
                 ... < a * a : sia.lt_mul_pos_left a_pos a_pos
         ),
         or.elim either_lt_0_a left right
end

-- 1.2 in basic.lean

example : forall {a b: R}, not (a < b) -> [a ... b] -> false := -- 1.3; i.e. [a ... b] is empty
    assume a b,
    assume not_a_lt_b,
    assume bad_elem,
    have bad: a < bad_elem.val /\ bad_elem.val < b, from bad_elem.property,
    not_a_lt_b (sia.lt_trans (and.elim_left bad) (and.elim_right bad))

-- 1.4 in basic.lean
