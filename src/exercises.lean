import .core
import .basic

variable {R : Type}
variable [sia R]


theorem neg_flips_order : forall {a b : R}, a < b -> -b < -a :=
    assume a b,
    assume lt: a < b,
    calc
        -b  = -b + 0        : eq.symm (add_zero _)
        ... = -b + (-a + a) : congr_arg _ (eq.symm (add_left_neg _))
        ... = (-b + -a) + a : eq.symm (add_assoc _ _ _)
        ... < (-b + -a) + b : sia.add_lt_add_left lt _
        ... = (-a + -b) + b : congr_arg (fun x, x + b) (add_comm _ _)
        ... = -a + (-b + b) : add_assoc _ _ _
        ... = -a + 0        : congr_arg _ (add_left_neg _)
        ... = -a            : add_zero _


section -- 1.1
    variable (a: R)

    example : 0 < a -> ne 0 a :=
        assume a_pos,
        assume a_zero_bad: 0 = a,
        strict_order.lt_irrefl 0 (calc
            0   < a : a_pos
            ... = 0 : eq.symm a_zero_bad
        )

    example : 0 < a <-> -a < 0 :=
        have forwards : 0 < a -> -a < 0, from (
            assume a_pos,
            calc
                -a  < -0 : neg_flips_order a_pos
                ... = 0  : neg_zero
        ),
        have backwards : -a < 0 -> 0 < a, from (
            assume neg_a_neg,
            calc
                0   = -0    : eq.symm (neg_zero)
                ... < -(-a) : neg_flips_order neg_a_neg
                ... = a     : neg_neg _
        ),
        iff.intro forwards backwards

    example : 0 < (1: R) + 1 := calc
        0   < 1     : sia.zero_lt_one R
        ... = 1 + 0 : eq.symm (add_monoid.add_zero 1)
        ... < 1 + 1 : sia.add_lt_add_left (sia.zero_lt_one R) 1

     example : a < 0 \/ 0 < a -> 0 < a * a :=
         assume either_lt_0_a,
         have left: a < 0 -> 0 < a * a, from (
            assume a_neg,
            have neg_a_pos: 0 < -a, from (calc
                0   = -0 : eq.symm neg_zero
                ... < -a : neg_flips_order a_neg
            ), calc
                0   = -a * 0     : by rw (mul_zero _)
                ... < -a * -a    : sia.mul_lt_mul_of_pos_left neg_a_pos neg_a_pos
                ... = a * a      : neg_mul_neg _ _
         ),
         have right: 0 < a -> 0 < a * a, from (
             assume a_pos,
             calc
                 0   = a * 0 : eq.symm (ring.mul_zero a)
                 ... < a * a : sia.mul_lt_mul_of_pos_left a_pos a_pos
         ),
         or.elim either_lt_0_a left right
end
