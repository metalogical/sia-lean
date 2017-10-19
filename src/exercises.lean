import .core
import .basic
import init.algebra.group

variable {R : Type}
variable [sia R]


section -- 1.1
    variable (a: R)

    example : 0 < a -> ne 0 a :=
        assume a_pos,
        assume a_zero_bad: 0 = a,
        strict_order.lt_irrefl (0: R) (calc
            0   < a : a_pos
            ... = 0 : by rw a_zero_bad
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
                0   = -0    : by rw neg_zero
                ... < -(-a) : neg_flips_order neg_a_neg
                ... = a     : by rw neg_neg
        ),
        iff.intro forwards backwards

    example : 0 < (1: R) + 1 := calc
        0   < 1           : sia.zero_lt_one
        ... = 1 + 0       : eq.symm (add_zero 1)
        ... < (1 + 1 : R) : sia.add_lt_add_left sia.zero_lt_one 1

     example : a < 0 \/ 0 < a -> 0 < a * a :=
         assume either_lt_0_a,
         have left: a < 0 -> 0 < a * a, from (
            assume a_neg,
            have neg_a_pos: 0 < -a, from (calc
                0   = -0 : by rw neg_zero
                ... < -a : neg_flips_order a_neg
            ), calc
                0   = -a * 0     : by rw mul_zero
                ... < -a * -a    : sia.mul_lt_mul_of_pos_left neg_a_pos neg_a_pos
                ... = a * a      : by rw neg_mul_neg
         ),
         have right: 0 < a -> 0 < a * a, from (
             assume a_pos,
             calc
                 0   = a * 0 : by rw (mul_zero a)
                 ... < a * a : sia.mul_lt_mul_of_pos_left a_pos a_pos
         ),
         or.elim either_lt_0_a left right
end


example : forall {a b: R}, a < b -> forall x: R, a < x \/ x < b := -- 1.2
    assume a b,
    assume a_lt_b,
    assume x,

    have b_minus_a_pos: 0 < b - a, from (calc
        0   = -a + a  : by rw add_left_neg
        ... < -a + b  : sia.add_lt_add_left a_lt_b _
        ... =  b + -a : by rw add_comm
        ... = b - a   : by rw sub_eq_add_neg),
    have b_minus_a_not_zero: ne (b - a) 0, from
        assume almost_bad: b - a = 0,
        have bad: (0: R) < 0, from (calc
            0   < b - a : b_minus_a_pos
            ... = 0     : by rw almost_bad),
        strict_order.lt_irrefl (0: R) bad,

    let y: R := (x - a) / (b - a) in
    have almost: 0 < y \/ y < 1, from sia.zero_one_far y,
    have left: 0 < y -> a < x \/ x < b, from
        assume y_pos,
        or.intro_left _ (calc
            a   = a + (b - a) * 0 : by rw [mul_zero, add_zero a]
            ... < a + (b - a) * y : sia.add_lt_add_left (sia.mul_lt_mul_of_pos_left y_pos b_minus_a_pos) _

            ... = a + (b - a) * ((x - a) / (b - a))     : by reflexivity
            ... = a + (b - a) * (inv (b - a) * (x - a)) : by rw [mul_comm (inv (b - a)) (x - a), division_def]
            ... = a + (b - a) * inv (b - a) * (x - a)   : by rw mul_assoc

            ... = a + 1 * (x - a) : by rw mul_inv_cancel b_minus_a_not_zero
            ... = x               : by rw [one_mul, add_comm, sub_add_cancel]),
    have right: y < 1 -> a < x \/ x < b, from
        assume y_lt_one,
        or.intro_right _ (calc
            x   = x - a + a       : by rw sub_add_cancel
            ... = y * (b - a) + a : by rw div_mul_cancel _ b_minus_a_not_zero
            ... = a + (b - a) * y : by rw [add_comm, mul_comm]
            ... < a + (b - a) * 1 : sia.add_lt_add_left (sia.mul_lt_mul_of_pos_left y_lt_one b_minus_a_pos) _
            ... = a + b - a       : by rw [mul_one, add_sub_assoc]
            ... = -a + a + b      : by rw [sub_eq_add_neg, add_comm, add_assoc]
            ... = b               : by rw [add_left_neg, zero_add]),
    or.elim almost left right
