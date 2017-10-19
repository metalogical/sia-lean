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

    -- shift x by [a ... b] -> [0 ... 1]
    let delta: R := b - a in
    let y: R := (x - a) / delta in

    have delta_pos : 0 < b - a, from (calc
        0   = -a + a : by rw add_left_neg
        ... < -a + b : sia.add_lt_add_left a_lt_b _
        ... =  b - a : by rw [add_comm, sub_eq_add_neg]
    ),
    have delta_ne_zero : ne (b - a) 0, from ne.symm (lt_ne delta_pos),

    have almost: 0 < y \/ y < 1, from sia.zero_one_far y,
    have left: 0 < y -> a < x \/ x < b, from
        assume y_pos : 0 < y,
        or.intro_left _ (calc -- show a < x
            a   = a + delta * 0               : by rw [mul_zero, add_zero a]
            ... < a + delta * y               : sia.add_lt_add_left (sia.mul_lt_mul_of_pos_left y_pos delta_pos) _
            ... = a + (x - a) / delta * delta : by rw mul_comm
            ... = a + (x - a)                 : by rw div_mul_cancel _ delta_ne_zero
            ... = x                           : by rw [add_comm, sub_add_cancel]
        ),
    have right: y < 1 -> a < x \/ x < b, from
        assume y_lt_one: y < 1,
        or.intro_right _ (calc -- show x < b
            x   = (x - a) + a   : by rw sub_add_cancel
            ... = a + delta * y : by rw [mul_comm, add_comm, div_mul_cancel _ delta_ne_zero]
            ... < a + delta * 1 : sia.add_lt_add_left (sia.mul_lt_mul_of_pos_left y_lt_one delta_pos) _
            ... = a + b - a     : by rw [mul_one, add_sub_assoc]
            ... = b             : by rw [sub_eq_add_neg, add_comm, neg_add_cancel_left]
        ),
    or.elim almost left right
