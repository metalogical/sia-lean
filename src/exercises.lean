import .core
import .basic

variable {R : Type}
variable [sia R]
open sia


section -- 1.1
    variable (a: R)

    example : 0 < a -> ne 0 a :=
        assume a_pos,
        assume a_zero_bad: 0 = a,
        lt_irrefl (0: R) (calc
            0   < a : a_pos
            ... = 0 : by rw a_zero_bad
        )

    example : 0 < a <-> -a < 0 :=
        have forwards : 0 < a -> -a < 0, from (
            assume a_pos,
            calc
                -a  < -0 : lt_neg_flip a_pos
                ... = 0  : neg_zero
        ),
        have backwards : -a < 0 -> 0 < a, from (
            assume neg_a_neg,
            calc
                0   = -0    : by rw neg_zero
                ... < -(-a) : lt_neg_flip neg_a_neg
                ... = a     : by rw neg_neg
        ),
        iff.intro forwards backwards

    example : 0 < (1: R) + 1 := calc
        0   < 1           : lt_zero_one
        ... = 1 + 0       : eq.symm (add_zero 1)
        ... < (1 + 1 : R) : lt_add_left lt_zero_one 1

     example : a < 0 \/ 0 < a -> 0 < a * a :=
         assume either_lt_0_a,
         have left: a < 0 -> 0 < a * a, from (
            assume a_neg,
            have neg_a_pos: 0 < -a, from (calc
                0   = -0 : by rw neg_zero
                ... < -a : lt_neg_flip a_neg
            ), calc
                0   = -a * 0     : by rw mul_zero
                ... < -a * -a    : lt_mul_pos_left neg_a_pos neg_a_pos
                ... = a * a      : by rw neg_mul_neg
         ),
         have right: 0 < a -> 0 < a * a, from (
             assume a_pos,
             calc
                 0   = a * 0 : by rw (mul_zero a)
                 ... < a * a : lt_mul_pos_left a_pos a_pos
         ),
         or.elim either_lt_0_a left right
end

-- 1.2 in basic.lean

example : forall {a b: R}, not (a < b) -> forall x: R, not (set.mem x [a ... b]) := -- 1.3; i.e. [a ... b] is empty
    assume a b,
    assume not_a_lt_b,
    assume x,
    assume bad_elem,
    have bad: a < x /\ x < b, from bad_elem,
    not_a_lt_b (lt_trans (and.elim_left bad) (and.elim_right bad))

-- 1.4 in basic.lean

section --1.5
    @[reducible]
    def convex_comb (x y : R) (t : subtype [[(0: R) ... 1]]) := t.val * y + (1 - t.val) * x

    example : forall a b : R, forall x y : subtype [[a ... b]], forall t : subtype [[0 ... 1]],
                a <= convex_comb x.val y.val t /\ convex_comb x.val y.val t <= b :=
        assume a b,
        assume x y,
        assume t,
        have t_nonneg: 0 <= t.val, from and.elim_left t.property,

        have t.val <= 1, from and.elim_right t.property,
        have t_nonneg': 0 <= (1 - t.val), from (calc
            0   = 1 + -1       : by rw add_neg_self
            ... <= 1 + - t.val : le_add_left (le_neg_flip this)
            ... = 1 - t.val    : by rw <-sub_eq_add_neg
        ),

        have left: a <= convex_comb x.val y.val t, from
            have x_ineq: a <= x.val, from and.elim_left x.property,
            have y_ineq: a <= y.val, from and.elim_left y.property,
            (calc
                a   = 1 * a + (- (t.val * a) + t.val * a)  : by rw [<-add_comm (t.val * a) _, <-sub_eq_add_neg, sub_self, add_zero, one_mul]
                ... = 1 * a + -(t.val) * a + t.val * a     : by rw [add_assoc, neg_mul_eq_neg_mul]
                ... = (1 - t.val) * a + t.val * a          : by rw [sub_eq_add_neg, <-right_distrib]
                ... <= (1 - t.val) * a + t.val * y.val     : le_add_left (le_mul_pos_left y_ineq t_nonneg)
                ... = t.val * y.val + (1 - t.val) * a      : by rw add_comm
                ... <= t.val * y.val + (1 - t.val) * x.val : le_add_left (le_mul_pos_left x_ineq t_nonneg')
            ),
        have right: convex_comb x.val y.val t <= b, from
            have x_ineq: x.val <= b, from and.elim_right x.property,
            have y_ineq: y.val <= b, from and.elim_right y.property,
            (calc
                t.val * y.val + (1 - t.val) * x.val
                    <= t.val * y.val + (1 - t.val) * b    : le_add_left (le_mul_pos_left x_ineq t_nonneg')
                ... = (1 - t.val) * b + t.val * y.val     : by rw add_comm
                ... <= (1 - t.val) * b + t.val * b        : le_add_left (le_mul_pos_left y_ineq t_nonneg)
                ... = 1 * b + -(t.val) * b + t.val * b    : by rw [sub_eq_add_neg, right_distrib]
                ... = 1 * b + (- (t.val * b) + t.val * b) : by rw [add_assoc, neg_mul_eq_neg_mul]
                ... = b - (t.val * b) + t.val * b         : by rw [one_mul, sub_eq_add_neg, add_assoc]
                ... = b                                   : by rw sub_add_cancel
            ),
        and.intro left right
end

section -- 1.6
    example : forall d: subtype (Delta R), not (d.val < (0: R) \/ 0 < d.val) :=
        assume d,
        have 0 <= d.val /\ d.val <= 0, from delta_near_zero d,
        not_or this.left this.right

    example : forall d: subtype (Delta R), forall a: R, (Delta R) (d.val * a) :=
        assume d,
        assume a,
        have d.val * d.val = 0, from d.property,
        show (d.val * a) * (d.val * a) = 0, from calc
            (d.val * a) * (d.val * a)
                = d.val * d.val * a * a : by simp
            ... = 0 * a * a             : by rw this
            ... = 0                     : by simp [zero_mul]

    example : forall d: subtype (Delta R), forall a: R, 0 < a -> 0 < a + d.val :=
        assume d,
        assume a,
        assume a_pos,
        calc
            0   <= d.val    : and.elim_left (delta_near_zero d)
            ... = d.val + 0 : by rw add_zero
            ... < d.val + a : lt_add_left a_pos _
            ... = a + d.val : by rw add_comm
end

section -- 1.7
    example : forall a b : R, forall d e : subtype (Delta R), set.eq [[a ... b]] [[a + d.val ... b + e.val]] :=
        assume a b,
        assume d e,
        assume x,
        have forwards : set.mem x [[a ... b]] -> set.mem x [[a + d.val ... b + e.val]], from
            assume x_mem,
            have ge: a + d.val <= x, from
                have d.val <= 0, from and.elim_right (delta_near_zero d),
                calc a + d.val
                    <= a + 0 : by {apply le_add_left this}
                ... <= x     : by {simp, apply and.elim_left x_mem},
            have le: x <= b + e.val, from
                have 0 <= e.val, from and.elim_left (delta_near_zero e),
                calc
                  x <= b + 0     : by {simp, apply and.elim_right x_mem}
                ... <= b + e.val : le_add_left this,
            and.intro ge le,
        have backwards : set.mem x [[a + d.val ... b + e.val]] -> set.mem x [[a ... b]], from
            assume x_mem,
            have ge: a <= x, from
                have 0 <= d.val, from and.elim_left (delta_near_zero d),
                calc
                  a = a + 0      : by simp
                ... <= a + d.val : by {apply le_add_left this}
                ... <= x         : and.elim_left x_mem,
            have le: x <= b, from
                have e.val <= 0, from and.elim_right (delta_near_zero e),
                calc
                  x <= b + e.val : and.elim_right x_mem
                ... <= b + 0     : by {apply le_add_left this}
                ... = b          : by simp,
            and.intro ge le,
        iff.intro forwards backwards
end
