import .core
import .basic
import .util

section
parameters {R : Type} [sia R]
open sia

@[reducible] private def Delta := Delta R
@[reducible] private def DeltaT := subtype Delta


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
    example : forall d: subtype Delta, not (d.val < (0: R) \/ 0 < d.val) :=
        assume d,
        have 0 <= d.val /\ d.val <= 0, from delta_near_zero d,
        not_or this.left this.right

    example : forall d: subtype Delta, forall a: R, Delta (d.val * a) :=
        assume d,
        assume a,
        have d.val * d.val = 0, from d.property,
        show (d.val * a) * (d.val * a) = 0, from calc
            (d.val * a) * (d.val * a)
                = d.val * d.val * a * a : by simp
            ... = 0 * a * a             : by rw this
            ... = 0                     : by simp [zero_mul]

    example : forall d: subtype Delta, forall a: R, 0 < a -> 0 < a + d.val :=
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
    example : forall a b : R, forall d e : subtype Delta, [[a ... b]] = [[a + d.val ... b + e.val]] :=
        assume a b,
        assume d e,
        have set.eq [[a ... b]] [[a + d.val ... b + e.val]], from
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
            iff.intro forwards backwards,
        set.ext this
end

section -- 1.8
    @[reducible]
    def rigid_rod : Type := DeltaT -> R

    private meta def lift_funext : tactic unit := `[ intro f, intros, apply funext, intro d ]

    instance rigid_rod_ring [sia R] : ring rigid_rod := {
        add := fun f g, fun d, f d + g d,
        zero := fun d, 0,
        neg := fun f, fun d, -(f d),
        mul := fun f g, fun d, f d * g d,
        one := fun d, 1,

        add_assoc := by {lift_funext, show _ + _ = _ + _, rw add_assoc},
        add_comm := by {lift_funext, show _ + _ = _ + _, rw add_comm},
        add_zero := by {lift_funext, show f d + 0 = f d, rw add_zero},
        zero_add := by {lift_funext, show 0 + f d = f d, rw zero_add},
        add_left_neg := by {lift_funext, show -(f d) + f d = 0, rw add_left_neg},
        mul_assoc := by {lift_funext, show _ * _ = _ * _, rw mul_assoc},
        one_mul := by {lift_funext, show 1 * f d = f d, rw one_mul},
        mul_one := by {lift_funext, show f d * 1 = f d, rw mul_one},
        left_distrib := by {lift_funext, show _ * _ = _ + _, rw left_distrib},
        right_distrib := by {lift_funext, show _ * _ = _ + _, rw right_distrib},
    }

    instance prod_ring {T : Type} [ring T] : ring (T × T) := {
        add := fun x y, (x.fst + y.fst, x.snd + y.snd),
        zero := (0, 0),
        neg := fun x, (-x.fst, -x.snd),
        mul := fun x y, (x.fst * y.fst, x.fst * y.snd + x.snd * y.fst),
        one := (1, 0),

        add_assoc := by {intros, simp},
        add_comm := by {intros, show (_, _) = (_, _), simp},
        add_zero := by {intro x, cases x, show (_, _) = (_, _), simp},
        zero_add := by {intro x, cases x, show (_, _) = (_, _), simp},
        add_left_neg := by {intro x, cases x, show (_, _) = (_, _), simp},
        mul_assoc := by {intros, simp [left_distrib, right_distrib]},
        one_mul := by {intro x, cases x, show (_, _) = (_, _), simp},
        mul_one := by {intro x, cases x, show (_, _) = (_, _), simp},
        left_distrib := by {intros, simp [left_distrib]},
        right_distrib := by {intros, simp [right_distrib]},
    }

    @[reducible]
    def iso : R × R -> rigid_rod := fun ab, fun d, ab.fst + ab.snd * d.val

    example : forall x y: R × R, iso (x + y) = iso x + iso y := begin
        intros,
        apply funext,
        intro,
        show (_ + _) + (_ + _) * _ = (_ + _ * _) + (_ + _ * _), -- reduce iso
        simp [left_distrib]
    end

    example : forall x y: R × R, iso (x * y) = iso x * iso y := begin
        intros,
        apply funext,
        intro d,
        have sq_zero: d.val * d.val = 0, from d.property,
        show (_ * _) + (_ + _) * _ = (_ + _ * _) * (_ + _ * _), -- reduce iso
        simp [left_distrib, sq_zero],
    end

    example : iso 1 = (1: rigid_rod) := begin
        apply funext,
        intro,
        show (_, _).fst + (_, _).snd * _ = (1 : R),
        simp
    end
end

section -- 1.9
    lemma microproduct_not_zero : not (forall e n : subtype Delta, e.val * n.val = 0) :=
        assume bad,
        have forall d e : subtype Delta, d.val = e.val, from
            assume d e,
            have forall n : subtype Delta, d.val * n.val = e.val * n.val, from 
                assume n,
                (calc
                    d.val * n.val = 0     : bad d n
                    ...   = e.val * n.val : eq.symm (bad e n)
                ),
            sia.microcancellation this,
        sia.delta_nondegenerate this

    example : not (sia.microstable Delta) :=
        assume bad,
        have forall a b : subtype Delta, a.val * b.val = 0, from
            assume a b,
            have a_nilpotent : a.val * a.val = 0, from a.property,
            have b_nilpotent : b.val * b.val = 0, from b.property,
            have sum_nilpotent : (a.val + b.val) * (a.val + b.val) = 0, from bad a b,
            have ne (2 : R) (0 : R), from ne.symm (sia.lt_ne (calc (0:R)
                < 1     : sia.lt_zero_one
            ... = 1 + 0 : by simp
            ... < 1 + 1 : sia.lt_add_left sia.lt_zero_one 1)),
            (calc a.val * b.val
                = (a.val * b.val) * 2 / 2 : by rw (mul_div_cancel _ this)
            ... = (a.val * b.val) * (1 + 1) / 2 : by refl
            ... = (a.val * b.val + a.val * b.val) / 2 : by rw [left_distrib, mul_one]
            ... = ((0 + a.val * b.val) + (a.val * b.val + 0)) / 2 : by simp
            ... = ((a.val * a.val + a.val * b.val) + (a.val * b.val + b.val * b.val)) / 2 : by rw [a_nilpotent, b_nilpotent]
            ... = ((a.val + b.val) * (a.val + b.val)) / 2 : by simp [left_distrib, right_distrib]
            ... = 0 / 2 : by rw [sum_nilpotent]
            ... = 0 : by rw [zero_div]),
        microproduct_not_zero this

    example : not (forall x y : R, x * x + y * y = 0 -> x * x = 0) :=
        assume bad,
        sorry
end

end
