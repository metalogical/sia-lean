prelude
import init.algebra.field
import init.algebra.order

constant ℝ : Type

-- Smooth Infinitesimal Analysis
class sia α extends field α, strict_order α :=
-- Axiom 1 (field α)
-- Axiom 2 (strict_order α); we can't just use ordered_field due to antisymmetric ≤
(zero_lt_one :            0 < 1)
(add_lt_add_left :        ∀ a b : α, a < b → ∀ c : α, c + a < c + b)
(mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(neq_distinguishable :    ∀ a b : α, a ≠ b → a < b ∨ b < a)
-- Axiom 3
(exists_unique_sqrt :     ∀ a : α, ∃! b, b * b = a)
-- Axiom 4 (TODO Knock-Lawvere Axiom)
