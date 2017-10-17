prelude
import init.core
import init.algebra.order

universe u

class strict_order (t : Type u) extends has_le t, has_lt t :=
(lt_irrefl : forall a : t, not (a < a))
(lt_trans : forall a b c : t, a < b -> b < c -> a < c)
(le_iff_not_rev_lt : forall a b : t, a <= b <-> not (b < a))
(ne_distinguishable : forall a b : t, ne a b -> a < b \/ b < a)
