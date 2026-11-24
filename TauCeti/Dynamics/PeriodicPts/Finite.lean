/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Filter.Cofinite

/-!
# Periods of distinct periodic points tend to infinity

Let `f : α → α` be a map each of whose positive iterates `f^[n]` has only finitely many fixed
points. Then `f` has only finitely many points of each positive period, so if `x i` are distinct
points of positive periods `d i`, the periods `d i` tend to infinity along the cofinite filter
(`Function.tendsto_cofinite_atTop_of_finite_ptsOfPeriod`). For instance, the closed orbits of the
suspension flow of a diffeomorphism with this property are finite in number below every period.
-/

public section

open Filter

namespace Function

/-- **Periods of distinct periodic points tend to infinity.** If each positive iterate of `f` has
only finitely many fixed points, and `x i` are distinct points of positive periods `d i`, then
`d i → ∞` along the cofinite filter: the fibre of `d` over `n > 0` lies in the preimage under `x`
of the finite set of fixed points of `f^[n]`. -/
theorem tendsto_cofinite_atTop_of_finite_ptsOfPeriod {α ι : Type*} {f : α → α}
    (hfin : ∀ n, 0 < n → (ptsOfPeriod f n).Finite) {x : ι → α} (hx : Injective x) {d : ι → ℕ}
    (hxd : ∀ i, IsPeriodicPt f (d i) (x i)) (hd : ∀ i, 0 < d i) :
    Tendsto d cofinite atTop := by
  rw [← Nat.cofinite_eq_atTop]
  refine Tendsto.cofinite_of_finite_preimage_singleton fun n ↦ Set.Finite.to_subtype ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.finite_empty.subset fun i hi ↦
      (hd i).ne' (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hi))
  · refine ((hfin n hn).preimage hx.injOn).subset fun i hi ↦ ?_
    rw [Set.mem_preimage, mem_ptsOfPeriod, ← Set.mem_singleton_iff.mp (Set.mem_preimage.mp hi)]
    exact hxd i

end Function
