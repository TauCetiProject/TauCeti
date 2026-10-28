/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Gluing functions along a sequence of sets

Functions prescribed on a sequence of measurable sets, which agree almost everywhere on the
pairwise intersections, come from a single function. This is the step which glues local limits,
obtained on each member of a compact exhaustion, into one function, as in the diagonal argument
for sequential compactness in `Lᵖ_loc`.

## Main results

* `TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter`: functions on a sequence of
  measurable sets which agree almost everywhere on the pairwise intersections glue to a single
  function.
-/

public section

namespace TauCeti

open MeasureTheory Filter

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Gluing along a sequence of sets.** If `L` is a sequence of measurable sets and the functions
`a m` are compatible, in the sense that `a k = a m` almost everywhere on `L k ∩ L m`, then a single
function agrees almost everywhere on each `L m` with `a m`. -/
theorem exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter {Y : Type*} {L : ℕ → Set X}
    (hL : ∀ m, MeasurableSet (L m)) {a : ℕ → X → Y}
    (ha : ∀ k m, a k =ᵐ[μ.restrict (L k ∩ L m)] a m) :
    ∃ v : X → Y, ∀ m, v =ᵐ[μ.restrict (L m)] a m := by
  classical
  -- On the points of `⋃ k, L k`, take `v = a k` for the least `k` with the point in `L k`.
  refine ⟨fun y => if h : ∃ m, y ∈ L m then a (Nat.find h) y else a 0 y, fun m => ?_⟩
  have hall : ∀ᵐ y ∂μ.restrict (L m), ∀ k, y ∈ L k → a k y = a m y := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' ((hL k).inter (hL m))).1 (ha k m)),
      ae_restrict_mem (hL m)] with y hy hym hyk using hy ⟨hyk, hym⟩
  filter_upwards [hall, ae_restrict_mem (hL m)] with y hy hym
  have h : ∃ m, y ∈ L m := ⟨m, hym⟩
  rw [dite_eq_left h]
  exact hy _ (Nat.find_spec h)

end TauCeti
