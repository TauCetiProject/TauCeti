/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.BruhatTits.Facet
import TauCeti.GroupTheory.BruhatTits.SL2

/-!
# Facets of the `SL₂` apartment

For the standard valuation of `SL₂(K)` the base point is special, so its facet is not an alcove.
When `ω (Kˣ) = ℤ`, the affine roots of either gradient have constants exactly `ℤ`, and a point is
in an alcove exactly when the roots take non-integral values at its displacement: the alcoves are
the open strips `n < a (x - φ) < n + 1`. A discrete valuation has an alcove above every facet.
-/

namespace TauCeti.BruhatTits

open DynkinType

variable {K : Type*} [Field K] (ω : AddValuation K (WithTop ℝ))
  (hω : ∃ x : K, x ≠ 0 ∧ ω x ≠ 0)

/-- The base point of the standard `SL₂` apartment is special: `ω 1 = 0` puts the wall of the
affine root `a + 0` through it, for both roots `a`. -/
example : (Apartment.base (Valuation.sl2 ℝ ω hω)).IsSpecial :=
    Apartment.isSpecial_iff.mpr fun i ↦ by
  have h : (0 : ℝ) ∈ (Valuation.sl2 ℝ ω hω).primedValueSet i := by
    simp only [Valuation.primedValueSet_eq_valueSet, Valuation.valueSet_sl2, Set.mem_ofPred_eq]
    exact ⟨1, one_ne_zero, by simp⟩
  exact ⟨⟨i, 0, h⟩, by simp, 1, one_pos, by simp⟩

/-- The facet of a special point of the `SL₂` apartment is not an alcove. -/
example (x : Apartment (Valuation.sl2 ℝ ω hω)) (hx : x.IsSpecial) : ¬ x.facet.IsAlcove :=
  hx.not_isAlcove

/-- If `ω (Kˣ) = ℤ`, a point of the `SL₂` apartment lies in an alcove exactly when both roots take
non-integral values at its displacement. -/
example (hℤ : {r : ℝ | ∃ x : K, x ≠ 0 ∧ ω x = r} = Set.range (Int.cast : ℤ → ℝ))
    (x : Apartment (Valuation.sl2 ℝ ω hω)) :
    x.facet.IsAlcove ↔ ∀ i (n : ℤ), (sl2RootPairing ℝ).root' i x.displacement ≠ n := by
  have hΓ (i) : (Valuation.sl2 ℝ ω hω).primedValueSet i = Set.range (Int.cast : ℤ → ℝ) := by
    rw [Valuation.primedValueSet_eq_valueSet, Valuation.valueSet_sl2, hℤ]
  simp only [Facet.isAlcove_facet_iff, Facet.mem_wall_iff, not_exists, AffineRoot.eval_def]
  constructor
  · intro h i n hn
    have hk : ((-n : ℤ) : ℝ) ∈ (Valuation.sl2 ℝ ω hω).primedValueSet i := hΓ i ▸ ⟨-n, rfl⟩
    exact h ⟨i, _, hk⟩ (by push_cast; rw [hn, add_neg_cancel])
  · intro h α hα
    obtain ⟨n, hn⟩ : α.constant ∈ Set.range (Int.cast : ℤ → ℝ) := hΓ _ ▸ α.constant_mem
    exact h α.gradient (-n) (by push_cast; linarith)

/-- If `ω` takes integer values on `Kˣ`, every facet of the `SL₂` apartment lies in the closure
of an alcove. -/
example (h : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ω x = ((n : ℝ) : WithTop ℝ))
    (F : Facet (Valuation.sl2 ℝ ω hω)) : ∃ C : Facet (Valuation.sl2 ℝ ω hω), C.IsAlcove ∧ F ≤ C :=
  Facet.exists_isAlcove_le (Valuation.isDiscrete_sl2_of_forall_exists_int ℝ ω hω h) F

end TauCeti.BruhatTits
