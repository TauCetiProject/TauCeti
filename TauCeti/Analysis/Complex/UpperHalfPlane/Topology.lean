/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Topology of the upper half-plane

Every real point lies in the closure of the open upper half-plane, so limits taken along the
half-plane at a real point are well posed.  The half-plane is also unbounded, so the filter along
which it approaches infinity is nontrivial and limits taken along it are unique.

A function on the upper half-plane, extended to `ℂ` by `ofComplex`, is periodic with a real
period exactly when the original function is invariant under the corresponding translation.

## Main declarations

* `Real.nhdsWithin_upperHalfPlaneSet_neBot`.
* `TauCeti.cobounded_inf_principal_upperHalfPlaneSet_neBot`.
* `TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft the periodicity criterion ports onto the current
  Mathlib pin.
-/

public section

open Bornology Filter Topology UpperHalfPlane

namespace Real

/-- Every real point is in the closure of the open upper half-plane, so limits along the
half-plane at a real point are well posed. -/
theorem nhdsWithin_upperHalfPlaneSet_neBot (x : ℝ) :
    (𝓝[upperHalfPlaneSet] ((x : ℂ))).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by simp [upperHalfPlaneSet])

end Real

namespace TauCeti

/-- The upper half-plane is unbounded, so the filter along which it approaches infinity is
nontrivial and limits taken along it are unique. -/
instance cobounded_inf_principal_upperHalfPlaneSet_neBot :
    (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet).NeBot := by
  -- The imaginary axis runs off to infinity inside the half-plane, so the filter it pushes
  -- forward from `atTop` is below both factors.
  have hcob : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa using tendsto_abs_atTop_atTop
  refine Filter.neBot_of_le (f := map (fun t : ℝ => (t : ℂ) * Complex.I) atTop)
    (le_inf hcob ?_)
  rw [le_principal_iff, mem_map]
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Set.mem_preimage, upperHalfPlaneSet, Set.mem_ofPred_eq]
  simpa using ht

end TauCeti

namespace TauCeti.UpperHalfPlane

/-- A function `ℍ → α`, extended to `ℂ` via `ofComplex`, is periodic with real period `c` iff
the original function is invariant under translation by `c`. -/
lemma periodic_comp_ofComplex_iff {α : Type*} {f : ℍ → α} {c : ℝ} :
    Function.Periodic (f ∘ ofComplex) c ↔ ∀ τ : ℍ, f (c +ᵥ τ) = f τ := by
  constructor
  · intro h τ
    have := h ↑τ
    simp only [Function.comp_apply] at this
    -- Identify the translated coercion with the coercion of the translate, so both
    -- `ofComplex` applications land back on `ℍ`.
    rwa [show (τ : ℂ) + ↑c = ↑(c +ᵥ τ) by rw [coe_vadd]; ring, ofComplex_apply,
      ofComplex_apply] at this
  · intro h w
    rcases le_or_gt w.im 0 with hw | hw
    · exact congrArg f (ofComplex_apply_eq_of_im_nonpos (by simpa using hw) hw)
    · have hw' : 0 < (w + ↑c).im := by simpa using hw
      simp only [Function.comp_apply]
      -- Both points have positive imaginary part; identify the shifted point with the
      -- vector translate so the hypothesis applies.
      rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw,
        show (⟨w + ↑c, hw'⟩ : ℍ) = c +ᵥ (⟨w, hw⟩ : ℍ) from _root_.UpperHalfPlane.ext
          (by simp [add_comm])]
      exact h _

end TauCeti.UpperHalfPlane

end
