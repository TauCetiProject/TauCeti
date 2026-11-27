/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.AddHaar
public import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Affine invariance of weak derivatives under arbitrary Haar measures

Combining the linear weak chain rule between arbitrary finite-dimensional real normed spaces with
arbitrary additive Haar measures
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure` in
`TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving`) and translation invariance
(`TauCeti.HasWeakFDerivOn.comp_add_right` in `TauCeti.Analysis.Sobolev.WeakDeriv.Translation`)
gives the weak chain rule for general invertible affine maps `x ↦ e x + b` between different
spaces (`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add`).

## Main declarations

* `TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv_add`: affine chain rule between arbitrary
  finite-dimensional real normed spaces with arbitrary additive Haar measures.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti

section LinearEquiv

variable {E E₁ F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E₁} [ν.IsAddHaarMeasure]
  {U : Opens E} {V : Opens E₁} {u : E₁ → F} {D : E₁ → E₁ →L[ℝ] F}

/-- **The weak chain rule for affine isomorphisms between arbitrary finite-dimensional spaces.**
For any continuous linear equivalence `e : E ≃L[ℝ] E₁`, translation `b : E₁`, and additive
Haar measures `μ` on `E` and `ν` on `E₁`, if `x ↦ e x + b` maps `U` into `V`, then
`x ↦ u (e x + b)` has weak derivative `x ↦ D (e x + b) ∘L e` on `U`. -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add
    (h : HasWeakFDerivOn ν V u D) (e : E ≃L[ℝ] E₁) (b : E₁)
    (hUV : MapsTo (fun x => e x + b) U V) :
    HasWeakFDerivOn μ U (fun x => u (e x + b))
      fun x => (D (e x + b)).comp (e : E →L[ℝ] E₁) := by
  let W : Opens E₁ :=
    ⟨(· + b) ⁻¹' V, V.isOpen.preimage (continuous_id.add continuous_const)⟩
  have htrans : HasWeakFDerivOn ν W (fun y => u (y + b)) (fun y => D (y + b)) :=
    h.comp_add_right (mapsTo_preimage (· + b) V)
  exact htrans.comp_continuousLinearEquiv_of_isAddHaarMeasure e hUV

end LinearEquiv

end TauCeti
