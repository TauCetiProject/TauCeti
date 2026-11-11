/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import TauCeti.Analysis.Calculus.FDeriv.ImageCone
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Tangent cones of bi-Lipschitz patches

Almost every point of a bi-Lipschitz image of a subset of a Euclidean space has a
plane of the parameter dimension about which the entire patch lies locally in arbitrarily
narrow cones. This is stronger than the vanishing of the measure outside each such cone.

The plane is the range of the derivative of a Lipschitz extension of the parametrization.
Rademacher's theorem and the zero-Jacobian image theorem remove the points where that range
might not have the required dimension. No local finiteness assumption is needed for this
patchwise assertion. It does not assert tangency of an arbitrary larger rectifiable set:
other patches must still be controlled by measure differentiation. The derivative-range
form is also used to construct measurable tangent projections in `Rectifiable.MeasurableTangent`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (tangents to rectifiable sets).
* H. Federer, *Geometric Measure Theory*, §3.2 (decomposition of parametrizations).
-/

public section

open Set MeasureTheory Metric
open scoped NNReal ENNReal

/-- At Hausdorff-almost every point of a bi-Lipschitz patch, the derivative range of a
Lipschitz parametrization has the parameter dimension and contains the patch locally in
every cone. The parameter domain need not be measurable. -/
theorem LipschitzWith.ae_exists_fderiv_range_forall_infDist_le
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {K L : ℝ≥0} (hf : LipschitzWith K f)
    (hi : AntilipschitzWith L (s.domRestrict f)) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V), y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ Module.finrank ℝ (fderiv ℝ f x).range = Module.finrank ℝ U ∧
        ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ f '' s, dist z y < r →
          infDist (z - y) ((fderiv ℝ f x).range : Set V) ≤ ε * dist z y := by
  have hgood : ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V),
      y ∉ f '' {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}ᶜ :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using
      hf.euclideanHausdorffMeasure_image_compl_setOf_regular)
  filter_upwards [hgood] with y hreg hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxreg : DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0 := by
    by_contra h
    exact hreg ⟨x, h, rfl⟩
  refine ⟨x, hx, rfl, ?_, ?_⟩
  · exact LinearMap.finrank_range_of_inj
      (((fderiv ℝ f x).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hxreg.2)
  · intro ε hε
    exact hxreg.1.hasFDerivAt.hasFDerivWithinAt.exists_pos_forall_infDist_range_le hx hi hε

/-- At Hausdorff-almost every point of a bi-Lipschitz patch, the patch is locally
contained in every cone about some plane of the parameter dimension. Hausdorff measure
has the normalized Euclidean convention. -/
theorem LipschitzOnWith.ae_exists_submodule_forall_infDist_le
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hi : AntilipschitzWith L (s.domRestrict f)) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V), y ∈ f '' s →
      ∃ P : Submodule ℝ V, Module.finrank ℝ P = Module.finrank ℝ U ∧
        ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ f '' s, dist z y < r →
          infDist (z - y) (P : Set V) ≤ ε * dist z y := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_finite_dimension
  have himage : f '' s = g '' s := image_congr hfg
  have hi' : AntilipschitzWith L (s.domRestrict g) := by
    intro x y
    simpa only [domRestrict_apply, ← hfg x.property, ← hfg y.property] using hi x y
  rw [himage]
  filter_upwards [hg.ae_exists_fderiv_range_forall_infDist_le hi'] with y hy hyimage
  obtain ⟨x, _, _, hdim, hcone⟩ := hy hyimage
  exact ⟨(fderiv ℝ g x).range, hdim, hcone⟩
