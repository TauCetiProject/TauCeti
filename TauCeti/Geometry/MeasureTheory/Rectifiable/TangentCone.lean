/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
public import TauCeti.Analysis.Calculus.FDeriv.ImageCone
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Tangent cones of bi-Lipschitz patches

Almost every point of a bi-Lipschitz image of a subset of a Euclidean space has a
plane of the parameter dimension about which the entire patch lies locally in arbitrarily
narrow cones. This is stronger than the vanishing of the measure outside each such cone.

The plane is the range of the derivative of a Lipschitz extension of the parametrization.
Rademacher's theorem and the zero-Jacobian image theorem remove the points where that range
might not have the required dimension. No local finiteness assumption is needed for this
patchwise assertion. It does not assert tangency of an arbitrary larger rectifiable set:
other patches must still be controlled by measure differentiation. We also obtain a
countable Borel cover, up to a null set, whose pieces have pointwise cone containment.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (tangents to rectifiable sets).
* H. Federer, *Geometric Measure Theory*, §3.2 (decomposition of parametrizations).
-/

public section

open Set MeasureTheory Metric
open scoped NNReal ENNReal

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
  have hnull := hg.euclideanHausdorffMeasure_image_compl_setOf_regular
  have hgood : ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V),
      y ∉ g '' {x | DifferentiableAt ℝ g x ∧ (fderiv ℝ g x).normDet ≠ 0}ᶜ :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hnull)
  filter_upwards [hgood] with y hreg hy
  rw [himage] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  have hxreg : DifferentiableAt ℝ g x ∧ (fderiv ℝ g x).normDet ≠ 0 := by
    by_contra h
    exact hreg ⟨x, h, rfl⟩
  refine ⟨LinearMap.range (fderiv ℝ g x).toLinearMap, ?_, ?_⟩
  · exact LinearMap.finrank_range_of_inj
      (((fderiv ℝ g x).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hxreg.2)
  · intro ε hε
    exact hxreg.1.hasFDerivAt.hasFDerivWithinAt.exists_pos_forall_infDist_range_le hx hi' hε

namespace TauCeti

/-- A countably rectifiable set is covered, up to a Hausdorff-null set, by countably many
Borel pieces each of which has pointwise cone containment about a plane of the correct
dimension. The pieces may extend beyond the original set. The plane and the neighborhood
radius may depend on the point; no measurable choice of planes is asserted. -/
theorem CountablyRectifiable.exists_measurable_cover_forall_infDist_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) :
    ∃ T : ℕ → Set V, (∀ n, MeasurableSet (T n)) ∧
      μHE[k] (s \ ⋃ n, T n) = 0 ∧
      ∀ n, ∀ y ∈ T n, ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
        ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ T n, dist z y < r →
          infDist (z - y) (P : Set V) ≤ ε * dist z y := by
  classical
  obtain ⟨A, F, hAm, hbi, hcover⟩ := hs.exists_bilipschitz_cover
  choose K L hLip hAnti using hbi
  let S (n : ℕ) := F n '' A n
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    (hAm n).image_of_continuousOn_injOn (hLip n).continuous.continuousOn
      (injOn_iff_injective.mpr (hAnti n).injective)
  let G (n : ℕ) : Set V := {y | ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
    ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ S n, dist z y < r →
      infDist (z - y) (P : Set V) ≤ ε * dist z y}
  have hgood (n : ℕ) : ∀ᵐ y ∂(μHE[k] : Measure V).restrict (S n), y ∈ G n := by
    apply (ae_restrict_iff' (hSm n)).mpr
    simpa only [finrank_euclideanSpace_fin, G, S, mem_ofPred_eq] using
      (hLip n).lipschitzOnWith.ae_exists_submodule_forall_infDist_le (hAnti n)
  -- Choose measurable full-measure subsets where cone containment holds pointwise.
  choose B hBae hBm hBG using fun n ↦ (hgood n).exists_measurable_mem
  let T (n : ℕ) := S n ∩ B n
  have hST (n : ℕ) : S n ≤ᵐ[μHE[k]] T n := by
    filter_upwards [(ae_restrict_iff' (hSm n)).mp (hBae n)] with y hy hys
    exact ⟨hys, hy hys⟩
  refine ⟨T, fun n ↦ (hSm n).inter (hBm n), ?_, ?_⟩
  · apply ae_le_set.mp
    exact (ae_le_set.mpr hcover).trans (Filter.EventuallySubset.countable_iUnion hST)
  · intro n y hy
    obtain ⟨P, hdim, hP⟩ := hBG n y hy.2
    exact ⟨P, hdim, fun ε hε ↦ by
      obtain ⟨r, hr, hcone⟩ := hP ε hε
      exact ⟨r, hr, fun z hz ↦ hcone z hz.1⟩⟩

end TauCeti
