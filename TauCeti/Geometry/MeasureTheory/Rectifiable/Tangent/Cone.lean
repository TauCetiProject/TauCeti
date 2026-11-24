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
form is also used to construct measurable tangent projections in `Rectifiable.Tangent.Measurable`.

The measure-theoretic counterpart, used for approximate tangent planes of rectifiable sets, is the
cone-density condition `TauCeti.DensityZeroOutsideCones`: the part of a set `S` outside every cone
about the affine subspace `x + P` has `k`-dimensional density zero at `x`. It passes to subsets,
depends only on the set near `x`, and holds trivially for the whole space `P = ⊤` and, for every
`P`, at isolated points of `S`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (tangents to rectifiable sets).
* H. Federer, *Geometric Measure Theory*, §3.2 (decomposition of parametrizations).
-/

public section

open Set MeasureTheory Metric
open scoped NNReal ENNReal

/-- At Hausdorff-almost every point of a bi-Lipschitz patch, a Lipschitz parametrization is
differentiable, and its derivative range has the parameter dimension and contains the patch
locally in every cone. The parameter domain need not be measurable. -/
theorem LipschitzWith.ae_exists_fderiv_range_forall_infDist_le
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {K L : ℝ≥0} (hf : LipschitzWith K f)
    (hi : AntilipschitzWith L (s.domRestrict f)) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V), y ∈ f '' s →
      ∃ x ∈ s, f x = y ∧ DifferentiableAt ℝ f x ∧
        Module.finrank ℝ (fderiv ℝ f x).range = Module.finrank ℝ U ∧
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
  refine ⟨x, hx, rfl, hxreg.1, ?_, ?_⟩
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
  obtain ⟨x, _, _, _, hdim, hcone⟩ := hy hyimage
  exact ⟨(fderiv ℝ g x).range, hdim, hcone⟩

namespace TauCeti

open Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {k : ℕ}

/-- The **cone-density condition** of an approximate tangent plane: the part of `S` outside every
cone about the affine subspace `x + P` has `k`-dimensional density zero at `x`. Here `P` is an
arbitrary subspace, and the condition holds trivially for `P = ⊤`
(`TauCeti.densityZeroOutsideCones_top`). For a `k`-dimensional `P`, together with positive density,
which holds almost everywhere on a countably `k`-rectifiable set of locally finite measure, it says
that `P` is an approximate tangent plane of `S` at `x`. -/
def DensityZeroOutsideCones (k : ℕ) (S : Set V) (x : V) (P : Submodule ℝ V) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto (fun r ↦
    μHE[k] {z ∈ S ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
      volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0)

/-- Unfolding the cone-density condition. -/
theorem densityZeroOutsideCones_iff {S : Set V} {x : V} {P : Submodule ℝ V} :
    DensityZeroOutsideCones k S x P ↔ ∀ ε > (0 : ℝ), Tendsto (fun r ↦
      μHE[k] {z ∈ S ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- Every set satisfies the cone-density condition for the whole space: no point lies outside a
cone about it. -/
theorem densityZeroOutsideCones_top (S : Set V) (x : V) :
    DensityZeroOutsideCones k S x ⊤ := fun ε hε ↦ by
  refine tendsto_const_nhds.congr fun r ↦ ?_
  have hempty : {z ∈ S ∩ closedBall x r |
      ε * dist z x < infDist (z - x) ((⊤ : Submodule ℝ V) : Set V)} = ∅ := by
    ext z
    simp only [Submodule.top_coe, infDist_zero_of_mem (mem_univ _), mem_sep_iff,
      mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun _ ↦ mul_nonneg hε.le dist_nonneg
  rw [hempty, measure_empty, ENNReal.zero_div]

/-- The cone-density condition passes to subsets. -/
theorem DensityZeroOutsideCones.mono {S T : Set V} {x : V} {P : Submodule ℝ V}
    (h : DensityZeroOutsideCones k T x P) (hST : S ⊆ T) : DensityZeroOutsideCones k S x P :=
  fun ε hε ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ zero_le) fun _ ↦ ENNReal.div_le_div_right (measure_mono fun _ hz ↦ by
      exact ⟨⟨hST hz.1.1, hz.1.2⟩, hz.2⟩) _

/-- The cone-density condition at `x` only depends on the set near `x`. -/
theorem densityZeroOutsideCones_inter_iff {S B : Set V} {x : V} {P : Submodule ℝ V} {δ : ℝ}
    (hδ : 0 < δ) (hB : closedBall x δ ⊆ B) :
    DensityZeroOutsideCones k (S ∩ B) x P ↔ DensityZeroOutsideCones k S x P := by
  refine forall₂_congr fun ε _ ↦ tendsto_congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  congr 3
  ext z
  simp only [mem_inter_iff, and_congr_left_iff]
  intro _ hz
  exact and_iff_left (hB (closedBall_subset_closedBall hr.le hz))

/-- At an isolated point `x` of `S`, the cone-density condition holds for every subspace: near `x`
the only point of `S` is `x` itself, which lies in every cone about `x + P`. -/
theorem densityZeroOutsideCones_of_inter_closedBall_subset {S : Set V} {x : V} {δ : ℝ}
    (hδ : 0 < δ) (hS : S ∩ closedBall x δ ⊆ {x}) (P : Submodule ℝ V) :
    DensityZeroOutsideCones k S x P := by
  refine (densityZeroOutsideCones_inter_iff hδ subset_rfl).1 fun ε _ ↦
    tendsto_const_nhds.congr fun r ↦ ?_
  have hempty : {z ∈ S ∩ closedBall x δ ∩ closedBall x r |
      ε * dist z x < infDist (z - x) (P : Set V)} = ∅ := by
    refine eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain rfl : z = x := hS hz.1.1
    simp [infDist_zero_of_mem P.zero_mem] at hz
  rw [hempty, measure_empty, ENNReal.zero_div]

end TauCeti
