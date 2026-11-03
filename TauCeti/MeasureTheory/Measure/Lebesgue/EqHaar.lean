/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Haar measure under dilations and affine maps

The dimension root of outer volume scales by the absolute value of a real dilation
in a positive-dimensional real inner product space. The identity applies to arbitrary
sets and infinite outer volumes, and supplies the scaling law for volume inequalities.

An affine map of a finite-dimensional real normed space multiplies every additive Haar measure
by the absolute value of the determinant of its linear part
(`MeasureTheory.Measure.addHaar_image_affineMap`, and
`MeasureTheory.Measure.addHaar_image_affineEquiv` for affine equivalences), the affine form of
Mathlib's `MeasureTheory.Measure.addHaar_image_linearMap`.

A linear map into a finite-dimensional real normed space that is not surjective has almost every
fibre empty for every additive Haar measure on the codomain
(`LinearMap.ae_preimage_singleton_eq_empty`), since its range is a strict subspace.

For an invertible real square matrix `A` and nonnegative bounds `a i`, the region
`{x | ∀ i, |(A *ᵥ x) i| ≤ a i}` cut out by the linear forms of `A` has volume
`2 ^ n * (∏ i, a i) / |det A|`, where `n` is the size of `A`
(`Matrix.volume_setOf_forall_abs_mulVec_le`). It is the preimage of a coordinate box under `A`;
this is the volume computation behind Minkowski's linear forms theorem.

We also bound the additive Haar measure of the closure of a set in a finite-dimensional real
normed space by the measure of the unit ball times the dimension power of its diameter. This is
the elementary estimate converting coverings by sets of small diameter into measure bounds.
Combined with the diameter bound for Lipschitz images, it bounds the measure of the closure of
the image of a set under a Lipschitz map.

An element of finite order acting linearly on a finite-dimensional real space preserves every
additive Haar measure, because its determinant has finite order and so absolute value one
(`MeasureTheory.Measure.addHaar_preimage_smul_of_isOfFinOrder`). Hence a finite group acting
linearly preserves every additive Haar measure
(`MeasureTheory.Measure.smulInvariantMeasure_addHaar`).
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dimension-root volume scales linearly under every real dilation, including zero.
This identity holds for arbitrary sets and infinite outer volumes. -/
theorem volume_smul_rpow {A : Set E} (hn : Module.finrank ℝ E ≠ 0) (c : ℝ) :
    volume (c • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      ENNReal.ofReal |c| * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  rw [Measure.addHaar_smul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    abs_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (abs_nonneg c) hn]

end TauCeti

namespace MeasureTheory.Measure

section Affine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- The image of a set under an affine map has Haar measure equal to the absolute value of the
determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineMap (f : F →ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f.linear| * μ s := by
  have hf : f '' s = (fun y ↦ y + f 0) '' (f.linear '' s) := by
    rw [image_image]
    exact image_congr fun x _ ↦ by simpa using f.map_vadd 0 x
  rw [hf, image_add_right, measure_preimage_add_right, addHaar_image_linearMap]

/-- The image of a set under an affine equivalence has Haar measure equal to the absolute value of
the determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineEquiv (f : F ≃ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f.linear : F →ₗ[ℝ] F)| * μ s :=
  addHaar_image_affineMap μ (f : F →ᵃ[ℝ] F) s

end Affine

section Diameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The closure of a set of diameter `d` in an `n`-dimensional real normed space has additive
Haar measure at most `μ (ball 0 1) * d ^ n`, since it lies in a closed ball of radius `d`.
This holds for every set, including empty and unbounded ones. -/
theorem addHaar_closure_le_mul_ediam_pow (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) :
    μ (closure s) ≤ μ (Metric.ball 0 1) * Metric.ediam s ^ Module.finrank ℝ E := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : Metric.ediam s = ∞
  · have hE : Module.finrank ℝ E ≠ 0 := by
      intro hE
      have : Subsingleton E := Module.finrank_zero_iff.1 hE
      rw [Metric.ediam_subsingleton Set.subsingleton_of_subsingleton] at hs
      exact ENNReal.zero_ne_top hs
    rw [hs, ENNReal.top_pow hE, ENNReal.mul_top (Metric.measure_ball_pos μ 0 one_pos).ne']
    exact le_top
  have hb : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.2 hs
  have hsub : closure s ⊆ Metric.closedBall x (Metric.diam s) := fun y hy ↦ by
    rw [Metric.mem_closedBall, ← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hb.closure hy (subset_closure hx)
  calc μ (closure s) ≤ μ (Metric.closedBall x (Metric.diam s)) := measure_mono hsub
    _ = μ (Metric.ball 0 1) * Metric.ediam s ^ Module.finrank ℝ E := by
      rw [addHaar_closedBall μ x Metric.diam_nonneg, mul_comm,
        ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam, ENNReal.ofReal_toReal hs]

end Diameter

section FiniteOrder

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- An element of finite order acting linearly on a finite-dimensional real space preserves
every additive Haar measure. Its determinant has finite order in `ℝ`, hence absolute value
one. -/
theorem addHaar_preimage_smul_of_isOfFinOrder [Monoid G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] {g : G} (hg : IsOfFinOrder g) (s : Set E) :
    μ ((g • ·) ⁻¹' s) = μ s := by
  set L := DistribMulAction.toModuleEnd ℝ E g
  have habs : |LinearMap.det L| = 1 :=
    ((((absHom (α := ℝ)).toMonoidHom).comp
      (LinearMap.det.comp (DistribMulAction.toModuleEnd ℝ E))).isOfFinOrder hg).eq_one
      (abs_nonneg _)
  have hdet : LinearMap.det L ≠ 0 := fun h => by simp [h] at habs
  have h := addHaar_preimage_linearMap μ hdet s
  rwa [abs_inv, habs, inv_one, ENNReal.ofReal_one, one_mul] at h

/-- A finite group acting linearly on a finite-dimensional real space preserves every additive
Haar measure. -/
theorem smulInvariantMeasure_addHaar [Group G] [Finite G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] : SMulInvariantMeasure G E μ :=
  ⟨fun g s _ => addHaar_preimage_smul_of_isOfFinOrder μ (isOfFinOrder_of_finite g) s⟩

end FiniteOrder

end MeasureTheory.Measure

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A linear map that is not surjective has almost every fibre empty, for every additive Haar
measure on its finite-dimensional codomain. -/
theorem ae_preimage_singleton_eq_empty (μ : Measure F) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] F)
    (hL : ¬Function.Surjective L) :
    ∀ᵐ y ∂μ, L ⁻¹' {y} = ∅ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (Measure.addHaar_submodule μ _ (mt range_eq_top.mp hL))] with y hy
  exact eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx⟩

end LinearMap

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The region cut out by the linear forms of an invertible real square matrix `A`: for
nonnegative bounds `a i`, the set of `x : ι → ℝ` with `|(A *ᵥ x) i| ≤ a i` for every `i` has
volume `2 ^ n * (∏ i, a i) / |det A|`, where `n` is the cardinality of `ι`. This includes the case
of an empty `ι`, where both sides are `1`. -/
theorem volume_setOf_forall_abs_mulVec_le (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) {a : ι → ℝ}
    (ha : 0 ≤ a) :
    volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i} =
      ENNReal.ofReal (2 ^ Fintype.card ι * (∏ i, a i) / |A.det|) := by
  have hS : {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i} = toLin' A ⁻¹' Icc (-a) a := by
    ext x
    simp [abs_le, Pi.le_def, forall_and]
  rw [hS, Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', Real.volume_Icc_pi]
  simp_rw [Pi.neg_apply, sub_neg_eq_add, ← two_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ mul_nonneg zero_le_two (ha i),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, inv_mul_eq_div]

end Matrix

namespace LipschitzOnWith

open MeasureTheory
open scoped NNReal

variable {X E : Type*} [PseudoEMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The closure of the image of a set `A` under a `K`-Lipschitz map into an `n`-dimensional real
normed space has additive Haar measure at most `μ (ball 0 1) * K ^ n * ediam A ^ n`. -/
theorem addHaar_closure_image_le_mul_ediam_pow (μ : Measure E) [μ.IsAddHaarMeasure] {K : ℝ≥0}
    {f : X → E} {A : Set X} (hf : LipschitzOnWith K f A) :
    μ (closure (f '' A)) ≤
      μ (Metric.ball 0 1) * K ^ Module.finrank ℝ E * Metric.ediam A ^ Module.finrank ℝ E := by
  have hdiam : Metric.ediam (f '' A) ≤ K * Metric.ediam A :=
    Metric.ediam_image_le_iff.2 fun x hx x' hx' ↦
      (hf hx hx').trans (by gcongr; exact Metric.edist_le_ediam_of_mem hx hx')
  calc μ (closure (f '' A)) ≤ μ (Metric.ball 0 1) * Metric.ediam (f '' A) ^ Module.finrank ℝ E :=
        Measure.addHaar_closure_le_mul_ediam_pow μ _
    _ ≤ μ (Metric.ball 0 1) * (K * Metric.ediam A) ^ Module.finrank ℝ E := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

end LipschitzOnWith
