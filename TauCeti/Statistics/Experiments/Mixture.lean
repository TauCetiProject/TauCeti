/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Statistics.Experiments.Density

import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Countable mixtures and the Halmos–Savage domination lemma

This file defines countable convex mixtures of parametric families of measures using the geometric
weights `TauCeti.mixtureWeight n = (2 ^ (n + 1))⁻¹`:
`TauCeti.countableMixture P θs = Measure.sum fun n ↦ mixtureWeight n • P (θs n)`.

It develops the basic API for `mixtureWeight` and `countableMixture` (total weight `1`, null sets
and almost-everywhere properties, preservation of probability/s-finite measures, pushforwards,
composition products, and densities) and proves the Halmos–Savage domination lemma
(`TauCeti.exists_absolutelyContinuous_countableMixture_of_withDensity`,
`TauCeti.exists_absolutelyContinuous_countableMixture_of_absolutelyContinuous`, and
`TauCeti.exists_absolutelyContinuous_countableMixture`): any nonempty family of measures with
densities with respect to an s-finite reference measure `μ` (or that are absolutely continuous and
admit a Lebesgue decomposition relative to `μ`, which Mathlib supplies automatically when `μ` and
each `P θ` are σ-finite) is dominated by a countable mixture of members of the family.

The domination proof reduces the covering of the positivity sets `{x | 0 < g θ x}` to Mathlib's
`MeasureTheory.Measure.exists_ae_subset_biUnion_countable`.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Lemma 1.2.1 (p. 4).
* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorem A.78 (p. 600).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ### Geometric mixture weights -/

/-- The geometric weights `2 ^ (-(n + 1))` used to form countable mixtures of measures. -/
def mixtureWeight (n : ℕ) : ℝ≥0∞ := (2 ^ (n + 1))⁻¹

/-- Unfolding lemma for `mixtureWeight`. -/
theorem mixtureWeight_def (n : ℕ) : mixtureWeight n = (2 ^ (n + 1))⁻¹ :=
  (rfl)

/-- Every mixture weight is strictly positive. -/
theorem mixtureWeight_pos (n : ℕ) : 0 < mixtureWeight n := by
  rw [mixtureWeight_def]
  exact ENNReal.inv_pos.mpr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)

/-- Every mixture weight is nonzero. -/
theorem mixtureWeight_ne_zero (n : ℕ) : mixtureWeight n ≠ 0 :=
  (mixtureWeight_pos n).ne'

/-- Every mixture weight is finite. -/
theorem mixtureWeight_lt_top (n : ℕ) : mixtureWeight n < ∞ := by
  rw [mixtureWeight_def]
  exact ENNReal.inv_lt_top.mpr (by positivity)

/-- Every mixture weight is not `∞`. -/
theorem mixtureWeight_ne_top (n : ℕ) : mixtureWeight n ≠ ∞ :=
  (mixtureWeight_lt_top n).ne

/-- The geometric mixture weights sum to `1`. -/
@[simp]
theorem tsum_mixtureWeight : ∑' n, mixtureWeight n = 1 := by
  simp_rw [mixtureWeight_def, ENNReal.inv_pow]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (OfNat.ofNat_ne_zero 2) ENNReal.ofNat_ne_top

/-- Real value of `mixtureWeight n`. -/
theorem toReal_mixtureWeight (n : ℕ) : (mixtureWeight n).toReal = ((2 : ℝ) ^ (n + 1))⁻¹ := by
  rw [mixtureWeight_def, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- The real-valued mixture weights are summable. -/
theorem summable_toReal_mixtureWeight : Summable fun n ↦ (mixtureWeight n).toReal :=
  ENNReal.summable_toReal (by simp)

/-- The real-valued mixture weights sum to `1`. -/
@[simp]
theorem tsum_toReal_mixtureWeight : ∑' n, (mixtureWeight n).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq mixtureWeight_ne_top, tsum_mixtureWeight, ENNReal.toReal_one]

/-! ### Countable mixtures of measures -/

/-- The countable mixture `∑' n, mixtureWeight n • P (θs n)` of a parametric family `P` along a
sequence of parameters `θs`. -/
def countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) : Measure X :=
  Measure.sum fun n ↦ mixtureWeight n • P (θs n)

/-- Unfolding lemma for `countableMixture`. -/
theorem countableMixture_def (P : Θ → Measure X) (θs : ℕ → Θ) :
    countableMixture P θs = Measure.sum fun n ↦ mixtureWeight n • P (θs n) :=
  (rfl)

/-- Evaluation of a countable mixture on an arbitrary set. -/
theorem countableMixture_apply (P : Θ → Measure X) (θs : ℕ → Θ) (s : Set X) :
    countableMixture P θs s = ∑' n, mixtureWeight n * P (θs n) s := by
  rw [countableMixture_def, Measure.sum_apply_of_countable]
  simp_rw [smul_apply, smul_eq_mul]

/-- A set has measure zero under `countableMixture P θs` if and only if it has measure zero under
every component `P (θs n)`. -/
theorem countableMixture_apply_eq_zero_iff (P : Θ → Measure X) (θs : ℕ → Θ) {s : Set X} :
    countableMixture P θs s = 0 ↔ ∀ n, P (θs n) s = 0 := by
  rw [countableMixture_def, Measure.sum_apply_eq_zero]
  simp [mixtureWeight_ne_zero]

/-- A property holds almost everywhere under `countableMixture P θs` if and only if it holds almost
everywhere under every component `P (θs n)`. -/
theorem ae_countableMixture_iff (P : Θ → Measure X) (θs : ℕ → Θ) {p : X → Prop} :
    (∀ᵐ x ∂countableMixture P θs, p x) ↔ ∀ n, ∀ᵐ x ∂P (θs n), p x :=
  countableMixture_apply_eq_zero_iff P θs

/-- A countable mixture of a constant family equals that measure. -/
@[simp]
theorem countableMixture_const_left (μ : Measure X) (θs : ℕ → Θ) :
    countableMixture (fun _ ↦ μ) θs = μ := by
  ext s _
  rw [countableMixture_apply, ENNReal.tsum_mul_right, tsum_mixtureWeight, one_mul]

/-- A countable mixture along a constant parameter sequence equals that member of the family. -/
@[simp]
theorem countableMixture_const_right (P : Θ → Measure X) (θ₀ : Θ) :
    countableMixture P (fun _ ↦ θ₀) = P θ₀ :=
  countableMixture_const_left (P θ₀) (fun _ ↦ θ₀)

/-- A countable mixture of probability measures is a probability measure. -/
instance isProbabilityMeasure_countableMixture (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (θs : ℕ → Θ) :
    IsProbabilityMeasure (countableMixture P θs) :=
  ⟨by rw [countableMixture_apply]; simp⟩

/-- A countable mixture of s-finite measures is s-finite. -/
instance sFinite_countableMixture (P : Θ → Measure X) [∀ θ, SFinite (P θ)] (θs : ℕ → Θ) :
    SFinite (countableMixture P θs) := by
  rw [countableMixture_def]
  infer_instance

/-- Every component `P (θs n)` is absolutely continuous with respect to `countableMixture P θs`. -/
theorem absolutelyContinuous_countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) (n : ℕ) :
    P (θs n) ≪ countableMixture P θs :=
  Measure.AbsolutelyContinuous.mk fun _ _ h0 ↦
    (countableMixture_apply_eq_zero_iff P θs).mp h0 n

/-- If every component `P (θs n)` is absolutely continuous with respect to `μ`, then so is
`countableMixture P θs`. -/
theorem countableMixture_absolutelyContinuous {P : Θ → Measure X} {θs : ℕ → Θ} {μ : Measure X}
    (h : ∀ n, P (θs n) ≪ μ) :
    countableMixture P θs ≪ μ :=
  Measure.AbsolutelyContinuous.mk fun _ _ h0 ↦
    (countableMixture_apply_eq_zero_iff P θs).mpr fun n ↦ h n h0

/-- Pushforward commutes with taking a countable mixture. -/
theorem map_countableMixture {P : Θ → Measure X} {θs : ℕ → Θ} {φ : X → Y}
    (hφ : AEMeasurable φ (countableMixture P θs)) :
    (countableMixture P θs).map φ = countableMixture (fun θ ↦ (P θ).map φ) θs := by
  rw [countableMixture_def, countableMixture_def, Measure.map_sum (by rwa [← countableMixture_def])]
  exact Measure.sum_congr fun n ↦
    Measure.map_smul _ (hφ.mono_ac (absolutelyContinuous_countableMixture P θs n))

/-- Composition product with an s-finite kernel distributes over a countable mixture on the left. -/
theorem countableMixture_compProd (P : Θ → Measure X) [∀ θ, SFinite (P θ)] (θs : ℕ → Θ)
    (κ : Kernel X Y) [IsSFiniteKernel κ] :
    countableMixture P θs ⊗ₘ κ = countableMixture (fun θ ↦ P θ ⊗ₘ κ) θs := by
  rw [countableMixture_def, countableMixture_def, Measure.compProd_sum_left]
  exact Measure.sum_congr fun n ↦ Measure.compProd_smul_left _

/-- The countable mixture of `withDensity` measures has the mixed `ℝ≥0∞`-valued density. -/
theorem countableMixture_withDensity (μ : Measure X) (g : Θ → X → ℝ≥0∞)
    (hg : ∀ θ, Measurable (g θ)) (θs : ℕ → Θ) :
    countableMixture (fun θ ↦ μ.withDensity (g θ)) θs =
      μ.withDensity (fun x ↦ ∑' n, mixtureWeight n * g (θs n) x) := by
  have htsum : (fun x ↦ ∑' n, mixtureWeight n * g (θs n) x) =
      ∑' n, fun x ↦ mixtureWeight n * g (θs n) x :=
    funext fun x ↦ (ENNReal.tsum_apply (f := fun n x ↦ mixtureWeight n * g (θs n) x) (x := x)).symm
  rw [countableMixture_def, htsum,
    withDensity_tsum (f := fun n x ↦ mixtureWeight n * g (θs n) x)
      fun n ↦ measurable_const.mul (hg _)]
  exact Measure.sum_congr fun n ↦ (withDensity_smul (mixtureWeight n) (hg _)).symm

/-- If `countableMixture P θs` is a finite measure, then it has the mixed real density
`fun x ↦ ∑' n, (mixtureWeight n).toReal * f (θs n) x`. -/
theorem hasDensity_countableMixture {P : Θ → Measure X} {μ : Measure X} {f : Θ → X → ℝ}
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (θs : ℕ → Θ)
    [IsFiniteMeasure (countableMixture P θs)] :
    HasDensity (countableMixture P θs) μ
      (fun x ↦ ∑' n, (mixtureWeight n).toReal * f (θs n) x) := by
  let a : ℕ → X → ℝ := fun n x ↦ (mixtureWeight n).toReal * f (θs n) x
  have ha : ∀ n, Measurable (a n) := fun n ↦ measurable_const.mul (hf _).measurable
  -- Measurability of the real `tsum` follows directly from Mathlib's `StronglyMeasurable.tsum`.
  have hmeas : Measurable fun x ↦ ∑' n, a n x :=
    (StronglyMeasurable.tsum fun n ↦ (ha n).stronglyMeasurable).measurable
  -- Express the mixture as a `withDensity` in `ℝ≥0∞`, whose density is finite `μ`-a.e. since the
  -- mixture is finite.
  have hwd : countableMixture P θs =
      μ.withDensity (fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)) := by
    have hP : P = fun θ ↦ μ.withDensity (fun x ↦ ENNReal.ofReal (f θ x)) :=
      funext fun θ ↦ (hf θ).eq_withDensity
    rw [hP]
    exact countableMixture_withDensity μ (fun θ x ↦ ENNReal.ofReal (f θ x))
      (fun θ ↦ (hf θ).measurable.ennreal_ofReal) θs
  have hlt : ∀ᵐ x ∂μ, (∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)) < ∞ := by
    refine ae_lt_top
      (Measurable.tsum fun n ↦ measurable_const.mul (hf _).measurable.ennreal_ofReal) ?_
    have huniv : ∫⁻ x, (∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)) ∂μ =
        countableMixture P θs univ := by
      rw [hwd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [huniv]
    exact measure_ne_top _ _
  have hnn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f (θs n) x := ae_all_iff.mpr fun n ↦ (hf _).ae_nonneg
  rw [hasDensity_def]
  refine ⟨hmeas, ?_, ?_⟩
  · filter_upwards [hnn] with x hx
    exact tsum_nonneg fun n ↦ mul_nonneg ENNReal.toReal_nonneg (hx n)
  · -- Match the `ℝ≥0∞` mixed density with `ENNReal.ofReal` of the real `tsum` `μ`-a.e.
    rw [hwd]
    refine withDensity_congr_ae ?_
    filter_upwards [hlt, hnn] with x hxlt hxnn
    have hterm : ∀ n, mixtureWeight n * ENNReal.ofReal (f (θs n) x) =
        ENNReal.ofReal (a n x) := fun n ↦ by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (mixtureWeight_ne_top n)]
    have hsum : Summable fun n ↦ a n x := by
      have hne : (∑' n, ENNReal.ofReal (a n x)) ≠ ∞ := by
        rw [← tsum_congr hterm]
        exact hxlt.ne
      exact (ENNReal.summable_toReal hne).congr fun n ↦
        ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (hxnn n))
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n ↦ mul_nonneg ENNReal.toReal_nonneg (hxnn n)) hsum]
    exact tsum_congr hterm

/-! ### The Halmos–Savage domination lemma -/

/-- The Halmos–Savage domination lemma for families of `withDensity` measures with respect to an
s-finite reference measure `μ`: there exists a countable mixture of members of the family that
dominates the entire family.

Proved by applying Mathlib's `MeasureTheory.Measure.exists_ae_subset_biUnion_countable` to the
positivity sets `{x | 0 < g θ x}`. -/
theorem exists_absolutelyContinuous_countableMixture_of_withDensity [Nonempty Θ]
    (P : Θ → Measure X) (μ : Measure X) [SFinite μ] (g : Θ → X → ℝ≥0∞)
    (hg : ∀ θ, Measurable (g θ)) (hP : ∀ θ, P θ = μ.withDensity (g θ)) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs := by
  let S : Θ → Set X := fun θ ↦ {x | 0 < g θ x}
  have hS : ∀ θ, MeasurableSet (S θ) := fun θ ↦ measurableSet_lt measurable_const (hg θ)
  have hnull : ∀ (θ : Θ) (A : Set X), P θ A = 0 ↔ μ (A ∩ S θ) = 0 := fun θ A ↦ by
    rw [hP θ, withDensity_apply_eq_zero (hg θ), inter_comm]
    simp only [S, pos_iff_ne_zero]
  obtain ⟨D, hDsub, hDcount, hDae⟩ :=
    Measure.exists_ae_subset_biUnion_countable μ (C := range S) (by rintro _ ⟨θ, rfl⟩; exact hS θ)
  rcases D.eq_empty_or_nonempty with rfl | hDne
  · refine ⟨fun _ ↦ Classical.arbitrary Θ, fun θ ↦ Measure.AbsolutelyContinuous.mk fun A _ _ ↦ ?_⟩
    rw [hnull θ A]
    have hle : S θ ≤ᵐ[μ] (∅ : Set X) := by simpa using hDae (S θ) ⟨θ, rfl⟩
    have hμS : μ (S θ) = 0 := by simpa [ae_subset] using hle
    exact measure_mono_null inter_subset_right hμS
  · obtain ⟨d, hd⟩ := hDcount.exists_eq_range hDne
    have hmem : ∀ n, ∃ θ, S θ = d n := fun n ↦ hDsub (hd ▸ mem_range_self n)
    choose θs hθs using hmem
    have hU : ⋃₀ D = ⋃ n, S (θs n) := by
      rw [hd, sUnion_range]
      simp_rw [hθs]
    refine ⟨θs, fun θ ↦ Measure.AbsolutelyContinuous.mk fun A _ h0 ↦ ?_⟩
    rw [hnull θ A]
    have hcomp : ∀ n, μ (A ∩ S (θs n)) = 0 := fun n ↦
      (hnull (θs n) A).mp ((countableMixture_apply_eq_zero_iff P θs).mp h0 n)
    have hμU : μ (A ∩ ⋃ n, S (θs n)) = 0 := by
      rw [inter_iUnion]
      exact measure_iUnion_null hcomp
    have hdiff : μ (S θ \ ⋃ n, S (θs n)) = 0 :=
      ae_subset.mp (hU ▸ hDae (S θ) ⟨θ, rfl⟩)
    refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null hμU hdiff)
    by_cases hxU : x ∈ ⋃ n, S (θs n)
    · exact Or.inl ⟨hx.1, hxU⟩
    · exact Or.inr ⟨hx.2, hxU⟩

/-- The Halmos–Savage domination lemma for families of measures that are absolutely continuous and
admit a Lebesgue decomposition with respect to an s-finite reference measure `μ` (in particular,
whenever `μ` and each `P θ` are σ-finite). -/
theorem exists_absolutelyContinuous_countableMixture_of_absolutelyContinuous [Nonempty Θ]
    (P : Θ → Measure X) (μ : Measure X) [SFinite μ]
    [∀ θ, (P θ).HaveLebesgueDecomposition μ] (hac : ∀ θ, P θ ≪ μ) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs :=
  exists_absolutelyContinuous_countableMixture_of_withDensity P μ
    (fun θ ↦ (P θ).rnDeriv μ) (fun θ ↦ Measure.measurable_rnDeriv (P θ) μ)
    (fun θ ↦ (Measure.withDensity_rnDeriv_eq (P θ) μ (hac θ)).symm)

/-- The Halmos–Savage domination lemma, density form: any nonempty family of measures with real
densities with respect to an s-finite reference measure `μ` is dominated by a countable mixture of
members of the family. -/
theorem exists_absolutelyContinuous_countableMixture [Nonempty Θ]
    (P : Θ → Measure X) (μ : Measure X) [SFinite μ] (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs :=
  exists_absolutelyContinuous_countableMixture_of_withDensity P μ
    (fun θ x ↦ ENNReal.ofReal (f θ x)) (fun θ ↦ (hf θ).measurable.ennreal_ofReal)
    (fun θ ↦ (hf θ).eq_withDensity)

end TauCeti
