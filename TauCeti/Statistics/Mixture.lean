/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Density
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Countable mixtures and the Halmos–Savage lemma

A dominated family of probability measures admits a single dominating countable mixture drawn from
the family itself. This file defines the dyadic mixture weights `TauCeti.mixtureWeight` and the
countable mixture `TauCeti.countableMixture`, establishes their basic measure-theoretic and density
properties, and proves the Halmos–Savage lemma.

The Halmos–Savage exhaustion argument delegates directly to Mathlib's
`MeasureTheory.Measure.exists_ae_subset_biUnion_countable`, which yields the lemma for any s-finite
reference measure `μ`.

## Main definitions

* `TauCeti.mixtureWeight n`: the dyadic weight `2 ^ (-(n + 1))` in `ℝ≥0∞`.
* `TauCeti.countableMixture P θs`: the countable mixture `∑' n, mixtureWeight n • P (θs n)`.

## Main results

* `TauCeti.tsum_mixtureWeight`: `∑' n, mixtureWeight n = 1`.
* `TauCeti.isProbabilityMeasure_countableMixture`: a countable mixture of probability measures is a
  probability measure.
* `TauCeti.countableMixture_apply_eq_zero_iff`: a set is null for a countable mixture iff it is null
  for every component.
* `TauCeti.hasDensity_countableMixture`: a finite countable mixture of measures with real densities
  has the mixed real density.
* `TauCeti.exists_absolutelyContinuous_countableMixture_of_eq_withDensity`: general `withDensity`
  form of the Halmos–Savage lemma for an s-finite reference measure.
* `TauCeti.exists_absolutelyContinuous_countableMixture`: real-density form of the Halmos–Savage
  lemma.
* `TauCeti.exists_absolutelyContinuous_countableMixture_of_absolutelyContinuous`: dominated-family
  form of the Halmos–Savage lemma.

## References

* P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory of
  sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241, Lemma 7.
* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter, 1994, Lemma 1.2.1.
* M. J. Schervish, *Theory of Statistics*, Springer, 1995, Theorem A.78.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace TauCeti

section MixtureWeight

/-- The dyadic weights `2 ^ (-(n + 1))` used to form countable mixtures of measures. -/
def mixtureWeight (n : ℕ) : ℝ≥0∞ := (2 ^ (n + 1))⁻¹

/-- Defining formula for `mixtureWeight`. -/
theorem mixtureWeight_def (n : ℕ) : mixtureWeight n = (2 ^ (n + 1))⁻¹ :=
  (rfl)

/-- The zeroth dyadic mixture weight is `2⁻¹`. -/
@[simp]
theorem mixtureWeight_zero : mixtureWeight 0 = 2⁻¹ := by
  simp [mixtureWeight_def]

/-- Each dyadic mixture weight is half the previous one. -/
theorem mixtureWeight_succ (n : ℕ) : mixtureWeight (n + 1) = 2⁻¹ * mixtureWeight n := by
  rw [mixtureWeight_def, mixtureWeight_def, pow_succ', ENNReal.mul_inv (Or.inl (by simp))
    (Or.inl (by simp))]

/-- Every dyadic mixture weight is strictly positive. -/
theorem mixtureWeight_pos (n : ℕ) : 0 < mixtureWeight n := by
  rw [mixtureWeight_def, ENNReal.inv_pos]
  exact ENNReal.pow_ne_top (by simp)

/-- Every dyadic mixture weight is nonzero. -/
@[simp]
theorem mixtureWeight_ne_zero (n : ℕ) : mixtureWeight n ≠ 0 :=
  (mixtureWeight_pos n).ne'

/-- Every dyadic mixture weight is finite. -/
@[simp]
theorem mixtureWeight_ne_top (n : ℕ) : mixtureWeight n ≠ ∞ := by
  rw [mixtureWeight_def]
  exact ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by simp))

/-- Every dyadic mixture weight is strictly less than `∞`. -/
theorem mixtureWeight_lt_top (n : ℕ) : mixtureWeight n < ∞ :=
  (mixtureWeight_ne_top n).lt_top

/-- Every dyadic mixture weight is at most `1`. -/
theorem mixtureWeight_le_one (n : ℕ) : mixtureWeight n ≤ 1 := by
  rw [mixtureWeight_def, ENNReal.inv_le_one]
  exact one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- The dyadic mixture weights sum to `1`. -/
@[simp]
theorem tsum_mixtureWeight : ∑' n, mixtureWeight n = 1 := by
  simp only [mixtureWeight_def, ENNReal.inv_pow, ENNReal.tsum_geometric_add_one,
    ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- Every dyadic mixture weight has strictly positive real value. -/
theorem mixtureWeight_toReal_pos (n : ℕ) : 0 < (mixtureWeight n).toReal :=
  ENNReal.toReal_pos (mixtureWeight_ne_zero n) (mixtureWeight_ne_top n)

end MixtureWeight

section CountableMixture

variable {Θ X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The countable mixture `∑' n, mixtureWeight n • P (θs n)` of a sequence of measures selected
from a family `P`. -/
def countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) : Measure X :=
  Measure.sum fun n ↦ mixtureWeight n • P (θs n)

/-- Defining formula for `countableMixture`. -/
theorem countableMixture_def (P : Θ → Measure X) (θs : ℕ → Θ) :
    countableMixture P θs = Measure.sum fun n ↦ mixtureWeight n • P (θs n) :=
  (rfl)

/-- Value of a countable mixture on a measurable set. -/
theorem countableMixture_apply (P : Θ → Measure X) (θs : ℕ → Θ) {s : Set X}
    (hs : MeasurableSet s) :
    countableMixture P θs s = ∑' n, mixtureWeight n * P (θs n) s := by
  simp [countableMixture_def, Measure.sum_apply _ hs]

/-- A countable mixture with constant index sequence recovers that single measure. -/
@[simp]
theorem countableMixture_const (P : Θ → Measure X) (θ₀ : Θ) :
    countableMixture P (fun _ ↦ θ₀) = P θ₀ := by
  ext s hs
  rw [countableMixture_apply _ _ hs, ENNReal.tsum_mul_right, tsum_mixtureWeight, one_mul]

/-- A countable mixture of probability measures is a probability measure. -/
instance isProbabilityMeasure_countableMixture (P : Θ → Measure X)
    [hP : ∀ θ, IsProbabilityMeasure (P θ)] (θs : ℕ → Θ) :
    IsProbabilityMeasure (countableMixture P θs) := by
  constructor
  rw [countableMixture_apply _ _ MeasurableSet.univ]
  simp_rw [@measure_univ _ _ _ (hP _), mul_one, tsum_mixtureWeight]

/-- A countable mixture of s-finite measures is s-finite. -/
instance sFinite_countableMixture (P : Θ → Measure X) [∀ θ, SFinite (P θ)] (θs : ℕ → Θ) :
    SFinite (countableMixture P θs) := by
  rw [countableMixture_def]
  infer_instance

/-- A set (not necessarily measurable) has zero measure under a countable mixture iff it has zero
measure under every component. -/
theorem countableMixture_apply_eq_zero_iff (P : Θ → Measure X) (θs : ℕ → Θ) (s : Set X) :
    countableMixture P θs s = 0 ↔ ∀ n, P (θs n) s = 0 := by
  constructor
  · intro h n
    have hle : mixtureWeight n * P (θs n) s ≤ countableMixture P θs s := by
      rw [countableMixture_def]
      exact (le_tsum (fun k ↦ (mixtureWeight k • P (θs k)) s) n).trans
        (Measure.le_sum_apply (fun k ↦ mixtureWeight k • P (θs k)) s)
    have hmul : mixtureWeight n * P (θs n) s = 0 := le_antisymm (hle.trans h.le) zero_le
    exact (mul_eq_zero.mp hmul).resolve_left (mixtureWeight_ne_zero n)
  · intro h
    let t : Set X := ⋂ n, toMeasurable (P (θs n)) s
    have ht : MeasurableSet t := MeasurableSet.iInter fun n ↦ measurableSet_toMeasurable _ _
    have hst : s ⊆ t := subset_iInter fun n ↦ subset_toMeasurable _ _
    refine measure_mono_null hst ?_
    rw [countableMixture_apply _ _ ht, tsum_eq_zero_iff]
    intro n
    have h0 : P (θs n) t = 0 := measure_mono_null (iInter_subset _ n) (by simp [h n])
    simp [h0]

/-- A property holds almost everywhere for a countable mixture iff it holds almost everywhere for
every component. -/
theorem ae_countableMixture_iff (P : Θ → Measure X) (θs : ℕ → Θ) {p : X → Prop} :
    (∀ᵐ x ∂countableMixture P θs, p x) ↔ ∀ n, ∀ᵐ x ∂P (θs n), p x := by
  simp only [ae_iff, countableMixture_apply_eq_zero_iff]

/-- Every component of a countable mixture is absolutely continuous with respect to the mixture. -/
theorem absolutelyContinuous_countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) (n : ℕ) :
    P (θs n) ≪ countableMixture P θs :=
  Measure.AbsolutelyContinuous.mk fun s _ hs ↦
    (countableMixture_apply_eq_zero_iff P θs s).mp hs n

/-- Pushing a countable mixture forward along a measurable map pushes each component forward. -/
theorem map_countableMixture (P : Θ → Measure X) (θs : ℕ → Θ) {φ : X → Y} (hφ : Measurable φ) :
    (countableMixture P θs).map φ = countableMixture (fun θ ↦ (P θ).map φ) θs := by
  ext s hs
  rw [Measure.map_apply hφ hs, countableMixture_apply _ _ (hφ hs), countableMixture_apply _ _ hs]
  simp_rw [Measure.map_apply hφ hs]

/-- A countable mixture of `withDensity` measures has the corresponding `tsum` density in `ℝ≥0∞`. -/
theorem countableMixture_eq_withDensity (P : Θ → Measure X) (μ : Measure X)
    (g : Θ → X → ℝ≥0∞) (hgm : ∀ θ, Measurable (g θ))
    (hP : ∀ θ, P θ = μ.withDensity (g θ)) (θs : ℕ → Θ) :
    countableMixture P θs = μ.withDensity (fun x ↦ ∑' n, mixtureWeight n * g (θs n) x) := by
  ext s hs
  rw [countableMixture_apply _ _ hs, withDensity_apply _ hs,
    lintegral_tsum (f := fun n x ↦ mixtureWeight n * g (θs n) x)
      fun n ↦ (measurable_const.mul (hgm (θs n))).aemeasurable]
  congr 1
  ext n
  rw [hP (θs n), withDensity_apply _ hs, lintegral_const_mul _ (hgm (θs n))]

/-- A finite countable mixture of measures with real densities has the mixed real density
`x ↦ (∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)).toReal`. -/
theorem hasDensity_countableMixture (P : Θ → Measure X) (μ : Measure X)
    (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (θs : ℕ → Θ)
    [IsFiniteMeasure (countableMixture P θs)] :
    HasDensity (countableMixture P θs) μ
      (fun x ↦ (∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)).toReal) := by
  let g : X → ℝ≥0∞ := fun x ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)
  have hg_meas : Measurable g :=
    Measurable.tsum fun n ↦ measurable_const.mul (hf (θs n)).measurable.ennreal_ofReal
  have hmix : countableMixture P θs = μ.withDensity g :=
    countableMixture_eq_withDensity P μ (fun θ x ↦ ENNReal.ofReal (f θ x))
      (fun θ ↦ (hf θ).measurable.ennreal_ofReal) (fun θ ↦ (hf θ).eq_withDensity) θs
  have hg_lt_top : ∀ᵐ x ∂μ, g x < ∞ := by
    refine ae_lt_top hg_meas ?_
    have huniv : ∫⁻ x, g x ∂μ = countableMixture P θs Set.univ := by
      rw [hmix, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [huniv]
    exact measure_ne_top _ _
  refine hasDensity_iff.mpr ⟨hg_meas.ennreal_toReal, ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
  rw [hmix]
  refine withDensity_congr_ae ?_
  filter_upwards [hg_lt_top] with x hx
  exact (ENNReal.ofReal_toReal hx.ne).symm

/-- Almost everywhere with respect to `μ`, the `toReal` of a `mixtureWeight`-weighted `ENNReal`
series of almost-everywhere nonnegative real functions agrees with the corresponding real series. -/
theorem toReal_tsum_mixtureWeight_mul_ofReal_ae_eq {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) :
    (fun x ↦ (∑' n, mixtureWeight n * ENNReal.ofReal (f n x)).toReal) =ᵐ[μ]
      fun x ↦ ∑' n, (mixtureWeight n).toReal * f n x := by
  filter_upwards [ae_all_iff.mpr hf] with x hxn
  rw [ENNReal.tsum_toReal_eq fun n ↦
    ENNReal.mul_ne_top (mixtureWeight_ne_top n) ENNReal.ofReal_ne_top]
  congr 1
  ext n
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hxn n)]

/-- **Halmos–Savage lemma** (`withDensity` form): a nonempty family of measures having measurable
`ℝ≥0∞`-valued densities against an s-finite reference measure `μ` is dominated by a countable
mixture of members of the family. -/
theorem exists_absolutelyContinuous_countableMixture_of_eq_withDensity [Nonempty Θ]
    (P : Θ → Measure X) (μ : Measure X) [SFinite μ]
    (g : Θ → X → ℝ≥0∞) (hgm : ∀ θ, Measurable (g θ))
    (hP : ∀ θ, P θ = μ.withDensity (g θ)) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs := by
  let posSet : Θ → Set X := fun θ ↦ {x | g θ x ≠ 0}
  have hpos_meas : ∀ θ, MeasurableSet (posSet θ) := fun θ ↦
    (hgm θ (measurableSet_singleton 0)).compl
  have hC : ∀ s ∈ Set.range posSet, MeasurableSet s := by
    rintro s ⟨θ, rfl⟩
    exact hpos_meas θ
  obtain ⟨D, hDC, hD_count, hD_cov⟩ := Measure.exists_ae_subset_biUnion_countable μ hC
  have ⟨θs, hθs⟩ : ∃ θs : ℕ → Θ, ⋃₀ D ⊆ ⋃ n, posSet (θs n) := by
    rcases D.eq_empty_or_nonempty with rfl | hDne
    · exact ⟨fun _ ↦ Classical.arbitrary Θ, by simp⟩
    · obtain ⟨u, hu⟩ := hD_count.exists_eq_range hDne
      have hmem : ∀ n, ∃ θ, posSet θ = u n := fun n ↦ hDC (hu ▸ mem_range_self n)
      choose θs hθs using hmem
      refine ⟨θs, ?_⟩
      rw [hu, sUnion_range]
      exact iUnion_mono fun n ↦ (hθs n).symm.subset
  refine ⟨θs, fun θ ↦ Measure.AbsolutelyContinuous.mk fun A hA hA0 ↦ ?_⟩
  have hcomp_null : ∀ n, P (θs n) A = 0 :=
    (countableMixture_apply_eq_zero_iff P θs A).mp hA0
  have h_inter_null : ∀ n, μ (A ∩ posSet (θs n)) = 0 := by
    intro n
    have hzero : ∫⁻ x in A, g (θs n) x ∂μ = 0 := by
      have h := hcomp_null n
      rwa [hP (θs n), withDensity_apply _ hA] at h
    have hae : ∀ᵐ x ∂μ.restrict A, g (θs n) x = 0 :=
      (lintegral_eq_zero_iff (hgm (θs n))).mp hzero
    rw [ae_restrict_iff' hA, ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro x hx h
    exact hx.2 (h hx.1)
  have h_union_null : μ (A ∩ ⋃ n, posSet (θs n)) = 0 := by
    rw [inter_iUnion]
    exact measure_iUnion_null h_inter_null
  have h_ae_sub : posSet θ ≤ᵐ[μ] ⋃ n, posSet (θs n) :=
    (hD_cov (posSet θ) (mem_range_self θ)).trans (LE.le.eventuallySubset hθs)
  have h_pos_null : μ (A ∩ posSet θ) = 0 := by
    refine le_antisymm ?_ zero_le
    calc μ (A ∩ posSet θ)
        ≤ μ (A ∩ ⋃ n, posSet (θs n)) :=
          measure_mono_ae (h_ae_sub.mono fun x hx hxA ↦ ⟨hxA.1, hx hxA.2⟩)
      _ = 0 := h_union_null
  rw [hP θ, withDensity_apply _ hA, lintegral_eq_zero_iff (hgm θ), Filter.EventuallyEq,
    ae_restrict_iff' hA, ae_iff]
  exact measure_mono_null (fun x hx ↦ by simpa [posSet] using hx) h_pos_null

/-- **Halmos–Savage lemma** (real-density form): a nonempty family of measures having real
densities against an s-finite reference measure `μ` is dominated by a countable mixture of members
of the family. -/
theorem exists_absolutelyContinuous_countableMixture [Nonempty Θ] (P : Θ → Measure X)
    (μ : Measure X) [SFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs :=
  exists_absolutelyContinuous_countableMixture_of_eq_withDensity P μ
    (fun θ x ↦ ENNReal.ofReal (f θ x))
    (fun θ ↦ (hf θ).measurable.ennreal_ofReal)
    (fun θ ↦ (hf θ).eq_withDensity)

/-- **Halmos–Savage lemma** (dominated-family form): a nonempty family of measures dominated by an
s-finite reference measure `μ` admitting Lebesgue decompositions is dominated by a countable
mixture of members of the family. -/
theorem exists_absolutelyContinuous_countableMixture_of_absolutelyContinuous [Nonempty Θ]
    (P : Θ → Measure X) (μ : Measure X) [SFinite μ] [∀ θ, (P θ).HaveLebesgueDecomposition μ]
    (hP : ∀ θ, P θ ≪ μ) :
    ∃ θs : ℕ → Θ, ∀ θ, P θ ≪ countableMixture P θs :=
  exists_absolutelyContinuous_countableMixture_of_eq_withDensity P μ
    (fun θ ↦ (P θ).rnDeriv μ)
    (fun _ ↦ Measure.measurable_rnDeriv _ _)
    (fun θ ↦ (Measure.withDensity_rnDeriv_eq (P θ) μ (hP θ)).symm)

end CountableMixture

end TauCeti
