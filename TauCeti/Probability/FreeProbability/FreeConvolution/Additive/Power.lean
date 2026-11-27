/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.FreeConvolution.Additive.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Finite free additive convolutions and free convolution powers

This file develops finite-family free additive convolution via `Finset.fold`, C⋆- and von Neumann
transport for finite sums of freely independent selfadjoint families, and the `n`-fold free additive
convolution power `MeasureTheory.Measure.freeConvPow`.

## Main definitions

* `MeasureTheory.Measure.freeConvPow`: the `n`-fold free additive convolution power
  `μ.freeConvPow n`, with `μ.freeConvPow 0 = Measure.dirac 0`.

## Main results

* `Finset.isProbabilityMeasure_fold_freeConv_iff`,
  `Finset.fold_freeConv_map_affine`,
  `Finset.fold_freeConv_map_add`,
  `Finset.fold_freeConv_map_mul`,
  `Finset.fold_freeConv_neg`,
  `Finset.rSeries_integral_fold_freeConv`,
  `Finset.freeCumulant_fold_freeConv`,
  `Finset.eq_fold_freeConv_iff_rSeries_integral_eq`,
  `Finset.eq_fold_freeConv_iff_forall_freeCumulant_eq`,
  `Finset.support_fold_freeConv_subset_Icc`,
  `Finset.fold_freeConv_const`: validity, affine/reflection, formal series, cumulants,
  determinacy, and support bounds for finite `Finset.fold`s of `MeasureTheory.Measure.freeConv`.
* `TauCeti.IsFreelyIndependentElements.law_sum`, `TauCeti.IsFreelyIndependent.law_sum`:
  C⋆- and von Neumann finite-sum transport.
* `MeasureTheory.Measure.freeConvPow_add`,
  `MeasureTheory.Measure.freeConvPow_mul`,
  `MeasureTheory.Measure.freeConvPow_map_affine`,
  `MeasureTheory.Measure.rSeries_integral_freeConvPow`,
  `MeasureTheory.Measure.freeCumulant_freeConvPow`,
  `MeasureTheory.Measure.eq_freeConvPow_iff_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_freeConvPow_iff_forall_freeCumulant_eq`: algebraic,
  affine, support, series, cumulant, determinacy, mean, and variance laws for
  `freeConvPow`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 12 and 16.
-/

public section

noncomputable section

open Finset MeasureTheory PowerSeries ProbabilityTheory
open scoped ComplexOrder ENNReal NNReal

/-! ### Finite-family free convolution (`Finset.fold`) and transport -/

namespace Finset

variable {ι : Type*} (s : Finset ι) {μ : ι → Measure ℝ}

/-- Folding `Measure.freeConv` with base `Measure.dirac 0` always yields a measure with compact
support. -/
theorem isCompact_support_fold_freeConv (μ : ι → Measure ℝ) :
    IsCompact (s.fold Measure.freeConv (Measure.dirac 0) μ).support := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp [Measure.support_dirac]
  · rw [← Finset.insert_erase hi, Finset.fold_insert (Finset.notMem_erase i s)]
    exact Measure.isCompact_support_freeConv _ _

/-- Folding `Measure.freeConv` with base `Measure.dirac 0` always yields either `0` or a
probability measure (hence a finite measure). -/
instance isZeroOrProbabilityMeasure_fold_freeConv (μ : ι → Measure ℝ) :
    IsZeroOrProbabilityMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp only [Finset.fold_empty]; infer_instance
  · rw [← Finset.insert_erase hi, Finset.fold_insert (Finset.notMem_erase i s)]
    infer_instance

/-- Folding `Measure.freeConv` with base `Measure.dirac 0` yields a probability measure iff every
indexed measure in `s` is a compactly supported probability measure (including when `s = ∅`). -/
@[simp] theorem isProbabilityMeasure_fold_freeConv_iff :
    IsProbabilityMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) ↔
      ∀ i ∈ s, (μ i).IsCompactProbabilityMeasure := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.fold_empty, notMem_empty, IsEmpty.forall_iff, implies_true, iff_true]
      infer_instance
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, Measure.isProbabilityMeasure_freeConv_iff,
        Finset.forall_mem_insert]
      exact and_congr_right fun _ => (and_iff_left (s.isCompact_support_fold_freeConv μ)).trans ih

/-- Folding `Measure.freeConv` with base `Measure.dirac 0` yields `0` iff some indexed measure in
`s` is not a compactly supported probability measure. -/
@[simp] theorem fold_freeConv_eq_zero_iff :
    s.fold Measure.freeConv (Measure.dirac 0) μ = 0 ↔
      ∃ i ∈ s, ¬(μ i).IsCompactProbabilityMeasure := by
  rw [eq_zero_iff_not_isProbabilityMeasure, s.isProbabilityMeasure_fold_freeConv_iff, not_forall]
  simp only [not_imp]

/-- Folding `Measure.freeConv` with base `Measure.dirac 0` over compactly supported probability
measures yields a probability measure (including when `s = ∅`). -/
theorem isProbabilityMeasure_fold_freeConv (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    IsProbabilityMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) :=
  s.isProbabilityMeasure_fold_freeConv_iff.mpr fun i hi => ⟨hprob i hi, hcomp i hi⟩

/-- Interval support bounds add across a finite `Finset.fold` of `Measure.freeConv`, including
`s = ∅` and when any factor is not a probability measure. -/
theorem support_fold_freeConv_subset_Icc {m M : ι → ℝ}
    (hI : ∀ i ∈ s, (μ i).support ⊆ Set.Icc (m i) (M i)) :
    (s.fold Measure.freeConv (Measure.dirac 0) μ).support ⊆
      Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.support_dirac]
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, sum_insert hi, sum_insert hi]
      exact Measure.support_freeConv_subset_Icc (hI i (mem_insert_self i s))
        (ih fun j hj => hI j (mem_insert_of_mem hj))

/-- **Affine equivariance of finite free additive convolution.** Pushing each `μ i` (`i ∈ s`)
forward by `x ↦ a i + b * x` and folding with `Measure.freeConv` pushes the folded convolution
forward by `x ↦ (∑ i ∈ s, a i) + b * x` (valid for all real slopes `b`, including `b = 0` and
`b < 0`, and including `s = ∅`). -/
theorem fold_freeConv_map_affine (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) (a : ι → ℝ) (b : ℝ) :
    (s.fold Measure.freeConv (Measure.dirac 0) fun i => (μ i).map fun x => a i + b * x) =
      (s.fold Measure.freeConv (Measure.dirac 0) μ).map fun x => (∑ i ∈ s, a i) + b * x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hp' := fun j hj => hprob j (mem_insert_of_mem hj)
      have hc' := fun j hj => hcomp j (mem_insert_of_mem hj)
      have := hprob i (mem_insert_self i s)
      have := s.isProbabilityMeasure_fold_freeConv hp' hc'
      rw [Finset.fold_insert hi, Finset.fold_insert hi, ih hp' hc', Finset.sum_insert hi,
        Measure.freeConv_map_affine (hcomp i (mem_insert_self i s))
          (s.isCompact_support_fold_freeConv μ) (a i) (∑ j ∈ s, a j) b]

/-- Translating each `μ i` (`i ∈ s`) by `a i` translates the folded free convolution by
`∑ i ∈ s, a i`, unconditionally for all measures on `ℝ` (including `s = ∅`). -/
theorem fold_freeConv_map_add (μ : ι → Measure ℝ) (a : ι → ℝ) :
    (s.fold Measure.freeConv (Measure.dirac 0) fun i => (μ i).map (a i + ·)) =
      (s.fold Measure.freeConv (Measure.dirac 0) μ).map ((∑ i ∈ s, a i) + ·) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, Finset.fold_insert hi, ih, Finset.sum_insert hi,
        Measure.freeConv_map_add]

/-- Scaling each `μ i` (`i ∈ s`) by `b` scales the folded free convolution by `b` (including
`s = ∅` and `b = 0`). -/
theorem fold_freeConv_map_mul (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) (b : ℝ) :
    (s.fold Measure.freeConv (Measure.dirac 0) fun i => (μ i).map (b * ·)) =
      (s.fold Measure.freeConv (Measure.dirac 0) μ).map (b * ·) := by
  simpa using s.fold_freeConv_map_affine hprob hcomp (fun _ => 0) b

/-- Reflection `Measure.neg` commutes with finite folded free convolution unconditionally. -/
theorem fold_freeConv_neg (μ : ι → Measure ℝ) :
    (s.fold Measure.freeConv (Measure.dirac 0) fun i => (μ i).neg) =
      (s.fold Measure.freeConv (Measure.dirac 0) μ).neg := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.neg_def, Measure.map_dirac' measurable_neg]
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, Finset.fold_insert hi, ih, Measure.neg_freeConv_neg]

/-- The formal R-series of a finite `Finset.fold` of `Measure.freeConv` is the sum of the
individual formal R-series, including `s = ∅`. -/
theorem rSeries_integral_fold_freeConv (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    TauCeti.rSeries
        (fun f : ℝ → ℝ => ∫ x, f x ∂(s.fold Measure.freeConv (Measure.dirac 0) μ)) id =
      ∑ i ∈ s, TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ i) id := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hp' := fun j hj => hprob j (mem_insert_of_mem hj)
      have hc' := fun j hj => hcomp j (mem_insert_of_mem hj)
      have := hprob i (mem_insert_self i s)
      have := s.isProbabilityMeasure_fold_freeConv hp' hc'
      rw [Finset.fold_insert hi, sum_insert hi, Measure.rSeries_integral_freeConv
        (hcomp i (mem_insert_self i s)) (s.isCompact_support_fold_freeConv μ), ih hp' hc']

/-- Positive-order free cumulants add across a finite `Finset.fold` of `Measure.freeConv`. -/
theorem freeCumulant_fold_freeConv (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) {n : ℕ} (hn : n ≠ 0) :
    (s.fold Measure.freeConv (Measure.dirac 0) μ).freeCumulant n =
      ∑ i ∈ s, (μ i).freeCumulant n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp_rw [Measure.freeCumulant_succ_eq_coeff_rSeries,
    s.rSeries_integral_fold_freeConv hprob hcomp, _root_.map_sum (PowerSeries.coeff k)]

/-- A compactly supported probability measure `ρ` equals
`s.fold Measure.freeConv (Measure.dirac 0) μ` iff its formal R-series equals the sum of those of
`μ i` over `i ∈ s`. -/
theorem eq_fold_freeConv_iff_rSeries_integral_eq {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : IsCompact ρ.support) (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    ρ = s.fold Measure.freeConv (Measure.dirac 0) μ ↔
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id =
        ∑ i ∈ s, TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ i) id := by
  have := s.isProbabilityMeasure_fold_freeConv hprob hcomp
  rw [Measure.eq_iff_rSeries_integral_eq hρ (s.isCompact_support_fold_freeConv μ),
    s.rSeries_integral_fold_freeConv hprob hcomp]

/-- A compactly supported probability measure `ρ` equals
`s.fold Measure.freeConv (Measure.dirac 0) μ` iff all positive-order free cumulants of `ρ` equal
the sums of those of `μ i` over `i ∈ s`. -/
theorem eq_fold_freeConv_iff_forall_freeCumulant_eq {ρ : Measure ℝ}
    [IsProbabilityMeasure ρ] (hρ : IsCompact ρ.support)
    (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    ρ = s.fold Measure.freeConv (Measure.dirac 0) μ ↔ ∀ n : ℕ, n ≠ 0 →
      ρ.freeCumulant n = ∑ i ∈ s, (μ i).freeCumulant n := by
  have := s.isProbabilityMeasure_fold_freeConv hprob hcomp
  rw [Measure.eq_iff_forall_freeCumulant_eq hρ (s.isCompact_support_fold_freeConv μ)]
  exact forall₂_congr fun n hn => by rw [s.freeCumulant_fold_freeConv hprob hcomp hn]

end Finset

namespace TauCeti

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Law of a finite sum of freely independent selfadjoint elements** (including `s = ∅`). -/
theorem IsFreelyIndependentElements.law_sum {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    φ.law (∑ i ∈ s, a i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i => φ.law (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, Finset.fold_empty, φ.law_zero_of_apply_one hφ]
  | @insert i s hi ih =>
      let f : ι → Bool := fun j => decide (j = i)
      rw [sum_insert hi, Finset.fold_insert hi,
        (ha.adjoin_image_fiber hφ f).law_add hφ Bool.false_ne_true.symm
          (Algebra.subset_adjoin ⟨i, by simp [f], rfl⟩)
          (sum_mem fun j hj => Algebra.subset_adjoin
            ⟨j, by simp [f, ne_of_mem_of_not_mem hj hi], rfl⟩)
          (hasa i (mem_insert_self i s))
          (isSelfAdjoint_sum s fun j hj => hasa j (mem_insert_of_mem hj)),
        ih fun j hj => hasa j (mem_insert_of_mem hj)]

/-- **Law of a finite sum from freely independent subalgebras.** -/
theorem IsFreelyIndependent.law_sum {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) (s : Finset ι) {a : ι → A}
    (haB : ∀ i ∈ s, a i ∈ B i) (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    φ.law (∑ i ∈ s, a i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i => φ.law (a i)) := by
  have h := ((hB.comp Subtype.val_injective).isFreelyIndependentElements_of_mem fun i : s =>
      haB i.val i.property).law_sum hφ univ fun i _ => hasa i.val i.property
  rw [Finset.univ_eq_attach, Finset.sum_attach] at h
  exact h.trans <| (Finset.fold_map (f := fun i => φ.law (a i))
    (g := Function.Embedding.subtype _)).symm.trans (by rw [Finset.attach_map_val])

namespace FreeLawRealization

variable [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

/-- In `algebra μ`, `∑ i ∈ s, generator μ i` has law `s.fold freeConv (dirac 0) μ`. -/
theorem law_sum_generator (s : Finset ι) :
    (state μ).law (∑ i ∈ s, generator μ i) = s.fold Measure.freeConv (Measure.dirac 0) μ := by
  simp [(isFreelyIndependentElements_generator μ).law_sum (state_one μ) s
    fun i _ => isSelfAdjoint_generator μ i]

/-- In `vonNeumannAlgebra μ`, `∑ i ∈ s, vonNeumannGenerator μ i` realizes the folded free
convolution of `μ` over `s`. -/
theorem law_sum_vonNeumannGenerator (s : Finset ι) :
    (vonNeumannState μ).law (∑ i ∈ s, vonNeumannGenerator μ i) =
      s.fold Measure.freeConv (Measure.dirac 0) μ := by
  simp [(isFreelyIndependentElements_vonNeumannGenerator μ).law_sum (vonNeumannState_one μ) s
    fun i _ => isSelfAdjoint_vonNeumannGenerator μ i]

end FreeLawRealization

end TauCeti

/-! ### Finite free convolution powers -/

namespace MeasureTheory.Measure

/-- The `n`-fold free additive convolution power `μ.freeConvPow n` of a measure on `ℝ`,
with zeroth power `Measure.dirac 0`. -/
def freeConvPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (freeConvPow μ n).freeConv μ

/-- The zeroth free convolution power of any measure on `ℝ` is `Measure.dirac 0`. -/
@[simp] theorem freeConvPow_zero (μ : Measure ℝ) :
    μ.freeConvPow 0 = Measure.dirac 0 := by rfl

/-- Right recursion `μ.freeConvPow (n + 1) = (μ.freeConvPow n).freeConv μ` for
free convolution powers. -/
theorem freeConvPow_succ (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvPow (n + 1) = (μ.freeConvPow n).freeConv μ := by rfl

/-- Every free convolution power is either `0` or a probability measure (hence finite). -/
instance isZeroOrProbabilityMeasure_freeConvPow (μ : Measure ℝ) :
    ∀ n : ℕ, IsZeroOrProbabilityMeasure (μ.freeConvPow n)
  | 0 => by rw [freeConvPow_zero]; infer_instance
  | _ + 1 => by rw [freeConvPow_succ]; infer_instance

/-- For `n ≠ 0`, outside compactly supported probability measures `freeConvPow` is `0`. -/
theorem freeConvPow_undef {μ : Measure ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : ¬μ.IsCompactProbabilityMeasure) : μ.freeConvPow n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact freeConv_of_not_right h

/-- Every free convolution power of any measure on `ℝ` has compact topological support. -/
theorem isCompact_support_freeConvPow (μ : Measure ℝ) :
    ∀ n : ℕ, IsCompact (μ.freeConvPow n).support
  | 0 => by simp [Measure.support_dirac]
  | _ + 1 => isCompact_support_freeConv _ _

/-- Every free convolution power of a compactly supported probability measure is a probability
measure. -/
theorem isProbabilityMeasure_freeConvPow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : ∀ n : ℕ, IsProbabilityMeasure (μ.freeConvPow n)
  | 0 => by rw [freeConvPow_zero]; infer_instance
  | n + 1 => by
      have := isProbabilityMeasure_freeConvPow hμ n
      exact isProbabilityMeasure_freeConv (isCompact_support_freeConvPow μ n) hμ

/-- `μ.freeConvPow n` is a probability measure iff `n = 0` or `μ` is a compactly supported
probability measure. -/
@[simp] theorem isProbabilityMeasure_freeConvPow_iff {μ : Measure ℝ} {n : ℕ} :
    IsProbabilityMeasure (μ.freeConvPow n) ↔
      n = 0 ∨ μ.IsCompactProbabilityMeasure := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [freeConvPow_zero, true_or, iff_true]; infer_instance
  · simp only [hn, false_or]
    exact ⟨fun hp => by
      by_contra h
      exact not_isProbabilityMeasure_zero (freeConvPow_undef hn h ▸ hp),
      fun ⟨_, hμ⟩ => isProbabilityMeasure_freeConvPow hμ n⟩

/-- `μ.freeConvPow n` equals `0` iff `n ≠ 0` and `μ` is not a compactly supported
probability measure. -/
@[simp] theorem freeConvPow_eq_zero_iff {μ : Measure ℝ} {n : ℕ} :
    μ.freeConvPow n = 0 ↔ n ≠ 0 ∧ ¬μ.IsCompactProbabilityMeasure := by
  rw [eq_zero_iff_not_isProbabilityMeasure, isProbabilityMeasure_freeConvPow_iff, not_or]

/-- The first free convolution power of a compactly supported probability measure is itself. -/
@[simp] theorem freeConvPow_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : μ.freeConvPow 1 = μ := dirac_zero_freeConv μ hμ

/-- Free convolution powers turn addition of exponents into `freeConv`, unconditionally for all
measures on `ℝ`. -/
theorem freeConvPow_add (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvPow (m + n) =
      (μ.freeConvPow m).freeConv (μ.freeConvPow n) := by
  induction n with
  | zero =>
      by_cases h : μ.IsCompactProbabilityMeasure
      · have := h.1; have := isProbabilityMeasure_freeConvPow h.2 m
        exact (freeConv_dirac_zero (μ.freeConvPow m) (isCompact_support_freeConvPow μ m)).symm
      · rcases eq_or_ne m 0 with rfl | hm
        · simp
        · simp [freeConvPow_undef hm h]
  | succ n ih =>
      rw [Nat.add_succ, freeConvPow_succ, freeConvPow_succ, ih, freeConv_assoc]

/-- Left recursion `μ.freeConvPow (n + 1) = μ.freeConv (μ.freeConvPow n)`,
unconditionally for all measures on `ℝ`. -/
theorem freeConvPow_succ' (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvPow (n + 1) = μ.freeConv (μ.freeConvPow n) := freeConv_comm _ _

end MeasureTheory.Measure

namespace Finset

/-- Folding `Measure.freeConv` over a constant measure on `s` gives `μ.freeConvPow #s`. -/
theorem fold_freeConv_const {ι : Type*} (s : Finset ι) (μ : Measure ℝ) :
    s.fold Measure.freeConv (Measure.dirac 0) (fun _ => μ) = μ.freeConvPow #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, card_insert_of_notMem hi, ih, Measure.freeConvPow_succ']

end Finset

namespace MeasureTheory.Measure

/-- Free convolution powers of a Dirac mass add its atom `n` times. -/
@[simp] theorem freeConvPow_dirac (a : ℝ) (n : ℕ) :
    (Measure.dirac a).freeConvPow n = Measure.dirac (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [freeConvPow_succ, ih, dirac_freeConv_dirac, succ_nsmul]

/-- Iterated free convolution powers multiply exponents, unconditionally for all measures on `ℝ`. -/
theorem freeConvPow_mul (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvPow (m * n) = (μ.freeConvPow m).freeConvPow n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, freeConvPow_add, ih, freeConvPow_succ]

/-- **Affine equivariance of free convolution powers.** For a compactly supported probability
measure `μ`, pushing `μ` forward by `x ↦ a + b * x` and taking the `n`-th free convolution power
equals pushing `μ.freeConvPow n` forward by `x ↦ (n : ℝ) * a + b * x`. -/
theorem freeConvPow_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) (n : ℕ) :
    (μ.map fun x => a + b * x).freeConvPow n =
      (μ.freeConvPow n).map fun x => (n : ℝ) * a + b * x := by
  simpa [Finset.fold_freeConv_const, nsmul_eq_mul] using
    (univ : Finset (Fin n)).fold_freeConv_map_affine (μ := fun _ => μ)
      (fun _ _ => inferInstance) (fun _ _ => hμ) (fun _ => a) b

/-- Translating `μ` by `a` translates `μ.freeConvPow n` by `n • a`, unconditionally for
all measures on `ℝ`. -/
theorem freeConvPow_map_add (μ : Measure ℝ) (a : ℝ) (n : ℕ) :
    (μ.map (a + ·)).freeConvPow n = (μ.freeConvPow n).map (n • a + ·) := by
  simpa [Finset.fold_freeConv_const] using
    (univ : Finset (Fin n)).fold_freeConv_map_add (fun _ => μ) (fun _ => a)

/-- Scaling `μ` by `b` scales `μ.freeConvPow n` by `b` (including `n = 0` and `b = 0`). -/
theorem freeConvPow_map_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (b : ℝ) (n : ℕ) :
    (μ.map (b * ·)).freeConvPow n = (μ.freeConvPow n).map (b * ·) := by
  simpa using freeConvPow_map_affine hμ 0 b n

/-- Reflection `Measure.neg` commutes with free convolution powers unconditionally. -/
theorem freeConvPow_neg (μ : Measure ℝ) (n : ℕ) :
    μ.neg.freeConvPow n = (μ.freeConvPow n).neg := by
  simpa [Finset.fold_freeConv_const] using
    (univ : Finset (Fin n)).fold_freeConv_neg (fun _ => μ)

/-- Interval support bounds scale by `n` under `freeConvPow`, unconditionally for all
measures on `ℝ` and including `n = 0`. -/
theorem support_freeConvPow_subset_Icc {μ : Measure ℝ} {m M : ℝ}
    (hI : μ.support ⊆ Set.Icc m M) (n : ℕ) :
    (μ.freeConvPow n).support ⊆ Set.Icc ((n : ℝ) * m) ((n : ℝ) * M) := by
  simpa [Finset.fold_freeConv_const _ μ, nsmul_eq_mul] using
    (univ : Finset (Fin n)).support_fold_freeConv_subset_Icc (μ := fun _ => μ) fun _ _ => hI

/-- The formal R-series of `μ.freeConvPow n` is `n` times the formal R-series of `μ`. -/
theorem rSeries_integral_freeConvPow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConvPow n)) id =
      n • TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by
  simpa [Finset.fold_freeConv_const _ μ] using
    (univ : Finset (Fin n)).rSeries_integral_fold_freeConv (μ := fun _ => μ)
      (fun _ _ => inferInstance) (fun _ _ => hμ)

/-- Every positive-order free cumulant of `μ.freeConvPow n` is `n` times that of `μ`. -/
theorem freeCumulant_freeConvPow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (μ.freeConvPow n).freeCumulant k = n • μ.freeCumulant k := by
  simpa [Finset.fold_freeConv_const _ μ] using
    (univ : Finset (Fin n)).freeCumulant_fold_freeConv (μ := fun _ => μ)
      (fun _ _ => inferInstance) (fun _ _ => hμ) hk

/-- A compactly supported probability measure `ρ` equals `μ.freeConvPow n` iff its formal
R-series equals `n` times that of `μ`. -/
theorem eq_freeConvPow_iff_rSeries_integral_eq {ρ μ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] (hρ : IsCompact ρ.support)
    (hμ : IsCompact μ.support) (n : ℕ) :
    ρ = μ.freeConvPow n ↔
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id =
        n • TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by
  have := isProbabilityMeasure_freeConvPow hμ n
  rw [eq_iff_rSeries_integral_eq hρ (isCompact_support_freeConvPow μ n),
    rSeries_integral_freeConvPow hμ n]

/-- A compactly supported probability measure `ρ` equals `μ.freeConvPow n` iff all
positive-order free cumulants of `ρ` equal `n` times those of `μ`. -/
theorem eq_freeConvPow_iff_forall_freeCumulant_eq {ρ μ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] (hρ : IsCompact ρ.support)
    (hμ : IsCompact μ.support) (n : ℕ) :
    ρ = μ.freeConvPow n ↔ ∀ k : ℕ, k ≠ 0 → ρ.freeCumulant k = n • μ.freeCumulant k := by
  have := isProbabilityMeasure_freeConvPow hμ n
  rw [eq_iff_forall_freeCumulant_eq hρ (isCompact_support_freeConvPow μ n)]
  exact forall₂_congr fun k hk => by rw [freeCumulant_freeConvPow hμ n hk]

/-- The mean of `μ.freeConvPow n` is `n` times the mean of `μ`. -/
theorem integral_id_freeConvPow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    ∫ x, x ∂(μ.freeConvPow n) = n * ∫ x, x ∂μ := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, TauCeti.constantCoeff_rSeries, nsmul_eq_mul]
    using congrArg (PowerSeries.coeff 0) (rSeries_integral_freeConvPow hμ n)

/-- The variance of `μ.freeConvPow n` is `n` times the variance of `μ`. -/
theorem variance_id_freeConvPow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    variance id (μ.freeConvPow n) = n * variance id μ := by
  have := isProbabilityMeasure_freeConvPow hμ n
  simpa [coeff_one_rSeries_integral_eq_variance (continuousOn_id.memLp_of_isCompact_support
        (isCompact_support_freeConvPow μ n) support_mem_ae),
    coeff_one_rSeries_integral_eq_variance
      (continuousOn_id.memLp_of_isCompact_support hμ support_mem_ae), nsmul_eq_mul] using
    congrArg (PowerSeries.coeff 1) (rSeries_integral_freeConvPow hμ n)

end MeasureTheory.Measure

namespace TauCeti

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `a` is a freely independent family of selfadjoint elements with common law `μ` under a state
`φ`, then `∑ i ∈ s, a i` has law `μ.freeConvPow #s`. -/
theorem IsFreelyIndependentElements.law_sum_eq_freeConvPow {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    {μ : Measure ℝ} (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvPow #s := by
  rw [ha.law_sum hφ s hasa, Finset.fold_congr (g := fun _ => μ) fun i hi => hlaw i hi,
    Finset.fold_freeConv_const s μ]

/-- Subalgebra version of `IsFreelyIndependentElements.law_sum_eq_freeConvPow`. -/
theorem IsFreelyIndependent.law_sum_eq_freeConvPow {φ : A →ₚ[ℂ] ℂ}
    {B : ι → Subalgebra ℂ A} (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1)
    (s : Finset ι) {a : ι → A} {μ : Measure ℝ} (haB : ∀ i ∈ s, a i ∈ B i)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvPow #s := by
  rw [hB.law_sum hφ s haB hasa, Finset.fold_congr (g := fun _ => μ) fun i hi => hlaw i hi,
    Finset.fold_freeConv_const s μ]

end TauCeti
