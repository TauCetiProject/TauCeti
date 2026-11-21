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
convolution power `MeasureTheory.Measure.freeConvolutionPower` (`μ^{⊞ n}`).

## Main definitions

* `MeasureTheory.Measure.freeConvolutionPower`: the `n`-fold free additive convolution power
  `μ^{⊞ n}`, with `μ^{⊞ 0} = Measure.dirac 0`.

## Main results

* `MeasureTheory.Measure.isProbabilityMeasure_fold_freeConv_iff`,
  `MeasureTheory.Measure.rSeries_integral_fold_freeConv`,
  `MeasureTheory.Measure.freeCumulant_integral_fold_freeConv`,
  `MeasureTheory.Measure.eq_fold_freeConv_iff_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_fold_freeConv_iff_forall_freeCumulant_integral_eq`,
  `MeasureTheory.Measure.support_fold_freeConv_subset_Icc`: validity, formal series, cumulants,
  determinacy, and support bounds for finite `Finset.fold`s of `freeConv`.
* `TauCeti.IsFreelyIndependentElements.law_sum`, `TauCeti.IsFreelyIndependent.law_sum`:
  C⋆- and von Neumann finite-sum transport.
* `MeasureTheory.Measure.freeConvolutionPower_add`,
  `MeasureTheory.Measure.freeConvolutionPower_mul`,
  `MeasureTheory.Measure.freeConvolutionPower_map_affine`,
  `MeasureTheory.Measure.rSeries_integral_freeConvolutionPower`,
  `MeasureTheory.Measure.freeCumulant_integral_freeConvolutionPower`,
  `MeasureTheory.Measure.eq_freeConvolutionPower_iff_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_freeConvolutionPower_iff_forall_freeCumulant_integral_eq`: algebraic,
  affine, support, series, cumulant, determinacy, mean, and variance laws for
  `freeConvolutionPower`.

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

namespace MeasureTheory.Measure

variable {ι : Type*} (s : Finset ι) {μ : ι → Measure ℝ}

/-- Folding `freeConv` with base `Measure.dirac 0` always yields a measure with compact support. -/
theorem isCompact_support_fold_freeConv (μ : ι → Measure ℝ) :
    IsCompact (s.fold freeConv (Measure.dirac 0) μ).support := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp [Measure.support_dirac]
  · rw [← Finset.insert_erase hi, Finset.fold_insert (Finset.notMem_erase i s)]
    exact isCompact_support_freeConv _ _

/-- Folding `freeConv` with base `Measure.dirac 0` always yields either `0` or a probability
measure (hence a finite measure). -/
instance isZeroOrProbabilityMeasure_fold_freeConv (μ : ι → Measure ℝ) :
    IsZeroOrProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp only [Finset.fold_empty]; infer_instance
  · rw [← Finset.insert_erase hi, Finset.fold_insert (Finset.notMem_erase i s)]
    infer_instance

/-- Folding `freeConv` with base `Measure.dirac 0` yields a probability measure iff every indexed
measure in `s` is a compactly supported probability measure (including when `s = ∅`). -/
theorem isProbabilityMeasure_fold_freeConv_iff :
    IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) ↔
      ∀ i ∈ s, IsProbabilityMeasure (μ i) ∧ IsCompact (μ i).support := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.fold_empty, notMem_empty, IsEmpty.forall_iff, implies_true, iff_true]
      infer_instance
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, isProbabilityMeasure_freeConv_iff,
        and_iff_left (isCompact_support_fold_freeConv s μ), ih, Finset.forall_mem_insert]

/-- Folding `freeConv` with base `Measure.dirac 0` yields `0` iff some indexed measure in `s` is
not a compactly supported probability measure. -/
theorem fold_freeConv_eq_zero_iff :
    s.fold freeConv (Measure.dirac 0) μ = 0 ↔
      ∃ i ∈ s, ¬(IsProbabilityMeasure (μ i) ∧ IsCompact (μ i).support) := by
  have h : s.fold freeConv (Measure.dirac 0) μ = 0 ↔
      ¬IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) :=
    ⟨fun h0 hp => not_isProbabilityMeasure_zero (h0 ▸ hp),
      fun hnp => (eq_zero_or_isProbabilityMeasure _).resolve_right hnp⟩
  rw [isProbabilityMeasure_fold_freeConv_iff, not_forall] at h
  simpa only [not_imp, exists_prop] using h

/-- Folding `freeConv` with base `Measure.dirac 0` over compactly supported probability measures
yields a probability measure (including when `s = ∅`). -/
theorem isProbabilityMeasure_fold_freeConv (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) :=
  (isProbabilityMeasure_fold_freeConv_iff s).mpr fun i hi => ⟨hprob i hi, hcomp i hi⟩

/-- Interval support bounds add across a finite `Finset.fold` of `freeConv`, including `s = ∅` and
when any factor is not a probability measure. -/
theorem support_fold_freeConv_subset_Icc {m M : ι → ℝ}
    (hI : ∀ i ∈ s, (μ i).support ⊆ Set.Icc (m i) (M i)) :
    (s.fold freeConv (Measure.dirac 0) μ).support ⊆ Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.support_dirac]
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, sum_insert hi, sum_insert hi]
      exact support_freeConv_subset_Icc (hI i (mem_insert_self i s))
        (ih fun j hj => hI j (mem_insert_of_mem hj))

/-- The formal R-series of a finite `Finset.fold` of `freeConv` is the sum of the individual formal
R-series, including `s = ∅`. -/
theorem rSeries_integral_fold_freeConv (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(s.fold freeConv (Measure.dirac 0) μ)) id =
      ∑ i ∈ s, TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ i) id := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hp' := fun j hj => hprob j (mem_insert_of_mem hj)
      have hc' := fun j hj => hcomp j (mem_insert_of_mem hj)
      have := hprob i (mem_insert_self i s)
      have := isProbabilityMeasure_fold_freeConv s hp' hc'
      rw [Finset.fold_insert hi, sum_insert hi, rSeries_integral_freeConv
        (hcomp i (mem_insert_self i s)) (isCompact_support_fold_freeConv s μ), ih hp' hc']

/-- Nonempty free cumulants add across a finite `Finset.fold` of `freeConv`. -/
theorem freeCumulant_integral_fold_freeConv (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) {α : Type*} [LinearOrder α] {t : Finset α}
    (ht : t.Nonempty) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂(s.fold freeConv (Measure.dirac 0) μ))
        (fun _ : α => (id : ℝ → ℝ)) t =
      ∑ i ∈ s, TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ i)
        (fun _ : α => (id : ℝ → ℝ)) t := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht.card_pos.ne'
  simp_rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries, hk,
    TauCeti.coeff_succ_freeCumulantSeries, rSeries_integral_fold_freeConv s hprob hcomp,
    _root_.map_sum (PowerSeries.coeff k)]

/-- A compactly supported probability measure `ρ` equals `s.fold freeConv (Measure.dirac 0) μ`
iff its formal R-series equals the sum of those of `μ i` over `i ∈ s`. -/
theorem eq_fold_freeConv_iff_rSeries_integral_eq {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : IsCompact ρ.support) (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    ρ = s.fold freeConv (Measure.dirac 0) μ ↔
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id =
        ∑ i ∈ s, TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ i) id := by
  have := isProbabilityMeasure_fold_freeConv s hprob hcomp
  rw [eq_iff_rSeries_integral_eq hρ (isCompact_support_fold_freeConv s μ),
    rSeries_integral_fold_freeConv s hprob hcomp]

/-- A compactly supported probability measure `ρ` equals `s.fold freeConv (Measure.dirac 0) μ`
iff all positive-order free cumulants of `ρ` equal the sums of those of `μ i` over `i ∈ s`. -/
theorem eq_fold_freeConv_iff_forall_freeCumulant_integral_eq {ρ : Measure ℝ}
    [IsProbabilityMeasure ρ] (hρ : IsCompact ρ.support)
    (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    ρ = s.fold freeConv (Measure.dirac 0) μ ↔ ∀ n : ℕ, n ≠ 0 →
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) (fun _ : Fin n => (id : ℝ → ℝ)) univ =
        ∑ i ∈ s, TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ i)
          (fun _ : Fin n => (id : ℝ → ℝ)) univ := by
  have := isProbabilityMeasure_fold_freeConv s hprob hcomp
  rw [eq_iff_forall_freeCumulant_integral_eq hρ (isCompact_support_fold_freeConv s μ)]
  exact forall₂_congr fun n hn => by
    rw [freeCumulant_integral_fold_freeConv s hprob hcomp ⟨⟨0, Nat.pos_of_ne_zero hn⟩, mem_univ _⟩]

end MeasureTheory.Measure

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
  have h := ((hB.comp Subtype.val_injective).isFreelyIndependentElements fun i : s =>
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

/-- The `n`-fold free additive convolution power `μ^{⊞ n}` of a measure on `ℝ`, with zeroth power
`Measure.dirac 0`. -/
def freeConvolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (freeConvolutionPower μ n).freeConv μ

/-- The zeroth free convolution power of any measure on `ℝ` is `Measure.dirac 0`. -/
@[simp] theorem freeConvolutionPower_zero (μ : Measure ℝ) :
    μ.freeConvolutionPower 0 = Measure.dirac 0 := by rfl

/-- Right recursion `μ^{⊞ (n + 1)} = μ^{⊞ n} ⊞ μ` for free convolution powers. -/
@[simp] theorem freeConvolutionPower_succ (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = (μ.freeConvolutionPower n).freeConv μ := by rfl

/-- Every free convolution power is either `0` or a probability measure (hence finite). -/
instance isZeroOrProbabilityMeasure_freeConvolutionPower (μ : Measure ℝ) :
    ∀ n : ℕ, IsZeroOrProbabilityMeasure (μ.freeConvolutionPower n)
  | 0 => by rw [freeConvolutionPower_zero]; infer_instance
  | _ + 1 => by rw [freeConvolutionPower_succ]; infer_instance

/-- For `n ≠ 0`, outside compactly supported probability measures `freeConvolutionPower` is `0`. -/
theorem freeConvolutionPower_eq_zero_of_not {μ : Measure ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support)) : μ.freeConvolutionPower n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact freeConv_eq_zero_of_not fun h' => h h'.2

/-- Every free convolution power of any measure on `ℝ` has compact topological support. -/
theorem isCompact_support_freeConvolutionPower (μ : Measure ℝ) :
    ∀ n : ℕ, IsCompact (μ.freeConvolutionPower n).support
  | 0 => by simp [Measure.support_dirac]
  | _ + 1 => isCompact_support_freeConv _ _

/-- Every free convolution power of a compactly supported probability measure is a probability
measure. -/
theorem isProbabilityMeasure_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : ∀ n : ℕ, IsProbabilityMeasure (μ.freeConvolutionPower n)
  | 0 => by rw [freeConvolutionPower_zero]; infer_instance
  | n + 1 => by
      have := isProbabilityMeasure_freeConvolutionPower hμ n
      exact isProbabilityMeasure_freeConv (isCompact_support_freeConvolutionPower μ n) hμ

/-- `μ.freeConvolutionPower n` is a probability measure iff `n = 0` or `μ` is a compactly supported
probability measure. -/
theorem isProbabilityMeasure_freeConvolutionPower_iff {μ : Measure ℝ} {n : ℕ} :
    IsProbabilityMeasure (μ.freeConvolutionPower n) ↔
      n = 0 ∨ (IsProbabilityMeasure μ ∧ IsCompact μ.support) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [freeConvolutionPower_zero, true_or, iff_true]; infer_instance
  · simp only [hn, false_or]
    exact ⟨fun hp => by
      by_contra h
      exact not_isProbabilityMeasure_zero (freeConvolutionPower_eq_zero_of_not hn h ▸ hp),
      fun ⟨_, hμ⟩ => isProbabilityMeasure_freeConvolutionPower hμ n⟩

/-- `μ.freeConvolutionPower n` equals `0` iff `n ≠ 0` and `μ` is not a compactly supported
probability measure. -/
theorem freeConvolutionPower_eq_zero_iff {μ : Measure ℝ} {n : ℕ} :
    μ.freeConvolutionPower n = 0 ↔
      n ≠ 0 ∧ ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support) := by
  have h : μ.freeConvolutionPower n = 0 ↔ ¬IsProbabilityMeasure (μ.freeConvolutionPower n) :=
    ⟨fun h0 hp => not_isProbabilityMeasure_zero (h0 ▸ hp),
      fun hnp => (eq_zero_or_isProbabilityMeasure _).resolve_right hnp⟩
  rwa [isProbabilityMeasure_freeConvolutionPower_iff, not_or] at h

/-- The first free convolution power of a compactly supported probability measure is itself. -/
theorem freeConvolutionPower_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : μ.freeConvolutionPower 1 = μ := dirac_zero_freeConv hμ

/-- Free convolution powers turn addition of exponents into `freeConv`, unconditionally for all
measures on `ℝ`. -/
theorem freeConvolutionPower_add (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvolutionPower (m + n) =
      (μ.freeConvolutionPower m).freeConv (μ.freeConvolutionPower n) := by
  induction n with
  | zero =>
      by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support
      · have := h.1; have := isProbabilityMeasure_freeConvolutionPower h.2 m
        exact (freeConv_dirac_zero (isCompact_support_freeConvolutionPower μ m)).symm
      · rcases eq_or_ne m 0 with rfl | hm
        · simp
        · simp [freeConvolutionPower_eq_zero_of_not hm h]
  | succ n ih =>
      rw [Nat.add_succ, freeConvolutionPower_succ, freeConvolutionPower_succ, ih, freeConv_assoc]

/-- Left recursion `μ^{⊞ (n + 1)} = μ ⊞ μ^{⊞ n}`, unconditionally for all measures on `ℝ`. -/
theorem freeConvolutionPower_succ' (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ.freeConv (μ.freeConvolutionPower n) := freeConv_comm _ _

/-- Free convolution powers of a Dirac mass add its atom `n` times. -/
@[simp] theorem freeConvolutionPower_dirac (a : ℝ) (n : ℕ) :
    (Measure.dirac a).freeConvolutionPower n = Measure.dirac (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [freeConvolutionPower_succ, ih, dirac_freeConv_dirac, succ_nsmul]

/-- Iterated free convolution powers multiply exponents, unconditionally for all measures on `ℝ`. -/
theorem freeConvolutionPower_mul (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvolutionPower (m * n) = (μ.freeConvolutionPower m).freeConvolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, freeConvolutionPower_add, ih, freeConvolutionPower_succ]

/-- **Affine equivariance of free convolution powers.** For a compactly supported probability
measure `μ`, pushing `μ` forward by `x ↦ a + b * x` and taking the `n`-th free convolution power
equals pushing `μ.freeConvolutionPower n` forward by `x ↦ (n : ℝ) * a + b * x`. -/
theorem freeConvolutionPower_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) (n : ℕ) :
    (μ.map fun x => a + b * x).freeConvolutionPower n =
      (μ.freeConvolutionPower n).map fun x => (n : ℝ) * a + b * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have := isProbabilityMeasure_freeConvolutionPower hμ n
      rw [freeConvolutionPower_succ, ih,
        freeConv_map_affine (isCompact_support_freeConvolutionPower μ n) hμ ((n : ℝ) * a) a b,
        ← freeConvolutionPower_succ]
      congr 1; funext x; push_cast; ring

/-- Translating `μ` by `a` translates `μ.freeConvolutionPower n` by `n • a`, unconditionally for
all measures on `ℝ`. -/
theorem freeConvolutionPower_map_add (μ : Measure ℝ) (a : ℝ) (n : ℕ) :
    (μ.map (a + ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (n • a + ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [freeConvolutionPower_succ, ih, freeConv_map_add, ← freeConvolutionPower_succ, succ_nsmul]

/-- Scaling `μ` by `b` scales `μ.freeConvolutionPower n` by `b` (including `n = 0` and `b = 0`). -/
theorem freeConvolutionPower_map_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (b : ℝ) (n : ℕ) :
    (μ.map (b * ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (b * ·) := by
  simpa using freeConvolutionPower_map_affine hμ 0 b n

/-- Reflection `Measure.neg` commutes with free convolution powers unconditionally. -/
theorem freeConvolutionPower_neg (μ : Measure ℝ) (n : ℕ) :
    μ.neg.freeConvolutionPower n = (μ.freeConvolutionPower n).neg := by
  induction n with
  | zero => simp [Measure.neg_def, Measure.map_dirac' measurable_neg]
  | succ n ih => rw [freeConvolutionPower_succ, ih, neg_freeConv_neg, freeConvolutionPower_succ]

/-- Folding `freeConv` over a constant measure on `s` gives `μ.freeConvolutionPower #s`. -/
theorem fold_freeConv_const {ι : Type*} (s : Finset ι) (μ : Measure ℝ) :
    s.fold freeConv (Measure.dirac 0) (fun _ => μ) = μ.freeConvolutionPower #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, card_insert_of_notMem hi, ih, freeConvolutionPower_succ']

/-- Interval support bounds scale by `n` under `freeConvolutionPower`, unconditionally for all
measures on `ℝ` and including `n = 0`. -/
theorem support_freeConvolutionPower_subset_Icc {μ : Measure ℝ} {m M : ℝ}
    (hI : μ.support ⊆ Set.Icc m M) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Icc ((n : ℝ) * m) ((n : ℝ) * M) := by
  simpa [fold_freeConv_const _ μ, nsmul_eq_mul] using
    support_fold_freeConv_subset_Icc (univ : Finset (Fin n)) (μ := fun _ => μ) fun _ _ => hI

/-- **Formal R-series of a free convolution power**: `R_{μ^{⊞ n}} = n • R_μ`. -/
theorem rSeries_integral_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConvolutionPower n)) id =
      n • TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by
  simpa [fold_freeConv_const _ μ] using rSeries_integral_fold_freeConv (univ : Finset (Fin n))
    (μ := fun _ => μ) (fun _ _ => inferInstance) (fun _ _ => hμ)

/-- **Free cumulants of a free convolution power**: `κ_s(μ^{⊞ n}) = n • κ_s(μ)` for nonempty `s`. -/
theorem freeCumulant_integral_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) {α : Type*} [LinearOrder α] {s : Finset α}
    (hs : s.Nonempty) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConvolutionPower n))
        (fun _ : α => (id : ℝ → ℝ)) s =
      n • TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : α => (id : ℝ → ℝ)) s := by
  simpa [fold_freeConv_const _ μ] using freeCumulant_integral_fold_freeConv (univ : Finset (Fin n))
    (μ := fun _ => μ) (fun _ _ => inferInstance) (fun _ _ => hμ) hs

/-- A compactly supported probability measure `ρ` equals `μ.freeConvolutionPower n` iff its formal
R-series equals `n` times that of `μ`. -/
theorem eq_freeConvolutionPower_iff_rSeries_integral_eq {ρ μ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] (hρ : IsCompact ρ.support)
    (hμ : IsCompact μ.support) (n : ℕ) :
    ρ = μ.freeConvolutionPower n ↔
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id =
        n • TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by
  have := isProbabilityMeasure_freeConvolutionPower hμ n
  rw [eq_iff_rSeries_integral_eq hρ (isCompact_support_freeConvolutionPower μ n),
    rSeries_integral_freeConvolutionPower hμ n]

/-- A compactly supported probability measure `ρ` equals `μ.freeConvolutionPower n` iff all
positive-order free cumulants of `ρ` equal `n` times those of `μ`. -/
theorem eq_freeConvolutionPower_iff_forall_freeCumulant_integral_eq {ρ μ : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] (hρ : IsCompact ρ.support)
    (hμ : IsCompact μ.support) (n : ℕ) :
    ρ = μ.freeConvolutionPower n ↔ ∀ k : ℕ, k ≠ 0 →
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) (fun _ : Fin k => (id : ℝ → ℝ)) univ =
        n • TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ)
          (fun _ : Fin k => (id : ℝ → ℝ)) univ := by
  have := isProbabilityMeasure_freeConvolutionPower hμ n
  rw [eq_iff_forall_freeCumulant_integral_eq hρ (isCompact_support_freeConvolutionPower μ n)]
  exact forall₂_congr fun k hk => by
    rw [freeCumulant_integral_freeConvolutionPower hμ n ⟨⟨0, Nat.pos_of_ne_zero hk⟩, mem_univ _⟩]

/-- The mean of `μ^{⊞ n}` is `n` times the mean of `μ`. -/
theorem integral_id_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    ∫ x, x ∂(μ.freeConvolutionPower n) = n * ∫ x, x ∂μ := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, TauCeti.constantCoeff_rSeries, nsmul_eq_mul]
    using congrArg (PowerSeries.coeff 0) (rSeries_integral_freeConvolutionPower hμ n)

/-- The variance of `μ^{⊞ n}` is `n` times the variance of `μ`. -/
theorem variance_id_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    variance id (μ.freeConvolutionPower n) = n * variance id μ := by
  have := isProbabilityMeasure_freeConvolutionPower hμ n
  simpa [coeff_one_rSeries_integral_eq_variance (continuousOn_id.memLp_of_isCompact_support
        (isCompact_support_freeConvolutionPower μ n) support_mem_ae),
    coeff_one_rSeries_integral_eq_variance
      (continuousOn_id.memLp_of_isCompact_support hμ support_mem_ae), nsmul_eq_mul] using
    congrArg (PowerSeries.coeff 1) (rSeries_integral_freeConvolutionPower hμ n)

end MeasureTheory.Measure

namespace TauCeti

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `a` is a freely independent family of selfadjoint elements with common law `μ` under a state
`φ`, then `∑ i ∈ s, a i` has law `μ.freeConvolutionPower #s`. -/
theorem IsFreelyIndependentElements.law_sum_eq_freeConvolutionPower {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    {μ : Measure ℝ} (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvolutionPower #s := by
  rw [ha.law_sum hφ s hasa, Finset.fold_congr (g := fun _ => μ) fun i hi => hlaw i hi,
    Measure.fold_freeConv_const s μ]

/-- Subalgebra version of `IsFreelyIndependentElements.law_sum_eq_freeConvolutionPower`. -/
theorem IsFreelyIndependent.law_sum_eq_freeConvolutionPower {φ : A →ₚ[ℂ] ℂ}
    {B : ι → Subalgebra ℂ A} (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1)
    (s : Finset ι) {a : ι → A} {μ : Measure ℝ} (haB : ∀ i ∈ s, a i ∈ B i)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvolutionPower #s := by
  rw [hB.law_sum hφ s haB hasa, Finset.fold_congr (g := fun _ => μ) fun i hi => hlaw i hi,
    Measure.fold_freeConv_const s μ]

end TauCeti
