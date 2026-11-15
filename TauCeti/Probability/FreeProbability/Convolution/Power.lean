/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Convolution.Basic

/-!
# Free additive convolution powers and finite free families

This file develops the `n`-fold free additive convolution power `μ.freeConvolutionPower n` and the
finite-family free additive convolution `Measure.finsetFreeConv s μ` on `Measure ℝ`, mirroring the
classical convolution power interface in `TauCeti.MeasureTheory.Group.Convolution.Power`.

Because `Measure.freeConv` (`⊞`) is unconditionally commutative and associative on `Measure ℝ`,
folding `⊞` over any finite set `s : Finset ι` with initial value `Measure.dirac 0` defines
`Measure.finsetFreeConv s μ` without hypotheses on `μ`, and `finsetFreeConv s (fun _ => μ)` agrees
unconditionally with `μ.freeConvolutionPower #s`.

In any C⋆-probability space—and hence in any concrete von Neumann algebra—the law of a finite sum
`∑ i ∈ s, a i` of freely independent selfadjoint elements with respect to a state `φ` is
`Measure.finsetFreeConv s (fun i => φ.law (a i))`, and reduces to `μ.freeConvolutionPower #s` when
the summands share a common law `μ`. In particular, finite sums in the canonical tracial C⋆- and
von Neumann realizations `FreeLawRealization` realize `Measure.finsetFreeConv` and
`Measure.freeConvolutionPower`.

## Main declarations

* `MeasureTheory.Measure.freeConvolutionPower`: the `n`-fold free additive convolution power of a
  measure on `ℝ`.
* `MeasureTheory.Measure.freeConvolutionPower_add`,
  `MeasureTheory.Measure.freeConvolutionPower_mul`,
  `MeasureTheory.Measure.freeConvolutionPower_one`: exponent laws for compactly supported
  probability measures.
* `MeasureTheory.Measure.rSeries_freeConvolutionPower`,
  `MeasureTheory.Measure.freeCumulant_freeConvolutionPower`: `R_{μ^{⊞ n}} = n • R_μ` and
  `κ_k(μ^{⊞ n}) = n • κ_k(μ)` for `k ≥ 1`.
* `MeasureTheory.Measure.freeConvolutionPower_map_affine`: affine equivariance of free convolution
  powers.
* `MeasureTheory.Measure.support_freeConvolutionPower_subset_Icc`,
  `MeasureTheory.Measure.support_freeConvolutionPower_subset_closedBall`: support bounds for free
  convolution powers.
* `MeasureTheory.Measure.finsetFreeConv`: free additive convolution of a finite family of measures.
* `TauCeti.IsFreelyIndependent.law_sum`, `TauCeti.IsFreelyIndependentElements.law_sum`,
  `TauCeti.IsFreelyIndependentElements.law_sum_freeConvolutionPower`: the law of a finite sum of
  freely independent selfadjoint elements in any C⋆- or von Neumann probability space.
* `TauCeti.FreeLawRealization.law_sum_cstarElement`,
  `TauCeti.FreeLawRealization.law_sum_vonNeumannElement`: transport of finite free convolutions
  through the canonical tracial C⋆- and von Neumann realizations.

## References

* D. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

noncomputable section

open MeasureTheory PowerSeries Finset
open scoped ComplexOrder NNReal FreeProbability

namespace MeasureTheory.Measure

/-! ### Finite free additive convolution powers -/

/-- The `n`-fold **free additive convolution power** `μ^{⊞ n}` of a measure `μ` on `ℝ`. The zeroth
power is the point mass `Measure.dirac 0`. -/
def freeConvolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ.freeConvolutionPower n ⊞ μ

@[simp]
theorem freeConvolutionPower_zero (μ : Measure ℝ) :
    μ.freeConvolutionPower 0 = Measure.dirac 0 :=
  (rfl)

@[simp]
theorem freeConvolutionPower_succ (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ.freeConvolutionPower n ⊞ μ :=
  (rfl)

instance isFiniteMeasure_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsFiniteMeasure (μ.freeConvolutionPower n) := by
  induction n with
  | zero => rw [freeConvolutionPower_zero]; infer_instance
  | succ n _ => rw [freeConvolutionPower_succ]; infer_instance

/-- Every free convolution power has compact topological support. -/
theorem isCompact_support_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsCompact (μ.freeConvolutionPower n).support := by
  induction n with
  | zero => simp [Measure.support_dirac]
  | succ n _ => exact isCompact_support_freeConv _ _

/-- Every free convolution power of a compactly supported probability measure is a probability
measure. -/
theorem isProbabilityMeasure_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    IsProbabilityMeasure (μ.freeConvolutionPower n) := by
  induction n with
  | zero => rw [freeConvolutionPower_zero]; infer_instance
  | succ n ih =>
    exact isProbabilityMeasure_freeConv (isCompact_support_freeConvolutionPower μ n) hμ

/-- The first free convolution power of a compactly supported probability measure is itself. -/
theorem freeConvolutionPower_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : μ.freeConvolutionPower 1 = μ := by
  rw [freeConvolutionPower_succ, freeConvolutionPower_zero, dirac_zero_freeConv hμ]

/-- Free convolution powers turn addition of exponents into free additive convolution. -/
theorem freeConvolutionPower_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (m n : ℕ) :
    μ.freeConvolutionPower (m + n) = μ.freeConvolutionPower m ⊞ μ.freeConvolutionPower n := by
  induction n with
  | zero =>
    have := isProbabilityMeasure_freeConvolutionPower hμ m
    rw [Nat.add_zero, freeConvolutionPower_zero,
      freeConv_dirac_zero (isCompact_support_freeConvolutionPower μ m)]
  | succ n ih =>
    rw [Nat.add_succ, freeConvolutionPower_succ, freeConvolutionPower_succ, ih, freeConv_assoc]

/-- Free convolution powers also satisfy the left recursion `μ^{⊞ (n + 1)} = μ ⊞ μ^{⊞ n}`. -/
theorem freeConvolutionPower_succ' (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ ⊞ μ.freeConvolutionPower n := by
  rw [freeConvolutionPower_succ, freeConv_comm]

/-- Free convolution powers turn multiplication of exponents into iterated powers. -/
theorem freeConvolutionPower_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (m n : ℕ) :
    μ.freeConvolutionPower (m * n) = (μ.freeConvolutionPower m).freeConvolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, freeConvolutionPower_add hμ, ih, freeConvolutionPower_succ]

/-- The R-series of `μ.freeConvolutionPower n` is `n • μ.rSeries`. -/
theorem rSeries_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    (μ.freeConvolutionPower n).rSeries = n • μ.rSeries := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := isProbabilityMeasure_freeConvolutionPower hμ n
    rw [freeConvolutionPower_succ,
      rSeries_freeConv (isCompact_support_freeConvolutionPower μ n) hμ, ih, succ_nsmul]

/-- Each positive-order free cumulant of `μ.freeConvolutionPower n` is `n` times that of `μ`. -/
theorem freeCumulant_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (μ.freeConvolutionPower n).freeCumulant k = n • μ.freeCumulant k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa [coeff_rSeries] using congrArg (coeff m) (rSeries_freeConvolutionPower hμ n)

/-- Free convolution powers of a point mass multiply its atom by `n`. -/
@[simp]
theorem freeConvolutionPower_dirac (x : ℝ) (n : ℕ) :
    (Measure.dirac x).freeConvolutionPower n = Measure.dirac (n • x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [freeConvolutionPower_succ, ih, dirac_freeConv_dirac, succ_nsmul]

/-- Every free convolution power of `Measure.dirac 0` is `Measure.dirac 0`. -/
theorem freeConvolutionPower_dirac_zero (n : ℕ) :
    (Measure.dirac (0 : ℝ)).freeConvolutionPower n = Measure.dirac 0 := by
  simp

/-- Free convolution powers of a semicircle law scale both its centre and its variance by `n`. -/
@[simp]
theorem freeConvolutionPower_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    (TauCeti.Probability.semicircleReal a v).freeConvolutionPower n =
      TauCeti.Probability.semicircleReal (n • a) (n • v) := by
  induction n with
  | zero => simp [TauCeti.Probability.semicircleReal_zero_var]
  | succ n ih =>
    rw [freeConvolutionPower_succ, ih, semicircleReal_freeConv_semicircleReal, succ_nsmul,
      succ_nsmul]

/-- Applying a real affine map `x ↦ a + b * x` commutes with `freeConvolutionPower`, accumulating
the offset `n` times. -/
theorem freeConvolutionPower_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) (n : ℕ) :
    (μ.map fun x => a + b * x).freeConvolutionPower n =
      (μ.freeConvolutionPower n).map fun x => (n : ℝ) * a + b * x := by
  induction n with
  | zero =>
    rw [freeConvolutionPower_zero, freeConvolutionPower_zero, Measure.map_dirac' (by fun_prop)]
    simp
  | succ n ih =>
    have := isProbabilityMeasure_freeConvolutionPower hμ n
    rw [freeConvolutionPower_succ, ih,
      freeConv_map_affine (isCompact_support_freeConvolutionPower μ n) hμ ((n : ℝ) * a) a b,
      ← freeConvolutionPower_succ]
    congr 1
    ext x
    push_cast
    ring

/-- Interval support bound for free convolution powers: `μ.support ⊆ [a, b]` implies
`(μ.freeConvolutionPower n).support ⊆ [n • a, n • b]`. -/
theorem support_freeConvolutionPower_subset_Icc {μ : Measure ℝ} {a b : ℝ}
    (hμ : μ.support ⊆ Set.Icc a b) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Icc (n • a) (n • b) := by
  induction n with
  | zero => simp [Measure.support_dirac]
  | succ n ih =>
    simpa only [freeConvolutionPower_succ, succ_nsmul] using support_freeConv_subset_Icc ih hμ

/-- Closed-ball support bound for free convolution powers: `μ.support ⊆ closedBall 0 r` implies
`(μ.freeConvolutionPower n).support ⊆ closedBall 0 (n * r)`. -/
theorem support_freeConvolutionPower_subset_closedBall {μ : Measure ℝ} {r : ℝ}
    (hμ : μ.support ⊆ Metric.closedBall 0 r) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Metric.closedBall 0 ((n : ℝ) * r) := by
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hμ ⊢
  simpa only [nsmul_eq_mul, mul_neg] using support_freeConvolutionPower_subset_Icc hμ n

/-! ### Free additive convolution of finite families -/

section Finset

variable {ι : Type*}

/-- The free additive convolution `⊞_{i ∈ s} μ i` of a finite family of measures on `ℝ`, folded
with identity `Measure.dirac 0`. -/
def finsetFreeConv (s : Finset ι) (μ : ι → Measure ℝ) : Measure ℝ :=
  s.fold freeConv (Measure.dirac 0) μ

@[simp]
theorem finsetFreeConv_empty (μ : ι → Measure ℝ) :
    finsetFreeConv ∅ μ = Measure.dirac 0 :=
  fold_empty

/-- Inserting a fresh index `i ∉ s` convolves `finsetFreeConv s μ` on the left by `μ i`. -/
theorem finsetFreeConv_insert [DecidableEq ι] {i : ι} {s : Finset ι} (hi : i ∉ s)
    (μ : ι → Measure ℝ) :
    finsetFreeConv (insert i s) μ = μ i ⊞ finsetFreeConv s μ :=
  fold_insert hi

/-- `finsetFreeConv s μ` depends only on the values of `μ` at indices in `s`. -/
theorem finsetFreeConv_congr {s : Finset ι} {μ ν : ι → Measure ℝ}
    (h : ∀ i ∈ s, μ i = ν i) : finsetFreeConv s μ = finsetFreeConv s ν :=
  fold_congr h

/-- Folding a constant measure `μ` over `s` gives `μ.freeConvolutionPower #s`, unconditionally on
`μ`. -/
@[simp]
theorem finsetFreeConv_const (s : Finset ι) (μ : Measure ℝ) :
    finsetFreeConv s (fun _ => μ) = μ.freeConvolutionPower #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [finsetFreeConv_insert hi, card_insert_of_notMem hi, ih, freeConvolutionPower_succ']

/-- `finsetFreeConv s μ` is always a finite measure. -/
instance isFiniteMeasure_finsetFreeConv (s : Finset ι) (μ : ι → Measure ℝ) :
    IsFiniteMeasure (finsetFreeConv s μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [finsetFreeConv_empty]; infer_instance
  | @insert i s hi _ => rw [finsetFreeConv_insert hi]; infer_instance

/-- The topological support of `finsetFreeConv s μ` is always compact. -/
theorem isCompact_support_finsetFreeConv (s : Finset ι) (μ : ι → Measure ℝ) :
    IsCompact (finsetFreeConv s μ).support := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.support_dirac]
  | @insert i s hi _ => rw [finsetFreeConv_insert hi]; exact isCompact_support_freeConv _ _

/-- `finsetFreeConv s μ` is a probability measure whenever every `μ i` (`i ∈ s`) is a compactly
supported probability measure. -/
theorem isProbabilityMeasure_finsetFreeConv {s : Finset ι} {μ : ι → Measure ℝ}
    (hP : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hK : ∀ i ∈ s, IsCompact (μ i).support) :
    IsProbabilityMeasure (finsetFreeConv s μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [finsetFreeConv_empty]; infer_instance
  | @insert i s hi ih =>
    have := hP i (mem_insert_self i s)
    have := ih (fun j hj => hP j (mem_insert_of_mem hj))
      (fun j hj => hK j (mem_insert_of_mem hj))
    rw [finsetFreeConv_insert hi]
    exact isProbabilityMeasure_freeConv (hK i (mem_insert_self i s))
      (isCompact_support_finsetFreeConv s μ)

@[simp]
theorem finsetFreeConv_singleton (i : ι) (μ : ι → Measure ℝ) [IsProbabilityMeasure (μ i)]
    (hμ : IsCompact (μ i).support) :
    finsetFreeConv {i} μ = μ i := by
  classical
  rw [← insert_empty_eq i, finsetFreeConv_insert (notMem_empty i), finsetFreeConv_empty,
    freeConv_dirac_zero hμ]

/-- Over a disjoint union `s ∪ t`, `finsetFreeConv` splits into `finsetFreeConv s μ ⊞
finsetFreeConv t μ` whenever the measures indexed by `t` are compactly supported probability
measures. -/
theorem finsetFreeConv_union [DecidableEq ι] {s t : Finset ι} (hst : Disjoint s t)
    {μ : ι → Measure ℝ} (hP : ∀ i ∈ t, IsProbabilityMeasure (μ i))
    (hK : ∀ i ∈ t, IsCompact (μ i).support) :
    finsetFreeConv (s ∪ t) μ = finsetFreeConv s μ ⊞ finsetFreeConv t μ := by
  induction s using Finset.induction_on with
  | empty =>
    have := isProbabilityMeasure_finsetFreeConv hP hK
    simp [dirac_zero_freeConv (isCompact_support_finsetFreeConv t μ)]
  | @insert i s hi ih =>
    rw [disjoint_insert_left] at hst
    have hi_ut : i ∉ s ∪ t := by simp [hi, hst.1]
    rw [insert_union, finsetFreeConv_insert hi_ut, finsetFreeConv_insert hi, ih hst.2,
      freeConv_assoc]

/-- The R-series of `finsetFreeConv s μ` is the sum `∑ i ∈ s, (μ i).rSeries`. -/
theorem rSeries_finsetFreeConv {s : Finset ι} {μ : ι → Measure ℝ}
    (hP : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hK : ∀ i ∈ s, IsCompact (μ i).support) :
    (finsetFreeConv s μ).rSeries = ∑ i ∈ s, (μ i).rSeries := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have := hP i (mem_insert_self i s)
    have := isProbabilityMeasure_finsetFreeConv
      (fun j hj => hP j (mem_insert_of_mem hj)) (fun j hj => hK j (mem_insert_of_mem hj))
    rw [finsetFreeConv_insert hi,
      rSeries_freeConv (hK i (mem_insert_self i s)) (isCompact_support_finsetFreeConv s μ),
      ih (fun j hj => hP j (mem_insert_of_mem hj)) (fun j hj => hK j (mem_insert_of_mem hj)),
      sum_insert hi]

/-- Each positive-order free cumulant of `finsetFreeConv s μ` is `∑ i ∈ s, (μ i).freeCumulant n`. -/
theorem freeCumulant_finsetFreeConv {s : Finset ι} {μ : ι → Measure ℝ}
    (hP : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hK : ∀ i ∈ s, IsCompact (μ i).support)
    {n : ℕ} (hn : n ≠ 0) :
    (finsetFreeConv s μ).freeCumulant n = ∑ i ∈ s, (μ i).freeCumulant n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa [coeff_rSeries] using congrArg (coeff m) (rSeries_finsetFreeConv hP hK)

/-- Interval support bound for `finsetFreeConv`: if `(μ i).support ⊆ [a i, b i]` for `i ∈ s`, then
`(finsetFreeConv s μ).support ⊆ [∑ i ∈ s, a i, ∑ i ∈ s, b i]`. -/
theorem support_finsetFreeConv_subset_Icc {s : Finset ι} {μ : ι → Measure ℝ} {a b : ι → ℝ}
    (h : ∀ i ∈ s, (μ i).support ⊆ Set.Icc (a i) (b i)) :
    (finsetFreeConv s μ).support ⊆ Set.Icc (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.support_dirac]
  | @insert i s hi ih =>
    rw [finsetFreeConv_insert hi, sum_insert hi, sum_insert hi]
    exact support_freeConv_subset_Icc (h i (mem_insert_self i s))
      (ih fun j hj => h j (mem_insert_of_mem hj))

/-- Affine equivariance of `finsetFreeConv` with a common slope `b`: translations accumulate as
`∑ i ∈ s, a i`. -/
theorem finsetFreeConv_map_affine {s : Finset ι} {μ : ι → Measure ℝ}
    (hP : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hK : ∀ i ∈ s, IsCompact (μ i).support)
    (a : ι → ℝ) (b : ℝ) :
    finsetFreeConv s (fun i => (μ i).map fun x => a i + b * x) =
      (finsetFreeConv s μ).map fun x => (∑ i ∈ s, a i) + b * x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [finsetFreeConv_empty, finsetFreeConv_empty, Measure.map_dirac' (by fun_prop)]
    simp
  | @insert i s hi ih =>
    have := hP i (mem_insert_self i s)
    have := isProbabilityMeasure_finsetFreeConv
      (fun j hj => hP j (mem_insert_of_mem hj)) (fun j hj => hK j (mem_insert_of_mem hj))
    rw [finsetFreeConv_insert hi,
      ih (fun j hj => hP j (mem_insert_of_mem hj)) (fun j hj => hK j (mem_insert_of_mem hj)),
      freeConv_map_affine (hK i (mem_insert_self i s)) (isCompact_support_finsetFreeConv s μ)
        (a i) (∑ j ∈ s, a j) b,
      ← finsetFreeConv_insert hi, sum_insert hi]

end Finset

end MeasureTheory.Measure

namespace TauCeti

section FamilyLaw

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : A →ₚ[ℂ] ℂ}

/-- **Law of a sum over a freely independent family of subalgebras.** In any C⋆-algebra (including
any concrete von Neumann algebra) with state `φ`, if `B` is freely independent for `φ` and each
`a i` (`i ∈ s`) is a selfadjoint element of `B i`, then `φ.law (∑ i ∈ s, a i)` is the finite free
additive convolution `Measure.finsetFreeConv s (fun i => φ.law (a i))`. -/
theorem IsFreelyIndependent.law_sum {B : ι → Subalgebra ℂ A}
    (h : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) {s : Finset ι} {a : ι → A}
    (haB : ∀ i ∈ s, a i ∈ B i) (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    φ.law (∑ i ∈ s, a i) = Measure.finsetFreeConv s (fun i => φ.law (a i)) := by
  have hsa : IsSelfAdjoint (∑ i ∈ s, a i) := isSelfAdjoint_sum s ha
  have : IsProbabilityMeasure (φ.law (∑ i ∈ s, a i)) := φ.isProbabilityMeasure_law hφ hsa
  have : IsProbabilityMeasure (Measure.finsetFreeConv s fun i => φ.law (a i)) :=
    Measure.isProbabilityMeasure_finsetFreeConv
      (fun i hi => φ.isProbabilityMeasure_law hφ (ha i hi))
      (fun i _ => φ.isCompact_support_law (a i))
  rw [← Measure.rSeries_eq_iff (φ.isCompact_support_law _)
      (Measure.isCompact_support_finsetFreeConv s _),
    Measure.rSeries_finsetFreeConv (fun i hi => φ.isProbabilityMeasure_law hφ (ha i hi))
      (fun i _ => φ.isCompact_support_law (a i))]
  ext n
  apply Complex.ofReal_injective
  have hcoeff := congrArg (coeff n) ((φ.map_ofReal_rSeries_law hsa).trans (h.rSeries_sum hφ haB))
  simp only [coeff_map, Complex.ofRealHom_eq_coe, map_sum, Complex.ofReal_sum] at hcoeff ⊢
  rw [hcoeff]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa using (congrArg (coeff n) (φ.map_ofReal_rSeries_law (ha i hi))).symm

/-- If `c` is a freely independent family of elements for a state `φ` and each `c i` (`i ∈ s`) is
selfadjoint, then `φ.law (∑ i ∈ s, c i) = Measure.finsetFreeConv s (fun i => φ.law (c i))`. -/
theorem IsFreelyIndependentElements.law_sum {c : ι → A}
    (h : IsFreelyIndependentElements φ.toLinearMap c) (hφ : φ 1 = 1) (s : Finset ι)
    (hc : ∀ i ∈ s, IsSelfAdjoint (c i)) :
    φ.law (∑ i ∈ s, c i) = Measure.finsetFreeConv s (fun i => φ.law (c i)) :=
  (isFreelyIndependentElements_iff.1 h).law_sum hφ
    (fun i _ => Algebra.self_mem_adjoin_singleton ℂ (c i)) hc

/-- **Law of a sum of identically distributed freely independent selfadjoint elements.** If `c` is
freely independent for a state `φ` and every `c i` (`i ∈ s`) is selfadjoint with law `μ`, then
`φ.law (∑ i ∈ s, c i) = μ.freeConvolutionPower #s`. -/
theorem IsFreelyIndependentElements.law_sum_freeConvolutionPower {c : ι → A}
    (h : IsFreelyIndependentElements φ.toLinearMap c) (hφ : φ 1 = 1) (s : Finset ι)
    (hc : ∀ i ∈ s, IsSelfAdjoint (c i)) {μ : Measure ℝ} (hμ : ∀ i ∈ s, φ.law (c i) = μ) :
    φ.law (∑ i ∈ s, c i) = μ.freeConvolutionPower #s := by
  rw [h.law_sum hφ s hc, Measure.finsetFreeConv_congr hμ, Measure.finsetFreeConv_const]

end FamilyLaw

namespace FreeLawRealization

variable {I : Type*} [DecidableEq I]

/-- In the canonical C⋆-realization of `μ`, the sum of generators over `s : Finset I` has law
`Measure.finsetFreeConv s μ` whenever the measures indexed by `s` are compactly supported
probability measures. -/
theorem law_sum_cstarElement {μ : I → Measure ℝ} {s : Finset I}
    (hP : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hK : ∀ i ∈ s, IsCompact (μ i).support) :
    (cstarState μ).law (∑ i ∈ s, cstarElement μ i) = Measure.finsetFreeConv s μ := by
  rw [(isFreelyIndependentElements_cstarElement μ).law_sum (cstarState_one μ) s
    (fun i _ => isSelfAdjoint_cstarElement μ i)]
  refine Measure.finsetFreeConv_congr fun i hi => ?_
  have := hP i hi
  exact law_cstarElement (hK i hi)

/-- In the canonical von Neumann realization of `μ`, the sum of generators over `s : Finset I` has
law `Measure.finsetFreeConv s μ` whenever the measures indexed by `s` are compactly supported
probability measures. -/
theorem law_sum_vonNeumannElement {μ : I → Measure ℝ} {s : Finset I}
    (hP : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hK : ∀ i ∈ s, IsCompact (μ i).support) :
    (vonNeumannState μ).law (∑ i ∈ s, vonNeumannElement μ i) = Measure.finsetFreeConv s μ := by
  simp_rw [← toVonNeumann_cstarElement]
  rw [← map_sum (toVonNeumann μ),
    law_toVonNeumann μ (isSelfAdjoint_sum s fun i _ => isSelfAdjoint_cstarElement μ i),
    law_sum_cstarElement hP hK]

/-- For a constant family `fun _ : I => ν`, the sum over `s` in the canonical C⋆-realization has
law `ν.freeConvolutionPower #s`. -/
theorem law_sum_cstarElement_const {ν : Measure ℝ} [hP : IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (s : Finset I) :
    (cstarState fun _ : I => ν).law (∑ i ∈ s, cstarElement (fun _ : I => ν) i) =
      ν.freeConvolutionPower #s := by
  rw [law_sum_cstarElement (fun _ _ => hP) (fun _ _ => hν), Measure.finsetFreeConv_const]

/-- For a constant family `fun _ : I => ν`, the sum over `s` in the canonical von Neumann
realization has law `ν.freeConvolutionPower #s`. -/
theorem law_sum_vonNeumannElement_const {ν : Measure ℝ} [hP : IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (s : Finset I) :
    (vonNeumannState fun _ : I => ν).law (∑ i ∈ s, vonNeumannElement (fun _ : I => ν) i) =
      ν.freeConvolutionPower #s := by
  rw [law_sum_vonNeumannElement (fun _ _ => hP) (fun _ _ => hν), Measure.finsetFreeConv_const]

end FreeLawRealization

end TauCeti
