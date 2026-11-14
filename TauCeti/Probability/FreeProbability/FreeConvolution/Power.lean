/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.FreeConvolution.Basic
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.FreeProbability.WeakClosure

/-!
# Free additive convolution powers and laws of finite free sums

For a Borel measure `μ` on `ℝ`, `μ.freeConvolutionPower n` is the `n`-fold free additive
convolution `μ^{⊞ n}`, with `μ^{⊞ 0} = δ₀` and `μ^{⊞ (n + 1)} = μ^{⊞ n} ⊞ μ`. Because
`MeasureTheory.Measure.freeConv` is totalized by `0` outside compactly supported probability
measures, the exponent laws `μ^{⊞ (m + n)} = μ^{⊞ m} ⊞ μ^{⊞ n}` and
`μ^{⊞ (m * n)} = (μ^{⊞ m})^{⊞ n}`, point-mass powers, translations, reflections, nonconstant
affine pushforwards, and interval support bounds hold unconditionally for all Borel measures `μ`
and all `m, n : ℕ`.

For any finite freely independent family of selfadjoint elements in a C⋆-algebra (including any
concrete von Neumann algebra or weak-operator closure under a normalized vector state), the law
of their finite sum is the `Finset.fold` of their individual laws under `⊞`, specializing to
`μ.freeConvolutionPower #s` when the summands share a common law `μ`.

## Main definitions

* `MeasureTheory.Measure.freeConvolutionPower`: the `n`-fold free additive convolution `μ^{⊞ n}`
  of a Borel measure `μ` on `ℝ`.

## Main results

* `MeasureTheory.Measure.freeConvolutionPower_add`,
  `MeasureTheory.Measure.freeConvolutionPower_mul`, and
  `MeasureTheory.Measure.freeConvolutionPower_succ'`: unconditional exponent laws.
* `MeasureTheory.Measure.freeConvolutionPower_map_add`,
  `MeasureTheory.Measure.freeConvolutionPower_neg`,
  `MeasureTheory.Measure.freeConvolutionPower_map_mul_left`, and
  `MeasureTheory.Measure.freeConvolutionPower_map_affine`: pushforward laws under translations,
  reflections, dilations, and affine maps.
* `MeasureTheory.Measure.support_freeConvolutionPower_subset_Icc`: if `μ` is supported in
  `[a, b]`, then `μ.freeConvolutionPower n` is supported in `[n • a, n • b]`.
* `MeasureTheory.Measure.rSeries_freeConvolutionPower` and
  `MeasureTheory.Measure.freeCumulant_freeConvolutionPower`: scaling of the formal R-series and
  positive-order free cumulants by `n`.
* `Finset.fold_freeConv_const`, `MeasureTheory.Measure.rSeries_fold_freeConv`, and
  `MeasureTheory.Measure.freeCumulant_fold_freeConv`: finite `⊞`-folds and their cumulants.
* `PositiveLinearMap.law_sum_eq_fold_freeConv`,
  `PositiveLinearMap.law_finset_sum_eq_freeConvolutionPower`,
  `PositiveLinearMap.law_sum_eq_freeConvolutionPower`, and
  `PositiveLinearMap.law_innerPositiveLinearMap_sum_eq_fold_freeConv_of_mem_weakOperatorClosure`:
  laws of finite sums of freely independent selfadjoint elements.
* `TauCeti.Probability.freeConvolutionPower_semicircleReal`:
  `(semicircleReal a v).freeConvolutionPower n = semicircleReal (n • a) (n • v)`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§3.2–3.3.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory PowerSeries Finset
open scoped ENNReal NNReal MeasureTheory InnerProductSpace ComplexOrder

namespace MeasureTheory.Measure

/-! ### Definition and exponent laws of free additive convolution powers -/

/-- The `n`-fold free additive convolution `μ^{⊞ n}` of a Borel measure `μ` on `ℝ`, with
`μ.freeConvolutionPower 0 = Measure.dirac 0` and
`μ.freeConvolutionPower (n + 1) = μ.freeConvolutionPower n ⊞ μ`. -/
def freeConvolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => freeConvolutionPower μ n ⊞ μ

/-- The zeroth free additive convolution power is the point mass at `0`. -/
@[simp]
theorem freeConvolutionPower_zero (μ : Measure ℝ) :
    μ.freeConvolutionPower 0 = Measure.dirac 0 := (rfl)

/-- A successor free additive convolution power appends one copy of `μ` on the right. -/
@[simp]
theorem freeConvolutionPower_succ (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ.freeConvolutionPower n ⊞ μ := (rfl)

/-- Every free additive convolution power of any Borel measure on `ℝ` is finite. -/
instance isFiniteMeasure_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsFiniteMeasure (μ.freeConvolutionPower n) := by
  induction n with
  | zero => simp only [freeConvolutionPower_zero]; infer_instance
  | succ n _ => simp only [freeConvolutionPower_succ]; infer_instance

/-- Every free additive convolution power of any Borel measure on `ℝ` has compact topological
support. -/
theorem isCompact_support_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsCompact (μ.freeConvolutionPower n).support := by
  induction n with
  | zero =>
      rw [freeConvolutionPower_zero, Measure.support_dirac (a := (0 : ℝ)), closure_singleton]
      exact isCompact_singleton
  | succ n _ =>
      rw [freeConvolutionPower_succ]
      exact isCompact_support_freeConv _ _

/-- Every free additive convolution power of a compactly supported probability measure is a
probability measure. -/
theorem isProbabilityMeasure_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) : IsProbabilityMeasure (μ.freeConvolutionPower n) := by
  induction n with
  | zero => simp only [freeConvolutionPower_zero]; infer_instance
  | succ n ih =>
      rw [freeConvolutionPower_succ]
      exact isProbabilityMeasure_freeConv (isCompact_support_freeConvolutionPower μ n) hμ

/-- Outside compactly supported probability measures, all positive free convolution powers vanish.
-/
theorem freeConvolutionPower_of_not {μ : Measure ℝ}
    (h : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support)) {n : ℕ} (hn : n ≠ 0) :
    μ.freeConvolutionPower n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [freeConvolutionPower_succ]
  by_cases hp : IsProbabilityMeasure μ
  · exact freeConv_of_not_isCompact_support_right fun hc ↦ h ⟨hp, hc⟩
  · exact freeConv_of_not_isProbabilityMeasure_right hp

/-- `μ.freeConvolutionPower n` is a probability measure if and only if `n = 0` or `μ` is a
compactly supported probability measure. -/
theorem isProbabilityMeasure_freeConvolutionPower_iff {μ : Measure ℝ} {n : ℕ} :
    IsProbabilityMeasure (μ.freeConvolutionPower n) ↔
      n = 0 ∨ IsProbabilityMeasure μ ∧ IsCompact μ.support := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [freeConvolutionPower_zero, true_or, iff_true]
    infer_instance
  · simp only [hn, false_or]
    refine ⟨fun hprob ↦ ?_, fun ⟨hp, hc⟩ ↦ isProbabilityMeasure_freeConvolutionPower hc n⟩
    by_contra h
    rw [freeConvolutionPower_of_not h hn] at hprob
    exact one_ne_zero hprob.measure_univ.symm

/-- `Measure.dirac 0` acts as a left identity on every free additive convolution power `μ^{⊞ n}`,
without hypotheses on `μ`. -/
@[simp]
theorem dirac_zero_freeConv_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    Measure.dirac 0 ⊞ μ.freeConvolutionPower n = μ.freeConvolutionPower n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · classical
    by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support
    · obtain ⟨hp, hc⟩ := h
      have _ := isProbabilityMeasure_freeConvolutionPower hc n
      exact dirac_zero_freeConv (isCompact_support_freeConvolutionPower μ n)
    · rw [freeConvolutionPower_of_not h hn, freeConv_zero]

/-- `Measure.dirac 0` acts as a right identity on every free additive convolution power `μ^{⊞ n}`,
without hypotheses on `μ`. -/
@[simp]
theorem freeConvolutionPower_freeConv_dirac_zero (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower n ⊞ Measure.dirac 0 = μ.freeConvolutionPower n := by
  rw [freeConv_comm, dirac_zero_freeConv_freeConvolutionPower]

/-- For a compactly supported probability measure `μ`, the first free convolution power is `μ`. -/
theorem freeConvolutionPower_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : μ.freeConvolutionPower 1 = μ := by
  rw [freeConvolutionPower_succ, freeConvolutionPower_zero, dirac_zero_freeConv hμ]

/-- Free additive convolution powers commute with `μ`: `μ^{⊞ (n + 1)} = μ ⊞ μ^{⊞ n}`. -/
theorem freeConvolutionPower_succ' (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ ⊞ μ.freeConvolutionPower n := by
  rw [freeConvolutionPower_succ, freeConv_comm]

/-- Free additive convolution powers turn addition of exponents into free additive convolution. -/
theorem freeConvolutionPower_add (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvolutionPower (m + n) = μ.freeConvolutionPower m ⊞ μ.freeConvolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, freeConvolutionPower_succ, freeConvolutionPower_succ, ih, freeConv_assoc]

/-- Free additive convolution powers turn multiplication of exponents into iterated powers. -/
theorem freeConvolutionPower_mul (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvolutionPower (m * n) = (μ.freeConvolutionPower m).freeConvolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, freeConvolutionPower_add, ih, freeConvolutionPower_succ]

/-- Free additive convolution powers of a point mass multiply its atom by `n`. -/
theorem freeConvolutionPower_dirac (c : ℝ) (n : ℕ) :
    (Measure.dirac c).freeConvolutionPower n = Measure.dirac (n • c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [freeConvolutionPower_succ, ih, dirac_freeConv_dirac, succ_nsmul]

/-- Positive free additive convolution powers of the zero measure vanish. -/
theorem freeConvolutionPower_zero_measure {n : ℕ} (hn : n ≠ 0) :
    (0 : Measure ℝ).freeConvolutionPower n = 0 :=
  freeConvolutionPower_of_not (fun h ↦ one_ne_zero h.1.measure_univ.symm) hn

/-! ### Pushforwards, affine images, and support bounds -/

/-- Nonconstant affine pushforwards commute with free additive convolution powers unconditionally,
accumulating the intercept `n` times. -/
theorem freeConvolutionPower_map_affine_of_ne_zero (μ : Measure ℝ) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    (n : ℕ) :
    (μ.map fun x ↦ a + b * x).freeConvolutionPower n =
      (μ.freeConvolutionPower n).map fun x ↦ (n : ℝ) * a + b * x := by
  induction n with
  | zero =>
      rw [freeConvolutionPower_zero, freeConvolutionPower_zero, Measure.map_dirac' (by fun_prop)]
      simp
  | succ n ih =>
      rw [freeConvolutionPower_succ, ih, freeConv_map_affine_of_ne_zero _ _ _ _ hb,
        ← freeConvolutionPower_succ]
      congr 1
      ext x
      push_cast
      ring

/-- Translation by `a` shifts the `n`-th free additive convolution power by `n • a`. -/
theorem freeConvolutionPower_map_add (μ : Measure ℝ) (a : ℝ) (n : ℕ) :
    (μ.map (a + ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (n • a + ·) := by
  simpa [nsmul_eq_mul] using freeConvolutionPower_map_affine_of_ne_zero μ a one_ne_zero n

/-- Reflection commutes with free additive convolution powers. -/
theorem freeConvolutionPower_neg (μ : Measure ℝ) (n : ℕ) :
    μ.neg.freeConvolutionPower n = (μ.freeConvolutionPower n).neg := by
  induction n with
  | zero =>
      rw [freeConvolutionPower_zero, freeConvolutionPower_zero, Measure.neg_def,
        Measure.map_dirac' measurable_neg, neg_zero]
  | succ n ih => rw [freeConvolutionPower_succ, ih, freeConv_neg, ← freeConvolutionPower_succ]

/-- Nonzero left dilation commutes with free additive convolution powers unconditionally. -/
theorem freeConvolutionPower_map_mul_left_of_ne_zero (μ : Measure ℝ) {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    (μ.map (b * ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (b * ·) := by
  simpa using freeConvolutionPower_map_affine_of_ne_zero μ 0 hb n

/-- **Affine pushforward law for free additive convolution powers.** Applying `x ↦ a + b * x` to a
compactly supported probability measure `μ` accumulates the translation `n` times at every slope
`b` (including `b = 0`) and for every `n : ℕ`. -/
theorem freeConvolutionPower_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) (n : ℕ) :
    (μ.map fun x ↦ a + b * x).freeConvolutionPower n =
      (μ.freeConvolutionPower n).map fun x ↦ (n : ℝ) * a + b * x := by
  by_cases hb : b = 0
  · subst hb
    have _ := isProbabilityMeasure_freeConvolutionPower hμ n
    simp [Measure.map_const, freeConvolutionPower_dirac, nsmul_eq_mul]
  · exact freeConvolutionPower_map_affine_of_ne_zero μ a hb n

/-- Left dilation commutes with free additive convolution powers of a compactly supported
probability measure at every real scale `b` (including `b = 0`). -/
theorem freeConvolutionPower_map_mul_left {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (b : ℝ) (n : ℕ) :
    (μ.map (b * ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (b * ·) := by
  simpa using freeConvolutionPower_map_affine hμ 0 b n

/-- **Support bound for free additive convolution powers.** If `μ.support ⊆ [a, b]`, then
`(μ.freeConvolutionPower n).support ⊆ [n • a, n • b]`. -/
theorem support_freeConvolutionPower_subset_Icc {μ : Measure ℝ} {a b : ℝ}
    (hμ : μ.support ⊆ Set.Icc a b) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Icc (n • a) (n • b) := by
  induction n with
  | zero =>
      rw [freeConvolutionPower_zero, Measure.support_dirac (a := (0 : ℝ)), closure_singleton]
      simp
  | succ n ih =>
      rw [freeConvolutionPower_succ, succ_nsmul, succ_nsmul]
      exact support_freeConv_subset_Icc ih hμ

/-- Almost-everywhere interval concentration for free additive convolution powers. -/
theorem ae_mem_Icc_freeConvolutionPower {μ : Measure ℝ} {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (n : ℕ) :
    ∀ᵐ x ∂μ.freeConvolutionPower n, x ∈ Set.Icc (n • a) (n • b) := by
  have hsupp := support_freeConvolutionPower_subset_Icc
    (Measure.support_subset_of_isClosed isClosed_Icc hμ) n
  filter_upwards [Measure.support_mem_ae (μ := μ.freeConvolutionPower n)] with x hx
  exact hsupp hx

/-! ### Formal R-series and free cumulants of convolution powers -/

/-- The formal R-series of the `n`-th free additive convolution power scales by `n`. -/
theorem rSeries_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    (μ.freeConvolutionPower n).rSeries = n • μ.rSeries := by
  induction n with
  | zero => simp
  | succ n ih =>
      have _ := isProbabilityMeasure_freeConvolutionPower hμ n
      rw [freeConvolutionPower_succ,
        rSeries_freeConv (isCompact_support_freeConvolutionPower μ n) hμ, ih, succ_nsmul]

/-- Every positive-order free cumulant of `μ.freeConvolutionPower n` scales by `n`. -/
theorem freeCumulant_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (μ.freeConvolutionPower n).freeCumulant k = n • μ.freeCumulant k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using congrArg (coeff m) (rSeries_freeConvolutionPower hμ n)

end MeasureTheory.Measure

/-! ### Finite `⊞`-folds over `Finset` -/

namespace Finset

/-- Folding a constant measure `μ` over a finite set `s` under `⊞` with base `δ₀` produces
`μ.freeConvolutionPower #s`, without hypotheses on `μ`. -/
theorem fold_freeConv_const {ι : Type*} (s : Finset ι) (μ : Measure ℝ) :
    s.fold Measure.freeConv (Measure.dirac 0) (fun _ ↦ μ) = μ.freeConvolutionPower #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, ih, Finset.card_insert_of_notMem hi,
        Measure.freeConvolutionPower_succ']

end Finset

namespace MeasureTheory.Measure

/-- Any finite `⊞`-fold of Borel measures on `ℝ` with base `δ₀` is finite. -/
instance isFiniteMeasure_fold_freeConv {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ) :
    IsFiniteMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.fold_empty]; infer_instance
  | @insert i s hi _ => rw [Finset.fold_insert hi]; infer_instance

/-- Any finite `⊞`-fold of Borel measures on `ℝ` with base `δ₀` has compact support. -/
theorem isCompact_support_fold_freeConv {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ) :
    IsCompact (s.fold Measure.freeConv (Measure.dirac 0) μ).support := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.fold_empty, Measure.support_dirac (a := (0 : ℝ)), closure_singleton]
      exact isCompact_singleton
  | @insert i s hi _ =>
      rw [Finset.fold_insert hi]
      exact isCompact_support_freeConv _ _

/-- A finite `⊞`-fold of compactly supported probability measures with base `δ₀` is a probability
measure. -/
theorem isProbabilityMeasure_fold_freeConv {ι : Type*} (s : Finset ι) {μ : ι → Measure ℝ}
    (hp : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hc : ∀ i ∈ s, IsCompact (μ i).support) :
    IsProbabilityMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.fold_empty]; infer_instance
  | @insert i s hi ih =>
      have _ : IsProbabilityMeasure (μ i) := hp i (mem_insert_self i s)
      have _ : IsProbabilityMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) :=
        ih (fun j hj ↦ hp j (mem_insert_of_mem hj)) (fun j hj ↦ hc j (mem_insert_of_mem hj))
      rw [Finset.fold_insert hi]
      exact isProbabilityMeasure_freeConv (hc i (mem_insert_self i s))
        (isCompact_support_fold_freeConv s μ)

/-- The formal R-series of a finite `⊞`-fold of compactly supported probability measures is the
sum of their individual R-series. -/
theorem rSeries_fold_freeConv {ι : Type*} (s : Finset ι) {μ : ι → Measure ℝ}
    (hp : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hc : ∀ i ∈ s, IsCompact (μ i).support) :
    (s.fold Measure.freeConv (Measure.dirac 0) μ).rSeries = ∑ i ∈ s, (μ i).rSeries := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have _ : IsProbabilityMeasure (μ i) := hp i (mem_insert_self i s)
      have hs_p : ∀ j ∈ s, IsProbabilityMeasure (μ j) := fun j hj ↦ hp j (mem_insert_of_mem hj)
      have hs_c : ∀ j ∈ s, IsCompact (μ j).support := fun j hj ↦ hc j (mem_insert_of_mem hj)
      have _ : IsProbabilityMeasure (s.fold Measure.freeConv (Measure.dirac 0) μ) :=
        isProbabilityMeasure_fold_freeConv s hs_p hs_c
      rw [Finset.fold_insert hi, Finset.sum_insert hi,
        rSeries_freeConv (hc i (mem_insert_self i s)) (isCompact_support_fold_freeConv s μ),
        ih hs_p hs_c]

/-- Every positive-order free cumulant of a finite `⊞`-fold of compactly supported probability
measures is the sum of their individual free cumulants. -/
theorem freeCumulant_fold_freeConv {ι : Type*} (s : Finset ι) {μ : ι → Measure ℝ}
    (hp : ∀ i ∈ s, IsProbabilityMeasure (μ i)) (hc : ∀ i ∈ s, IsCompact (μ i).support)
    {k : ℕ} (hk : k ≠ 0) :
    (s.fold Measure.freeConv (Measure.dirac 0) μ).freeCumulant k =
      ∑ i ∈ s, (μ i).freeCumulant k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using congrArg (coeff m) (rSeries_fold_freeConv s hp hc)

end MeasureTheory.Measure

/-! ### Laws of finite sums of freely independent selfadjoint elements -/

namespace PositiveLinearMap

/-- In any unital C⋆-algebra (including any concrete von Neumann algebra), if `B` is freely
independent for a state `φ` (`φ 1 = 1`), then the law of a finite sum `∑ i ∈ s, a i` of
selfadjoint elements `a i ∈ B i` is the `Finset.fold` of their individual laws under `⊞`. -/
theorem law_sum_eq_fold_freeConv {A ι : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) {B : ι → Subalgebra ℂ A}
    (hfree : TauCeti.IsFreelyIndependent φ.toLinearMap B) (s : Finset ι) {a : ι → A}
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) (haB : ∀ i ∈ s, a i ∈ B i) :
    φ.law (∑ i ∈ s, a i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i ↦ φ.law (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [hφ]
  | @insert i s hi ih =>
      let g : ι → Bool := fun j ↦ decide (j = i)
      have hfib := hfree.iSup_fiber hφ g
      have hai_mem : a i ∈ ⨆ (j) (_ : g j = true), B j :=
        le_iSup₂ (f := fun j (_ : g j = true) ↦ B j) i (by simp [g])
          (haB i (mem_insert_self i s))
      have hsum_mem : (∑ j ∈ s, a j) ∈ ⨆ (j) (_ : g j = false), B j := by
        refine sum_mem fun j hj ↦ ?_
        have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
        exact le_iSup₂ (f := fun k (_ : g k = false) ↦ B k) j (by simp [g, hji])
          (haB j (mem_insert_of_mem hj))
      have hsum_sa : IsSelfAdjoint (∑ j ∈ s, a j) := by
        rw [IsSelfAdjoint, star_sum]
        exact Finset.sum_congr rfl fun j hj ↦ (ha j (mem_insert_of_mem hj)).star_eq
      rw [Finset.sum_insert hi, Finset.fold_insert hi,
        φ.law_add_eq_freeConv hφ hfib (by decide : true ≠ false)
          (ha i (mem_insert_self i s)) hsum_sa hai_mem hsum_mem,
        ih (fun j hj ↦ ha j (mem_insert_of_mem hj)) (fun j hj ↦ haB j (mem_insert_of_mem hj))]

/-- Element-level specialization of `PositiveLinearMap.law_sum_eq_fold_freeConv` for a freely
independent family `a`. -/
theorem law_sum_eq_fold_freeConv_of_isFreelyIndependentElements {A ι : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) {a : ι → A}
    (hfree : TauCeti.IsFreelyIndependentElements φ.toLinearMap a) (s : Finset ι)
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    φ.law (∑ i ∈ s, a i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i ↦ φ.law (a i)) :=
  φ.law_sum_eq_fold_freeConv hφ (TauCeti.isFreelyIndependentElements_iff.mp hfree) s ha
    fun i _ ↦ Algebra.self_mem_adjoin_singleton ℂ (a i)

/-- The law of a finite sum over `s : Finset ι` of freely independent selfadjoint elements with
common law `μ` is `μ.freeConvolutionPower #s` (including the empty sum `s = ∅`). -/
theorem law_finset_sum_eq_freeConvolutionPower {A ι : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) {a : ι → A}
    (hfree : TauCeti.IsFreelyIndependentElements φ.toLinearMap a) (s : Finset ι)
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) {μ : Measure ℝ} (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvolutionPower #s := by
  rw [φ.law_sum_eq_fold_freeConv_of_isFreelyIndependentElements hφ hfree s ha,
    Finset.fold_congr hlaw, Finset.fold_freeConv_const]

/-- The law of the sum of a finite freely independent family of selfadjoint elements with common
law `μ` is `μ.freeConvolutionPower (Fintype.card ι)`. -/
theorem law_sum_eq_freeConvolutionPower {A ι : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) {a : ι → A}
    (hfree : TauCeti.IsFreelyIndependentElements φ.toLinearMap a)
    (ha : ∀ i, IsSelfAdjoint (a i)) {μ : Measure ℝ} (hlaw : ∀ i, φ.law (a i) = μ) :
    φ.law (∑ i, a i) = μ.freeConvolutionPower (Fintype.card ι) := by
  simpa using φ.law_finset_sum_eq_freeConvolutionPower hφ hfree Finset.univ
    (fun i _ ↦ ha i) (fun i _ ↦ hlaw i)

/-- **Weak-operator-closure transport for finite free sums.** If `B` is freely independent with
respect to the vector state of a unit vector `ξ : H`, then any finite family of selfadjoint
operators `T i` in the weak-operator closures of `B i` (`i ∈ s`) has sum law equal to the
`Finset.fold` of their individual laws under `⊞`. -/
theorem law_innerPositiveLinearMap_sum_eq_fold_freeConv_of_mem_weakOperatorClosure
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ξ : H} (hξ : ‖ξ‖ = 1) {B : ι → Subalgebra ℂ (H →L[ℂ] H)}
    (hfree : TauCeti.IsFreelyIndependent
      (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).toLinearMap B)
    (s : Finset ι) {T : ι → H →L[ℂ] H}
    (hT : ∀ i ∈ s, IsSelfAdjoint (T i))
    (hTB : ∀ i ∈ s, ContinuousLinearMapWOT.ofCLM (T i) ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (B i : Set (H →L[ℂ] H)))) :
    (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).law (∑ i ∈ s, T i) =
      s.fold Measure.freeConv (Measure.dirac 0)
        (fun i ↦ (ContinuousLinearMap.innerPositiveLinearMap ℂ ξ).law (T i)) := by
  let ω := ContinuousLinearMap.innerPositiveLinearMap ℂ ξ
  let e := ContinuousLinearMapWOT.algEquiv (𝕜₁ := ℂ) (E := H) ℂ
  have hω₁ : ω 1 = 1 := by simp [ω, hξ]
  have hfree_wot : TauCeti.IsFreelyIndependent (ω.toLinearMap.comp e.toLinearMap)
      (fun k ↦ ((B k).map e.symm.toAlgHom).topologicalClosure) :=
    (TauCeti.isFreelyIndependent_weakOperatorClosure_iff_of_vectorState hω₁ ξ
      fun X ↦ ContinuousLinearMap.innerPositiveLinearMap_apply ξ X).mpr hfree
  have hfree_cl : TauCeti.IsFreelyIndependent ω.toLinearMap
      (fun k ↦ (((B k).map e.symm.toAlgHom).topologicalClosure).map e.toAlgHom) :=
    hfree_wot.map e.toAlgHom (by ext X; simp [e])
  exact ω.law_sum_eq_fold_freeConv hω₁ hfree_cl s hT fun i hi ↦
    ⟨ContinuousLinearMapWOT.ofCLM (T i), hTB i hi, rfl⟩

end PositiveLinearMap

namespace TauCeti.Probability

/-- The `n`-th free additive convolution power of a real semicircle law scales both its centre and
its variance by `n`. -/
theorem freeConvolutionPower_semicircleReal (a : ℝ) (v : ℝ≥0) (n : ℕ) :
    (semicircleReal a v).freeConvolutionPower n = semicircleReal (n • a) (n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Measure.freeConvolutionPower_succ, ih, semicircleReal_freeConv_semicircleReal,
        succ_nsmul, succ_nsmul]

end TauCeti.Probability
