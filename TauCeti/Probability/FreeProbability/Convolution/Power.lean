/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Convolution.Basic
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Support

/-!
# Free additive convolution powers and finite sums of free laws

This file defines the `n`-fold free additive convolution power `Measure.freeConvolutionPower μ n`
(`μ^{⊞ n}`) of a Borel measure `μ` on `ℝ`, parallel to `Measure.convolutionPower` for classical
additive convolution, and proves the distribution formulas for finite sums of freely independent
selfadjoint variables.

Following the total-function convention of `Measure.freeConv`, the zeroth power is `Measure.dirac 0`
for every `μ : Measure ℝ`, while positive powers vanish whenever `μ` is not a compactly supported
probability measure. Under this convention, the monoid-power laws `freeConvolutionPower_add`,
`freeConvolutionPower_succ'`, and `freeConvolutionPower_mul`, together with compactness of
topological support, translation/reflection equivariance, and interval support bounds, all hold
unconditionally for arbitrary `μ : Measure ℝ`.

## Main definitions

* `MeasureTheory.Measure.freeConvolutionPower` — the `n`-fold free additive convolution `μ^{⊞ n}`
  of `μ : Measure ℝ`, with `μ.freeConvolutionPower 0 = Measure.dirac 0` and
  `μ.freeConvolutionPower (n + 1) = (μ.freeConvolutionPower n).freeConv μ`.

## Main results

* `MeasureTheory.Measure.freeConvolutionPower_one`,
  `MeasureTheory.Measure.freeConvolutionPower_add`,
  `MeasureTheory.Measure.freeConvolutionPower_succ'`, and
  `MeasureTheory.Measure.freeConvolutionPower_mul` — monoid-power identities for `⊞`.
* `MeasureTheory.Measure.rSeries_freeConvolutionPower` and
  `MeasureTheory.Measure.freeCumulant_freeConvolutionPower` — `R_{μ^{⊞ n}} = n • R_μ` and
  `κ_k(μ^{⊞ n}) = n * κ_k(μ)` (`k ≠ 0`) for compactly supported probability measures.
* `MeasureTheory.Measure.freeConvolutionPower_dirac`,
  `MeasureTheory.Measure.freeConvolutionPower_map_affine`,
  `MeasureTheory.Measure.freeConvolutionPower_map_mul_left`,
  `MeasureTheory.Measure.freeConvolutionPower_map_add_right`, and
  `MeasureTheory.Measure.freeConvolutionPower_map_neg` — point-mass and affine pushforward laws.
* `MeasureTheory.Measure.support_freeConvolutionPower_subset_Iic`,
  `MeasureTheory.Measure.support_freeConvolutionPower_subset_Ici`,
  `MeasureTheory.Measure.support_freeConvolutionPower_subset_Icc`, and
  `MeasureTheory.Measure.support_freeConvolutionPower_subset_closedBall` — linear scaling of
  topological support bounds under `n`-fold free additive convolution.
* `TauCeti.IsFreelyIndependent.rSeries_law_sum`,
  `TauCeti.IsFreelyIndependent.freeCumulant_law_sum`,
  `TauCeti.IsFreelyIndependent.law_sum_eq_freeConvolutionPower`,
  `TauCeti.IsFreelyIndependentElements.law_sum_eq_freeConvolutionPower`,
  `TauCeti.IsFreelyIndependent.law_sum_affine_eq_map_freeConvolutionPower`, and
  `TauCeti.IsFreelyIndependent.law_sum_eq_freeConvolutionPower_of_mem_vonNeumannAlgebraAdjoin` —
  finite free sums in C⋆- and von Neumann probability spaces.
-/

public section

noncomputable section

open MeasureTheory PowerSeries
open scoped ComplexInnerProductSpace ComplexOrder

namespace MeasureTheory.Measure

/-- The `n`-fold free additive convolution power `μ^{⊞ n}` of a Borel measure `μ` on `ℝ`. The
zeroth power is the point mass at `0`; each successor appends one free convolution with `μ`. -/
def freeConvolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (μ.freeConvolutionPower n).freeConv μ

/-- The zeroth free additive convolution power is the point mass at `0`. -/
@[simp]
theorem freeConvolutionPower_zero (μ : Measure ℝ) :
    μ.freeConvolutionPower 0 = Measure.dirac 0 := (rfl)

/-- A successor free additive convolution power appends one free convolution with `μ`. -/
@[simp]
theorem freeConvolutionPower_succ (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = (μ.freeConvolutionPower n).freeConv μ := (rfl)

/-- Every positive free additive convolution power vanishes when `μ` is not a compactly supported
probability measure. -/
theorem freeConvolutionPower_succ_of_not {μ : Measure ℝ}
    (h : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support)) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = 0 := by
  rw [freeConvolutionPower_succ]
  exact freeConv_of_not fun ⟨_, _, hprob, hcomp⟩ ↦ h ⟨hprob, hcomp⟩

/-- Positive free additive convolution powers of the zero measure vanish. -/
theorem zero_freeConvolutionPower_succ (n : ℕ) :
    (0 : Measure ℝ).freeConvolutionPower (n + 1) = 0 := by
  simp

/-- Every free additive convolution power is a finite measure. -/
instance isFiniteMeasure_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsFiniteMeasure (μ.freeConvolutionPower n) := by
  cases n with
  | zero => simp only [freeConvolutionPower_zero]; infer_instance
  | succ n => simp only [freeConvolutionPower_succ]; infer_instance

/-- Every free additive convolution power has compact topological support. -/
theorem isCompact_support_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsCompact (μ.freeConvolutionPower n).support := by
  cases n with
  | zero => simp [Measure.support_dirac]
  | succ n => exact isCompact_support_freeConv (μ.freeConvolutionPower n) μ

/-- Every free additive convolution power of a compactly supported probability measure is a
probability measure. -/
theorem isProbabilityMeasure_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) : IsProbabilityMeasure (μ.freeConvolutionPower n) := by
  induction n with
  | zero => simp only [freeConvolutionPower_zero]; infer_instance
  | succ n ih =>
    rw [freeConvolutionPower_succ]
    exact isProbabilityMeasure_freeConv (isCompact_support_freeConvolutionPower μ n) hμ

/-- A positive free additive convolution power `μ.freeConvolutionPower (n + 1)` is a probability
measure if and only if `μ` is a compactly supported probability measure. -/
theorem isProbabilityMeasure_freeConvolutionPower_succ_iff {μ : Measure ℝ} {n : ℕ} :
    IsProbabilityMeasure (μ.freeConvolutionPower (n + 1)) ↔
      IsProbabilityMeasure μ ∧ IsCompact μ.support := by
  refine ⟨fun h ↦ ?_, fun ⟨hprob, hcomp⟩ ↦ isProbabilityMeasure_freeConvolutionPower hcomp (n + 1)⟩
  rw [freeConvolutionPower_succ, isProbabilityMeasure_freeConv_iff] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- The first free additive convolution power of a compactly supported probability measure is the
measure itself. -/
theorem freeConvolutionPower_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : μ.freeConvolutionPower 1 = μ := by
  rw [freeConvolutionPower_succ, freeConvolutionPower_zero, dirac_zero_freeConv hμ]

/-- Free additive convolution powers turn addition of exponents into free additive convolution,
unconditionally for every `μ : Measure ℝ`. -/
theorem freeConvolutionPower_add (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvolutionPower (m + n) =
      (μ.freeConvolutionPower m).freeConv (μ.freeConvolutionPower n) := by
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support
  · obtain ⟨hprob, hcomp⟩ := h
    induction n with
    | zero =>
      have _ := isProbabilityMeasure_freeConvolutionPower hcomp m
      simp [freeConv_dirac_zero (isCompact_support_freeConvolutionPower μ m)]
    | succ n ih =>
      rw [Nat.add_succ, freeConvolutionPower_succ, freeConvolutionPower_succ, ih, freeConv_assoc]
  · cases n with
    | zero =>
      cases m with
      | zero => simp
      | succ m =>
        rw [Nat.add_zero, freeConvolutionPower_succ_of_not h m, freeConvolutionPower_zero,
          zero_freeConv]
    | succ n =>
      rw [Nat.add_succ, freeConvolutionPower_succ_of_not h (m + n),
        freeConvolutionPower_succ_of_not h n, freeConv_zero]

/-- Free additive convolution powers also satisfy the left recursion
`μ.freeConvolutionPower (n + 1) = μ.freeConv (μ.freeConvolutionPower n)`. -/
theorem freeConvolutionPower_succ' (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ.freeConv (μ.freeConvolutionPower n) := by
  rw [freeConvolutionPower_succ, freeConv_comm]

/-- Free additive convolution powers turn multiplication of exponents into iterated powers,
unconditionally for every `μ : Measure ℝ`. -/
theorem freeConvolutionPower_mul (μ : Measure ℝ) (m n : ℕ) :
    μ.freeConvolutionPower (m * n) = (μ.freeConvolutionPower m).freeConvolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, freeConvolutionPower_add, ih, freeConvolutionPower_succ]

/-- Free additive convolution powers of a point mass multiply its location by `n`. -/
theorem freeConvolutionPower_dirac (c : ℝ) (n : ℕ) :
    (Measure.dirac c).freeConvolutionPower n = Measure.dirac (n * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [freeConvolutionPower_succ, ih, dirac_freeConv_dirac]
    congr 1
    push_cast
    ring

/-- Every free additive convolution power of `Measure.dirac 0` is `Measure.dirac 0`. -/
@[simp]
theorem freeConvolutionPower_dirac_zero (n : ℕ) :
    (Measure.dirac (0 : ℝ)).freeConvolutionPower n = Measure.dirac 0 := by
  simpa using freeConvolutionPower_dirac 0 n

/-- **Linearity of the formal R-series under free additive convolution powers.** For a compactly
supported probability measure `μ` on `ℝ`, `(μ.freeConvolutionPower n).rSeries = n • μ.rSeries`. -/
theorem rSeries_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    (μ.freeConvolutionPower n).rSeries = n • μ.rSeries := by
  induction n with
  | zero => simp
  | succ n ih =>
    have _ := isProbabilityMeasure_freeConvolutionPower hμ n
    rw [freeConvolutionPower_succ,
      rSeries_freeConv (isCompact_support_freeConvolutionPower μ n) hμ, ih, succ_nsmul]

/-- Every positive-order free cumulant `κ_k` (`k ≠ 0`) scales by `n` under the `n`-th free additive
convolution power of a compactly supported probability measure. -/
theorem freeCumulant_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    (μ.freeConvolutionPower n).freeCumulant k = n * μ.freeCumulant k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [← coeff_rSeries, ← coeff_rSeries, rSeries_freeConvolutionPower hμ n, map_nsmul,
    nsmul_eq_mul]

/-- **Affine equivariance of free additive convolution powers.** Pushing a compactly supported
probability measure `μ` forward by `x ↦ r * x + c` and taking the `n`-th free additive convolution
power accumulates the translation `n` times at the same slope `r` (including `r = 0`, `n = 0`). -/
theorem freeConvolutionPower_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (r c : ℝ) (n : ℕ) :
    (μ.map (fun x ↦ r * x + c)).freeConvolutionPower n =
      (μ.freeConvolutionPower n).map (fun x ↦ r * x + n * c) := by
  induction n with
  | zero =>
    rw [freeConvolutionPower_zero, freeConvolutionPower_zero, Measure.map_dirac' (by fun_prop)]
    simp
  | succ n ih =>
    have _ := isProbabilityMeasure_freeConvolutionPower hμ n
    rw [freeConvolutionPower_succ, ih,
      freeConv_map_affine (isCompact_support_freeConvolutionPower μ n) hμ r (n * c) c,
      ← freeConvolutionPower_succ]
    congr 1
    funext x
    push_cast
    ring

/-- Rescaling a compactly supported probability measure `μ` by `r : ℝ` commutes with every free
additive convolution power. -/
theorem freeConvolutionPower_map_mul_left {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (r : ℝ) (n : ℕ) :
    (μ.map (r * ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (r * ·) := by
  simpa using freeConvolutionPower_map_affine hμ r 0 n

/-- Translating any measure `μ` on `ℝ` by `c` translates its `n`-th free additive convolution power
by `n * c`. -/
theorem freeConvolutionPower_map_add_right (μ : Measure ℝ) (c : ℝ) (n : ℕ) :
    (μ.map (· + c)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (· + n * c) := by
  induction n with
  | zero =>
    rw [freeConvolutionPower_zero, freeConvolutionPower_zero, Measure.map_dirac' (by fun_prop)]
    simp
  | succ n ih =>
    rw [freeConvolutionPower_succ, ih, freeConv_map_add_right, ← freeConvolutionPower_succ]
    congr 1
    funext x
    push_cast
    ring

/-- Reflecting any measure `μ` on `ℝ` through the origin commutes with every free additive
convolution power. -/
theorem freeConvolutionPower_map_neg (μ : Measure ℝ) (n : ℕ) :
    (μ.map (-·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (-·) := by
  induction n with
  | zero =>
    rw [freeConvolutionPower_zero, freeConvolutionPower_zero, Measure.map_dirac' measurable_neg,
      neg_zero]
  | succ n ih =>
    rw [freeConvolutionPower_succ, ih, freeConv_map_neg, ← freeConvolutionPower_succ]

/-! ### Topological support bounds for free additive convolution powers -/

/-- An upper interval bound `μ.support ⊆ (-∞, r]` scales to `(-∞, n * r]` on the `n`-th free
additive convolution power. -/
theorem support_freeConvolutionPower_subset_Iic {μ : Measure ℝ} {r : ℝ}
    (h : μ.support ⊆ Set.Iic r) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Iic (n * r) := by
  induction n with
  | zero => simp [Measure.support_dirac]
  | succ n ih =>
    rw [freeConvolutionPower_succ]
    refine (support_freeConv_subset_Iic ih h).trans ?_
    push_cast
    rw [add_one_mul]

/-- A lower interval bound `μ.support ⊆ [l, ∞)` scales to `[n * l, ∞)` on the `n`-th free additive
convolution power. -/
theorem support_freeConvolutionPower_subset_Ici {μ : Measure ℝ} {l : ℝ}
    (h : μ.support ⊆ Set.Ici l) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Ici (n * l) := by
  induction n with
  | zero => simp [Measure.support_dirac]
  | succ n ih =>
    rw [freeConvolutionPower_succ]
    refine (support_freeConv_subset_Ici ih h).trans ?_
    push_cast
    rw [add_one_mul]

/-- A closed-interval bound `μ.support ⊆ [l, r]` scales to `[n * l, n * r]` on the `n`-th free
additive convolution power. -/
theorem support_freeConvolutionPower_subset_Icc {μ : Measure ℝ} {l r : ℝ}
    (h : μ.support ⊆ Set.Icc l r) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Icc (n * l) (n * r) :=
  Set.subset_inter
    (support_freeConvolutionPower_subset_Ici (h.trans Set.Icc_subset_Ici_self) n)
    (support_freeConvolutionPower_subset_Iic (h.trans Set.Icc_subset_Iic_self) n)

/-- A symmetric closed-ball bound `μ.support ⊆ [-R, R]` scales to `[-(n * R), n * R]` on the `n`-th
free additive convolution power. -/
theorem support_freeConvolutionPower_subset_closedBall {μ : Measure ℝ} {R : ℝ}
    (h : μ.support ⊆ Metric.closedBall 0 R) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Metric.closedBall 0 (n * R) := by
  simp only [Real.closedBall_eq_Icc, zero_sub, zero_add] at h ⊢
  simpa only [neg_mul_eq_mul_neg] using support_freeConvolutionPower_subset_Icc h n

end MeasureTheory.Measure

/-! ### Finite sums of freely independent selfadjoint variables -/

namespace TauCeti

private theorem isSelfAdjoint_sum {A ι : Type*} [AddCommMonoid A] [StarAddMonoid A]
    {s : Finset ι} {a : ι → A} (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    IsSelfAdjoint (∑ i ∈ s, a i) :=
  Finset.sum_induction a IsSelfAdjoint (fun _ _ hx hy ↦ hx.add hy) (IsSelfAdjoint.zero A) ha

section FiniteSums

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Additivity of the law R-series on finite free sums.** If `(B i)` is freely independent for a
state `φ` on `A` and `a i ∈ B i` (`i ∈ s`) are selfadjoint, then the R-series of the law of
`∑ i ∈ s, a i` is `∑ i ∈ s, (φ.law (a i)).rSeries`. -/
theorem IsFreelyIndependent.rSeries_law_sum {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hfree : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) (s : Finset ι) {a : ι → A}
    (hmem : ∀ i ∈ s, a i ∈ B i) (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    (φ.law (∑ i ∈ s, a i)).rSeries = ∑ i ∈ s, (φ.law (a i)).rSeries := by
  have hφ' : φ.toLinearMap 1 = 1 := by simpa [PositiveLinearMap.coe_toLinearMap] using hφ
  apply PowerSeries.map_injective Complex.ofRealHom Complex.ofReal_injective
  rw [PositiveLinearMap.map_ofReal_rSeries_law φ (isSelfAdjoint_sum ha), map_sum,
    Finset.sum_congr rfl fun i hi ↦ PositiveLinearMap.map_ofReal_rSeries_law φ (ha i hi)]
  exact hfree.rSeries_sum hφ' hmem

/-- Element version of `IsFreelyIndependent.rSeries_law_sum`. -/
theorem IsFreelyIndependentElements.rSeries_law_sum {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (hfree : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    (φ.law (∑ i ∈ s, a i)).rSeries = ∑ i ∈ s, (φ.law (a i)).rSeries := by
  rw [isFreelyIndependentElements_iff] at hfree
  exact hfree.rSeries_law_sum hφ s (fun i _ ↦ Algebra.self_mem_adjoin_singleton ℂ (a i)) ha

/-- Every positive-order free cumulant `κ_k` (`k ≠ 0`) is additive over a finite sum of freely
independent selfadjoint elements. -/
theorem IsFreelyIndependent.freeCumulant_law_sum {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hfree : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) (s : Finset ι) {a : ι → A}
    (hmem : ∀ i ∈ s, a i ∈ B i) (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) {k : ℕ} (hk : k ≠ 0) :
    (φ.law (∑ i ∈ s, a i)).freeCumulant k = ∑ i ∈ s, (φ.law (a i)).freeCumulant k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [← Measure.coeff_rSeries, hfree.rSeries_law_sum hφ s hmem ha, map_sum]

/-- Element version of `IsFreelyIndependent.freeCumulant_law_sum`. -/
theorem IsFreelyIndependentElements.freeCumulant_law_sum {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (hfree : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) {k : ℕ} (hk : k ≠ 0) :
    (φ.law (∑ i ∈ s, a i)).freeCumulant k = ∑ i ∈ s, (φ.law (a i)).freeCumulant k := by
  rw [isFreelyIndependentElements_iff] at hfree
  exact hfree.freeCumulant_law_sum hφ s (fun i _ ↦ Algebra.self_mem_adjoin_singleton ℂ (a i)) ha hk

/-- **Law of a finite sum of identically distributed free selfadjoint variables.** If `(B i)` is
freely independent for a state `φ` on `A` and `a i ∈ B i` (`i ∈ s`) are selfadjoint with common law
`μ`, then `∑ i ∈ s, a i` has law `μ.freeConvolutionPower s.card` (including when `s = ∅`). -/
theorem IsFreelyIndependent.law_sum_eq_freeConvolutionPower {φ : A →ₚ[ℂ] ℂ}
    {B : ι → Subalgebra ℂ A} (hfree : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1)
    (s : Finset ι) {a : ι → A} {μ : Measure ℝ} (hmem : ∀ i ∈ s, a i ∈ B i)
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvolutionPower s.card := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp [PositiveLinearMap.law_zero φ hφ]
  · have _ : IsProbabilityMeasure (φ.law (a i₀)) :=
      PositiveLinearMap.isProbabilityMeasure_law φ hφ (ha i₀ hi₀)
    have _ : IsProbabilityMeasure μ := hlaw i₀ hi₀ ▸ ‹_›
    have hKμ : IsCompact μ.support :=
      hlaw i₀ hi₀ ▸ PositiveLinearMap.isCompact_support_law φ (a i₀)
    have _ : IsProbabilityMeasure (φ.law (∑ i ∈ s, a i)) :=
      PositiveLinearMap.isProbabilityMeasure_law φ hφ (isSelfAdjoint_sum ha)
    have _ : IsProbabilityMeasure (μ.freeConvolutionPower s.card) :=
      Measure.isProbabilityMeasure_freeConvolutionPower hKμ s.card
    rw [Measure.eq_iff_rSeries_eq (PositiveLinearMap.isCompact_support_law φ _)
        (Measure.isCompact_support_freeConvolutionPower μ s.card),
      hfree.rSeries_law_sum hφ s hmem ha, Measure.rSeries_freeConvolutionPower hKμ s.card,
      Finset.sum_congr rfl fun i hi ↦ congrArg Measure.rSeries (hlaw i hi), Finset.sum_const]

/-- Element version of `IsFreelyIndependent.law_sum_eq_freeConvolutionPower`. -/
theorem IsFreelyIndependentElements.law_sum_eq_freeConvolutionPower {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (hfree : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    {μ : Measure ℝ} (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvolutionPower s.card := by
  rw [isFreelyIndependentElements_iff] at hfree
  exact hfree.law_sum_eq_freeConvolutionPower hφ s
    (fun i _ ↦ Algebra.self_mem_adjoin_singleton ℂ (a i)) ha hlaw

/-- **Law of a finite sum of affine images of identically distributed free selfadjoint variables.**
With common slope `r : ℝ` and arbitrary intercepts `c : ι → ℝ`, the sum
`∑ i ∈ s, (r • a i + algebraMap ℝ A (c i))` has law
`(μ.freeConvolutionPower s.card).map (fun x ↦ r * x + ∑ i ∈ s, c i)` (including `s = ∅` and
`r = 0`). -/
theorem IsFreelyIndependent.law_sum_affine_eq_map_freeConvolutionPower {φ : A →ₚ[ℂ] ℂ}
    {B : ι → Subalgebra ℂ A} (hfree : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1)
    (s : Finset ι) {a : ι → A} {μ : Measure ℝ} (hmem : ∀ i ∈ s, a i ∈ B i)
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ)
    (r : ℝ) (c : ι → ℝ) :
    φ.law (∑ i ∈ s, (r • a i + algebraMap ℝ A (c i))) =
      (μ.freeConvolutionPower s.card).map (fun x ↦ r * x + ∑ i ∈ s, c i) := by
  have hsum : (∑ i ∈ s, (r • a i + algebraMap ℝ A (c i))) =
      r • (∑ i ∈ s, a i) + algebraMap ℝ A (∑ i ∈ s, c i) := by
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, map_sum]
  rw [hsum, PositiveLinearMap.law_smul_add_algebraMap φ (isSelfAdjoint_sum ha) r (∑ i ∈ s, c i),
    hfree.law_sum_eq_freeConvolutionPower hφ s hmem ha hlaw]

end FiniteSums

section VonNeumannFiniteSums

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Von Neumann / WOT-closure version of `IsFreelyIndependent.law_sum_eq_freeConvolutionPower`: if
`S` is a freely independent family of `⋆`-subalgebras of `H →L[ℂ] H` for a WOT-continuous state `φ`
and `a i ∈ VonNeumannAlgebra.adjoin (S i)` (`i ∈ s`) are selfadjoint with common law `μ`, then
`∑ i ∈ s, a i` has law `μ.freeConvolutionPower s.card`. -/
theorem IsFreelyIndependent.law_sum_eq_freeConvolutionPower_of_mem_vonNeumannAlgebraAdjoin
    {φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ} {S : ι → StarSubalgebra ℂ (H →L[ℂ] H)}
    (hfree : IsFreelyIndependent φ.toLinearMap (fun k ↦ (S k).toSubalgebra)) (hφ : φ 1 = 1)
    (hcont : Continuous (fun T : H →WOT[ℂ] H ↦ φ T.toCLM)) (s : Finset ι) {a : ι → H →L[ℂ] H}
    {μ : Measure ℝ} (hmem : ∀ i ∈ s, a i ∈ VonNeumannAlgebra.adjoin (S i : Set (H →L[ℂ] H)))
    (ha : ∀ i ∈ s, IsSelfAdjoint (a i)) (hlaw : ∀ i ∈ s, φ.law (a i) = μ) :
    φ.law (∑ i ∈ s, a i) = μ.freeConvolutionPower s.card := by
  have hφ' : φ.toLinearMap 1 = 1 := by simpa [PositiveLinearMap.coe_toLinearMap] using hφ
  have hcont' : Continuous (fun T : H →WOT[ℂ] H ↦ φ.toLinearMap T.toCLM) := by
    simpa only [PositiveLinearMap.coe_toLinearMap] using hcont
  exact ((isFreelyIndependent_vonNeumannAlgebraAdjoin_iff S hφ' hcont').mpr hfree)
    |>.law_sum_eq_freeConvolutionPower hφ s hmem ha hlaw

end VonNeumannFiniteSums

end TauCeti
