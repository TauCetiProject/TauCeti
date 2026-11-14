/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.LocationScale
public import TauCeti.Probability.FreeProbability.FreeConvolution.Additive.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Law
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Finite free additive convolutions, convolution powers, and semicircle laws

This file develops finite-family free additive convolution via `Finset.fold`, transport of finite
sums of freely independent selfadjoint families across C⋆- and concrete von Neumann realizations,
the `n`-fold free additive convolution power `MeasureTheory.Measure.freeConvolutionPower`
(`μ^{⊞ n}`), and closure of the location-scale Wigner semicircle family
`TauCeti.Probability.semicircleReal` under free additive convolution and convolution powers.

## Main definitions

* `MeasureTheory.Measure.freeConvolutionPower`: the `n`-fold free additive convolution power
  `μ^{⊞ n}`, with `μ^{⊞ 0} = Measure.dirac 0`.

## Main results

* `MeasureTheory.Measure.rSeries_integral_fold_freeConv`,
  `MeasureTheory.Measure.freeCumulant_integral_fold_freeConv`,
  `MeasureTheory.Measure.support_fold_freeConv_subset_Icc`: formal series, cumulants, and support
  bounds for finite `Finset.fold`s of `freeConv`.
* `TauCeti.IsFreelyIndependentElements.law_sum`, `TauCeti.IsFreelyIndependent.law_sum`,
  `TauCeti.law_sum_eq_fold_freeConv_of_vonNeumannAlgebra`: C⋆- and von Neumann transport for finite
  sums of freely independent selfadjoint elements.
* `MeasureTheory.Measure.freeConvolutionPower_add`,
  `MeasureTheory.Measure.freeConvolutionPower_map_affine`,
  `MeasureTheory.Measure.rSeries_integral_freeConvolutionPower`,
  `MeasureTheory.Measure.freeCumulant_integral_freeConvolutionPower`: algebraic, affine, support,
  formal R-series, cumulant, mean, and variance laws for `freeConvolutionPower`.
* `TauCeti.Probability.semicircleReal_freeConv`,
  `TauCeti.Probability.semicircleReal_freeConvolutionPower`: closure of Wigner semicircle laws.

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

section Fold

variable {ι : Type*} (s : Finset ι) {μ : ι → Measure ℝ}

private theorem rSeries_integral_dirac_zero :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂Measure.dirac (0 : ℝ)) id = 0 := by
  let eval₀ : (ℝ → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  have hm : TauCeti.momentSeries (fun f : ℝ → ℝ => ∫ x, f x ∂Measure.dirac (0 : ℝ)) id =
      TauCeti.momentSeries eval₀ (algebraMap ℝ (ℝ → ℝ) 0) := by
    ext n
    simp [TauCeti.coeff_momentSeries, eval₀, Algebra.algebraMap_eq_smul_one]
  rw [TauCeti.rSeries_congr _ _ hm, TauCeti.rSeries_algebraMap (φ := eval₀) rfl 0, map_zero]

/-- Folding `freeConv` with base `Measure.dirac 0` always yields a measure with compact support. -/
theorem isCompact_support_fold_freeConv (μ : ι → Measure ℝ) :
    IsCompact (s.fold freeConv (Measure.dirac 0) μ).support := by
  classical
  cases s.eq_empty_or_nonempty with
  | inl h0 =>
      subst h0
      rw [Finset.fold_empty, Measure.support_dirac (0 : ℝ), closure_singleton]
      exact isCompact_singleton
  | inr hne =>
      obtain ⟨i, hi⟩ := hne
      rw [← Finset.insert_erase hi, Finset.fold_insert (Finset.notMem_erase i s)]
      exact isCompact_support_freeConv _ _

/-- Folding `freeConv` with base `Measure.dirac 0` over a family of compactly supported probability
measures yields a probability measure, including when `s = ∅`. -/
theorem isProbabilityMeasure_fold_freeConv
    (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.fold_empty]
      infer_instance
  | @insert i s hi ih =>
      have : IsProbabilityMeasure (μ i) := hprob i (mem_insert_self i s)
      have : IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) :=
        ih (fun j hj => hprob j (mem_insert_of_mem hj))
          (fun j hj => hcomp j (mem_insert_of_mem hj))
      rw [Finset.fold_insert hi]
      exact isProbabilityMeasure_freeConv (hcomp i (mem_insert_self i s))
        (isCompact_support_fold_freeConv s μ)

/-- Interval support bounds add across a finite `Finset.fold` of `freeConv`, including `s = ∅`. -/
theorem support_fold_freeConv_subset_Icc {m M : ι → ℝ}
    (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hI : ∀ i ∈ s, (μ i).support ⊆ Set.Icc (m i) (M i)) :
    (s.fold freeConv (Measure.dirac 0) μ).support ⊆
      Set.Icc (∑ i ∈ s, m i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.support_dirac (0 : ℝ)]
  | @insert i s hi ih =>
      have hcomp : ∀ j ∈ s, IsCompact (μ j).support := fun j hj =>
        isCompact_Icc.of_isClosed_subset Measure.isClosed_support (hI j (mem_insert_of_mem hj))
      have : IsProbabilityMeasure (μ i) := hprob i (mem_insert_self i s)
      have : IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) :=
        isProbabilityMeasure_fold_freeConv s
          (fun j hj => hprob j (mem_insert_of_mem hj)) hcomp
      rw [Finset.fold_insert hi, sum_insert hi, sum_insert hi]
      exact support_freeConv_subset_Icc (hI i (mem_insert_self i s))
        (ih (fun j hj => hprob j (mem_insert_of_mem hj))
          (fun j hj => hI j (mem_insert_of_mem hj)))

/-- The formal R-series of a finite `Finset.fold` of `freeConv` is the sum of the individual formal
R-series, including `s = ∅`. -/
theorem rSeries_integral_fold_freeConv
    (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support) :
    TauCeti.rSeries
        (fun f : ℝ → ℝ => ∫ x, f x ∂(s.fold freeConv (Measure.dirac 0) μ)) id =
      ∑ i ∈ s, TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ i) id := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.fold_empty, sum_empty, rSeries_integral_dirac_zero]
  | @insert i s hi ih =>
      have : IsProbabilityMeasure (μ i) := hprob i (mem_insert_self i s)
      have : IsProbabilityMeasure (s.fold freeConv (Measure.dirac 0) μ) :=
        isProbabilityMeasure_fold_freeConv s
          (fun j hj => hprob j (mem_insert_of_mem hj))
          (fun j hj => hcomp j (mem_insert_of_mem hj))
      rw [Finset.fold_insert hi, sum_insert hi,
        rSeries_integral_freeConv (hcomp i (mem_insert_self i s))
          (isCompact_support_fold_freeConv s μ),
        ih (fun j hj => hprob j (mem_insert_of_mem hj))
          (fun j hj => hcomp j (mem_insert_of_mem hj))]

/-- Nonempty free cumulants add across a finite `Finset.fold` of `freeConv`. -/
theorem freeCumulant_integral_fold_freeConv
    (hprob : ∀ i ∈ s, IsProbabilityMeasure (μ i))
    (hcomp : ∀ i ∈ s, IsCompact (μ i).support)
    {α : Type*} [LinearOrder α] {t : Finset α} (ht : t.Nonempty) :
    TauCeti.freeCumulant
        (fun f : ℝ → ℝ => ∫ x, f x ∂(s.fold freeConv (Measure.dirac 0) μ))
        (fun _ : α => (id : ℝ → ℝ)) t =
      ∑ i ∈ s, TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ i)
        (fun _ : α => (id : ℝ → ℝ)) t := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht.card_pos.ne'
  simp_rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries, hk,
    TauCeti.coeff_succ_freeCumulantSeries]
  rw [rSeries_integral_fold_freeConv s hprob hcomp, _root_.map_sum (PowerSeries.coeff k)]

end Fold

end MeasureTheory.Measure

namespace TauCeti

section FiniteFamily

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Law of a finite sum of freely independent selfadjoint elements.** For a state `φ` and a freely
independent family `a`, the law of `∑ i ∈ s, a i` is the `Finset.fold` of `Measure.freeConv` over
the individual laws `φ.law (a i)`, including `s = ∅`. -/
theorem IsFreelyIndependentElements.law_sum {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) (s : Finset ι)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    φ.law (∑ i ∈ s, a i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i => φ.law (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, Finset.fold_empty, φ.law_zero_of_apply_one hφ]
  | @insert i s hi ih =>
      let f : ι → Bool := fun j => decide (j = i)
      have hB := ha.adjoin_image_fiber hφ f
      have hai_mem : a i ∈ Algebra.adjoin ℂ (a '' (f ⁻¹' {true})) :=
        Algebra.subset_adjoin ⟨i, by simp [f], rfl⟩
      have hsum_mem : (∑ j ∈ s, a j) ∈ Algebra.adjoin ℂ (a '' (f ⁻¹' {false})) :=
        sum_mem fun j hj => Algebra.subset_adjoin
          ⟨j, by simp [f, ne_of_mem_of_not_mem hj hi], rfl⟩
      have hsa_sum : IsSelfAdjoint (∑ j ∈ s, a j) :=
        isSelfAdjoint_sum s fun j hj => hasa j (mem_insert_of_mem hj)
      rw [sum_insert hi, Finset.fold_insert hi,
        hB.law_add hφ Bool.false_ne_true.symm hai_mem hsum_mem (hasa i (mem_insert_self i s))
          hsa_sum,
        ih (fun j hj => hasa j (mem_insert_of_mem hj))]

/-- **Law of a finite sum from freely independent subalgebras.** -/
theorem IsFreelyIndependent.law_sum {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) (s : Finset ι) {a : ι → A}
    (haB : ∀ i ∈ s, a i ∈ B i) (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) :
    φ.law (∑ i ∈ s, a i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i => φ.law (a i)) := by
  have ha' : IsFreelyIndependentElements φ.toLinearMap (fun i : s => a i.1) :=
    isFreelyIndependentElements_iff.mpr <| (hB.comp Subtype.val_injective).mono fun i =>
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (haB i.1 i.2))
  have h := ha'.law_sum hφ univ fun i _ => hasa i.1 i.2
  rw [Finset.univ_eq_attach, Finset.sum_attach] at h
  rw [h]
  exact (Finset.fold_map (f := fun i => φ.law (a i))
    (g := Function.Embedding.subtype _)).symm.trans (by rw [Finset.attach_map_val])

/-- **Finite-family von Neumann transport.** If `M : ι → VonNeumannAlgebra H` has freely independent
subalgebras for a state `ω` on `H →L[ℂ] H`, and `T i ∈ M i` (`i ∈ s`) are selfadjoint, then
`ω.law (∑ i ∈ s, T i)` is the `Finset.fold` of `Measure.freeConv` over `ω.law (T i)`. -/
theorem law_sum_eq_fold_freeConv_of_vonNeumannAlgebra {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ω : (H →L[ℂ] H) →ₚ[ℂ] ℂ}
    {M : ι → VonNeumannAlgebra H}
    (hM : IsFreelyIndependent ω.toLinearMap fun i => (M i).toSubalgebra) (hω : ω 1 = 1)
    (s : Finset ι) {T : ι → H →L[ℂ] H} (hTM : ∀ i ∈ s, T i ∈ M i)
    (hsa : ∀ i ∈ s, IsSelfAdjoint (T i)) :
    ω.law (∑ i ∈ s, T i) = s.fold Measure.freeConv (Measure.dirac 0) (fun i => ω.law (T i)) :=
  hM.law_sum hω s hTM hsa

namespace FreeLawRealization

variable [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

/-- In the canonical C⋆-realization of `μ`, any finite sum `∑ i ∈ s, generator μ i` realizes the
folded free convolution `s.fold Measure.freeConv (Measure.dirac 0) μ`. -/
theorem law_sum_generator (s : Finset ι) :
    (state μ).law (∑ i ∈ s, generator μ i) = s.fold Measure.freeConv (Measure.dirac 0) μ := by
  rw [(isFreelyIndependentElements_generator μ).law_sum (state_one μ) s
    fun i _ => isSelfAdjoint_generator μ i]
  simp

/-- In the concrete von Neumann realization of `μ`, any finite sum
`∑ i ∈ s, vonNeumannGenerator μ i` realizes `s.fold Measure.freeConv (Measure.dirac 0) μ`. -/
theorem law_sum_vonNeumannGenerator (s : Finset ι) :
    (vonNeumannState μ).law (∑ i ∈ s, vonNeumannGenerator μ i) =
      s.fold Measure.freeConv (Measure.dirac 0) μ := by
  rw [(isFreelyIndependentElements_vonNeumannGenerator μ).law_sum (vonNeumannState_one μ) s
    fun i _ => isSelfAdjoint_vonNeumannGenerator μ i]
  simp

end FreeLawRealization

end FiniteFamily

end TauCeti

/-! ### Finite free convolution powers -/

namespace MeasureTheory.Measure

/-- The `n`-fold free additive convolution power `μ^{⊞ n}` of a measure on `ℝ`, with zeroth power
`Measure.dirac 0`. -/
def freeConvolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (freeConvolutionPower μ n).freeConv μ

@[simp]
theorem freeConvolutionPower_zero (μ : Measure ℝ) : μ.freeConvolutionPower 0 = Measure.dirac 0 := by
  rfl

@[simp]
theorem freeConvolutionPower_succ (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = (μ.freeConvolutionPower n).freeConv μ := by
  rfl

instance isFiniteMeasure_freeConvolutionPower (μ : Measure ℝ) (n : ℕ) :
    IsFiniteMeasure (μ.freeConvolutionPower n) := by
  induction n with
  | zero => simp only [freeConvolutionPower_zero]; infer_instance
  | succ _ _ => simp only [freeConvolutionPower_succ]; infer_instance

/-- Every free convolution power of any measure on `ℝ` has compact topological support. -/
theorem isCompact_support_freeConvolutionPower (μ : Measure ℝ) :
    ∀ n : ℕ, IsCompact (μ.freeConvolutionPower n).support
  | 0 => by
      rw [freeConvolutionPower_zero, Measure.support_dirac (0 : ℝ), closure_singleton]
      exact isCompact_singleton
  | n + 1 => by rw [freeConvolutionPower_succ]; exact isCompact_support_freeConv _ _

/-- Every free convolution power of a compactly supported probability measure is a probability
measure. -/
theorem isProbabilityMeasure_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : ∀ n : ℕ, IsProbabilityMeasure (μ.freeConvolutionPower n)
  | 0 => by rw [freeConvolutionPower_zero]; infer_instance
  | n + 1 => by
      have := isProbabilityMeasure_freeConvolutionPower hμ n
      rw [freeConvolutionPower_succ]
      exact isProbabilityMeasure_freeConv (isCompact_support_freeConvolutionPower μ n) hμ

/-- The first free convolution power of a compactly supported probability measure is itself. -/
theorem freeConvolutionPower_one {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : μ.freeConvolutionPower 1 = μ := by
  rw [freeConvolutionPower_succ, freeConvolutionPower_zero, dirac_zero_freeConv hμ]

/-- Free convolution powers turn addition of exponents into `freeConv`. -/
theorem freeConvolutionPower_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (m n : ℕ) :
    μ.freeConvolutionPower (m + n) =
      (μ.freeConvolutionPower m).freeConv (μ.freeConvolutionPower n) := by
  induction n with
  | zero =>
      have := isProbabilityMeasure_freeConvolutionPower hμ m
      rw [Nat.add_zero, freeConvolutionPower_zero,
        freeConv_dirac_zero (isCompact_support_freeConvolutionPower μ m)]
  | succ n ih =>
      rw [Nat.add_succ, freeConvolutionPower_succ, freeConvolutionPower_succ, ih, freeConv_assoc]

/-- Left recursion `μ^{⊞ (n + 1)} = μ ⊞ μ^{⊞ n}`, unconditionally for all measures on `ℝ`. -/
theorem freeConvolutionPower_succ' (μ : Measure ℝ) (n : ℕ) :
    μ.freeConvolutionPower (n + 1) = μ.freeConv (μ.freeConvolutionPower n) := by
  rw [freeConvolutionPower_succ, freeConv_comm]

/-- Free convolution powers of a Dirac mass add its atom `n` times. -/
theorem freeConvolutionPower_dirac (a : ℝ) (n : ℕ) :
    (Measure.dirac a).freeConvolutionPower n = Measure.dirac (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [freeConvolutionPower_succ, ih, dirac_freeConv_dirac, succ_nsmul]

@[simp]
theorem freeConvolutionPower_dirac_zero (n : ℕ) :
    (Measure.dirac (0 : ℝ)).freeConvolutionPower n = Measure.dirac 0 := by
  simpa using freeConvolutionPower_dirac 0 n

/-- Real affine pushforwards commute with free convolution powers, accumulating the translation `n`
times; valid for all slopes `b : ℝ` and at `n = 0`. -/
theorem freeConvolutionPower_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) (n : ℕ) :
    (μ.map fun x => a + b * x).freeConvolutionPower n =
      (μ.freeConvolutionPower n).map fun x => (n : ℝ) * a + b * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : IsProbabilityMeasure (μ.freeConvolutionPower n) :=
        isProbabilityMeasure_freeConvolutionPower hμ n
      rw [freeConvolutionPower_succ, ih,
        freeConv_map_affine (isCompact_support_freeConvolutionPower μ n) hμ ((n : ℝ) * a) a b,
        ← freeConvolutionPower_succ]
      congr 1
      funext x
      push_cast
      ring

/-- Translating a compactly supported probability measure by `a` translates its `n`-th free
convolution power by `n • a`. -/
theorem freeConvolutionPower_map_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a : ℝ) (n : ℕ) :
    (μ.map (a + ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (n • a + ·) := by
  simpa [nsmul_eq_mul] using freeConvolutionPower_map_affine hμ a 1 n

/-- Scaling a compactly supported probability measure by `b` scales its `n`-th free convolution
power by `b`, including at `n = 0` and `b = 0`. -/
theorem freeConvolutionPower_map_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (b : ℝ) (n : ℕ) :
    (μ.map (b * ·)).freeConvolutionPower n = (μ.freeConvolutionPower n).map (b * ·) := by
  simpa using freeConvolutionPower_map_affine hμ 0 b n

/-- Reflection `Measure.neg` commutes with free convolution powers, unconditionally for all measures
on `ℝ`. -/
theorem freeConvolutionPower_neg (μ : Measure ℝ) (n : ℕ) :
    μ.neg.freeConvolutionPower n = (μ.freeConvolutionPower n).neg := by
  induction n with
  | zero => simp [Measure.neg_def, Measure.map_dirac' measurable_neg]
  | succ n ih => rw [freeConvolutionPower_succ, ih, freeConv_neg, freeConvolutionPower_succ]

/-- Interval support bounds scale by `n` under `freeConvolutionPower`, including at `n = 0`. -/
theorem support_freeConvolutionPower_subset_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {m M : ℝ} (hI : μ.support ⊆ Set.Icc m M) (n : ℕ) :
    (μ.freeConvolutionPower n).support ⊆ Set.Icc ((n : ℝ) * m) ((n : ℝ) * M) := by
  have hμ : IsCompact μ.support := isCompact_Icc.of_isClosed_subset Measure.isClosed_support hI
  induction n with
  | zero => simp [Measure.support_dirac (0 : ℝ)]
  | succ n ih =>
      have := isProbabilityMeasure_freeConvolutionPower hμ n
      rw [freeConvolutionPower_succ]
      refine (support_freeConv_subset_Icc ih hI).trans ?_
      rintro x ⟨hx1, hx2⟩
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- Folding `freeConv` over a constant measure on `s` gives the `#s`-th free convolution power,
unconditionally for all measures on `ℝ`. -/
theorem fold_freeConv_const {ι : Type*} (s : Finset ι) (μ : Measure ℝ) :
    s.fold freeConv (Measure.dirac 0) (fun _ => μ) = μ.freeConvolutionPower #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.fold_insert hi, card_insert_of_notMem hi, ih, freeConvolutionPower_succ']

/-- **Formal R-series of a free convolution power**: `R_{μ^{⊞ n}} = n • R_μ`. -/
theorem rSeries_integral_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConvolutionPower n)) id =
      n • TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by
  have h := rSeries_integral_fold_freeConv (univ : Finset (Fin n)) (μ := fun _ => μ)
    (fun _ _ => inferInstance) (fun _ _ => hμ)
  simpa [fold_freeConv_const _ μ] using h

/-- **Free cumulants of a free convolution power**: `κ_s(μ^{⊞ n}) = n • κ_s(μ)` for nonempty `s`. -/
theorem freeCumulant_integral_freeConvolutionPower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (n : ℕ) {α : Type*} [LinearOrder α] {s : Finset α}
    (hs : s.Nonempty) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConvolutionPower n))
        (fun _ : α => (id : ℝ → ℝ)) s =
      n • TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : α => (id : ℝ → ℝ)) s := by
  have h := freeCumulant_integral_fold_freeConv (univ : Finset (Fin n)) (μ := fun _ => μ)
    (fun _ _ => inferInstance) (fun _ _ => hμ) hs
  simpa [fold_freeConv_const _ μ] using h

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
  induction n with
  | zero => simp
  | succ n ih =>
      have := isProbabilityMeasure_freeConvolutionPower hμ n
      rw [freeConvolutionPower_succ,
        variance_id_freeConv (isCompact_support_freeConvolutionPower μ n) hμ, ih]
      push_cast
      ring

end MeasureTheory.Measure

namespace TauCeti

section ConvolutionPowerLaw

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

end ConvolutionPowerLaw

end TauCeti

/-! ### Free additive convolution of Wigner semicircle laws -/

namespace TauCeti.Probability

private theorem isCompact_support_semicircleReal (m : ℝ) (v : ℝ≥0) :
    IsCompact (semicircleReal m v).support := by
  rw [support_semicircleReal]
  exact isCompact_Icc

/-- **Free additive convolution of Wigner semicircle laws.** Both centres and variances add, for all
`m₁, m₂ : ℝ` and `v₁, v₂ : ℝ≥0` (including the degenerate zero-variance Dirac cases). -/
theorem semicircleReal_freeConv (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) :
    (semicircleReal m₁ v₁).freeConv (semicircleReal m₂ v₂) =
      semicircleReal (m₁ + m₂) (v₁ + v₂) := by
  have hcentred : (semicircleReal 0 v₁).freeConv (semicircleReal 0 v₂) =
      semicircleReal 0 (v₁ + v₂) := by
    let τ : Bool → Measure ℝ := fun b => cond b (semicircleReal 0 v₁) (semicircleReal 0 v₂)
    have : ∀ b : Bool, IsProbabilityMeasure (τ b) := fun b => by
      cases b
      · exact inferInstanceAs (IsProbabilityMeasure (semicircleReal 0 v₂))
      · exact inferInstanceAs (IsProbabilityMeasure (semicircleReal 0 v₁))
    have : ∀ b : Bool, CompactSpace (τ b).support := fun b => by
      cases b
      · exact isCompact_iff_compactSpace.mp (isCompact_support_semicircleReal 0 v₂)
      · exact isCompact_iff_compactSpace.mp (isCompact_support_semicircleReal 0 v₁)
    let φ := FreeLawRealization.state τ
    let g := FreeLawRealization.generator τ
    have hg1 : IsSemicircular φ.toLinearMap (g true) ((v₁ : ℝ) : ℂ) :=
      (φ.law_eq_semicircleReal_iff (FreeLawRealization.isSelfAdjoint_generator τ true) v₁).mp
        (FreeLawRealization.law_generator τ true)
    have hg2 : IsSemicircular φ.toLinearMap (g false) ((v₂ : ℝ) : ℂ) :=
      (φ.law_eq_semicircleReal_iff (FreeLawRealization.isSelfAdjoint_generator τ false) v₂).mp
        (FreeLawRealization.law_generator τ false)
    have hsum : IsSemicircular φ.toLinearMap (g true + g false) (((v₁ + v₂ : ℝ≥0) : ℝ) : ℂ) := by
      simpa [NNReal.coe_add] using
        (FreeLawRealization.isFreelyIndependentElements_generator τ).isSemicircular_add
          Bool.false_ne_true.symm hg1 hg2
    have hlaw_add : φ.law (g true + g false) =
        (semicircleReal 0 v₁).freeConv (semicircleReal 0 v₂) :=
      FreeLawRealization.law_add_generator τ Bool.false_ne_true.symm
    rw [← hlaw_add]
    exact (φ.law_eq_semicircleReal_iff
      ((FreeLawRealization.isSelfAdjoint_generator τ true).add
        (FreeLawRealization.isSelfAdjoint_generator τ false)) (v₁ + v₂)).mpr hsum
  have hshift (m : ℝ) (v : ℝ≥0) :
      semicircleReal m v = (semicircleReal 0 v).map fun x => m + 1 * x := by
    simpa using (map_affine_semicircleReal 0 m 1 v).symm
  rw [hshift m₁ v₁, hshift m₂ v₂,
    Measure.freeConv_map_affine (isCompact_support_semicircleReal 0 v₁)
      (isCompact_support_semicircleReal 0 v₂) m₁ m₂ 1,
    hcentred, ← hshift (m₁ + m₂) (v₁ + v₂)]

/-- **Free convolution powers of Wigner semicircle laws.** -/
theorem semicircleReal_freeConvolutionPower (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    (semicircleReal m v).freeConvolutionPower n = semicircleReal (n * m) (n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Measure.freeConvolutionPower_succ, ih, semicircleReal_freeConv, succ_nsmul]
      congr 1
      push_cast
      ring

end TauCeti.Probability
