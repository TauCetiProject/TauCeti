/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.Probability.FreeProbability.Distribution.Free
public import TauCeti.Probability.FreeProbability.Law.Cumulant
public import TauCeti.Probability.FreeProbability.Law.Realization

/-!
# Free additive convolution of compactly supported probability measures on `ℝ`

For compactly supported probability measures `μ` and `ν` on `ℝ`, their **free additive convolution**
`μ ⊞ ν` (`MeasureTheory.Measure.freeConv μ ν`) is the law of `a + b` for freely independent
selfadjoint elements `a` and `b` with laws `μ` and `ν` in the canonical reduced C⋆-free product
realization. Outside compactly supported probability measures on `ℝ`, `μ ⊞ ν` is defined to be `0`
by convention.

Because the joint algebraic distribution of a freely independent family is uniquely determined by
its one-variable power moments (`IsFreelyIndependentElements.jointDistribution_eq_of_forall_pow`),
the law of `a + b` in *any* C⋆-probability space—and hence in any concrete von Neumann algebra—with
respect to any state is `φ.law a ⊞ φ.law b` whenever `a` and `b` are selfadjoint and freely
independent.

Consequently:
* `μ ⊞ ν` is a compactly supported probability measure whenever `μ` and `ν` are;
* its formal R-series and positive-order free cumulants are the sums of those of `μ` and `ν`,
  `(μ ⊞ ν).rSeries = μ.rSeries + ν.rSeries` and
  `(μ ⊞ ν).freeCumulant n = μ.freeCumulant n + ν.freeCumulant n` for `n ≥ 1`;
* `⊞` is commutative and associative on all of `Measure ℝ`, with `Measure.dirac 0` as identity on
  compactly supported probability measures;
* affine pushforwards with a common slope distribute over `⊞`, accumulating the translations;
* unlike classical convolution, `(μ ⊞ ν).support` need not equal `μ.support + ν.support` (for
  example, two symmetric Bernoulli laws convolve freely to an arcsine law on the full interval),
  but operator-order bounds on the C⋆-realization show that `μ.support ⊆ [a₁, b₁]` and
  `ν.support ⊆ [a₂, b₂]` imply `(μ ⊞ ν).support ⊆ [a₁ + a₂, b₁ + b₂]`;
* semicircle laws satisfy
  `semicircleReal a v ⊞ semicircleReal b w = semicircleReal (a + b) (v + w)`.

## Main declarations

* `MeasureTheory.Measure.freeConv` (scoped notation `μ ⊞ ν` in `FreeProbability`): free additive
  convolution on `Measure ℝ`.
* `TauCeti.IsFreelyIndependent.law_add`, `TauCeti.IsFreelyIndependentElements.law_add`:
  realization-independence of `μ ⊞ ν` in arbitrary C⋆- and von Neumann probability spaces.
* `TauCeti.FreeLawRealization.law_cstarElement_add`,
  `TauCeti.FreeLawRealization.law_vonNeumannElement_add`: transport of binary free convolution
  through the canonical tracial C⋆- and von Neumann realizations.
* `MeasureTheory.Measure.rSeries_freeConv`, `MeasureTheory.Measure.freeCumulant_freeConv`,
  `MeasureTheory.Measure.eq_freeConv_iff_rSeries_eq`: additivity of R-series and free cumulants,
  and cumulant characterization of `μ ⊞ ν`.
* `MeasureTheory.Measure.freeConv_comm`, `MeasureTheory.Measure.freeConv_assoc`,
  `MeasureTheory.Measure.dirac_zero_freeConv`, `MeasureTheory.Measure.freeConv_dirac_zero`:
  algebraic laws of `⊞`.
* `MeasureTheory.Measure.freeConv_map_affine`, `MeasureTheory.Measure.dirac_freeConv`,
  `MeasureTheory.Measure.freeConv_dirac`, `MeasureTheory.Measure.neg_freeConv_neg`: affine and
  translation equivariance.
* `MeasureTheory.Measure.support_freeConv_subset_Icc`,
  `MeasureTheory.Measure.support_freeConv_subset_Icc_sInf_sSup`,
  `MeasureTheory.Measure.support_freeConv_subset_closedBall`: support bounds.
* `MeasureTheory.Measure.semicircleReal_freeConv_semicircleReal`: additive stability of semicircle
  laws under `⊞`.

## References

* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

noncomputable section

open MeasureTheory PowerSeries
open scoped ComplexOrder NNReal

namespace MeasureTheory.Measure

private def pairMeasure (μ ν : Measure ℝ) : Bool → Measure ℝ :=
  fun b => if b then ν else μ

private instance isProbabilityMeasure_pairMeasure {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (b : Bool) : IsProbabilityMeasure (pairMeasure μ ν b) := by
  cases b <;> dsimp [pairMeasure] <;> infer_instance

open Classical in
/-- The **free additive convolution** `μ ⊞ ν` of two compactly supported probability measures on
`ℝ`: the law of `a + b` for freely independent selfadjoint elements `a` and `b` with laws `μ` and
`ν` in the reduced C⋆-free product realization. If either measure is not a compactly supported
probability measure, `μ.freeConv ν` is `0` by convention. -/
def freeConv (μ ν : Measure ℝ) : Measure ℝ :=
  if IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support then
    (TauCeti.FreeLawRealization.cstarState (pairMeasure μ ν)).law
      (TauCeti.FreeLawRealization.cstarElement (pairMeasure μ ν) false +
        TauCeti.FreeLawRealization.cstarElement (pairMeasure μ ν) true)
  else 0

/-- Scoped infix notation `μ ⊞ ν` for the free additive convolution `Measure.freeConv μ ν`. -/
scoped[FreeProbability] infixl:65 " ⊞ " => MeasureTheory.Measure.freeConv

open scoped FreeProbability

private theorem freeConv_eq_law {μ ν : Measure ℝ} [hμP : IsProbabilityMeasure μ]
    [hνP : IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ ⊞ ν =
      (TauCeti.FreeLawRealization.cstarState (pairMeasure μ ν)).law
        (TauCeti.FreeLawRealization.cstarElement (pairMeasure μ ν) false +
          TauCeti.FreeLawRealization.cstarElement (pairMeasure μ ν) true) := by
  simp [freeConv, hμP, hμ, hνP, hν]

/-- `μ ⊞ ν` vanishes when `μ` is not a probability measure. -/
theorem freeConv_of_not_isProbabilityMeasure_left {μ ν : Measure ℝ}
    (h : ¬IsProbabilityMeasure μ) : μ ⊞ ν = 0 := by
  simp [freeConv, h]

/-- `μ ⊞ ν` vanishes when `ν` is not a probability measure. -/
theorem freeConv_of_not_isProbabilityMeasure_right {μ ν : Measure ℝ}
    (h : ¬IsProbabilityMeasure ν) : μ ⊞ ν = 0 := by
  simp [freeConv, h]

/-- `μ ⊞ ν` vanishes when `μ` does not have compact support. -/
theorem freeConv_of_not_isCompact_support_left {μ ν : Measure ℝ}
    (h : ¬IsCompact μ.support) : μ ⊞ ν = 0 := by
  simp [freeConv, h]

/-- `μ ⊞ ν` vanishes when `ν` does not have compact support. -/
theorem freeConv_of_not_isCompact_support_right {μ ν : Measure ℝ}
    (h : ¬IsCompact ν.support) : μ ⊞ ν = 0 := by
  simp [freeConv, h]

@[simp]
theorem zero_freeConv (ν : Measure ℝ) : (0 : Measure ℝ) ⊞ ν = 0 :=
  freeConv_of_not_isProbabilityMeasure_left fun h => by simpa using h.measure_univ

@[simp]
theorem freeConv_zero (μ : Measure ℝ) : μ ⊞ (0 : Measure ℝ) = 0 :=
  freeConv_of_not_isProbabilityMeasure_right fun h => by simpa using h.measure_univ

instance isFiniteMeasure_freeConv (μ ν : Measure ℝ) : IsFiniteMeasure (μ ⊞ ν) := by
  classical
  unfold freeConv
  split_ifs
  · infer_instance
  · infer_instance

/-- The topological support of `μ ⊞ ν` is always compact. -/
theorem isCompact_support_freeConv (μ ν : Measure ℝ) : IsCompact (μ ⊞ ν).support := by
  classical
  unfold freeConv
  split_ifs
  · exact PositiveLinearMap.isCompact_support_law _ _
  · simp

/-- The free additive convolution of two compactly supported probability measures on `ℝ` is a
probability measure. -/
theorem isProbabilityMeasure_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    IsProbabilityMeasure (μ ⊞ ν) := by
  rw [freeConv_eq_law hμ hν]
  exact PositiveLinearMap.isProbabilityMeasure_law _
    (TauCeti.FreeLawRealization.cstarState_one _)
    ((TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement _ false).add
      (TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement _ true))

end MeasureTheory.Measure

namespace TauCeti

open scoped FreeProbability

section RealizationIndependence

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : A →ₚ[ℂ] ℂ}

/-- **Realization-independence of free additive convolution.** If `B` is a freely independent
family of unital subalgebras of a C⋆-algebra `A` (including any concrete von Neumann algebra) with
respect to a state `φ`, and `a ∈ B i`, `b ∈ B j` (`i ≠ j`) are selfadjoint, then the law of `a + b`
is `φ.law a ⊞ φ.law b`. -/
theorem IsFreelyIndependent.law_add {B : ι → Subalgebra ℂ A}
    (h : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    {a b : A} (haB : a ∈ B i) (hbB : b ∈ B j) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    φ.law (a + b) = φ.law a ⊞ φ.law b := by
  let μ := φ.law a
  let ν := φ.law b
  have : IsProbabilityMeasure μ := φ.isProbabilityMeasure_law hφ ha
  have : IsProbabilityMeasure ν := φ.isProbabilityMeasure_law hφ hb
  have hμ : IsCompact μ.support := φ.isCompact_support_law a
  have hν : IsCompact ν.support := φ.isCompact_support_law b
  let ρ := Measure.pairMeasure μ ν
  rw [Measure.freeConv_eq_law hμ hν]
  let f : Bool → A := fun k => if k then b else a
  have hf : IsFreelyIndependentElements φ.toLinearMap f := by
    rw [isFreelyIndependentElements_iff]
    refine (h.comp (e := fun k : Bool => if k then j else i) ?_).mono fun k =>
      Algebra.adjoin_le (Set.singleton_subset_iff.2 (by cases k <;> simp [f, haB, hbB]))
    rintro (_ | _) (_ | _) <;> simp [hij, hij.symm]
  have hjd := hf.jointDistribution_eq_of_forall_pow
    (FreeLawRealization.isFreelyIndependentElements_cstarElement ρ) hφ
    (FreeLawRealization.cstarState_one ρ) fun k n => by
      cases k
      · simp only [PositiveLinearMap.coe_toLinearMap, f, Bool.false_eq_true, ↓reduceIte]
        rw [← φ.ofReal_integral_pow_law ha n,
          ← (FreeLawRealization.cstarState ρ).ofReal_integral_pow_law
            (FreeLawRealization.isSelfAdjoint_cstarElement ρ false) n,
          FreeLawRealization.law_cstarElement (μ := ρ) (i := false) hμ]
        rfl
      · simp only [PositiveLinearMap.coe_toLinearMap, f, ↓reduceIte]
        rw [← φ.ofReal_integral_pow_law hb n,
          ← (FreeLawRealization.cstarState ρ).ofReal_integral_pow_law
            (FreeLawRealization.isSelfAdjoint_cstarElement ρ true) n,
          FreeLawRealization.law_cstarElement (μ := ρ) (i := true) hν]
        rfl
  refine (φ.law_eq_law_iff_forall_apply_pow (FreeLawRealization.cstarState ρ) (ha.add hb)
    ((FreeLawRealization.isSelfAdjoint_cstarElement ρ false).add
      (FreeLawRealization.isSelfAdjoint_cstarElement ρ true))).2 fun n => ?_
  have hval := LinearMap.congr_fun hjd ((FreeAlgebra.ι ℂ false + FreeAlgebra.ι ℂ true) ^ n)
  simpa [jointDistribution_apply, f] using hval

/-- If `c` is a freely independent family of elements for a state `φ` on a C⋆-algebra `A` and
`c i`, `c j` (`i ≠ j`) are selfadjoint, then `φ.law (c i + c j) = φ.law (c i) ⊞ φ.law (c j)`. -/
theorem IsFreelyIndependentElements.law_add {c : ι → A}
    (h : IsFreelyIndependentElements φ.toLinearMap c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hi : IsSelfAdjoint (c i)) (hj : IsSelfAdjoint (c j)) :
    φ.law (c i + c j) = φ.law (c i) ⊞ φ.law (c j) :=
  (isFreelyIndependentElements_iff.1 h).law_add hφ hij
    (Algebra.self_mem_adjoin_singleton ℂ (c i)) (Algebra.self_mem_adjoin_singleton ℂ (c j)) hi hj

end RealizationIndependence

namespace FreeLawRealization

variable {I : Type*} [DecidableEq I] {μ : I → Measure ℝ}

/-- In the canonical C⋆-realization of `μ`, the sum of distinct generators `i ≠ j` whose target
measures are compactly supported probability measures has law `μ i ⊞ μ j`. -/
theorem law_cstarElement_add {i j : I} (hij : i ≠ j)
    [IsProbabilityMeasure (μ i)] [IsProbabilityMeasure (μ j)]
    (hi : IsCompact (μ i).support) (hj : IsCompact (μ j).support) :
    (cstarState μ).law (cstarElement μ i + cstarElement μ j) = μ i ⊞ μ j := by
  rw [(isFreelyIndependentElements_cstarElement μ).law_add (cstarState_one μ) hij
    (isSelfAdjoint_cstarElement μ i) (isSelfAdjoint_cstarElement μ j),
    law_cstarElement hi, law_cstarElement hj]

/-- In the canonical von Neumann realization of `μ`, the sum of distinct generators `i ≠ j` whose
target measures are compactly supported probability measures has law `μ i ⊞ μ j`. -/
theorem law_vonNeumannElement_add {i j : I} (hij : i ≠ j)
    [IsProbabilityMeasure (μ i)] [IsProbabilityMeasure (μ j)]
    (hi : IsCompact (μ i).support) (hj : IsCompact (μ j).support) :
    (vonNeumannState μ).law (vonNeumannElement μ i + vonNeumannElement μ j) = μ i ⊞ μ j := by
  rw [(isFreelyIndependentElements_vonNeumannElement μ).law_add (vonNeumannState_one μ) hij
    (isSelfAdjoint_vonNeumannElement μ i) (isSelfAdjoint_vonNeumannElement μ j),
    law_vonNeumannElement hi, law_vonNeumannElement hj]

end FreeLawRealization

end TauCeti

namespace MeasureTheory.Measure

open scoped FreeProbability

section CumulantsAndAlgebra

/-- **Additivity of the R-series under free additive convolution.** For compactly supported
probability measures `μ` and `ν` on `ℝ`, `(μ ⊞ ν).rSeries = μ.rSeries + ν.rSeries`. -/
theorem rSeries_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    (μ ⊞ ν).rSeries = μ.rSeries + ν.rSeries := by
  let ρ := pairMeasure μ ν
  ext n
  apply Complex.ofReal_injective
  have hadd := (TauCeti.FreeLawRealization.isFreelyIndependentElements_cstarElement ρ).rSeries_add
    (TauCeti.FreeLawRealization.cstarState_one ρ) Bool.false_ne_true
  have hsum := (TauCeti.FreeLawRealization.cstarState ρ).map_ofReal_rSeries_law
    ((TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement ρ false).add
      (TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement ρ true))
  have h0 := (TauCeti.FreeLawRealization.cstarState ρ).map_ofReal_rSeries_law
    (TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement ρ false)
  have h1 := (TauCeti.FreeLawRealization.cstarState ρ).map_ofReal_rSeries_law
    (TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement ρ true)
  rw [← freeConv_eq_law hμ hν] at hsum
  rw [TauCeti.FreeLawRealization.law_cstarElement (μ := ρ) (i := false) hμ] at h0
  rw [TauCeti.FreeLawRealization.law_cstarElement (μ := ρ) (i := true) hν] at h1
  have hcoeff := congrArg (coeff n) (hsum.trans (hadd.trans (congrArg₂ (· + ·) h0.symm h1.symm)))
  simpa [ρ, pairMeasure] using hcoeff

/-- **Additivity of free cumulants under free additive convolution.** For compactly supported
probability measures `μ` and `ν` on `ℝ` and every `n ≠ 0`,
`κ_n(μ ⊞ ν) = κ_n(μ) + κ_n(ν)`. -/
theorem freeCumulant_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) {n : ℕ} (hn : n ≠ 0) :
    (μ ⊞ ν).freeCumulant n = μ.freeCumulant n + ν.freeCumulant n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa only [coeff_rSeries, map_add] using congrArg (coeff m) (rSeries_freeConv hμ hν)

/-- A compactly supported probability measure `ρ` equals `μ ⊞ ν` if and only if
`ρ.rSeries = μ.rSeries + ν.rSeries`. -/
theorem eq_freeConv_iff_rSeries_eq {ρ μ ν : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ ⊞ ν ↔ ρ.rSeries = μ.rSeries + ν.rSeries := by
  have : IsProbabilityMeasure (μ ⊞ ν) := isProbabilityMeasure_freeConv hμ hν
  rw [← rSeries_eq_iff hρ (isCompact_support_freeConv μ ν), rSeries_freeConv hμ hν]

/-- A compactly supported probability measure `ρ` equals `μ ⊞ ν` if and only if its positive-order
free cumulants are the sums of those of `μ` and `ν`. -/
theorem eq_freeConv_iff_forall_freeCumulant_eq {ρ μ ν : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ ⊞ ν ↔ ∀ n : ℕ, n ≠ 0 → ρ.freeCumulant n = μ.freeCumulant n + ν.freeCumulant n := by
  rw [eq_freeConv_iff_rSeries_eq hρ hμ hν, PowerSeries.ext_iff]
  refine ⟨fun h n hn => ?_, fun h m => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa [coeff_rSeries] using h m
  · simpa [coeff_rSeries] using h (m + 1) (Nat.succ_ne_zero m)

/-- Free additive convolution is commutative on all of `Measure ℝ`. -/
theorem freeConv_comm (μ ν : Measure ℝ) : μ ⊞ ν = ν ⊞ μ := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨hμP, hμ, hνP, hν⟩ := h
    have := isProbabilityMeasure_freeConv hμ hν
    have := isProbabilityMeasure_freeConv hν hμ
    rw [← rSeries_eq_iff (isCompact_support_freeConv μ ν) (isCompact_support_freeConv ν μ),
      rSeries_freeConv hμ hν, rSeries_freeConv hν hμ, add_comm]
  · have h' : ¬(IsProbabilityMeasure ν ∧ IsCompact ν.support ∧
        IsProbabilityMeasure μ ∧ IsCompact μ.support) := by tauto
    simp [freeConv, h, h']

instance : Std.Commutative freeConv := ⟨freeConv_comm⟩

/-- Free additive convolution is associative on all of `Measure ℝ`. -/
theorem freeConv_assoc (μ ν ρ : Measure ℝ) : (μ ⊞ ν) ⊞ ρ = μ ⊞ (ν ⊞ ρ) := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support ∧
      IsProbabilityMeasure ρ ∧ IsCompact ρ.support
  · obtain ⟨hμP, hμ, hνP, hν, hρP, hρ⟩ := h
    have := isProbabilityMeasure_freeConv hμ hν
    have := isProbabilityMeasure_freeConv hν hρ
    have := isProbabilityMeasure_freeConv (isCompact_support_freeConv μ ν) hρ
    have := isProbabilityMeasure_freeConv hμ (isCompact_support_freeConv ν ρ)
    rw [← rSeries_eq_iff (isCompact_support_freeConv (μ ⊞ ν) ρ)
        (isCompact_support_freeConv μ (ν ⊞ ρ)),
      rSeries_freeConv (isCompact_support_freeConv μ ν) hρ, rSeries_freeConv hμ hν,
      rSeries_freeConv hμ (isCompact_support_freeConv ν ρ), rSeries_freeConv hν hρ, add_assoc]
  · have hl : (μ ⊞ ν) ⊞ ρ = 0 := by
      by_cases hμν : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
          IsProbabilityMeasure ν ∧ IsCompact ν.support
      · have hρ' : ¬(IsProbabilityMeasure ρ ∧ IsCompact ρ.support) := fun hr =>
          h ⟨hμν.1, hμν.2.1, hμν.2.2.1, hμν.2.2.2, hr.1, hr.2⟩
        rcases not_and_or.1 hρ' with hρP | hρK
        · exact freeConv_of_not_isProbabilityMeasure_right hρP
        · exact freeConv_of_not_isCompact_support_right hρK
      · have h0 : μ ⊞ ν = 0 := by simp [freeConv, hμν]
        rw [h0, zero_freeConv]
    have hr : μ ⊞ (ν ⊞ ρ) = 0 := by
      by_cases hνρ : IsProbabilityMeasure ν ∧ IsCompact ν.support ∧
          IsProbabilityMeasure ρ ∧ IsCompact ρ.support
      · have hμ' : ¬(IsProbabilityMeasure μ ∧ IsCompact μ.support) := fun hm =>
          h ⟨hm.1, hm.2, hνρ.1, hνρ.2.1, hνρ.2.2.1, hνρ.2.2.2⟩
        rcases not_and_or.1 hμ' with hμP | hμK
        · exact freeConv_of_not_isProbabilityMeasure_left hμP
        · exact freeConv_of_not_isCompact_support_left hμK
      · have h0 : ν ⊞ ρ = 0 := by simp [freeConv, hνρ]
        rw [h0, freeConv_zero]
    rw [hl, hr]

instance : Std.Associative freeConv := ⟨freeConv_assoc⟩

/-- `Measure.dirac 0` is the left identity of `⊞` on compactly supported probability measures. -/
theorem dirac_zero_freeConv {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    Measure.dirac 0 ⊞ μ = μ := by
  symm
  rw [eq_freeConv_iff_rSeries_eq hμ (by simp [Measure.support_dirac]) hμ, rSeries_dirac_zero,
    zero_add]

/-- `Measure.dirac 0` is the right identity of `⊞` on compactly supported probability measures. -/
theorem freeConv_dirac_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    μ ⊞ Measure.dirac 0 = μ := by
  rw [freeConv_comm, dirac_zero_freeConv hμ]

end CumulantsAndAlgebra

section AffineAndSupport

/-- **Affine equivariance of free additive convolution.** Pushing two compactly supported
probability measures forward by real affine maps with a common slope `b` (positive, zero, or
negative) commutes with `⊞` and adds their translations. -/
theorem freeConv_map_affine {μ ν : Measure ℝ} [hμP : IsProbabilityMeasure μ]
    [hνP : IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    (a c b : ℝ) :
    (μ.map fun x => a + b * x) ⊞ (ν.map fun x => c + b * x) =
      (μ ⊞ ν).map fun x => a + c + b * x := by
  have : IsProbabilityMeasure (μ ⊞ ν) := isProbabilityMeasure_freeConv hμ hν
  have : IsProbabilityMeasure (μ.map fun x => a + b * x) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  have : IsProbabilityMeasure (ν.map fun x => c + b * x) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  have : IsProbabilityMeasure ((μ ⊞ ν).map fun x => a + c + b * x) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  have hμ' : IsCompact (μ.map fun x => a + b * x).support := by
    rw [TauCeti.Probability.support_map_affine]
    exact hμ.image (by fun_prop)
  have hν' : IsCompact (ν.map fun x => c + b * x).support := by
    rw [TauCeti.Probability.support_map_affine]
    exact hν.image (by fun_prop)
  have hμν' : IsCompact ((μ ⊞ ν).map fun x => a + c + b * x).support := by
    rw [TauCeti.Probability.support_map_affine]
    exact (isCompact_support_freeConv μ ν).image (by fun_prop)
  symm
  rw [eq_freeConv_iff_rSeries_eq hμν' hμ' hν',
    rSeries_map_affine (isCompact_support_freeConv μ ν), rSeries_freeConv hμ hν,
    rSeries_map_affine hμ, rSeries_map_affine hν]
  simp only [map_add, smul_add]
  ring

/-- Convolving freely with `Measure.dirac c` on the left translates by `c`. -/
theorem dirac_freeConv {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (c : ℝ) : Measure.dirac c ⊞ μ = μ.map (c + ·) := by
  have hc : Measure.dirac c = (Measure.dirac (0 : ℝ)).map fun x => c + 1 * x := by simp
  have hm : μ = μ.map fun x => 0 + 1 * x := by simp
  conv_lhs => rw [hc, hm]
  rw [freeConv_map_affine (by simp [Measure.support_dirac]) hμ c 0 1, dirac_zero_freeConv hμ]
  simp

/-- Convolving freely with `Measure.dirac c` on the right translates by `c`. -/
theorem freeConv_dirac {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (c : ℝ) : μ ⊞ Measure.dirac c = μ.map (· + c) := by
  rw [freeConv_comm, dirac_freeConv hμ c]
  congr 1
  ext x
  exact add_comm c x

/-- Free additive convolution of two point masses adds their atoms. -/
@[simp]
theorem dirac_freeConv_dirac (a b : ℝ) :
    Measure.dirac a ⊞ Measure.dirac b = Measure.dirac (a + b) := by
  rw [dirac_freeConv (by simp [Measure.support_dirac]) a, Measure.map_dirac' (by fun_prop)]

/-- Free additive convolution commutes with dilation `x ↦ b * x`. -/
theorem freeConv_map_mul {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (b : ℝ) :
    (μ.map (b * ·)) ⊞ (ν.map (b * ·)) = (μ ⊞ ν).map (b * ·) := by
  simpa using freeConv_map_affine hμ hν 0 0 b

/-- Free additive convolution commutes with reflection `Measure.neg`. -/
theorem neg_freeConv_neg {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ.neg ⊞ ν.neg = (μ ⊞ ν).neg := by
  have hneg (ρ : Measure ℝ) : ρ.neg = ρ.map fun x => 0 + (-1 : ℝ) * x := by
    rw [Measure.neg_def]
    congr 1
    ext x
    ring
  rw [hneg μ, hneg ν, hneg (μ ⊞ ν)]
  simpa using freeConv_map_affine hμ hν 0 0 (-1)

/-- **Interval support bound for free additive convolution.** If `μ.support ⊆ [a₁, b₁]` and
`ν.support ⊆ [a₂, b₂]`, then `(μ ⊞ ν).support ⊆ [a₁ + a₂, b₁ + b₂]`. No probability or
compactness hypotheses are required, as `μ ⊞ ν = 0` outside compactly supported probability
measures. -/
theorem support_freeConv_subset_Icc {μ ν : Measure ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (hμ : μ.support ⊆ Set.Icc a₁ b₁) (hν : ν.support ⊆ Set.Icc a₂ b₂) :
    (μ ⊞ ν).support ⊆ Set.Icc (a₁ + a₂) (b₁ + b₂) := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨hμP, hμK, hνP, hνK⟩ := h
    let ρ := pairMeasure μ ν
    rw [freeConv_eq_law hμK hνK]
    refine (PositiveLinearMap.support_law_subset_spectrum _ _).trans ?_
    let x := TauCeti.FreeLawRealization.cstarElement ρ false
    let y := TauCeti.FreeLawRealization.cstarElement ρ true
    have hx : IsSelfAdjoint x := TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement ρ false
    have hy : IsSelfAdjoint y := TauCeti.FreeLawRealization.isSelfAdjoint_cstarElement ρ true
    have hxspec : spectrum ℝ x ⊆ Set.Icc a₁ b₁ :=
      (TauCeti.FreeLawRealization.spectrum_cstarElement_subset_support
        (μ := ρ) (i := false) hμK).trans hμ
    have hyspec : spectrum ℝ y ⊆ Set.Icc a₂ b₂ :=
      (TauCeti.FreeLawRealization.spectrum_cstarElement_subset_support
        (μ := ρ) (i := true) hνK).trans hν
    have hlo : algebraMap ℝ _ (a₁ + a₂) ≤ x + y := by
      rw [map_add]
      exact add_le_add ((algebraMap_le_iff_le_spectrum hx).2 fun t ht => (hxspec ht).1)
        ((algebraMap_le_iff_le_spectrum hy).2 fun t ht => (hyspec ht).1)
    have hhi : x + y ≤ algebraMap ℝ _ (b₁ + b₂) := by
      rw [map_add]
      exact add_le_add ((le_algebraMap_iff_spectrum_le hx).2 fun t ht => (hxspec ht).2)
        ((le_algebraMap_iff_spectrum_le hy).2 fun t ht => (hyspec ht).2)
    exact fun t ht => ⟨(algebraMap_le_iff_le_spectrum (hx.add hy)).1 hlo t ht,
      (le_algebraMap_iff_spectrum_le (hx.add hy)).1 hhi t ht⟩
  · simp [freeConv, h]

/-- **Extreme-point support bound for free additive convolution.** For all measures `μ, ν` on `ℝ`,
`(μ ⊞ ν).support ⊆ [sInf μ.support + sInf ν.support, sSup μ.support + sSup ν.support]`. -/
theorem support_freeConv_subset_Icc_sInf_sSup (μ ν : Measure ℝ) :
    (μ ⊞ ν).support ⊆
      Set.Icc (sInf μ.support + sInf ν.support) (sSup μ.support + sSup ν.support) := by
  classical
  by_cases h : IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
      IsProbabilityMeasure ν ∧ IsCompact ν.support
  · obtain ⟨_, hμK, _, hνK⟩ := h
    exact support_freeConv_subset_Icc
      (fun x hx => ⟨csInf_le hμK.bddBelow hx, le_csSup hμK.bddAbove hx⟩)
      (fun x hx => ⟨csInf_le hνK.bddBelow hx, le_csSup hνK.bddAbove hx⟩)
  · simp [freeConv, h]

/-- **Closed-ball support bound for free additive convolution.** If `μ.support ⊆ closedBall 0 r₁`
and `ν.support ⊆ closedBall 0 r₂`, then `(μ ⊞ ν).support ⊆ closedBall 0 (r₁ + r₂)`. -/
theorem support_freeConv_subset_closedBall {μ ν : Measure ℝ} {r₁ r₂ : ℝ}
    (hμ : μ.support ⊆ Metric.closedBall 0 r₁) (hν : ν.support ⊆ Metric.closedBall 0 r₂) :
    (μ ⊞ ν).support ⊆ Metric.closedBall 0 (r₁ + r₂) := by
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hμ hν ⊢
  simpa only [neg_add] using support_freeConv_subset_Icc hμ hν

/-- **Free additive stability of semicircle laws.** Convolving two semicircle laws freely adds both
their centres and their variances. -/
@[simp]
theorem semicircleReal_freeConv_semicircleReal (a b : ℝ) (v w : ℝ≥0) :
    TauCeti.Probability.semicircleReal a v ⊞ TauCeti.Probability.semicircleReal b w =
      TauCeti.Probability.semicircleReal (a + b) (v + w) := by
  symm
  rw [eq_freeConv_iff_rSeries_eq (by simp [isCompact_Icc]) (by simp [isCompact_Icc])
      (by simp [isCompact_Icc]),
    rSeries_semicircleReal, rSeries_semicircleReal, rSeries_semicircleReal]
  simp only [map_add, NNReal.coe_add]
  ring

end AffineAndSupport

end MeasureTheory.Measure
