/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Law.AdditiveConvolution
public import TauCeti.Probability.FreeProbability.Law.FreeProduct
public import TauCeti.Probability.FreeProbability.Law.Independence
public import TauCeti.Probability.FreeProbability.Law.Series
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Free additive convolution of compactly supported laws on `ℝ`

Building on `MeasureTheory.Measure.freeConv` in
`TauCeti.Probability.FreeProbability.Law.AdditiveConvolution`, this file equips free additive
convolution with zero/probability characterizations, canonical C⋆- and concrete von Neumann
realizations (`TauCeti.FreeLawRealization`), subalgebra transport, simultaneous
translation and reflection equivariance, and additivity/determinacy of the formal R-series, free
cumulants, mean, and variance.

## Main results

* `MeasureTheory.Measure.isZeroOrProbabilityMeasure_freeConv`,
  `MeasureTheory.Measure.isProbabilityMeasure_freeConv_iff`,
  `MeasureTheory.Measure.freeConv_eq_zero_iff`: totalization and zero/probability iff lemmas.
* `MeasureTheory.Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv`,
  `TauCeti.IsFreelyIndependent.law_add`,
  `TauCeti.FreeLawRealization.law_add_generator`,
  `TauCeti.FreeLawRealization.law_add_vonNeumannGenerator`: binary realization and transport across
  C⋆- and concrete von Neumann probability spaces.
* `MeasureTheory.Measure.freeConv_map_add`,
  `MeasureTheory.Measure.neg_freeConv_neg`: simultaneous translation and reflection laws.
* `MeasureTheory.Measure.rSeries_freeConv`,
  `MeasureTheory.Measure.freeCumulant_freeConv`,
  `MeasureTheory.Measure.eq_freeConv_iff_rSeries_eq`,
  `MeasureTheory.Measure.eq_freeConv_iff_forall_freeCumulant_eq`,
  `MeasureTheory.Measure.integral_id_freeConv`,
  `MeasureTheory.Measure.variance_id_freeConv`: additivity of the formal R-series, free
  cumulants, mean, and variance, and cumulant determinacy of `μ.freeConv ν`.

## References

* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 12 and 16.
-/

public section

noncomputable section

open Finset MeasureTheory PowerSeries ProbabilityTheory
open scoped ComplexOrder ENNReal NNReal

namespace MeasureTheory.Measure

/-- `μ.freeConv ν` is always either `0` or a probability measure (hence a finite measure). -/
instance isZeroOrProbabilityMeasure_freeConv (μ ν : Measure ℝ) :
    IsZeroOrProbabilityMeasure (μ.freeConv ν) := by
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1; have := isProbabilityMeasure_freeConv h.1.2 h.2.2; infer_instance
  · rw [freeConv_of_not (not_and_or.mp h)]; infer_instance

/-- `μ.freeConv ν` is a probability measure iff both `μ` and `ν` are compactly supported probability
measures. -/
@[simp] theorem isProbabilityMeasure_freeConv_iff {μ ν : Measure ℝ} :
    IsProbabilityMeasure (μ.freeConv ν) ↔
      μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure :=
  ⟨fun hp => by
    by_contra h
    exact not_isProbabilityMeasure_zero (freeConv_of_not (not_and_or.mp h) ▸ hp),
    fun ⟨⟨_, hμc⟩, ⟨_, hνc⟩⟩ => isProbabilityMeasure_freeConv hμc hνc⟩

/-- `μ.freeConv ν` equals `0` iff at least one of `μ` or `ν` is not a compactly supported
probability measure. -/
@[simp] theorem freeConv_eq_zero_iff {μ ν : Measure ℝ} :
    μ.freeConv ν = 0 ↔ ¬μ.IsCompactProbabilityMeasure ∨ ¬ν.IsCompactProbabilityMeasure := by
  rw [eq_zero_iff_not_isProbabilityMeasure, isProbabilityMeasure_freeConv_iff, not_and_or]

/-- **Binary C⋆-probability realization of `μ`, `ν`, and `μ.freeConv ν`.** -/
theorem exists_isFreelyIndependentElements_law_add_eq_freeConv {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∃ (A : Type) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (g : Bool → A),
      φ 1 = 1 ∧ TauCeti.IsFreelyIndependentElements φ.toLinearMap g ∧
      IsSelfAdjoint (g true) ∧ IsSelfAdjoint (g false) ∧
      spectrum ℝ (g true) = μ.support ∧ spectrum ℝ (g false) = ν.support ∧
      φ.law (g true) = μ ∧ φ.law (g false) = ν ∧ φ.law (g true + g false) = μ.freeConv ν := by
  obtain ⟨A, _, _, _, φ, a, hφ, ha, hfree, hl0, hl1, hs0, hs1⟩ :=
    exists_isFreelyIndependentElements_law_eq_pair μ ν hμ hν
  have hinj : Function.Injective (fun b : Bool => (cond b 0 1 : Fin 2)) := by
    rintro (_ | _) (_ | _) h <;> simp_all
  refine ⟨A, _, _, _, φ, fun b => a (cond b 0 1), hφ, hfree.comp hinj, ha 0, ha 1,
    hs0, hs1, hl0, hl1, ?_⟩
  simpa [hl0, hl1] using hfree.law_add hφ (by decide : (0 : Fin 2) ≠ 1) (ha 0) (ha 1)

end MeasureTheory.Measure

/-! ### Realization-independence and transport across C⋆- and von Neumann probability spaces -/

namespace TauCeti

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Realization-independence of free additive convolution (subalgebras).** -/
theorem IsFreelyIndependent.law_add {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {x y : A}
    (hxB : x ∈ B i) (hyB : y ∈ B j) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    φ.law (x + y) = (φ.law x).freeConv (φ.law y) :=
  ((hB.comp ((Bool.injective_iff (f := (cond · i j))).mpr
      hij.symm)).isFreelyIndependentElements_of_mem
    (a := (cond · x y)) fun b => by cases b <;> assumption).law_add hφ Bool.false_ne_true.symm
    hx hy

namespace FreeLawRealization

variable (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

/-- In `algebra μ`, the sum of distinct generators `i ≠ j` has law `(μ i).freeConv (μ j)`. -/
theorem law_add_generator {i j : ι} (hij : i ≠ j) :
    (state μ).law (generator μ i + generator μ j) = (μ i).freeConv (μ j) := by
  simpa using (isFreelyIndependentElements_generator μ).law_add (state_one μ) hij
    (isSelfAdjoint_generator μ i) (isSelfAdjoint_generator μ j)

/-- In `vonNeumannAlgebra μ`, the sum of distinct generators `i ≠ j` has law
`(μ i).freeConv (μ j)`. -/
theorem law_add_vonNeumannGenerator {i j : ι} (hij : i ≠ j) :
    (vonNeumannState μ).law (vonNeumannGenerator μ i + vonNeumannGenerator μ j) =
      (μ i).freeConv (μ j) := by
  simpa using (isFreelyIndependentElements_vonNeumannGenerator μ).law_add (vonNeumannState_one μ)
    hij (isSelfAdjoint_vonNeumannGenerator μ i) (isSelfAdjoint_vonNeumannGenerator μ j)

end FreeLawRealization

end TauCeti

/-! ### Algebraic typeclasses, translations, and reflection -/

namespace MeasureTheory.Measure

instance : Std.Commutative (α := Measure ℝ) freeConv := ⟨freeConv_comm⟩

instance : Std.Associative (α := Measure ℝ) freeConv := ⟨freeConv_assoc⟩

/-- Translating `μ` by `a` and `ν` by `b` translates `μ.freeConv ν` by `a + b`, unconditionally. -/
theorem freeConv_map_add (μ ν : Measure ℝ) (a b : ℝ) :
    (μ.map (a + ·)).freeConv (ν.map (b + ·)) = (μ.freeConv ν).map (a + b + ·) := by
  simpa using freeConv_map_affine_of_ne_zero μ ν a b one_ne_zero

/-- Free additive convolution commutes with `Measure.neg` for all measures on `ℝ`. -/
theorem neg_freeConv_neg (μ ν : Measure ℝ) : μ.neg.freeConv ν.neg = (μ.freeConv ν).neg := by
  simpa [Measure.neg_def] using freeConv_map_affine_of_ne_zero μ ν 0 0 (by norm_num : (-1 : ℝ) ≠ 0)

/-! ### Formal R-series, free cumulants, mean, and variance -/

/-- **Additivity of the formal R-series under free additive convolution.** -/
theorem rSeries_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    (μ.freeConv ν).rSeries = μ.rSeries + ν.rSeries := by
  obtain ⟨A, _, _, _, φ, g, hφ1, hfree, hgt, hgf, -, -, hlt, hlf, hladd⟩ :=
    exists_isFreelyIndependentElements_law_add_eq_freeConv hμ hν
  have h1 := φ.map_ofReal_rSeries_law hgt
  have h2 := φ.map_ofReal_rSeries_law hgf
  rw [hlt] at h1
  rw [hlf] at h2
  apply PowerSeries.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
  rw [map_add, ← hladd, φ.map_ofReal_rSeries_law (hgt.add hgf)]
  exact (hfree.rSeries_add hφ1 Bool.false_ne_true.symm).trans
    (by simpa using congrArg₂ (· + ·) h1.symm h2.symm)

/-- **Additivity of free cumulants under free additive convolution.** -/
theorem freeCumulant_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    {n : ℕ} (hn : n ≠ 0) :
    (μ.freeConv ν).freeCumulant n = μ.freeCumulant n + ν.freeCumulant n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp_rw [freeCumulant_succ_eq_coeff_rSeries, rSeries_freeConv hμ hν, map_add]

/-- A compactly supported probability measure `ρ` equals `μ.freeConv ν` iff its formal R-series
equals the sum of those of `μ` and `ν`. -/
theorem eq_freeConv_iff_rSeries_eq {ρ μ ν : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ.freeConv ν ↔ ρ.rSeries = μ.rSeries + ν.rSeries := by
  have := isProbabilityMeasure_freeConv hμ hν
  rw [eq_iff_rSeries_eq hρ (isCompact_support_freeConv μ ν), rSeries_freeConv hμ hν]

/-- A compactly supported probability measure `ρ` equals `μ.freeConv ν` iff all positive-order free
cumulants of `ρ` equal the sums of those of `μ` and `ν`. -/
theorem eq_freeConv_iff_forall_freeCumulant_eq {ρ μ ν : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ.freeConv ν ↔ ∀ n : ℕ, n ≠ 0 →
      ρ.freeCumulant n = μ.freeCumulant n + ν.freeCumulant n := by
  have := isProbabilityMeasure_freeConv hμ hν
  rw [eq_iff_forall_freeCumulant_eq hρ (isCompact_support_freeConv μ ν)]
  exact forall₂_congr fun n hn => by rw [freeCumulant_freeConv hμ hν hn]

/-- The mean is additive under free additive convolution. -/
theorem integral_id_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∫ x, x ∂(μ.freeConv ν) = (∫ x, x ∂μ) + ∫ x, x ∂ν := by
  simpa [coeff_zero_rSeries] using congrArg (PowerSeries.coeff 0) (rSeries_freeConv hμ hν)

/-- The variance is additive under free additive convolution. -/
theorem variance_id_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    variance id (μ.freeConv ν) = variance id μ + variance id ν := by
  have := isProbabilityMeasure_freeConv hμ hν
  simpa [coeff_one_rSeries_eq_variance (isCompact_support_freeConv μ ν),
    coeff_one_rSeries_eq_variance hμ, coeff_one_rSeries_eq_variance hν] using
    congrArg (PowerSeries.coeff 1) (rSeries_freeConv hμ hν)

end MeasureTheory.Measure
