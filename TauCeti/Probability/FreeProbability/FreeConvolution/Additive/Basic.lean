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
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Free additive convolution of compactly supported laws on `ℝ`

Building on `MeasureTheory.Measure.freeConv` in
`TauCeti.Probability.FreeProbability.Law.AdditiveConvolution`, this file equips free additive
convolution with zero/probability characterizations, canonical C⋆- and concrete von Neumann
realizations (`TauCeti.FreeLawRealization`), subalgebra and three-term transport, simultaneous
affine and reflection equivariance, and additivity/determinacy of the formal R-series, free
cumulants, mean, and variance.

## Main results

* `MeasureTheory.Measure.isZeroOrProbabilityMeasure_freeConv`,
  `MeasureTheory.Measure.isProbabilityMeasure_freeConv_iff`,
  `MeasureTheory.Measure.freeConv_eq_zero_iff`: totalization and zero/probability iff lemmas.
* `MeasureTheory.Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv`,
  `TauCeti.IsFreelyIndependent.law_add`, `TauCeti.IsFreelyIndependentElements.law_add_add`,
  `TauCeti.FreeLawRealization.law_add_generator`,
  `TauCeti.FreeLawRealization.law_add_vonNeumannGenerator`: binary realization and transport across
  C⋆- and concrete von Neumann probability spaces.
* `MeasureTheory.Measure.freeConv_map_affine`, `MeasureTheory.Measure.freeConv_map_add`,
  `MeasureTheory.Measure.neg_freeConv_neg`: simultaneous affine, translation, and reflection laws.
* `MeasureTheory.Measure.rSeries_integral_freeConv`,
  `MeasureTheory.Measure.freeCumulant_freeConv`,
  `MeasureTheory.Measure.eq_freeConv_iff_rSeries_integral_eq`,
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
  let τ : Fin 2 → Measure ℝ := ![μ, ν]
  have : ∀ i, IsProbabilityMeasure (τ i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  have : ∀ i, CompactSpace (τ i).support :=
    Fin.forall_fin_two.2 ⟨isCompact_iff_compactSpace.mp hμ, isCompact_iff_compactSpace.mp hν⟩
  have hinj : Function.Injective (fun b : Bool => (cond b 0 1 : Fin 2)) := by
    rintro (_ | _) (_ | _) h <;> simp_all
  refine ⟨TauCeti.FreeLawRealization.algebra τ, inferInstance, inferInstance, inferInstance,
    TauCeti.FreeLawRealization.state τ,
    fun b => TauCeti.FreeLawRealization.generator τ (cond b 0 1),
    TauCeti.FreeLawRealization.state_one τ,
    (TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ).comp hinj,
    TauCeti.FreeLawRealization.isSelfAdjoint_generator τ 0,
    TauCeti.FreeLawRealization.isSelfAdjoint_generator τ 1,
    TauCeti.FreeLawRealization.spectrum_generator τ 0,
    TauCeti.FreeLawRealization.spectrum_generator τ 1,
    TauCeti.FreeLawRealization.law_generator τ 0,
    TauCeti.FreeLawRealization.law_generator τ 1, ?_⟩
  simp only [Bool.cond_true, Bool.cond_false]
  rw [(TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ).law_add
    (TauCeti.FreeLawRealization.state_one τ) (by decide : (0 : Fin 2) ≠ 1)
    (TauCeti.FreeLawRealization.isSelfAdjoint_generator τ 0)
    (TauCeti.FreeLawRealization.isSelfAdjoint_generator τ 1),
    TauCeti.FreeLawRealization.law_generator τ 0,
    TauCeti.FreeLawRealization.law_generator τ 1]
  rfl

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

/-- For pairwise distinct freely independent selfadjoint elements `a i`, `a j`, `a k`, the law of
`a i + a j + a k` is `((φ.law (a i)).freeConv (φ.law (a j))).freeConv (φ.law (a k))`. -/
theorem IsFreelyIndependentElements.law_add_add {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hai : IsSelfAdjoint (a i)) (haj : IsSelfAdjoint (a j)) (hak : IsSelfAdjoint (a k)) :
    φ.law (a i + a j + a k) = ((φ.law (a i)).freeConv (φ.law (a j))).freeConv (φ.law (a k)) := by
  classical
  let f : ι → Bool := fun t => decide (t = k)
  rw [(ha.adjoin_image_fiber hφ f).law_add hφ Bool.false_ne_true
    (add_mem (Algebra.subset_adjoin ⟨i, by simp [f, hik], rfl⟩)
      (Algebra.subset_adjoin ⟨j, by simp [f, hjk], rfl⟩))
    (Algebra.subset_adjoin ⟨k, by simp [f], rfl⟩) (hai.add haj) hak, ha.law_add hφ hij hai haj]

private theorem IsFreelyIndependentElements.law_smul_add_algebraMap_add {φ : A →ₚ[ℂ] ℂ}
    {a : ι → A} (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1)
    {i j : ι} (hij : i ≠ j) (hai : IsSelfAdjoint (a i)) (haj : IsSelfAdjoint (a j))
    (r₁ c₁ r₂ c₂ : ℝ) :
    φ.law ((r₁ • a i + algebraMap ℝ A c₁) + (r₂ • a j + algebraMap ℝ A c₂)) =
      ((φ.law (a i)).map fun x => r₁ * x + c₁).freeConv
        ((φ.law (a j)).map fun x => r₂ * x + c₂) := by
  have hadd := (isFreelyIndependentElements_iff.mp ha).law_add hφ hij
    (add_mem (((Algebra.adjoin ℂ {a i}).restrictScalars ℝ).smul_mem
        (Algebra.self_mem_adjoin_singleton ℂ (a i)) r₁)
      (((Algebra.adjoin ℂ {a i}).restrictScalars ℝ).algebraMap_mem c₁))
    (add_mem (((Algebra.adjoin ℂ {a j}).restrictScalars ℝ).smul_mem
        (Algebra.self_mem_adjoin_singleton ℂ (a j)) r₂)
      (((Algebra.adjoin ℂ {a j}).restrictScalars ℝ).algebraMap_mem c₂))
    (((IsSelfAdjoint.all r₁).smul hai).add (IsSelfAdjoint.algebraMap A (.all c₁)))
    (((IsSelfAdjoint.all r₂).smul haj).add (IsSelfAdjoint.algebraMap A (.all c₂)))
  rwa [φ.law_smul_add_algebraMap hai r₁ c₁, φ.law_smul_add_algebraMap haj r₂ c₂] at hadd

namespace FreeLawRealization

variable [DecidableEq ι] (μ : ι → Measure ℝ)
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

/-! ### Algebraic typeclasses, affine pushforwards, and reflection -/

namespace MeasureTheory.Measure

instance : Std.Commutative (α := Measure ℝ) freeConv := ⟨freeConv_comm⟩

instance : Std.Associative (α := Measure ℝ) freeConv := ⟨freeConv_assoc⟩

/-- **Affine equivariance of free additive convolution** (valid for all real slopes `b`, including
`b = 0` and `b < 0`). -/
theorem freeConv_map_affine {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (a c b : ℝ) :
    (μ.map fun x => a + b * x).freeConv (ν.map fun x => c + b * x) =
      (μ.freeConv ν).map fun x => a + c + b * x := by
  obtain ⟨A, _, _, _, φ, g, hφ, hfree, hg1, hg2, _, _, hlaw1, hlaw2, hadd⟩ :=
    exists_isFreelyIndependentElements_law_add_eq_freeConv hμ hν
  have halg : (b • g true + algebraMap ℝ _ a) + (b • g false + algebraMap ℝ _ c) =
      b • (g true + g false) + algebraMap ℝ _ (a + c) := by
    simp only [smul_add, map_add]; abel
  have hL := hfree.law_smul_add_algebraMap_add hφ Bool.false_ne_true.symm hg1 hg2 b a b c
  have hR := φ.law_smul_add_algebraMap (hg1.add hg2) b (a + c)
  rw [halg, hR, hadd, hlaw1, hlaw2] at hL
  simpa [add_comm (b * _)] using hL.symm

/-- Translating `μ` by `a` and `ν` by `b` translates `μ.freeConv ν` by `a + b`, unconditionally. -/
theorem freeConv_map_add (μ ν : Measure ℝ) (a b : ℝ) :
    (μ.map (a + ·)).freeConv (ν.map (b + ·)) = (μ.freeConv ν).map (a + b + ·) := by
  have hcp (σ : Measure ℝ) (c : ℝ) :
      (σ.map (c + ·)).IsCompactProbabilityMeasure → σ.IsCompactProbabilityMeasure :=
    (σ.isCompactProbabilityMeasure_map_homeomorph_iff (Homeomorph.addLeft c)).mp
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1; simpa using freeConv_map_affine h.1.2 h.2.2 a b 1
  · rw [freeConv_of_not ((not_and_or.mp h).imp (mt (hcp μ a)) (mt (hcp ν b))),
      freeConv_of_not (not_and_or.mp h), Measure.map_zero]

/-- Free additive convolution commutes with `Measure.neg` for all measures on `ℝ`. -/
theorem neg_freeConv_neg (μ ν : Measure ℝ) : μ.neg.freeConv ν.neg = (μ.freeConv ν).neg := by
  have hcp (σ : Measure ℝ) :
      σ.neg.IsCompactProbabilityMeasure → σ.IsCompactProbabilityMeasure := by
    rw [Measure.neg_def, ← Homeomorph.coe_neg,
      σ.isCompactProbabilityMeasure_map_homeomorph_iff (Homeomorph.neg ℝ)]
    exact id
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1
    simpa [Measure.neg_def] using freeConv_map_affine h.1.2 h.2.2 0 0 (-1)
  · rw [freeConv_of_not ((not_and_or.mp h).imp (mt (hcp μ)) (mt (hcp ν))),
      freeConv_of_not (not_and_or.mp h)]
    simp [Measure.neg_def]

/-! ### Formal R-series, free cumulants, mean, and variance -/

/-- **Additivity of the formal R-series under free additive convolution.** -/
theorem rSeries_integral_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConv ν)) id =
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id +
        TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
  obtain ⟨A, _, _, _, φ, g, hφ, hfree, hg1, hg2, _, _, hlaw1, hlaw2, hadd⟩ :=
    exists_isFreelyIndependentElements_law_add_eq_freeConv hμ hν
  have h1 := φ.map_ofReal_rSeries_integral_law hg1
  have h2 := φ.map_ofReal_rSeries_integral_law hg2
  rw [hlaw1] at h1
  rw [hlaw2] at h2
  apply PowerSeries.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
  rw [map_add, ← hadd, φ.map_ofReal_rSeries_integral_law (hg1.add hg2), h1, h2]
  exact hfree.rSeries_add hφ Bool.false_ne_true.symm

/-- **Additivity of free cumulants under free additive convolution.** -/
theorem freeCumulant_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    {n : ℕ} (hn : n ≠ 0) :
    (μ.freeConv ν).freeCumulant n = μ.freeCumulant n + ν.freeCumulant n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp_rw [freeCumulant_succ_eq_coeff_rSeries, rSeries_integral_freeConv hμ hν, map_add]

/-- A compactly supported probability measure `ρ` equals `μ.freeConv ν` iff its formal R-series
equals the sum of those of `μ` and `ν`. -/
theorem eq_freeConv_iff_rSeries_integral_eq {ρ μ ν : Measure ℝ} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ.freeConv ν ↔ TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id =
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id +
        TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
  have := isProbabilityMeasure_freeConv hμ hν
  rw [eq_iff_rSeries_integral_eq hρ (isCompact_support_freeConv μ ν),
    rSeries_integral_freeConv hμ hν]

/-- A compactly supported probability measure `ρ` equals `μ.freeConv ν` iff all positive-order free
cumulants of `ρ` equal the sums of those of `μ` and `ν`. -/
theorem eq_freeConv_iff_forall_freeCumulant_eq {ρ μ ν : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
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
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, TauCeti.constantCoeff_rSeries] using
    congrArg (PowerSeries.coeff 0) (rSeries_integral_freeConv hμ hν)

/-- The variance is additive under free additive convolution. -/
theorem variance_id_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    variance id (μ.freeConv ν) = variance id μ + variance id ν := by
  have := isProbabilityMeasure_freeConv hμ hν
  simpa [coeff_one_rSeries_integral_eq_variance
      (continuousOn_id.memLp_of_isCompact_support (isCompact_support_freeConv μ ν) support_mem_ae),
    coeff_one_rSeries_integral_eq_variance
      (continuousOn_id.memLp_of_isCompact_support hμ support_mem_ae),
    coeff_one_rSeries_integral_eq_variance
      (continuousOn_id.memLp_of_isCompact_support hν support_mem_ae)] using
    congrArg (PowerSeries.coeff 1) (rSeries_integral_freeConv hμ hν)

end MeasureTheory.Measure
