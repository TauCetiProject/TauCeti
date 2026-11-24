/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

For compactly supported Borel probability measures `μ` and `ν` on `ℝ`, Voiculescu's *free additive
convolution* `μ ⊞ ν` (`MeasureTheory.Measure.freeConv`) is the scalar law of `a + b` in the
canonical reduced C⋆-free product realization `TauCeti.FreeLawRealization` of `(μ, ν)`, extended by
`0` outside compactly supported probability measures. By uniqueness of joint distributions of freely
independent selfadjoint families, `φ.law (a + b) = (φ.law a).freeConv (φ.law b)` holds in every
unital C⋆- and concrete von Neumann probability space.

## Main definitions

* `MeasureTheory.Measure.freeConv`: free additive convolution on `ℝ` (`μ ⊞ ν` under
  `open scoped TauCeti.FreeProbability`), defaulting to `0` outside compactly supported probability
  laws.

## Main results

* `MeasureTheory.Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv`,
  `TauCeti.IsFreelyIndependentElements.law_add`, `TauCeti.IsFreelyIndependentElements.law_add_add`,
  `TauCeti.IsFreelyIndependent.law_add`: binary realization and realization-independence across
  C⋆- and von Neumann probability spaces.
* `MeasureTheory.Measure.freeConv_comm`, `MeasureTheory.Measure.freeConv_assoc`,
  `MeasureTheory.Measure.dirac_zero_freeConv`, `MeasureTheory.Measure.freeConv_map_affine`,
  `MeasureTheory.Measure.support_freeConv_subset_Icc`: algebraic, affine, and support laws.
* `MeasureTheory.Measure.rSeries_integral_freeConv`,
  `MeasureTheory.Measure.freeCumulant_integral_freeConv`,
  `MeasureTheory.Measure.eq_freeConv_iff_rSeries_integral_eq`: additivity of the formal R-series,
  free cumulants, mean, and variance, and cumulant determinacy of `μ ⊞ ν`.

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

open scoped Classical in
/-- **Free additive convolution** of compactly supported Borel probability measures on `ℝ`: the law
of `a + b` in the canonical reduced C⋆-free product realization of `(μ, ν)`, and `0` otherwise. -/
def freeConv (μ ν : Measure ℝ) : Measure ℝ :=
  if h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure then
    have := h.1.1; have := h.2.1
    have := isCompact_iff_compactSpace.mp h.1.2
    have := isCompact_iff_compactSpace.mp h.2.2
    (TauCeti.FreeLawRealization.state (cond · μ ν)).law
      (TauCeti.FreeLawRealization.generator (cond · μ ν) true +
        TauCeti.FreeLawRealization.generator (cond · μ ν) false)
  else 0

/-- Scoped notation `μ ⊞ ν` for the free additive convolution of measures on `ℝ`. -/
scoped[TauCeti.FreeProbability] infixr:80 " ⊞ " => MeasureTheory.Measure.freeConv

private theorem freeConv_def_of_isCompactProbabilityMeasure {μ ν : Measure ℝ}
    [hμp : IsProbabilityMeasure μ] [hνp : IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    have := isCompact_iff_compactSpace.mp hμ
    have := isCompact_iff_compactSpace.mp hν
    μ.freeConv ν = (TauCeti.FreeLawRealization.state (cond · μ ν)).law
      (TauCeti.FreeLawRealization.generator (cond · μ ν) true +
        TauCeti.FreeLawRealization.generator (cond · μ ν) false) := by
  simp [freeConv, IsCompactProbabilityMeasure, hμp, hνp, hμ, hν]

/-- Outside compactly supported probability measures, `freeConv` returns `0`. -/
theorem freeConv_undef {μ ν : Measure ℝ}
    (h : ¬(μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure)) :
    μ.freeConv ν = 0 := by
  simp [freeConv, h]

/-- Convolving the zero measure on the left gives `0`. -/
@[simp] theorem zero_freeConv (μ : Measure ℝ) : (0 : Measure ℝ).freeConv μ = 0 :=
  freeConv_undef fun h => not_isProbabilityMeasure_zero h.1.1

/-- Convolving the zero measure on the right gives `0`. -/
@[simp] theorem freeConv_zero (μ : Measure ℝ) : μ.freeConv (0 : Measure ℝ) = 0 :=
  freeConv_undef fun h => not_isProbabilityMeasure_zero h.2.1

/-- The free convolution of compactly supported probability laws is a probability measure. -/
theorem isProbabilityMeasure_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    IsProbabilityMeasure (μ.freeConv ν) := by
  have := isCompact_iff_compactSpace.mp hμ
  have := isCompact_iff_compactSpace.mp hν
  rw [freeConv_def_of_isCompactProbabilityMeasure hμ hν]
  exact PositiveLinearMap.isProbabilityMeasure_law _ (TauCeti.FreeLawRealization.state_one _)
    ((TauCeti.FreeLawRealization.isSelfAdjoint_generator _ true).add
      (TauCeti.FreeLawRealization.isSelfAdjoint_generator _ false))

/-- `μ.freeConv ν` is always either `0` or a probability measure (hence a finite measure). -/
instance isZeroOrProbabilityMeasure_freeConv (μ ν : Measure ℝ) :
    IsZeroOrProbabilityMeasure (μ.freeConv ν) := by
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1; have := isProbabilityMeasure_freeConv h.1.2 h.2.2; infer_instance
  · rw [freeConv_undef h]; infer_instance

/-- The free additive convolution of any two measures has compact topological support. -/
theorem isCompact_support_freeConv (μ ν : Measure ℝ) : IsCompact (μ.freeConv ν).support := by
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1
    rw [freeConv_def_of_isCompactProbabilityMeasure h.1.2 h.2.2]
    exact PositiveLinearMap.isCompact_support_law _ _
  · simp [freeConv_undef h]

/-- `μ.freeConv ν` is a probability measure iff both `μ` and `ν` are compactly supported probability
measures. -/
@[simp] theorem isProbabilityMeasure_freeConv_iff {μ ν : Measure ℝ} :
    IsProbabilityMeasure (μ.freeConv ν) ↔
      μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure :=
  ⟨fun hp => by by_contra h; exact not_isProbabilityMeasure_zero (freeConv_undef h ▸ hp),
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
  have := isCompact_iff_compactSpace.mp hμ
  have := isCompact_iff_compactSpace.mp hν
  let τ : Bool → Measure ℝ := (cond · μ ν)
  exact ⟨TauCeti.FreeLawRealization.algebra τ, inferInstance, inferInstance, inferInstance,
    TauCeti.FreeLawRealization.state τ, TauCeti.FreeLawRealization.generator τ,
    TauCeti.FreeLawRealization.state_one τ,
    TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ,
    TauCeti.FreeLawRealization.isSelfAdjoint_generator τ true,
    TauCeti.FreeLawRealization.isSelfAdjoint_generator τ false,
    TauCeti.FreeLawRealization.spectrum_generator τ true,
    TauCeti.FreeLawRealization.spectrum_generator τ false,
    TauCeti.FreeLawRealization.law_generator τ true,
    TauCeti.FreeLawRealization.law_generator τ false,
    (freeConv_def_of_isCompactProbabilityMeasure hμ hν).symm⟩

end MeasureTheory.Measure

/-! ### Realization-independence and transport across C⋆- and von Neumann probability spaces -/

namespace TauCeti

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Realization-independence of free additive convolution (elements).** -/
theorem IsFreelyIndependentElements.law_add {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hai : IsSelfAdjoint (a i)) (haj : IsSelfAdjoint (a j)) :
    φ.law (a i + a j) = (φ.law (a i)).freeConv (φ.law (a j)) := by
  have := φ.isProbabilityMeasure_law hφ hai; have := φ.isProbabilityMeasure_law hφ haj
  have := isCompact_iff_compactSpace.mp (φ.isCompact_support_law (a i))
  have := isCompact_iff_compactSpace.mp (φ.isCompact_support_law (a j))
  let τ : Bool → Measure ℝ := (cond · (φ.law (a i)) (φ.law (a j)))
  have : ∀ b : Bool, IsProbabilityMeasure (τ b) := fun b => by cases b <;> infer_instance
  have : ∀ b : Bool, CompactSpace (τ b).support := fun b => by
    cases b <;> exact isCompact_iff_compactSpace.mp (φ.isCompact_support_law _)
  exact (ha.law_add_eq_of_law_eq (FreeLawRealization.isFreelyIndependentElements_generator τ) hφ
    (FreeLawRealization.state_one τ) hij Bool.false_ne_true.symm hai haj
    (FreeLawRealization.isSelfAdjoint_generator τ true)
    (FreeLawRealization.isSelfAdjoint_generator τ false)
    (FreeLawRealization.law_generator τ true).symm
    (FreeLawRealization.law_generator τ false).symm).trans
    (Measure.freeConv_def_of_isCompactProbabilityMeasure
      (φ.isCompact_support_law (a i)) (φ.isCompact_support_law (a j))).symm

/-- **Realization-independence of free additive convolution (subalgebras).** -/
theorem IsFreelyIndependent.law_add {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {x y : A}
    (hxB : x ∈ B i) (hyB : y ∈ B j) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    φ.law (x + y) = (φ.law x).freeConv (φ.law y) :=
  ((hB.comp ((Bool.injective_iff (f := (cond · i j))).mpr hij.symm)).isFreelyIndependentElements
    (a := (cond · x y)) fun b => by cases b <;> assumption).law_add hφ Bool.false_ne_true.symm hx hy

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

/-! ### Algebraic laws, Dirac identity, affine pushforwards, and support bounds -/

namespace MeasureTheory.Measure

/-- Free additive convolution is commutative, unconditionally for all measures on `ℝ`. -/
theorem freeConv_comm (μ ν : Measure ℝ) : μ.freeConv ν = ν.freeConv μ := by
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1
    let τ : Bool → Measure ℝ := (cond · μ ν)
    have : ∀ b : Bool, IsProbabilityMeasure (τ b) := fun b => by cases b <;> infer_instance
    have : ∀ b : Bool, CompactSpace (τ b).support := fun b => by
      cases b <;> exact isCompact_iff_compactSpace.mp (by first | exact h.1.2 | exact h.2.2)
    simpa [τ] using
      (TauCeti.FreeLawRealization.law_add_generator τ Bool.false_ne_true.symm).symm.trans
        ((congrArg (TauCeti.FreeLawRealization.state τ).law (add_comm _ _)).trans
          (TauCeti.FreeLawRealization.law_add_generator τ Bool.false_ne_true))
  · rw [freeConv_undef h, freeConv_undef fun ⟨hν, hμ⟩ => h ⟨hμ, hν⟩]

instance : Std.Commutative (α := Measure ℝ) freeConv := ⟨freeConv_comm⟩

/-- Free additive convolution is associative, unconditionally for all measures on `ℝ`. -/
theorem freeConv_assoc (μ ν ρ : Measure ℝ) :
    (μ.freeConv ν).freeConv ρ = μ.freeConv (ν.freeConv ρ) := by
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure ∧
      ρ.IsCompactProbabilityMeasure
  · rcases h with ⟨⟨hμp, hμc⟩, ⟨hνp, hνc⟩, ⟨hρp, hρc⟩⟩
    let τ : Fin 3 → Measure ℝ := ![μ, ν, ρ]
    have : ∀ i : Fin 3, IsProbabilityMeasure (τ i) := fun i => by fin_cases i <;> assumption
    have : ∀ i : Fin 3, CompactSpace (τ i).support := fun i => by
      fin_cases i <;> exact isCompact_iff_compactSpace.mp ‹_›
    have hfree := TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ
    have h1 := TauCeti.FreeLawRealization.state_one τ
    have hsa := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ
    let g := TauCeti.FreeLawRealization.generator τ
    have hL : (TauCeti.FreeLawRealization.state τ).law (g 0 + g 1 + g 2) =
        (μ.freeConv ν).freeConv ρ := by
      simpa [g, τ, Matrix.cons_val_two] using hfree.law_add_add h1
        (by decide : (0 : Fin 3) ≠ 1) (by decide) (by decide) (hsa 0) (hsa 1) (hsa 2)
    have hR : (TauCeti.FreeLawRealization.state τ).law (g 1 + g 2 + g 0) =
        (ν.freeConv ρ).freeConv μ := by
      simpa [g, τ, Matrix.cons_val_two] using hfree.law_add_add h1
        (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide) (hsa 1) (hsa 2) (hsa 0)
    rw [← hL, freeConv_comm μ (ν.freeConv ρ), ← hR, add_assoc, add_comm (g 0)]
  · rw [freeConv_undef fun ⟨⟨hp, _⟩, hρ⟩ =>
        h ⟨(isProbabilityMeasure_freeConv_iff.mp hp).1,
          (isProbabilityMeasure_freeConv_iff.mp hp).2, hρ⟩,
      freeConv_undef fun ⟨hμ, ⟨hp, _⟩⟩ =>
        h ⟨hμ, (isProbabilityMeasure_freeConv_iff.mp hp).1,
          (isProbabilityMeasure_freeConv_iff.mp hp).2⟩]

instance : Std.Associative (α := Measure ℝ) freeConv := ⟨freeConv_assoc⟩

/-- **Affine equivariance of free additive convolution** (valid for all real slopes `b`, including
`b = 0` and `b < 0`). -/
theorem freeConv_map_affine {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (a c b : ℝ) :
    (μ.map fun x => a + b * x).freeConv (ν.map fun x => c + b * x) =
      (μ.freeConv ν).map fun x => a + c + b * x := by
  let τ : Bool → Measure ℝ := (cond · μ ν)
  have : ∀ i : Bool, IsProbabilityMeasure (τ i) := fun i => by cases i <;> infer_instance
  have : ∀ i : Bool, CompactSpace (τ i).support := fun i => by
    cases i <;> exact isCompact_iff_compactSpace.mp ‹_›
  let φ := TauCeti.FreeLawRealization.state τ
  have hg1 := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ true
  have hg2 := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ false
  have hfun (d : ℝ) : (fun x : ℝ => b * x + d) = fun x => d + b * x := funext fun _ => add_comm _ _
  have hadd :=
    (TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ).law_smul_add_algebraMap_add
      (TauCeti.FreeLawRealization.state_one τ) Bool.false_ne_true.symm hg1 hg2 b a b c
  simp only [TauCeti.FreeLawRealization.law_generator, τ, Bool.cond_true, Bool.cond_false,
    hfun] at hadd
  have hsum : φ.law (TauCeti.FreeLawRealization.generator τ true +
      TauCeti.FreeLawRealization.generator τ false) = μ.freeConv ν :=
    TauCeti.FreeLawRealization.law_add_generator τ Bool.false_ne_true.symm
  rw [← hadd, add_add_add_comm, ← smul_add, ← map_add,
    φ.law_smul_add_algebraMap (hg1.add hg2) b (a + c), hfun (a + c), hsum]

/-- Translating `μ` by `a` and `ν` by `b` translates `μ.freeConv ν` by `a + b`, unconditionally. -/
theorem freeConv_map_add (μ ν : Measure ℝ) (a b : ℝ) :
    (μ.map (a + ·)).freeConv (ν.map (b + ·)) = (μ.freeConv ν).map (a + b + ·) := by
  have hcp (σ : Measure ℝ) (c : ℝ) :
      (σ.map (c + ·)).IsCompactProbabilityMeasure → σ.IsCompactProbabilityMeasure :=
    (σ.isCompactProbabilityMeasure_map_homeomorph_iff (Homeomorph.addLeft c)).mp
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1; simpa using freeConv_map_affine h.1.2 h.2.2 a b 1
  · rw [freeConv_undef fun ⟨h1, h2⟩ => h ⟨hcp μ a h1, hcp ν b h2⟩,
      freeConv_undef h, Measure.map_zero]

/-- Scaling compactly supported probability measures by `b` scales `μ.freeConv ν` by `b`. -/
theorem freeConv_map_mul {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (b : ℝ) :
    (μ.map (b * ·)).freeConv (ν.map (b * ·)) = (μ.freeConv ν).map (b * ·) := by
  simpa using freeConv_map_affine hμ hν 0 0 b

/-- Free additive convolution commutes with `Measure.neg` for all measures on `ℝ`. -/
theorem neg_freeConv_neg (μ ν : Measure ℝ) : μ.neg.freeConv ν.neg = (μ.freeConv ν).neg := by
  have hcp (σ : Measure ℝ) :
      σ.neg.IsCompactProbabilityMeasure → σ.IsCompactProbabilityMeasure := by
    rw [Measure.neg_def, ← Homeomorph.coe_neg,
      σ.isCompactProbabilityMeasure_map_homeomorph_iff (Homeomorph.neg ℝ)]
    exact id
  by_cases h : μ.IsCompactProbabilityMeasure ∧ ν.IsCompactProbabilityMeasure
  · have := h.1.1; have := h.2.1; simpa [Measure.neg_def] using freeConv_map_mul h.1.2 h.2.2 (-1)
  · rw [freeConv_undef fun ⟨h1, h2⟩ => h ⟨hcp μ h1, hcp ν h2⟩,
      freeConv_undef h]; simp [Measure.neg_def]

/-- Convolving on the left with `Measure.dirac a` translates `μ` by `a`. -/
@[simp] theorem dirac_freeConv (a : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : (Measure.dirac a).freeConv μ = μ.map (a + ·) := by
  have := isCompact_iff_compactSpace.mp hμ
  let τ : Bool → Measure ℝ := fun _ => μ
  let φ := TauCeti.FreeLawRealization.state τ
  have hg1 := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ true
  have hg2 := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ false
  have hadd :=
    (TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ).law_smul_add_algebraMap_add
      (TauCeti.FreeLawRealization.state_one τ) Bool.false_ne_true.symm hg1 hg2 0 a 1 0
  simp only [TauCeti.FreeLawRealization.law_generator, τ, zero_mul, zero_add,
    Measure.map_const, measure_univ, one_smul, one_mul, add_zero, Measure.map_id'] at hadd
  rw [← hadd, zero_smul, zero_add, map_zero, add_zero, add_comm,
    ← one_smul ℝ (TauCeti.FreeLawRealization.generator τ false),
    φ.law_smul_add_algebraMap hg2 1 a, TauCeti.FreeLawRealization.law_generator]
  simp [τ, add_comm]

/-- Convolving on the right with `Measure.dirac a` translates `μ` by `a`. -/
@[simp] theorem freeConv_dirac {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (a : ℝ) : μ.freeConv (Measure.dirac a) = μ.map (· + a) := by
  simpa [add_comm] using (freeConv_comm μ (Measure.dirac a)).trans (dirac_freeConv a hμ)

/-- `Measure.dirac 0` is the left identity for `freeConv` on compactly supported laws. -/
theorem dirac_zero_freeConv {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) : (Measure.dirac 0).freeConv μ = μ := by simp [dirac_freeConv 0 hμ]

/-- `Measure.dirac 0` is the right identity for `freeConv` on compactly supported laws. -/
theorem freeConv_dirac_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) :
    μ.freeConv (Measure.dirac 0) = μ := (freeConv_comm _ _).trans (dirac_zero_freeConv hμ)

/-- Free additive convolution of two Dirac masses is the Dirac mass at the sum of their atoms. -/
@[simp] theorem dirac_freeConv_dirac (a b : ℝ) :
    (Measure.dirac a).freeConv (Measure.dirac b) = Measure.dirac (a + b) := by
  have hb : IsCompact (Measure.dirac b).support := by simp [Measure.support_dirac]
  rw [dirac_freeConv a hb, Measure.map_dirac' (measurable_const_add a)]

/-- **Support interval bound for free additive convolution** (unconditionally for all measures on
`ℝ`: when either measure is not a probability measure, `μ.freeConv ν = 0` has empty support). -/
theorem support_freeConv_subset_Icc {μ ν : Measure ℝ} {m₁ M₁ m₂ M₂ : ℝ}
    (hμI : μ.support ⊆ Set.Icc m₁ M₁) (hνI : ν.support ⊆ Set.Icc m₂ M₂) :
    (μ.freeConv ν).support ⊆ Set.Icc (m₁ + m₂) (M₁ + M₂) := by
  by_cases hp : IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν
  · obtain ⟨_, _⟩ := hp
    let τ : Bool → Measure ℝ := (cond · μ ν)
    have : ∀ i : Bool, IsProbabilityMeasure (τ i) := fun i => by cases i <;> infer_instance
    have : ∀ i : Bool, CompactSpace (τ i).support := fun i => by
      cases i <;> exact isCompact_iff_compactSpace.mp
        (isCompact_Icc.of_isClosed_subset Measure.isClosed_support ‹_›)
    have hsum : (TauCeti.FreeLawRealization.state τ).law
        (TauCeti.FreeLawRealization.generator τ true +
          TauCeti.FreeLawRealization.generator τ false) = μ.freeConv ν :=
      TauCeti.FreeLawRealization.law_add_generator τ Bool.false_ne_true.symm
    rw [← hsum]
    exact (TauCeti.FreeLawRealization.state τ).support_law_add_subset_Icc
      (TauCeti.FreeLawRealization.isSelfAdjoint_generator τ true)
      (TauCeti.FreeLawRealization.isSelfAdjoint_generator τ false)
      ((TauCeti.FreeLawRealization.spectrum_generator τ true).trans_subset hμI)
      ((TauCeti.FreeLawRealization.spectrum_generator τ false).trans_subset hνI)
  · simp [freeConv_undef fun h => hp ⟨h.1.1, h.2.1⟩]

/-! ### Formal R-series, free cumulants, mean, and variance -/

/-- **Additivity of the formal R-series under free additive convolution.** -/
theorem rSeries_integral_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConv ν)) id =
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id +
        TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
  let τ : Bool → Measure ℝ := (cond · μ ν)
  have : ∀ i : Bool, IsProbabilityMeasure (τ i) := fun i => by cases i <;> infer_instance
  have : ∀ i : Bool, CompactSpace (τ i).support := fun i => by
    cases i <;> exact isCompact_iff_compactSpace.mp ‹_›
  let φ := TauCeti.FreeLawRealization.state τ
  have hg1 := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ true
  have hg2 := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ false
  have h1 : φ.law (TauCeti.FreeLawRealization.generator τ true) = μ :=
    TauCeti.FreeLawRealization.law_generator τ true
  have h2 : φ.law (TauCeti.FreeLawRealization.generator τ false) = ν :=
    TauCeti.FreeLawRealization.law_generator τ false
  have hsum : φ.law (TauCeti.FreeLawRealization.generator τ true +
      TauCeti.FreeLawRealization.generator τ false) = μ.freeConv ν :=
    TauCeti.FreeLawRealization.law_add_generator τ Bool.false_ne_true.symm
  apply PowerSeries.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
  rw [map_add, ← hsum, ← h1, ← h2, φ.map_ofReal_rSeries_integral_law (hg1.add hg2),
    φ.map_ofReal_rSeries_integral_law hg1, φ.map_ofReal_rSeries_integral_law hg2]
  exact (TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ).rSeries_add
    (TauCeti.FreeLawRealization.state_one τ) Bool.false_ne_true.symm

/-- **Additivity of free cumulants under free additive convolution.** -/
theorem freeCumulant_integral_freeConv {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    {α : Type*} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConv ν))
        (fun _ : α => (id : ℝ → ℝ)) s =
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : α => (id : ℝ → ℝ)) s +
        TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ν) (fun _ : α => (id : ℝ → ℝ)) s := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs.card_pos.ne'
  simp_rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries, hk,
    TauCeti.coeff_succ_freeCumulantSeries, rSeries_integral_freeConv hμ hν, map_add]

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
theorem eq_freeConv_iff_forall_freeCumulant_integral_eq {ρ μ ν : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ.freeConv ν ↔ ∀ n : ℕ, n ≠ 0 →
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) (fun _ : Fin n => (id : ℝ → ℝ)) univ =
        TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : Fin n => (id : ℝ → ℝ)) univ +
          TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ν)
            (fun _ : Fin n => (id : ℝ → ℝ)) univ := by
  have := isProbabilityMeasure_freeConv hμ hν
  rw [eq_iff_forall_freeCumulant_integral_eq hρ (isCompact_support_freeConv μ ν)]
  exact forall₂_congr fun n hn => by
    rw [freeCumulant_integral_freeConv hμ hν ⟨⟨0, Nat.pos_of_ne_zero hn⟩, mem_univ _⟩]

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
