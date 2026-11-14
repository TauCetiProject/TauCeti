/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Law.FreeProduct
public import TauCeti.Probability.FreeProbability.Law.Independence
public import TauCeti.Probability.FreeProbability.Law.Series
import TauCeti.MeasureTheory.Group.Measure
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Free additive convolution of compactly supported laws on `ℝ`

For compactly supported Borel probability measures `μ` and `ν` on `ℝ`, Voiculescu's *free additive
convolution* `μ ⊞ ν` (`MeasureTheory.Measure.freeConv`) is the scalar law of `a + b` for freely
independent selfadjoint elements `a` and `b` with laws `μ` and `ν` in a C⋆-probability space.

Concretely, `μ.freeConv ν` is defined via the canonical reduced C⋆-free product realization
`TauCeti.FreeLawRealization` of `(μ, ν)` and extended by `0` outside compactly supported
probability measures. By moment determinacy on compact sets and uniqueness of joint distributions
of freely independent selfadjoint families, `φ.law (a + b) = (φ.law a).freeConv (φ.law b)` holds in
every unital C⋆-algebra and every concrete von Neumann algebra realization.

## Main definitions

* `MeasureTheory.Measure.freeConv`: free additive convolution of compactly supported probability
  measures on `ℝ` (`μ ⊞ ν` under `open scoped FreeProbability`), defaulting to `0` otherwise.

## Main results

* `MeasureTheory.Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv`: binary
  C⋆-probability realization of `μ`, `ν`, and `μ.freeConv ν`.
* `TauCeti.IsFreelyIndependentElements.law_add`, `TauCeti.IsFreelyIndependentElements.law_add_add`,
  `TauCeti.IsFreelyIndependent.law_add`, `TauCeti.law_add_eq_freeConv_of_vonNeumannAlgebra`:
  realization-independence across C⋆- and von Neumann probability spaces.
* `MeasureTheory.Measure.freeConv_comm`, `MeasureTheory.Measure.freeConv_assoc`,
  `MeasureTheory.Measure.dirac_zero_freeConv`, `MeasureTheory.Measure.freeConv_map_affine`,
  `MeasureTheory.Measure.support_freeConv_subset_Icc`: algebraic, affine, and support laws.
* `MeasureTheory.Measure.rSeries_integral_freeConv`,
  `MeasureTheory.Measure.freeCumulant_integral_freeConv`,
  `MeasureTheory.Measure.eq_freeConv_iff_rSeries_integral_eq`: additivity of the formal R-series,
  free cumulants, mean, and variance, together with cumulant determinacy of `μ ⊞ ν`.

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

private abbrev IsCompactProb (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support

private theorem instProbCond {μ ν : Measure ℝ} (hμ : IsProbabilityMeasure μ)
    (hν : IsProbabilityMeasure ν) : ∀ b : Bool, IsProbabilityMeasure (cond b μ ν)
  | true => hμ
  | false => hν

private theorem instCompactCond {μ ν : Measure ℝ} (hμ : IsCompact μ.support)
    (hν : IsCompact ν.support) : ∀ b : Bool, CompactSpace (cond b μ ν).support
  | true => isCompact_iff_compactSpace.mp hμ
  | false => isCompact_iff_compactSpace.mp hν

open scoped Classical in
/-- **Free additive convolution** of compactly supported Borel probability measures on `ℝ`: the law
of `a + b` in the canonical reduced C⋆-free product realization of `(μ, ν)`. If either measure is
not a compactly supported probability measure, this returns the zero measure `0`. -/
def freeConv (μ ν : Measure ℝ) : Measure ℝ :=
  if h : IsCompactProb μ ∧ IsCompactProb ν then
    have := instProbCond h.1.1 h.2.1
    have := instCompactCond h.1.2 h.2.2
    (TauCeti.FreeLawRealization.state fun b : Bool => cond b μ ν).law
      (TauCeti.FreeLawRealization.generator (fun b : Bool => cond b μ ν) true +
        TauCeti.FreeLawRealization.generator (fun b : Bool => cond b μ ν) false)
  else 0

/-- Scoped notation `μ ⊞ ν` for the free additive convolution of measures on `ℝ`. -/
scoped[FreeProbability] infixr:80 " ⊞ " => MeasureTheory.Measure.freeConv

private theorem freeConv_def_of_isCompactProb {μ ν : Measure ℝ}
    [hμp : IsProbabilityMeasure μ] [hνp : IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    have := instProbCond hμp hνp
    have := instCompactCond hμ hν
    μ.freeConv ν =
      (TauCeti.FreeLawRealization.state fun b : Bool => cond b μ ν).law
        (TauCeti.FreeLawRealization.generator (fun b : Bool => cond b μ ν) true +
          TauCeti.FreeLawRealization.generator (fun b : Bool => cond b μ ν) false) := by
  unfold freeConv
  simp [IsCompactProb, hμp, hνp, hμ, hν]

/-- Outside compactly supported probability measures, `freeConv` returns `0`. -/
theorem freeConv_eq_zero_of_not {μ ν : Measure ℝ}
    (h : ¬((IsProbabilityMeasure μ ∧ IsCompact μ.support) ∧
      (IsProbabilityMeasure ν ∧ IsCompact ν.support))) :
    μ.freeConv ν = 0 := by
  unfold freeConv
  simp [IsCompactProb, h]

/-- Convolving the zero measure on the left gives `0`. -/
@[simp]
theorem zero_freeConv (μ : Measure ℝ) : (0 : Measure ℝ).freeConv μ = 0 :=
  freeConv_eq_zero_of_not fun h => not_isProbabilityMeasure_zero h.1.1

/-- Convolving the zero measure on the right gives `0`. -/
@[simp]
theorem freeConv_zero (μ : Measure ℝ) : μ.freeConv (0 : Measure ℝ) = 0 :=
  freeConv_eq_zero_of_not fun h => not_isProbabilityMeasure_zero h.2.1

/-- The free additive convolution of two compactly supported probability measures is a probability
measure. -/
theorem isProbabilityMeasure_freeConv {μ ν : Measure ℝ}
    [hμp : IsProbabilityMeasure μ] [hνp : IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    IsProbabilityMeasure (μ.freeConv ν) := by
  have := instProbCond hμp hνp
  have := instCompactCond hμ hν
  rw [freeConv_def_of_isCompactProb hμ hν]
  exact PositiveLinearMap.isProbabilityMeasure_law _
    (TauCeti.FreeLawRealization.state_one _)
    ((TauCeti.FreeLawRealization.isSelfAdjoint_generator _ true).add
      (TauCeti.FreeLawRealization.isSelfAdjoint_generator _ false))

/-- The free additive convolution of any two measures on `ℝ` is either `0` or a probability
measure (and in particular a finite measure). -/
instance isZeroOrProbabilityMeasure_freeConv (μ ν : Measure ℝ) :
    IsZeroOrProbabilityMeasure (μ.freeConv ν) := by
  by_cases h : IsCompactProb μ ∧ IsCompactProb ν
  · have : IsProbabilityMeasure μ := h.1.1
    have : IsProbabilityMeasure ν := h.2.1
    have : IsProbabilityMeasure (μ.freeConv ν) := isProbabilityMeasure_freeConv h.1.2 h.2.2
    infer_instance
  · rw [freeConv_eq_zero_of_not h]
    infer_instance

/-- The free additive convolution of any two measures has compact topological support. -/
theorem isCompact_support_freeConv (μ ν : Measure ℝ) : IsCompact (μ.freeConv ν).support := by
  by_cases h : IsCompactProb μ ∧ IsCompactProb ν
  · have : IsProbabilityMeasure μ := h.1.1
    have : IsProbabilityMeasure ν := h.2.1
    rw [freeConv_def_of_isCompactProb h.1.2 h.2.2]
    exact PositiveLinearMap.isCompact_support_law _ _
  · rw [freeConv_eq_zero_of_not h]
    simp

/-- `μ.freeConv ν` is a probability measure if and only if both `μ` and `ν` are compactly supported
probability measures. -/
theorem isProbabilityMeasure_freeConv_iff {μ ν : Measure ℝ} :
    IsProbabilityMeasure (μ.freeConv ν) ↔
      (IsProbabilityMeasure μ ∧ IsCompact μ.support) ∧
        (IsProbabilityMeasure ν ∧ IsCompact ν.support) := by
  refine ⟨fun hp => ?_, fun ⟨⟨_, hμc⟩, ⟨_, hνc⟩⟩ => isProbabilityMeasure_freeConv hμc hνc⟩
  by_contra h
  exact not_isProbabilityMeasure_zero (freeConv_eq_zero_of_not h ▸ hp)

/-- **Binary C⋆-probability realization of `μ`, `ν`, and `μ.freeConv ν`.** Any two compactly
supported probability measures `μ` and `ν` on `ℝ` can be realized by freely independent selfadjoint
elements `g true` and `g false` in a unital C⋆-probability space `(A, φ)` whose real spectra lie in
`μ.support` and `ν.support`, with laws `μ`, `ν`, and `φ.law (g true + g false) = μ.freeConv ν`. -/
theorem exists_isFreelyIndependentElements_law_add_eq_freeConv {μ ν : Measure ℝ}
    [hμp : IsProbabilityMeasure μ] [hνp : IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∃ (A : Type) (_ : CStarAlgebra A) (_ : PartialOrder A) (_ : StarOrderedRing A)
      (φ : A →ₚ[ℂ] ℂ) (g : Bool → A),
      φ 1 = 1 ∧
      TauCeti.IsFreelyIndependentElements φ.toLinearMap g ∧
      IsSelfAdjoint (g true) ∧ IsSelfAdjoint (g false) ∧
      spectrum ℝ (g true) ⊆ μ.support ∧ spectrum ℝ (g false) ⊆ ν.support ∧
      φ.law (g true) = μ ∧ φ.law (g false) = ν ∧
      φ.law (g true + g false) = μ.freeConv ν := by
  let τ : Bool → Measure ℝ := fun b => cond b μ ν
  have : ∀ b : Bool, IsProbabilityMeasure (τ b) := instProbCond hμp hνp
  have : ∀ b : Bool, CompactSpace (τ b).support := instCompactCond hμ hν
  refine ⟨TauCeti.FreeLawRealization.algebra τ, inferInstance, inferInstance, inferInstance,
    TauCeti.FreeLawRealization.state τ, TauCeti.FreeLawRealization.generator τ,
    TauCeti.FreeLawRealization.state_one τ,
    TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ,
    TauCeti.FreeLawRealization.isSelfAdjoint_generator τ true,
    TauCeti.FreeLawRealization.isSelfAdjoint_generator τ false,
    TauCeti.FreeLawRealization.spectrum_generator_subset_support τ true,
    TauCeti.FreeLawRealization.spectrum_generator_subset_support τ false,
    TauCeti.FreeLawRealization.law_generator τ true,
    TauCeti.FreeLawRealization.law_generator τ false,
    (freeConv_def_of_isCompactProb hμ hν).symm⟩

end MeasureTheory.Measure

/-! ### Realization-independence and transport across C⋆- and von Neumann probability spaces -/

namespace TauCeti

section Transport

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Realization-independence of free additive convolution (elements).** If `a` is a freely
independent family for a state `φ` on a unital C⋆-algebra `A` (including any concrete von Neumann
algebra `M : VonNeumannAlgebra H`), then for distinct indices `i ≠ j` with `a i` and `a j`
selfadjoint, the law of `a i + a j` is `(φ.law (a i)).freeConv (φ.law (a j))`. -/
theorem IsFreelyIndependentElements.law_add {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    (hai : IsSelfAdjoint (a i)) (haj : IsSelfAdjoint (a j)) :
    φ.law (a i + a j) = (φ.law (a i)).freeConv (φ.law (a j)) := by
  have : IsProbabilityMeasure (φ.law (a i)) := φ.isProbabilityMeasure_law hφ hai
  have : IsProbabilityMeasure (φ.law (a j)) := φ.isProbabilityMeasure_law hφ haj
  obtain ⟨B, _, _, _, ψ, g, hψ, hg_free, hg1, hg2, -, -, hg1_law, hg2_law, hadd_law⟩ :=
    Measure.exists_isFreelyIndependentElements_law_add_eq_freeConv
      (φ.isCompact_support_law (a i)) (φ.isCompact_support_law (a j))
  rw [← hadd_law]
  exact ha.law_add_eq_of_law_eq hg_free hφ hψ hij Bool.false_ne_true.symm hai haj hg1 hg2
    hg1_law.symm hg2_law.symm

/-- **Realization-independence of free additive convolution (subalgebras).** If `B` is a freely
independent family of subalgebras for a state `φ` on a unital C⋆-algebra `A`, and `x ∈ B i`,
`y ∈ B j` (`i ≠ j`) are selfadjoint, then `φ.law (x + y) = (φ.law x).freeConv (φ.law y)`. -/
theorem IsFreelyIndependent.law_add {φ : A →ₚ[ℂ] ℂ} {B : ι → Subalgebra ℂ A}
    (hB : IsFreelyIndependent φ.toLinearMap B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j)
    {x y : A} (hxB : x ∈ B i) (hyB : y ∈ B j) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    φ.law (x + y) = (φ.law x).freeConv (φ.law y) := by
  let e : Bool → ι := fun b => cond b i j
  have he : Function.Injective e := by
    rintro (_ | _) (_ | _) h <;> simp [e] at h <;> tauto
  have hc : IsFreelyIndependentElements φ.toLinearMap (fun b : Bool => cond b x y) :=
    (hB.comp he).isFreelyIndependentElements fun b => by cases b <;> assumption
  exact hc.law_add hφ Bool.false_ne_true.symm hx hy

/-- For pairwise distinct freely independent selfadjoint elements `a i`, `a j`, `a k`, the law of
`a i + a j + a k` is `((φ.law (a i)).freeConv (φ.law (a j))).freeConv (φ.law (a k))`. -/
theorem IsFreelyIndependentElements.law_add_add {φ : A →ₚ[ℂ] ℂ} {a : ι → A}
    (ha : IsFreelyIndependentElements φ.toLinearMap a) (hφ : φ 1 = 1)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hai : IsSelfAdjoint (a i)) (haj : IsSelfAdjoint (a j)) (hak : IsSelfAdjoint (a k)) :
    φ.law (a i + a j + a k) =
      ((φ.law (a i)).freeConv (φ.law (a j))).freeConv (φ.law (a k)) := by
  classical
  let f : ι → Bool := fun t => decide (t = k)
  have hB := ha.adjoin_image_fiber hφ f
  have hai_mem : a i ∈ Algebra.adjoin ℂ (a '' (f ⁻¹' {false})) :=
    Algebra.subset_adjoin ⟨i, by simp [f, hik], rfl⟩
  have haj_mem : a j ∈ Algebra.adjoin ℂ (a '' (f ⁻¹' {false})) :=
    Algebra.subset_adjoin ⟨j, by simp [f, hjk], rfl⟩
  have hak_mem : a k ∈ Algebra.adjoin ℂ (a '' (f ⁻¹' {true})) :=
    Algebra.subset_adjoin ⟨k, by simp [f], rfl⟩
  rw [hB.law_add hφ Bool.false_ne_true (add_mem hai_mem haj_mem) hak_mem (hai.add haj) hak,
    ha.law_add hφ hij hai haj]

/-- **Von Neumann subalgebra transport of free additive convolution.** If `M` is a family of
concrete von Neumann subalgebras on a Hilbert space `H` freely independent for a state `ω` on
`H →L[ℂ] H`, then selfadjoint operators `T₁ ∈ M i` and `T₂ ∈ M j` (`i ≠ j`) satisfy
`ω.law (T₁ + T₂) = (ω.law T₁).freeConv (ω.law T₂)`. -/
theorem law_add_eq_freeConv_of_vonNeumannAlgebra {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ω : (H →L[ℂ] H) →ₚ[ℂ] ℂ}
    {M : ι → VonNeumannAlgebra H}
    (hM : IsFreelyIndependent ω.toLinearMap fun i => (M i).toSubalgebra) (hω : ω 1 = 1)
    {i j : ι} (hij : i ≠ j) {T₁ T₂ : H →L[ℂ] H} (hT₁ : T₁ ∈ M i) (hT₂ : T₂ ∈ M j)
    (hsa₁ : IsSelfAdjoint T₁) (hsa₂ : IsSelfAdjoint T₂) :
    ω.law (T₁ + T₂) = (ω.law T₁).freeConv (ω.law T₂) :=
  hM.law_add hω hij hT₁ hT₂ hsa₁ hsa₂

namespace FreeLawRealization

variable [DecidableEq ι] (μ : ι → Measure ℝ)
  [∀ i, IsProbabilityMeasure (μ i)] [∀ i, CompactSpace (μ i).support]

/-- In the canonical C⋆-realization of `μ`, the sum of distinct generators `i ≠ j` has law
`(μ i).freeConv (μ j)`. -/
theorem law_add_generator {i j : ι} (hij : i ≠ j) :
    (state μ).law (generator μ i + generator μ j) = (μ i).freeConv (μ j) := by
  simpa using (isFreelyIndependentElements_generator μ).law_add (state_one μ) hij
    (isSelfAdjoint_generator μ i) (isSelfAdjoint_generator μ j)

/-- In the concrete von Neumann realization of `μ`, the sum of distinct generators `i ≠ j` has law
`(μ i).freeConv (μ j)`. -/
theorem law_add_vonNeumannGenerator {i j : ι} (hij : i ≠ j) :
    (vonNeumannState μ).law (vonNeumannGenerator μ i + vonNeumannGenerator μ j) =
      (μ i).freeConv (μ j) := by
  simpa using (isFreelyIndependentElements_vonNeumannGenerator μ).law_add
    (vonNeumannState_one μ) hij (isSelfAdjoint_vonNeumannGenerator μ i)
    (isSelfAdjoint_vonNeumannGenerator μ j)

end FreeLawRealization

end Transport

end TauCeti

/-! ### Algebraic laws, Dirac identity, affine pushforwards, and support bounds -/

namespace MeasureTheory.Measure

/-- Free additive convolution is commutative, unconditionally for all measures on `ℝ`. -/
theorem freeConv_comm (μ ν : Measure ℝ) : μ.freeConv ν = ν.freeConv μ := by
  by_cases h : IsCompactProb μ ∧ IsCompactProb ν
  · have : IsProbabilityMeasure μ := h.1.1
    have : IsProbabilityMeasure ν := h.2.1
    obtain ⟨A, _, _, _, φ, g, hφ, hg_free, hg1, hg2, -, -, hg1_law, hg2_law, hadd_law⟩ :=
      exists_isFreelyIndependentElements_law_add_eq_freeConv h.1.2 h.2.2
    rw [← hadd_law, add_comm, hg_free.law_add hφ Bool.false_ne_true hg2 hg1, hg2_law, hg1_law]
  · have h' : ¬(IsCompactProb ν ∧ IsCompactProb μ) := fun ⟨hν, hμ⟩ => h ⟨hμ, hν⟩
    rw [freeConv_eq_zero_of_not h, freeConv_eq_zero_of_not h']

instance : Std.Commutative (α := Measure ℝ) freeConv := ⟨freeConv_comm⟩

/-- Free additive convolution is associative, unconditionally for all measures on `ℝ`. -/
theorem freeConv_assoc (μ ν ρ : Measure ℝ) :
    (μ.freeConv ν).freeConv ρ = μ.freeConv (ν.freeConv ρ) := by
  by_cases h : IsCompactProb μ ∧ IsCompactProb ν ∧ IsCompactProb ρ
  · rcases h with ⟨⟨hμp, hμc⟩, ⟨hνp, hνc⟩, ⟨hρp, hρc⟩⟩
    let τ : Fin 3 → Measure ℝ := ![μ, ν, ρ]
    have : ∀ i : Fin 3, IsProbabilityMeasure (τ i) := fun i => by fin_cases i <;> assumption
    have : ∀ i : Fin 3, CompactSpace (τ i).support := fun i => by
      fin_cases i
      · exact isCompact_iff_compactSpace.mp hμc
      · exact isCompact_iff_compactSpace.mp hνc
      · exact isCompact_iff_compactSpace.mp hρc
    have hfree := TauCeti.FreeLawRealization.isFreelyIndependentElements_generator τ
    have hφ := TauCeti.FreeLawRealization.state_one τ
    have hsa := TauCeti.FreeLawRealization.isSelfAdjoint_generator τ
    have hL := hfree.law_add_add hφ (by decide : (0 : Fin 3) ≠ 1) (by decide) (by decide)
      (hsa 0) (hsa 1) (hsa 2)
    have hR := hfree.law_add_add hφ (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide)
      (hsa 1) (hsa 2) (hsa 0)
    have hτ0 : τ 0 = μ := rfl
    have hτ1 : τ 1 = ν := rfl
    have hτ2 : τ 2 = ρ := rfl
    rw [TauCeti.FreeLawRealization.law_generator, TauCeti.FreeLawRealization.law_generator,
      TauCeti.FreeLawRealization.law_generator, hτ0, hτ1, hτ2] at hL hR
    rw [← hL, freeConv_comm μ (ν.freeConv ρ), ← hR, add_assoc,
      add_comm (TauCeti.FreeLawRealization.generator τ 0)]
  · have hL : ¬(IsCompactProb (μ.freeConv ν) ∧ IsCompactProb ρ) := by
      rintro ⟨⟨hp, _⟩, hρ⟩
      rcases isProbabilityMeasure_freeConv_iff.mp hp with ⟨hμ, hν⟩
      exact h ⟨hμ, hν, hρ⟩
    have hR : ¬(IsCompactProb μ ∧ IsCompactProb (ν.freeConv ρ)) := by
      rintro ⟨hμ, ⟨hp, _⟩⟩
      rcases isProbabilityMeasure_freeConv_iff.mp hp with ⟨hν, hρ⟩
      exact h ⟨hμ, hν, hρ⟩
    rw [freeConv_eq_zero_of_not hL, freeConv_eq_zero_of_not hR]

instance : Std.Associative (α := Measure ℝ) freeConv := ⟨freeConv_assoc⟩

private theorem isSelfAdjoint_smul_add_algebraMap {A : Type*} [CStarAlgebra A] {x : A}
    (hx : IsSelfAdjoint x) (b c : ℝ) :
    IsSelfAdjoint (b • x + algebraMap ℝ A c) :=
  ((IsSelfAdjoint.all b).smul hx).add (IsSelfAdjoint.algebraMap A (.all c))

private theorem algebraMap_real_mem_adjoin {A : Type*} [CStarAlgebra A] (x : A) (c : ℝ) :
    algebraMap ℝ A c ∈ Algebra.adjoin ℂ {x} := by
  rw [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact Subalgebra.smul_mem _ (one_mem _) _

private theorem smul_add_algebraMap_mem_adjoin {A : Type*} [CStarAlgebra A] (x : A) (b c : ℝ) :
    b • x + algebraMap ℝ A c ∈ Algebra.adjoin ℂ {x} := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact add_mem (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton ℂ x) _)
    (algebraMap_real_mem_adjoin x c)

private theorem smul_add_algebraMap_add {A : Type*} [CStarAlgebra A] (x y : A) (b a c : ℝ) :
    (b • x + algebraMap ℝ A a) + (b • y + algebraMap ℝ A c) =
      b • (x + y) + algebraMap ℝ A (a + c) := by
  rw [map_add, smul_add, add_add_add_comm]

/-- **Affine equivariance of free additive convolution.** For compactly supported probability
measures `μ` and `ν` on `ℝ` and any `a, c, b : ℝ` (including `b = 0` and `b < 0`), pushing forward
by `x ↦ a + b * x` and `x ↦ c + b * x` before `freeConv` agrees with pushing forward `μ.freeConv ν`
by `x ↦ a + c + b * x`. -/
theorem freeConv_map_affine {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (a c b : ℝ) :
    (μ.map fun x => a + b * x).freeConv (ν.map fun x => c + b * x) =
      (μ.freeConv ν).map fun x => a + c + b * x := by
  obtain ⟨A, _, _, _, φ, g, hφ, hg_free, hg1_sa, hg2_sa, -, -, hg1_law, hg2_law, hsum_law⟩ :=
    exists_isFreelyIndependentElements_law_add_eq_freeConv hμ hν
  have hfun (d : ℝ) : (fun x : ℝ => b * x + d) = fun x => d + b * x := by funext x; ring
  have hx₁_law : φ.law (b • g true + algebraMap ℝ A a) = μ.map fun x => a + b * x := by
    rw [φ.law_smul_add_algebraMap hg1_sa b a, hfun a, hg1_law]
  have hx₂_law : φ.law (b • g false + algebraMap ℝ A c) = ν.map fun x => c + b * x := by
    rw [φ.law_smul_add_algebraMap hg2_sa b c, hfun c, hg2_law]
  have hadd_law : φ.law ((b • g true + algebraMap ℝ A a) + (b • g false + algebraMap ℝ A c)) =
      (μ.map fun x => a + b * x).freeConv (ν.map fun x => c + b * x) := by
    rw [(TauCeti.isFreelyIndependentElements_iff.mp hg_free).law_add hφ Bool.false_ne_true.symm
      (smul_add_algebraMap_mem_adjoin (g true) b a)
      (smul_add_algebraMap_mem_adjoin (g false) b c)
      (isSelfAdjoint_smul_add_algebraMap hg1_sa b a)
      (isSelfAdjoint_smul_add_algebraMap hg2_sa b c), hx₁_law, hx₂_law]
  rw [← hadd_law, smul_add_algebraMap_add,
    φ.law_smul_add_algebraMap (hg1_sa.add hg2_sa) b (a + c), hfun (a + c), hsum_law]

/-- Translating two compactly supported probability measures by `a` and `b` translates their free
additive convolution by `a + b`. -/
theorem freeConv_map_add {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (a b : ℝ) :
    (μ.map (a + ·)).freeConv (ν.map (b + ·)) = (μ.freeConv ν).map (a + b + ·) := by
  simpa using freeConv_map_affine hμ hν a b 1

/-- Scaling two compactly supported probability measures by a common real factor `b` scales their
free additive convolution by `b`. -/
theorem freeConv_map_mul {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) (b : ℝ) :
    (μ.map (b * ·)).freeConv (ν.map (b * ·)) = (μ.freeConv ν).map (b * ·) := by
  simpa using freeConv_map_affine hμ hν 0 0 b

/-- Free additive convolution commutes with measure reflection `Measure.neg`, unconditionally for
all measures on `ℝ`. -/
theorem freeConv_neg (μ ν : Measure ℝ) : μ.neg.freeConv ν.neg = (μ.freeConv ν).neg := by
  have hcomp (σ : Measure ℝ) : IsCompact σ.neg.support ↔ IsCompact σ.support := by
    rw [Measure.neg_def, ← Homeomorph.coe_neg, σ.support_map_homeomorph (Homeomorph.neg ℝ),
      (Homeomorph.neg ℝ).isCompact_image]
  by_cases h : IsCompactProb μ ∧ IsCompactProb ν
  · have : IsProbabilityMeasure μ := h.1.1
    have : IsProbabilityMeasure ν := h.2.1
    simpa [Measure.neg_def] using freeConv_map_mul h.1.2 h.2.2 (-1)
  · have h' : ¬(IsCompactProb μ.neg ∧ IsCompactProb ν.neg) := by
      rintro ⟨⟨_, hc1⟩, ⟨_, hc2⟩⟩
      have hμp : IsProbabilityMeasure μ := by
        simpa using Measure.isProbabilityMeasure_neg μ.neg
      have hνp : IsProbabilityMeasure ν := by
        simpa using Measure.isProbabilityMeasure_neg ν.neg
      exact h ⟨⟨hμp, (hcomp μ).mp hc1⟩, ⟨hνp, (hcomp ν).mp hc2⟩⟩
    rw [freeConv_eq_zero_of_not h', freeConv_eq_zero_of_not h]
    simp [Measure.neg_def]

/-- Free additive convolution with the Dirac mass at `a` on the left translates a compactly
supported probability measure by `a`. -/
theorem dirac_freeConv (a : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) :
    (Measure.dirac a).freeConv μ = μ.map (a + ·) := by
  obtain ⟨A, _, _, _, φ, g, hφ, hg_free, -, hg_sa, -, -, -, hg_law, -⟩ :=
    exists_isFreelyIndependentElements_law_add_eq_freeConv hμ hμ
  have hadd := (TauCeti.isFreelyIndependentElements_iff.mp hg_free).law_add hφ
    Bool.false_ne_true.symm (algebraMap_real_mem_adjoin (g true) a)
    (Algebra.self_mem_adjoin_singleton ℂ (g false))
    (IsSelfAdjoint.algebraMap A (.all a)) hg_sa
  rw [φ.law_algebraMap_of_apply_one hφ a, hg_law] at hadd
  have hcomm : algebraMap ℝ A a + g false = (1 : ℝ) • g false + algebraMap ℝ A a := by
    rw [one_smul, add_comm]
  rw [← hadd, hcomm, φ.law_smul_add_algebraMap hg_sa 1 a, hg_law]
  congr 1
  funext x
  ring

/-- Free additive convolution with the Dirac mass at `a` on the right translates a compactly
supported probability measure by `a`. -/
theorem freeConv_dirac {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (a : ℝ) :
    μ.freeConv (Measure.dirac a) = μ.map (· + a) := by
  rw [freeConv_comm, dirac_freeConv a hμ]
  congr 1
  funext x
  ring

/-- `Measure.dirac 0` is the left identity for `freeConv` on compactly supported probability
measures. -/
theorem dirac_zero_freeConv {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    (Measure.dirac 0).freeConv μ = μ := by
  simp [dirac_freeConv 0 hμ]

/-- `Measure.dirac 0` is the right identity for `freeConv` on compactly supported probability
measures. -/
theorem freeConv_dirac_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    μ.freeConv (Measure.dirac 0) = μ := by
  rw [freeConv_comm, dirac_zero_freeConv hμ]

/-- The free additive convolution of two Dirac masses is the Dirac mass at the sum of their atoms.
-/
@[simp]
theorem dirac_freeConv_dirac (a b : ℝ) :
    (Measure.dirac a).freeConv (Measure.dirac b) = Measure.dirac (a + b) := by
  have hb : IsCompact (Measure.dirac b).support := by
    rw [Measure.support_dirac b, closure_singleton]
    exact isCompact_singleton
  rw [dirac_freeConv a hb, Measure.map_dirac' (measurable_const_add a)]

/-- **Support interval bound for free additive convolution.** For any measures `μ` and `ν` on `ℝ`
supported in `[m₁, M₁]` and `[m₂, M₂]`, `μ.freeConv ν` is supported in `[m₁ + m₂, M₁ + M₂]`. When
either measure is not a probability measure, `μ.freeConv ν = 0` has empty support. -/
theorem support_freeConv_subset_Icc {μ ν : Measure ℝ} {m₁ M₁ m₂ M₂ : ℝ}
    (hμI : μ.support ⊆ Set.Icc m₁ M₁) (hνI : ν.support ⊆ Set.Icc m₂ M₂) :
    (μ.freeConv ν).support ⊆ Set.Icc (m₁ + m₂) (M₁ + M₂) := by
  by_cases hp : IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν
  · obtain ⟨hμp, hνp⟩ := hp
    have hμc : IsCompact μ.support := isCompact_Icc.of_isClosed_subset Measure.isClosed_support hμI
    have hνc : IsCompact ν.support := isCompact_Icc.of_isClosed_subset Measure.isClosed_support hνI
    obtain ⟨A, _, _, _, φ, g, -, -, hg1, hg2, hspec1, hspec2, -, -, hadd_law⟩ :=
      exists_isFreelyIndependentElements_law_add_eq_freeConv hμc hνc
    rw [← hadd_law]
    exact φ.support_law_add_subset_Icc hg1 hg2 (hspec1.trans hμI) (hspec2.trans hνI)
  · rw [freeConv_eq_zero_of_not fun h => hp ⟨h.1.1, h.2.1⟩]
    simp

/-! ### Formal R-series, free cumulants, mean, and variance -/

/-- **Additivity of the formal R-series under free additive convolution.** -/
theorem rSeries_integral_freeConv {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConv ν)) id =
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id +
        TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
  obtain ⟨A, _, _, _, φ, g, hφ, hg_free, hg1, hg2, -, -, hg1_law, hg2_law, hadd_law⟩ :=
    exists_isFreelyIndependentElements_law_add_eq_freeConv hμ hν
  have hadd := hg_free.rSeries_add hφ Bool.false_ne_true.symm
  have hmap : PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
      (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConv ν)) id) =
      PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id +
          TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id) := by
    rw [map_add, ← hadd_law, ← hg1_law, ← hg2_law,
      φ.map_ofReal_rSeries_integral_law (hg1.add hg2),
      φ.map_ofReal_rSeries_integral_law hg1,
      φ.map_ofReal_rSeries_integral_law hg2]
    exact hadd
  ext n
  exact Complex.ofReal_injective (by simpa using congrArg (PowerSeries.coeff n) hmap)

/-- **Additivity of free cumulants under free additive convolution.** -/
theorem freeCumulant_integral_freeConv {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    {α : Type*} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂(μ.freeConv ν))
        (fun _ : α => (id : ℝ → ℝ)) s =
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : α => (id : ℝ → ℝ)) s +
        TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ν) (fun _ : α => (id : ℝ → ℝ)) s := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs.card_pos.ne'
  rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries, hk,
    TauCeti.coeff_succ_freeCumulantSeries, TauCeti.coeff_succ_freeCumulantSeries,
    TauCeti.coeff_succ_freeCumulantSeries, rSeries_integral_freeConv hμ hν, map_add]

/-- A compactly supported probability measure `ρ` equals `μ.freeConv ν` if and only if its formal
R-series equals the sum of the formal R-series of `μ` and `ν`. -/
theorem eq_freeConv_iff_rSeries_integral_eq {ρ μ ν : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ.freeConv ν ↔
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id =
        TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id +
          TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
  have : IsProbabilityMeasure (μ.freeConv ν) := isProbabilityMeasure_freeConv hμ hν
  rw [eq_iff_rSeries_integral_eq hρ (isCompact_support_freeConv μ ν),
    rSeries_integral_freeConv hμ hν]

/-- A compactly supported probability measure `ρ` equals `μ.freeConv ν` if and only if all of its
positive-order free cumulants equal the sums of those of `μ` and `ν`. -/
theorem eq_freeConv_iff_forall_freeCumulant_integral_eq {ρ μ ν : Measure ℝ}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hρ : IsCompact ρ.support) (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ρ = μ.freeConv ν ↔ ∀ n : ℕ, n ≠ 0 →
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) (fun _ : Fin n => (id : ℝ → ℝ)) univ =
        TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : Fin n => (id : ℝ → ℝ)) univ +
          TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ν)
            (fun _ : Fin n => (id : ℝ → ℝ)) univ := by
  have : IsProbabilityMeasure (μ.freeConv ν) := isProbabilityMeasure_freeConv hμ hν
  rw [eq_iff_forall_freeCumulant_integral_eq hρ (isCompact_support_freeConv μ ν)]
  refine forall₂_congr fun n hn => ?_
  rw [freeCumulant_integral_freeConv hμ hν ⟨⟨0, Nat.pos_of_ne_zero hn⟩, mem_univ _⟩]

/-- The mean is additive under free additive convolution. -/
theorem integral_id_freeConv {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    ∫ x, x ∂(μ.freeConv ν) = (∫ x, x ∂μ) + ∫ x, x ∂ν := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, TauCeti.constantCoeff_rSeries] using
    congrArg (PowerSeries.coeff 0) (rSeries_integral_freeConv hμ hν)

/-- The variance is additive under free additive convolution. -/
theorem variance_id_freeConv {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    variance id (μ.freeConv ν) = variance id μ + variance id ν := by
  have : IsProbabilityMeasure (μ.freeConv ν) := isProbabilityMeasure_freeConv hμ hν
  have h := congrArg (PowerSeries.coeff 1) (rSeries_integral_freeConv hμ hν)
  rwa [map_add, coeff_one_rSeries_eq_variance (isCompact_support_freeConv μ ν),
    coeff_one_rSeries_eq_variance hμ, coeff_one_rSeries_eq_variance hν] at h

end MeasureTheory.Measure
