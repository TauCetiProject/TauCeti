/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import TauCeti.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.HasLaw

/-!
# Joint Gaussianity of independent Gaussian processes

Complements `Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence`:
independent Gaussian processes are jointly Gaussian (on sigma, product, and `Sum` index types),
`IsGaussianProcess` is preserved by finite continuous linear combinations and measure completion,
and independence of jointly Gaussian processes is equivalent to vanishing cross-covariances.
The finite-dimensional laws of a real Gaussian process are the multivariate Gaussian laws with the
means and covariances of the process
(`ProbabilityTheory.IsGaussianProcess.map_toLp_eq_multivariateGaussian`).

## References

* S. Janson, *Gaussian Hilbert Spaces*, Cambridge University Press, 1997, Chapter 1.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1.
-/

public section

open MeasureTheory Finset InnerProductSpace
open scoped RealInnerProductSpace

namespace ProbabilityTheory

/-- Completing the ambient measure preserves `IsGaussianProcess`. -/
theorem IsGaussianProcess.completion {T Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E] {X : T → Ω → E}
    (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t (ω : NullMeasurableSpace Ω P) ↦ X t ω) P.completion :=
  ⟨fun I ↦ have := (hX.hasGaussianLaw I).isGaussian_map
    (hasLaw_map (hX.hasGaussianLaw I).aemeasurable).completion.hasGaussianLaw⟩

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

section Independence

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- Mutually independent Gaussian processes `X t : S t → Ω → E` are jointly Gaussian. -/
theorem iIndepFun.isGaussianProcess {S : T → Type*} {X : (t : T) → S t → Ω → E}
    (hX : ∀ t, IsGaussianProcess (X t) P) (hindep : iIndepFun (fun t ω s ↦ X t s ω) P) :
    IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P where
  hasGaussianLaw I := by
    classical
    let A : Finset T := I.image Sigma.fst
    let B (t : T) : Finset (S t) := I.preimage (Sigma.mk t) sigma_mk_injective.injOn
    have hY := ((hindep.precomp Subtype.val_injective).comp (fun a : A ↦ (B a.val).restrict)
      fun _ ↦ measurable_restrict _).hasGaussianLaw fun a ↦ (hX a.val).hasGaussianLaw (B a.val)
    exact hY.map ({
      toFun z p := z ⟨p.val.1, mem_image_of_mem _ p.property⟩ ⟨p.val.2, mem_preimage.mpr p.property⟩
      map_add' _ _ := rfl, map_smul' _ _ := rfl, cont := by fun_prop } :
      ((a : A) → B a.val → E) →L[ℝ] (I → E))

/-- Mutually independent Gaussian processes `X i : T → Ω → E` form a Gaussian process on `ι × T`. -/
theorem iIndepFun.isGaussianProcess_prod {ι : Type*} {X : ι → T → Ω → E}
    (hX : ∀ i, IsGaussianProcess (X i) P) (hindep : iIndepFun (fun i ω t ↦ X i t ω) P) :
    IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P :=
  (hindep.isGaussianProcess hX).comp_right fun (p : ι × T) ↦ ⟨p.1, p.2⟩

/-- Two independent Gaussian processes `X` and `Y` make `Sum.elim X Y` a Gaussian process. -/
theorem IndepFun.isGaussianProcess {S : Type*} {X : S → Ω → E} {Y : T → Ω → E}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hindep : IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P) :
    IsGaussianProcess (Sum.elim X Y) P where
  hasGaussianLaw I := by
    classical
    let A : Finset S := I.preimage Sum.inl Sum.inl_injective.injOn
    let B : Finset T := I.preimage Sum.inr Sum.inr_injective.injOn
    have hAB := (hindep.comp (measurable_restrict A) (measurable_restrict B)).hasGaussianLaw
      (hX.hasGaussianLaw A) (hY.hasGaussianLaw B)
    let L : (A → E) × (B → E) →L[ℝ] (I → E) :=
      { toFun := fun | z, ⟨.inl s, h⟩ => z.1 ⟨s, mem_preimage.mpr h⟩
                     | z, ⟨.inr t, h⟩ => z.2 ⟨t, mem_preimage.mpr h⟩
        map_add' _ _ := by ext ⟨p, _⟩; cases p <;> rfl
        map_smul' _ _ := by ext ⟨p, _⟩; cases p <;> rfl
        cont := continuous_pi fun ⟨p, _⟩ ↦ by cases p <;> fun_prop }
    have hL : (fun ω ↦ I.restrict (Sum.elim X Y · ω)) =
        L ∘ fun ω ↦ (A.restrict (X · ω), B.restrict (Y · ω)) := by ext ω ⟨p, _⟩; cases p <;> rfl
    exact hL ▸ hAB.map L

end Independence

namespace IsGaussianProcess

/-- The finite-dimensional laws of a real Gaussian process: the values at finitely many times
`s i`, collected into a Euclidean vector, have the multivariate Gaussian law whose mean and
covariance matrix are those of the process. The times need not be distinct. -/
theorem map_toLp_eq_multivariateGaussian {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → T) :
    P.map (fun ω ↦ WithLp.toLp 2 fun i ↦ X (s i) ω) =
      multivariateGaussian (WithLp.toLp 2 fun i ↦ P[X (s i)])
        (Matrix.of fun i j ↦ cov[X (s i), X (s j); P]) := by
  classical
  have := hX.isProbabilityMeasure
  let L : (↥(univ.image s) → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap ∘L
      { toFun x i := x ⟨s i, mem_image_of_mem s (mem_univ i)⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        cont := by fun_prop }
  have hG : HasGaussianLaw (fun ω ↦ WithLp.toLp 2 fun i ↦ X (s i) ω) P :=
    (hX.hasGaussianLaw _).map L
  have := hG.isGaussian_map
  have hV := hG.aemeasurable
  rw [TauCeti.Probability.eq_multivariateGaussian_covMatrix (P.map _)]
  congr 1
  · ext i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (IsGaussian.integrable_id (μ := P.map fun ω ↦ WithLp.toLp 2 fun i ↦ X (s i) ω))
    simp only [EuclideanSpace.coe_proj, id_eq] at h
    rw [← h, integral_map hV (by fun_prop)]
  · ext i j
    rw [TauCeti.covMatrix_apply, covariance_map (by fun_prop) (by fun_prop) hV]
    simp [Function.comp_def]

/-- Finite sums of pointwise continuous linear images preserve `IsGaussianProcess`. -/
theorem sum_comp_left [NormedSpace ℝ E] {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {X : ι → T → Ω → E}
    (hX : IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P)
    (s : Finset ι) (L : ι → T → E →L[ℝ] F) :
    IsGaussianProcess (fun t ω ↦ ∑ i ∈ s, L i t (X i t ω)) P := by
  classical
  refine hX.of_isGaussianProcess fun t ↦ ⟨s ×ˢ {t},
    { toFun z := ∑ i ∈ s.attach,
        L i.val t (z ⟨(i.val, t), mem_product.mpr ⟨i.property, mem_singleton_self t⟩⟩)
      map_add' _ _ := by simp [sum_add_distrib], map_smul' _ _ := by simp [smul_sum]
      cont := by fun_prop }, fun ω ↦ by
    simpa [restrict_def] using (sum_attach s fun i ↦ L i t (X i t ω)).symm⟩

/-- Finite pointwise linear combinations of jointly Gaussian scalar processes are Gaussian. -/
theorem sum_smul {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {X : ι → T → Ω → ℝ}
    (hX : IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P) (s : Finset ι) (v : T → ι → F) :
    IsGaussianProcess (fun t ω ↦ ∑ i ∈ s, X i t ω • v t i) P :=
  hX.sum_comp_left s fun i t ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t i)

/-- Jointly Gaussian processes are independent iff their dual functionals are uncorrelated. -/
theorem iIndepFun_iff_covariance_strongDual [NormedSpace ℝ E] [CompleteSpace E] {S : T → Type*}
    {X : (t : T) → S t → Ω → E} (hX : IsGaussianProcess (fun (p : (t : T) × S t) ↦ X p.1 p.2) P) :
    iIndepFun (fun t ω s ↦ X t s ω) P ↔ ∀ t₁ t₂, t₁ ≠ t₂ →
      ∀ (s₁ : S t₁) (s₂ : S t₂) (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0 :=
  have := hX.isProbabilityMeasure
  ⟨fun h t₁ t₂ ht s₁ s₂ L₁ L₂ ↦
      ((h.indepFun ht).comp (L₁.continuous.measurable.comp (measurable_pi_apply s₁))
        (L₂.continuous.measurable.comp (measurable_pi_apply s₂))).covariance_eq_zero
        ((hX.hasGaussianLaw_eval ⟨t₁, s₁⟩).map L₁).memLp_two
        ((hX.hasGaussianLaw_eval ⟨t₂, s₂⟩).map L₂).memLp_two,
    hX.iIndepFun_of_covariance_strongDual fun t s ↦ hX.aemeasurable ⟨t, s⟩⟩

/-- Jointly Gaussian processes are independent iff their inner products are uncorrelated. -/
theorem iIndepFun_iff_covariance_inner [InnerProductSpace ℝ E] [CompleteSpace E] {S : T → Type*}
    {X : (t : T) → S t → Ω → E} (hX : IsGaussianProcess (fun (p : (t : T) × S t) ↦ X p.1 p.2) P) :
    iIndepFun (fun t ω s ↦ X t s ω) P ↔ ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (x y : E),
      cov[fun ω ↦ ⟪x, X t₁ s₁ ω⟫, fun ω ↦ ⟪y, X t₂ s₂ ω⟫; P] = 0 := by
  rw [hX.iIndepFun_iff_covariance_strongDual]
  exact ⟨fun h t₁ t₂ ht s₁ s₂ x y ↦ h t₁ t₂ ht s₁ s₂ (innerSL ℝ x) (innerSL ℝ y),
    fun h t₁ t₂ ht s₁ s₂ L₁ L₂ ↦ by
      simpa using! h t₁ t₂ ht s₁ s₂ ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)⟩

/-- Jointly Gaussian scalar processes are independent iff cross-covariances vanish. -/
theorem iIndepFun_iff_covariance_eq_zero {S : T → Type*} {X : (t : T) → S t → Ω → ℝ}
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun t ω s ↦ X t s ω) P ↔
      ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0 := by
  have := hX.isProbabilityMeasure; rw [hX.iIndepFun_iff_covariance_inner]
  exact ⟨fun h t₁ t₂ ht s₁ s₂ ↦ by simpa using h t₁ t₂ ht s₁ s₂ 1 1, fun h t₁ t₂ ht s₁ s₂ _ _ ↦ by
    simp [covariance_mul_const_left, covariance_mul_const_right, h t₁ t₂ ht s₁ s₂]⟩

/-- Two jointly Gaussian processes are independent iff their dual functionals are uncorrelated. -/
theorem indepFun_iff_covariance_strongDual [NormedSpace ℝ E] [CompleteSpace E] {S : Type*}
    {X : S → Ω → E} {Y : T → Ω → E} (hXY : IsGaussianProcess (Sum.elim X Y) P) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P ↔
      ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0 :=
  have := hXY.isProbabilityMeasure
  ⟨fun h s t L₁ L₂ ↦
      (h.comp (L₁.continuous.measurable.comp (measurable_pi_apply s))
        (L₂.continuous.measurable.comp (measurable_pi_apply t))).covariance_eq_zero
        ((hXY.hasGaussianLaw_eval (.inl s)).map L₁).memLp_two
        ((hXY.hasGaussianLaw_eval (.inr t)).map L₂).memLp_two,
    hXY.indepFun_of_covariance_strongDual (fun s ↦ hXY.aemeasurable (.inl s))
      fun t ↦ hXY.aemeasurable (.inr t)⟩

/-- Two jointly Gaussian processes are independent iff inner products are uncorrelated. -/
theorem indepFun_iff_covariance_inner [InnerProductSpace ℝ E] [CompleteSpace E] {S : Type*}
    {X : S → Ω → E} {Y : T → Ω → E} (hXY : IsGaussianProcess (Sum.elim X Y) P) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P ↔
      ∀ s t (x y : E), cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0 := by
  rw [hXY.indepFun_iff_covariance_strongDual]
  exact ⟨fun h s t x y ↦ h s t (innerSL ℝ x) (innerSL ℝ y), fun h s t L₁ L₂ ↦ by
    simpa using! h s t ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)⟩

/-- Two jointly Gaussian scalar processes are independent iff they have zero cross-covariance. -/
theorem indepFun_iff_covariance_eq_zero {S : Type*} {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (hXY : IsGaussianProcess (Sum.elim X Y) P) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P ↔ ∀ s t, cov[X s, Y t; P] = 0 := by
  have := hXY.isProbabilityMeasure; rw [hXY.indepFun_iff_covariance_inner]
  exact ⟨fun h s t ↦ by simpa using h s t 1 1, fun h s t _ _ ↦ by
    simp [covariance_mul_const_left, covariance_mul_const_right, h s t]⟩

end IsGaussianProcess

end ProbabilityTheory
