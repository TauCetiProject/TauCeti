/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Independence.Basic

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Joint Gaussianity of independent Gaussian processes

`Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence` shows that a jointly
Gaussian family of processes with zero cross-covariances is independent. Here we prove the converse:
mutually independent Gaussian processes form a jointly Gaussian process on the sigma or product
index type, and two independent Gaussian processes form a Gaussian process on `Sum`. We also show
that finite pointwise continuous linear combinations preserve `IsGaussianProcess`.

## Main results

* `ProbabilityTheory.iIndepFun.isGaussianProcess`,
  `ProbabilityTheory.iIndepFun.isGaussianProcess_prod`,
  `ProbabilityTheory.IndepFun.isGaussianProcess`: independent Gaussian processes are jointly
  Gaussian.
* `ProbabilityTheory.IsGaussianProcess.sum_comp_left`,
  `ProbabilityTheory.IsGaussianProcess.sum_smul`: finite pointwise continuous linear combinations
  remain Gaussian processes.

## References

* S. Janson, *Gaussian Hilbert Spaces*, Cambridge University Press, 1997, Chapter 1.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1.
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

section Independence

variable [CompleteSpace E]

/-- Mutually independent Gaussian processes `X t : S t → Ω → E` form a jointly Gaussian process
indexed by `(t : T) × S t`, with no finiteness or countability assumption on `T` or `S t`. -/
theorem iIndepFun.isGaussianProcess {S : T → Type*} {X : (t : T) → S t → Ω → E}
    (hX : ∀ t, IsGaussianProcess (X t) P) (hindep : iIndepFun (fun t ω s ↦ X t s ω) P) :
    IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P where
  hasGaussianLaw I := by
    classical
    let A : Finset T := I.image Sigma.fst
    let B : ∀ t : T, Finset (S t) := fun t ↦ I.preimage (Sigma.mk t) sigma_mk_injective.injOn
    have hY : HasGaussianLaw (fun ω (a : A) ↦ (B a.1).restrict (X a.1 · ω)) P :=
      ((hindep.precomp Subtype.val_injective).comp (fun a : A ↦ (B a.1).restrict)
        fun _ ↦ measurable_restrict _).hasGaussianLaw fun a ↦ (hX a.1).hasGaussianLaw (B a.1)
    let L : ((a : A) → B a.1 → E) →L[ℝ] (I → E) :=
      { toFun z p := z ⟨p.1.1, mem_image_of_mem Sigma.fst p.2⟩ ⟨p.1.2, mem_preimage.mpr p.2⟩
        map_add' _ _ := rfl, map_smul' _ _ := rfl, cont := by fun_prop }
    exact hY.map L

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
      { toFun := fun | z, ⟨.inl s, hp⟩ => z.1 ⟨s, mem_preimage.mpr hp⟩
                     | z, ⟨.inr t, hp⟩ => z.2 ⟨t, mem_preimage.mpr hp⟩
        map_add' x y := by ext ⟨p, _⟩; cases p <;> rfl
        map_smul' c x := by ext ⟨p, _⟩; cases p <;> rfl
        cont := continuous_pi fun ⟨p, _⟩ ↦ by cases p <;> fun_prop }
    have hL : (fun ω ↦ I.restrict (Sum.elim X Y · ω)) =
        L ∘ fun ω ↦ (A.restrict (X · ω), B.restrict (Y · ω)) := by ext ω ⟨p, _⟩; cases p <;> rfl
    exact hL ▸ hAB.map L

end Independence

namespace IsGaussianProcess

/-- A finite sum of pointwise continuous linear images of a jointly Gaussian family of processes is
itself a Gaussian process. -/
theorem sum_comp_left {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : ι → T → Ω → E} (hX : IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P)
    (s : Finset ι) (L : ι → T → E →L[ℝ] F) :
    IsGaussianProcess (fun t ω ↦ ∑ i ∈ s, L i t (X i t ω)) P := by
  classical
  refine hX.of_isGaussianProcess fun t ↦ ⟨s ×ˢ {t},
    { toFun z := ∑ i ∈ s.attach,
        L i.1 t (z ⟨(i.1, t), mem_product.mpr ⟨i.2, mem_singleton_self t⟩⟩)
      map_add' _ _ := by simp [sum_add_distrib]
      map_smul' _ _ := by simp [smul_sum]
      cont := by fun_prop }, fun ω ↦ ?_⟩
  simpa [restrict_def] using (sum_attach s fun i ↦ L i t (X i t ω)).symm

/-- A finite pointwise linear combination of a jointly Gaussian family of scalar processes with
deterministic vectors in `F` is a Gaussian process in `F`. -/
theorem sum_smul {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : ι → T → Ω → ℝ} (hX : IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P)
    (s : Finset ι) (v : T → ι → F) :
    IsGaussianProcess (fun t ω ↦ ∑ i ∈ s, X i t ω • v t i) P :=
  hX.sum_comp_left s fun i t ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t i)

/-- A jointly Gaussian family of scalar processes is mutually independent iff distinct processes
have zero cross-covariance at all pairs of times. -/
theorem iIndepFun_iff_covariance_eq_zero {S : T → Type*} {X : (t : T) → S t → Ω → ℝ}
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun t ω s ↦ X t s ω) P ↔
      ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0 := by
  have := hX.isProbabilityMeasure
  refine ⟨fun h t₁ t₂ ht s₁ s₂ ↦ ((h.indepFun ht).comp (measurable_pi_apply s₁)
      (measurable_pi_apply s₂)).covariance_eq_zero (hX.hasGaussianLaw_eval ⟨t₁, s₁⟩).memLp_two
      (hX.hasGaussianLaw_eval ⟨t₂, s₂⟩).memLp_two,
    hX.iIndepFun_of_covariance_eq_zero fun t s ↦ hX.aemeasurable ⟨t, s⟩⟩

end IsGaussianProcess

end ProbabilityTheory
