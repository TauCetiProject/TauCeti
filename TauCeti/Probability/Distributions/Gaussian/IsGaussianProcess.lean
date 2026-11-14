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
Gaussian family of processes with vanishing cross-covariances is independent. This file proves the
converse: mutually independent Gaussian processes form a jointly Gaussian process over the sigma
or product index type, and two independent Gaussian processes form a jointly Gaussian process over
`Sum`. Together with the Mathlib direction this characterizes independence among marginal Gaussian
processes whose joint Gaussianity is known, and allows finite linear combinations of independent
Gaussian processes to inherit `ProbabilityTheory.IsGaussianProcess`.

## Main results

* `ProbabilityTheory.iIndepFun.isGaussianProcess`: mutually independent Gaussian processes
  `X t : S t → Ω → E` are jointly Gaussian as a process on `(t : T) × S t`.
* `ProbabilityTheory.iIndepFun.isGaussianProcess_prod`: non-dependent specialization to `ι × T`.
* `ProbabilityTheory.IndepFun.isGaussianProcess`: two independent Gaussian processes `X` and `Y`
  make `Sum.elim X Y` a Gaussian process.
* `ProbabilityTheory.IsGaussianProcess.sum_comp_left` and
  `ProbabilityTheory.IsGaussianProcess.sum_smul`: finite pointwise continuous linear combinations
  of a jointly Gaussian family of processes remain Gaussian processes.

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
indexed by the dependent pair type `(t : T) × S t`. No finiteness or countability assumption on
`T` or `S t` is required. -/
theorem iIndepFun.isGaussianProcess {S : T → Type*} {X : (t : T) → S t → Ω → E}
    (hX : ∀ t, IsGaussianProcess (X t) P) (hindep : iIndepFun (fun t ω s ↦ X t s ω) P) :
    IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P where
  hasGaussianLaw I := by
    classical
    let A : Finset T := I.image Sigma.fst
    let B : ∀ t : T, Finset (S t) := fun t ↦ I.preimage (Sigma.mk t) sigma_mk_injective.injOn
    have hY_indep : iIndepFun (fun (a : A) ω ↦ (B a.1).restrict (X a.1 · ω)) P :=
      (hindep.precomp Subtype.val_injective).comp
        (fun a : A ↦ (B a.1).restrict) (fun _ ↦ Finset.measurable_restrict _)
    have hY_gauss : HasGaussianLaw (fun ω (a : A) ↦ (B a.1).restrict (X a.1 · ω)) P :=
      hY_indep.hasGaussianLaw fun a ↦ (hX a.1).hasGaussianLaw (B a.1)
    let L : ((a : A) → B a.1 → E) →L[ℝ] (I → E) :=
      { toFun z p := z ⟨p.1.1, mem_image_of_mem Sigma.fst p.2⟩ ⟨p.1.2, mem_preimage.mpr p.2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        cont := by fun_prop }
    exact hY_gauss.map L

/-- Non-dependent specialization of `ProbabilityTheory.iIndepFun.isGaussianProcess`: mutually
independent Gaussian processes `X i : T → Ω → E` form a jointly Gaussian process on `ι × T`. -/
theorem iIndepFun.isGaussianProcess_prod {ι : Type*} {X : ι → T → Ω → E}
    (hX : ∀ i, IsGaussianProcess (X i) P) (hindep : iIndepFun (fun i ω t ↦ X i t ω) P) :
    IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P := by
  let e : ι × T → (_ : ι) × T := fun p ↦ ⟨p.1, p.2⟩
  exact (hindep.isGaussianProcess hX).comp_right e

/-- Two independent Gaussian processes `X : S → Ω → E` and `Y : T → Ω → E` are jointly Gaussian,
meaning that `Sum.elim X Y` is a Gaussian process on `S ⊕ T`. -/
theorem IndepFun.isGaussianProcess {S : Type*} {X : S → Ω → E} {Y : T → Ω → E}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hindep : IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P) :
    IsGaussianProcess (Sum.elim X Y) P where
  hasGaussianLaw I := by
    classical
    let A : Finset S := I.preimage Sum.inl Sum.inl_injective.injOn
    let B : Finset T := I.preimage Sum.inr Sum.inr_injective.injOn
    have hAB_indep :
        IndepFun (fun ω ↦ A.restrict (X · ω)) (fun ω ↦ B.restrict (Y · ω)) P :=
      hindep.comp (Finset.measurable_restrict A) (Finset.measurable_restrict B)
    have hAB_gauss :
        HasGaussianLaw (fun ω ↦ (A.restrict (X · ω), B.restrict (Y · ω))) P :=
      hAB_indep.hasGaussianLaw (hX.hasGaussianLaw A) (hY.hasGaussianLaw B)
    let L : (A → E) × (B → E) →L[ℝ] (I → E) :=
      { toFun
          | z, ⟨Sum.inl s, hp⟩ => z.1 ⟨s, mem_preimage.mpr hp⟩
          | z, ⟨Sum.inr t, hp⟩ => z.2 ⟨t, mem_preimage.mpr hp⟩
        map_add' x y := by
          ext ⟨p, hp⟩
          cases p <;> rfl
        map_smul' c x := by
          ext ⟨p, hp⟩
          cases p <;> rfl
        cont := by
          refine continuous_pi fun ⟨p, hp⟩ ↦ ?_
          cases p <;> fun_prop }
    have hL : (fun ω ↦ I.restrict (Sum.elim X Y · ω)) =
        L ∘ fun ω ↦ (A.restrict (X · ω), B.restrict (Y · ω)) := by
      ext ω ⟨p, hp⟩
      cases p <;> rfl
    rw [hL]
    exact hAB_gauss.map L

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
      map_add' x y := by simp [sum_add_distrib]
      map_smul' c x := by simp [smul_sum]
      cont := by fun_prop }, fun ω ↦ ?_⟩
  simpa [Finset.restrict_def] using (Finset.sum_attach s fun i ↦ L i t (X i t ω)).symm

/-- A finite pointwise linear combination of a jointly Gaussian family of scalar processes with
deterministic vectors in `F` is a Gaussian process in `F`. -/
theorem sum_smul {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : ι → T → Ω → ℝ} (hX : IsGaussianProcess (fun (p : ι × T) ω ↦ X p.1 p.2 ω) P)
    (s : Finset ι) (v : T → ι → F) :
    IsGaussianProcess (fun t ω ↦ ∑ i ∈ s, X i t ω • v t i) P :=
  hX.sum_comp_left s fun i t ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v t i)

/-- A jointly Gaussian family of scalar processes is mutually independent if and only if distinct
processes have zero cross-covariance at all pairs of times. -/
theorem iIndepFun_iff_covariance_eq_zero {S : T → Type*} {X : (t : T) → S t → Ω → ℝ}
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P) :
    iIndepFun (fun t ω s ↦ X t s ω) P ↔
      ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0 := by
  have := hX.isProbabilityMeasure
  refine ⟨fun hindep t₁ t₂ ht s₁ s₂ ↦ ?_,
    hX.iIndepFun_of_covariance_eq_zero fun t s ↦ hX.aemeasurable ⟨t, s⟩⟩
  have h12 : IndepFun (X t₁ s₁) (X t₂ s₂) P :=
    (hindep.indepFun ht).comp (measurable_pi_apply s₁) (measurable_pi_apply s₂)
  exact h12.covariance_eq_zero (hX.hasGaussianLaw_eval ⟨t₁, s₁⟩).memLp_two
    (hX.hasGaussianLaw_eval ⟨t₂, s₂⟩).memLp_two

end IsGaussianProcess

end ProbabilityTheory
