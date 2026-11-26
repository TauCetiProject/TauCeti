/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.KMS.ModularConjugation
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.RepresentationTheory.Continuous.Unitary.GaussianSmearing

/-!
# Tomita commutation for KMS states

For a β-KMS state `ω` of a point-norm continuous real action `α` on a unital C⋆-algebra `A`,
this file proves the reverse Tomita commutation inclusion `J₀ M' J₀ ⊆ M`
(`TauCeti.CStarAction.IsKMSState.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra`) and
hence `J₀ M J₀ = M'` for the GNS von Neumann algebra
`M = ω.toPositiveLinearMap.gnsVonNeumannAlgebra` and its modular conjugation `J₀`.

For `β = 0` (tracial states), `J₀ (R Ω) = R⋆ Ω` holds directly for every `R ∈ M'`. For `β ≠ 0`,
`ω` is invariant with strongly continuous implementing unitary group `U_t` commuting with `J₀`;
every `R ∈ M'` is approximated strongly by Gaussian smearings `R_c(z) = ∫ k_c(t - z) U_t R U_{-t}`
in `M'`, for which analytic continuation gives `J₀ (S(0) Ω) = S(iβ/2)⋆ Ω` and commutation of
`J₀ R J₀` with `M'`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_gnsVector_of_zero`:
  `J₀ (R Ω) = R⋆ Ω` for `R ∈ M'` at `β = 0`.
* `TauCeti.CStarAction.IsKMSState.modularConjugation_apply_gnsVector_of_commute`:
  `J₀ (R Ω) = R⋆ Ω` for `R ∈ M'` commuting with `U_t` when `β ≠ 0`.
* `TauCeti.CStarAction.IsKMSState.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra`:
  `J₀ M' J₀ ⊆ M`.
* `TauCeti.CStarAction.IsKMSState.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra_iff`:
  `J₀ T J₀ ∈ M ↔ T ∈ M'`.
* `TauCeti.CStarAction.IsKMSState.conjOperator_modularConjugation_mem_commutant_iff`:
  `J₀ T J₀ ∈ M' ↔ T ∈ M`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  second edition, Section 5.3.1 and Theorem 5.3.30.
-/

public section

noncomputable section

open Complex ContinuousLinearMap Filter PositiveLinearMap Topology
open scoped ComplexConjugate ComplexOrder CStarAlgebra InnerProductSpace

namespace TauCeti.CStarAction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-! ### The `β = 0` commutation theorem -/

/-- At `β = 0` (tracial states), `J₀ (R Ω) = R⋆ Ω` for every operator `R` in the commutant
`M_ω'`. -/
theorem IsKMSState.modularConjugation_apply_gnsVector_of_zero (hω : α.IsKMSState 0 ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant) :
    hω.modularConjugation (R ω.toPositiveLinearMap.gnsVector) =
      (star R) ω.toPositiveLinearMap.gnsVector := by
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom
  refine ext_inner_left ℂ fun u =>
    f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have hcomm := f.mem_gnsVonNeumannAlgebra_commutant_iff.mp (star_mem hR) (star a)
  rw [hω.inner_modularConjugation_right, hω.modularConjugation_apply_toGNS_of_zero a]
  calc ⟪R f.gnsVector, f.toGNS (star a)⟫_ℂ
      = ⟪f.gnsVector, (star R * ρ (star a)) f.gnsVector⟫_ℂ := by
        rw [mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_right]
        simp [ρ, toGNS_apply, gnsVector_def]
    _ = ⟪f.gnsVector, (ρ (star a) * star R) f.gnsVector⟫_ℂ := by rw [← hcomm]
    _ = ⟪f.toGNS a, (star R) f.gnsVector⟫_ℂ := by
        rw [mul_apply_eq_comp, map_star, star_eq_adjoint, adjoint_inner_right]
        simp [ρ, toGNS_apply, gnsVector_def]

/-- Tomita commutation at `β = 0`: `J₀ R J₀ ∈ M_ω` for every `R ∈ M_ω'`. -/
private theorem conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra_of_zero
    (hω : α.IsKMSState 0 ω)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant) :
    hω.modularConjugation.conjOperator R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra := by
  -- Show `(J₀ R J₀)` commutes with every `R' ∈ M_ω'` on GNS classes `[a]`, using that
  -- `R * (J₀ π(a) J₀) * R'⋆ ∈ M_ω'` and applying `J₀ (S Ω) = S⋆ Ω` for commutant operators `S`.
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom
  rw [← f.gnsVonNeumannAlgebra.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro R' hR'; ext v
  refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  let La := hω.modularConjugation.conjOperator (ρ a)
  have hLa : La ∈ f.gnsVonNeumannAlgebra.commutant :=
    hω.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_mem_commutant a
  have hprod : R * La * star R' ∈ f.gnsVonNeumannAlgebra.commutant :=
    mul_mem (mul_mem hR hLa) (star_mem hR')
  have hcommR' : ρ a * R' = R' * ρ a := f.mem_gnsVonNeumannAlgebra_commutant_iff.mp hR' a
  have h1 : R' (f.toGNS a) = ρ a (R' f.gnsVector) := by
    simpa [ρ, mul_apply_eq_comp, toGNS_apply, gnsVector_def] using
      (congrArg (fun T => T f.gnsVector) hcommR').symm
  have h2 : hω.modularConjugation (R' (f.toGNS a)) = (La * star R') f.gnsVector := by
    rw [h1, mul_apply_eq_comp, ← hω.modularConjugation_apply_gnsVector_of_zero hR']
    simp [La, f, LinearIsometryEquiv.conjOperator_apply]
  simp only [mul_apply_eq_comp, LinearIsometryEquiv.conjOperator_apply, hω.modularConjugation_symm]
  rw [h2, ← mul_apply_eq_comp, ← mul_assoc, hω.modularConjugation_apply_gnsVector_of_zero hprod,
    show star (R * La * star R') = R' * star La * star R by simp [star_mul, mul_assoc]]
  simp only [mul_apply_eq_comp]
  rw [← hω.modularConjugation_apply_gnsVector_of_zero hR,
    show star La = hω.modularConjugation.conjOperator (ρ (star a)) by
      simp only [La, map_star, LinearIsometryEquiv.conjOperator_star]]
  simp only [LinearIsometryEquiv.conjOperator_apply, hω.modularConjugation_symm,
    hω.modularConjugation_modularConjugation]
  have hcommR : ρ (star a) (R f.gnsVector) = R (ρ (star a) f.gnsVector) := by
    simpa [ρ, mul_apply_eq_comp] using
      congrArg (fun T => T f.gnsVector) (f.mem_gnsVonNeumannAlgebra_commutant_iff.mp hR (star a))
  rw [hcommR, show ρ (star a) f.gnsVector = hω.modularConjugation (f.toGNS a) by
    rw [hω.modularConjugation_apply_toGNS_of_zero a]; simp [ρ, f, toGNS_apply, gnsVector_def]]

/-! ### Gaussian smearing of commutant operators and the `β ≠ 0` commutation theorem -/

section Nonzero

private abbrev kmsUnitary (hω : α.IsKMSState β ω) (hβ : β ≠ 0) :
    ContRepresentation ℂ (Multiplicative ℝ) ω.toPositiveLinearMap.GNS :=
  α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a)

private theorem star_kmsUnitary (hω : α.IsKMSState β ω) (hβ : β ≠ 0) (r : ℝ) :
    star (kmsUnitary hω hβ (.ofAdd r)) = kmsUnitary hω hβ (.ofAdd (-r)) := by
  rw [star_eq_adjoint, (α.isUnitary_gnsImplementingGroup _).adjoint_eq_inv, ofAdd_neg]

/-- An analytic family in the GNS commutant for `β ≠ 0`: a locally bounded strongly entire family
(along with its reflected adjoint) in `M_ω'` whose restriction to `ℝ` is conjugation by `U_t`. -/
private structure IsAnalyticCommutantFamily (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    (S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)) : Prop where
  differentiable_apply (v : ω.toPositiveLinearMap.GNS) : Differentiable ℂ fun z => S z v
  differentiable_star_conj_apply (v : ω.toPositiveLinearMap.GNS) :
    Differentiable ℂ fun z => star (S (conj z)) v
  locallyBounded (z₀ : ℂ) : ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖S z‖ ≤ M
  mem_commutant (z : ℂ) : S z ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant
  apply_ofReal (t : ℝ) : S t = kmsUnitary hω hβ (.ofAdd t) * S 0 * kmsUnitary hω hβ (.ofAdd (-t))

/-- Local norm boundedness of the shifted reflected adjoint `z ↦ (S (conj z + w₀))⋆`. -/
private theorem IsAnalyticCommutantFamily.locallyBounded_star_conj_add
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) (w₀ z₀ : ℂ) :
    ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖star (S (conj z + w₀))‖ ≤ M := by
  obtain ⟨r, hr, M, hM⟩ := hS.locallyBounded (conj z₀ + w₀)
  refine ⟨r, hr, M, fun z hz => ?_⟩
  rw [star_eq_adjoint, LinearIsometryEquiv.norm_map]
  exact hM _ (by simpa [Metric.mem_ball, dist_eq_norm, ← map_sub] using hz)

/-- Real time translation of an analytic commutant family conjugates at every complex time. -/
private theorem IsAnalyticCommutantFamily.add_ofReal {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) (w : ℂ) (t : ℝ) :
    S (w + t) = kmsUnitary hω hβ (.ofAdd t) * S w * kmsUnitary hω hβ (.ofAdd (-t)) := by
  let U := kmsUnitary hω hβ; ext v
  refine congrFun (((hS.differentiable_apply v).comp (differentiable_id.add_const (t : ℂ)))
    |>.eq_of_ofReal_eq ((U (.ofAdd t)).differentiable.comp (hS.differentiable_apply _))
      fun s => ?_) w
  have heq : S (s + t : ℝ) = U (.ofAdd t) * S s * U (.ofAdd (-t)) := by
    rw [hS.apply_ofReal (s + t), hS.apply_ofReal s,
      show U (.ofAdd (s + t)) = U (.ofAdd t) * U (.ofAdd s) by rw [add_comm, ofAdd_add, map_mul],
      show U (.ofAdd (-(s + t))) = U (.ofAdd (-s)) * U (.ofAdd (-t)) by
        rw [neg_add, ofAdd_add, map_mul]]; simp only [U, mul_assoc]
  simpa [Complex.ofReal_add, mul_apply_eq_comp] using congrArg (fun X => X v) heq

/-- **Key identity for analytic commutant families:** `J₀ (S 0 Ω) = (S (iβ/2))⋆ Ω`. -/
private theorem IsAnalyticCommutantFamily.modularConjugation_apply_gnsVector
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hS : IsAnalyticCommutantFamily hω hβ S) :
    hω.modularConjugation (S 0 ω.toPositiveLinearMap.gnsVector) =
      (star (S ((β / 2 : ℝ) * I))) ω.toPositiveLinearMap.gnsVector := by
  -- Compare the entire functions `F z = ⟪[a], S(conj z)⋆ Ω⟫` and `G z = ⟪S(0) Ω, [α_{-z}(a⋆)]⟫`:
  -- they agree on `ℝ` by `S(t) = U_t S(0) U_{-t}`, hence everywhere; evaluate at `z = -iβ/2`.
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom; let U := kmsUnitary hω hβ
  have hUΩ (r : ℝ) : U (.ofAdd r) f.gnsVector = f.gnsVector := by simp [U, f, gnsVector_def]
  refine ext_inner_left ℂ fun u => (denseRange_toGNS_entireAnalytic α f).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.property
  let F : ℂ → ℂ := fun z => ⟪f.toGNS (a : A), star (S (conj z)) f.gnsVector⟫_ℂ
  let G : ℂ → ℂ := fun z => ⟪S 0 f.gnsVector, f.toGNS (α.entireExtension (star (a : A)) (-z))⟫_ℂ
  have hF : Differentiable ℂ F := (innerSL ℂ (f.toGNS (a : A))).differentiable.comp
    (hS.differentiable_star_conj_apply f.gnsVector)
  have hG : Differentiable ℂ G := ((innerSL ℂ (S 0 f.gnsVector)).comp f.toGNS).differentiable.comp
    ((differentiable_entireExtension α (star (a : A))).comp differentiable_neg)
  have hFG : F = G := hF.eq_of_ofReal_eq hG fun t => by
    have hTt : star (S (conj (t : ℂ))) = U (.ofAdd t) * star (S 0) * U (.ofAdd (-t)) := by
      simp only [U, Complex.conj_ofReal, hS.apply_ofReal t, star_mul, star_kmsUnitary, neg_neg,
        mul_assoc]
    have hcomm := congrArg (fun X => X f.gnsVector)
      (f.mem_gnsVonNeumannAlgebra_commutant_iff.mp (hS.mem_commutant 0)
        (α (.ofAdd (-t)) (a : A))).symm
    have h1 : ⟪f.toGNS (a : A), U (.ofAdd t) ((star (S 0)) f.gnsVector)⟫_ℂ =
        ⟪U (.ofAdd (-t)) (f.toGNS (a : A)), (star (S 0)) f.gnsVector⟫_ℂ := by
      rw [← star_kmsUnitary hω hβ t]; exact (adjoint_inner_left (U (.ofAdd t)) _ _).symm
    simp only [F, G, hTt, mul_apply_eq_comp, hUΩ]
    rw [h1, star_eq_adjoint, adjoint_inner_right,
      show U (.ofAdd (-t)) (f.toGNS (a : A)) = ρ (α (.ofAdd (-t)) (a : A)) f.gnsVector by
        simp [U, ρ, f, toGNS_apply, gnsVector_def],
      show S 0 (ρ (α (.ofAdd (-t)) (a : A)) f.gnsVector) =
        ρ (α (.ofAdd (-t)) (a : A)) (S 0 f.gnsVector) by simpa [ρ, mul_apply_eq_comp] using hcomm,
      show ⟪ρ (α (.ofAdd (-t)) (a : A)) (S 0 f.gnsVector), f.gnsVector⟫_ℂ =
        ⟪S 0 f.gnsVector, ρ (star (α (.ofAdd (-t)) (a : A))) f.gnsVector⟫_ℂ by
        rw [map_star, star_eq_adjoint, adjoint_inner_right]]
    congr 1; rw [← map_star (α (.ofAdd (-t))) (a : A), ← Complex.ofReal_neg,
      ha.star.entireExtension_ofReal (-t)]; simp [ρ, toGNS_apply, gnsVector_def]
  have heval := congrFun hFG (-((β / 2 : ℝ) * I))
  have hconj : conj (-((β / 2 : ℝ) * I)) = (β / 2 : ℝ) * I := by
    rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  simp only [F, G, hconj, neg_neg] at heval
  rw [← hω.modularConjugation_apply_toGNS ha, hω.inner_modularConjugation_right] at heval
  exact heval.symm

/-- Product of two analytic commutant families. -/
private theorem IsAnalyticCommutantFamily.mul {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {S₁ S₂ : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (h₁ : IsAnalyticCommutantFamily hω hβ S₁) (h₂ : IsAnalyticCommutantFamily hω hβ S₂) :
    IsAnalyticCommutantFamily hω hβ (fun z => S₁ z * S₂ z) where
  differentiable_apply v := by
    simpa only [mul_apply_eq_comp] using differentiable_clm_apply_of_locallyBounded
      h₁.differentiable_apply (h₂.differentiable_apply v) h₁.locallyBounded
  differentiable_star_conj_apply v := by
    have hb2 : ∀ z₀, ∃ r > 0, ∃ M, ∀ z ∈ Metric.ball z₀ r, ‖star (S₂ (conj z))‖ ≤ M :=
      fun z₀ => by simpa only [add_zero] using h₂.locallyBounded_star_conj_add 0 z₀
    simpa only [star_mul, mul_apply_eq_comp] using differentiable_clm_apply_of_locallyBounded
      (fun w => h₂.differentiable_star_conj_apply w) (h₁.differentiable_star_conj_apply v) hb2
  locallyBounded z₀ := by
    obtain ⟨r₁, hr₁, M₁, hM₁⟩ := h₁.locallyBounded z₀
    obtain ⟨r₂, hr₂, M₂, hM₂⟩ := h₂.locallyBounded z₀
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, max M₁ 0 * max M₂ 0, fun z hz =>
      (opNorm_comp_le (S₁ z) (S₂ z)).trans (mul_le_mul
        ((hM₁ z (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _)))).trans
          (le_max_left _ _))
        ((hM₂ z (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _)))).trans
          (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))⟩
  mem_commutant z := mul_mem (h₁.mem_commutant z) (h₂.mem_commutant z)
  apply_ofReal t := by
    let U := kmsUnitary hω hβ
    have hcancel : U (.ofAdd (-t)) * U (.ofAdd t) = 1 := by
      rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
    rw [h₁.apply_ofReal t, h₂.apply_ofReal t]
    calc U (.ofAdd t) * S₁ 0 * U (.ofAdd (-t)) * (U (.ofAdd t) * S₂ 0 * U (.ofAdd (-t)))
        = U (.ofAdd t) * S₁ 0 * (U (.ofAdd (-t)) * U (.ofAdd t)) * S₂ 0 * U (.ofAdd (-t)) := by
          simp only [mul_assoc]
      _ = U (.ofAdd t) * (S₁ 0 * S₂ 0) * U (.ofAdd (-t)) := by
          rw [hcancel, mul_one]; simp [mul_assoc]

/-- Shifted adjoint `z ↦ (R'(conj z + iβ/2))⋆` of an analytic commutant family. -/
private theorem IsAnalyticCommutantFamily.shiftedStar {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {R' : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hR' : IsAnalyticCommutantFamily hω hβ R') :
    IsAnalyticCommutantFamily hω hβ (fun z => star (R' (conj z + (β / 2 : ℝ) * I))) where
  differentiable_apply v := by
    rw [show (fun z : ℂ => star (R' (conj z + (β / 2 : ℝ) * I)) v) =
        fun z => star (R' (conj (z - (β / 2 : ℝ) * I))) v from
      funext fun z => by
        simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_neg_eq_add]]
    exact (hR'.differentiable_star_conj_apply v).comp (differentiable_id.sub_const _)
  differentiable_star_conj_apply v := by
    rw [show (fun z : ℂ => star (star (R' (conj (conj z) + (β / 2 : ℝ) * I))) v) =
        fun z => R' (z + (β / 2 : ℝ) * I) v from funext fun z => by simp]
    exact (hR'.differentiable_apply v).comp (differentiable_id.add_const _)
  locallyBounded z₀ := hR'.locallyBounded_star_conj_add ((β / 2 : ℝ) * I) z₀
  mem_commutant _ := star_mem (hR'.mem_commutant _)
  apply_ofReal t := by
    rw [Complex.conj_ofReal, add_comm (t : ℂ), hR'.add_ofReal ((β / 2 : ℝ) * I) t, star_mul,
      star_mul, star_kmsUnitary, star_kmsUnitary, neg_neg, map_zero, zero_add]; simp [mul_assoc]

/-- The right-multiplication analytic commutant family `z ↦ J₀ π_ω(α_{conj z}(a)) J₀` for
an entire analytic element `a`. -/
private theorem isAnalyticCommutantFamily_rightMul (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {a : A} (ha : α.IsEntireAnalytic a) :
    IsAnalyticCommutantFamily hω hβ
      (fun z => hω.modularConjugation.conjOperator
        (ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom (α.entireExtension a (conj z)))) := by
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom; let U := kmsUnitary hω hβ
  let Φ : (f.GNS →L[ℂ] f.GNS) →L[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    hω.modularConjugation.conjOperator.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (starL ℂ : (f.GNS →L[ℂ] f.GNS) ≃L⋆[ℂ] (f.GNS →L[ℂ] f.GNS)).toContinuousLinearMap
  let ρL : A →L[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    ⟨{ toFun := ρ, map_add' := map_add ρ, map_smul' := map_smul ρ }, map_continuous ρ⟩
  have hΦρ (x : A) : Φ (ρL x) = hω.modularConjugation.conjOperator (star (ρ x)) := by
    simp [Φ, ρL]
  have hdiff : Differentiable ℂ fun z : ℂ =>
      hω.modularConjugation.conjOperator (ρ (α.entireExtension a (conj z))) := by
    rw [show (fun z : ℂ => hω.modularConjugation.conjOperator (ρ (α.entireExtension a (conj z)))) =
        fun z => Φ (ρL (α.entireExtension (star a) z)) from funext fun z => by
      rw [hΦρ, ← map_star, entireExtension_star, star_star]]
    exact (Φ.comp ρL).differentiable.comp (differentiable_entireExtension α (star a))
  refine ⟨fun v => (ContinuousLinearMap.apply ℂ f.GNS v).differentiable.comp hdiff,
    fun v => ?_, fun z₀ => ?_,
    fun _ => hω.conjOperator_modularConjugation_gnsNonUnitalStarAlgHom_mem_commutant _,
    fun t => ?_⟩
  · rw [show (fun z : ℂ => star (hω.modularConjugation.conjOperator
        (ρ (α.entireExtension a (conj (conj z))))) v) =
        fun z => Φ (ρL (α.entireExtension a z)) v from funext fun z => by
      rw [hΦρ, conj_conj, LinearIsometryEquiv.conjOperator_star]]
    exact ((ContinuousLinearMap.apply ℂ f.GNS v).comp (Φ.comp ρL)).differentiable.comp
      (differentiable_entireExtension α a)
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
      ((hdiff.continuous.norm.continuousAt (x := z₀)).eventually (gt_mem_nhds (lt_add_one _)))
    exact ⟨r, hr, ‖hω.modularConjugation.conjOperator (ρ (α.entireExtension a (conj z₀)))‖ + 1,
      fun _ hz => (hball hz).le⟩
  · rw [Complex.conj_ofReal, ha.entireExtension_ofReal t, map_zero, ha.entireExtension_apply_zero]
    have hcov : ρ (α (.ofAdd t) a) = U (.ofAdd t) * ρ a * U (.ofAdd (-t)) := by
      simpa [U, ρ, ofAdd_neg] using
        (α.gnsCovariantRepresentation (fun s x => hω.apply_action hβ s x)).coefficient_action
          (.ofAdd t) a
    have hUconj (r : ℝ) : hω.modularConjugation.conjOperator (U (.ofAdd r)) = U (.ofAdd r) := by
      ext v
      simp [LinearIsometryEquiv.conjOperator_apply, hω.modularConjugation_symm, U,
        hω.modularConjugation_gnsImplementingGroup hβ]
    rw [hcov, LinearIsometryEquiv.conjOperator_mul, LinearIsometryEquiv.conjOperator_mul,
      hUconj, hUconj]

/-- Gaussian smearing of a commutant operator `R ∈ M_ω'` produces an analytic commutant family. -/
private theorem isAnalyticCommutantFamily_smearOp (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant) (c : ℝ) :
    IsAnalyticCommutantFamily hω hβ
      ((α.isUnitary_gnsImplementingGroup (fun s a => hω.apply_action hβ s a)).gaussianSmear
        (α.continuous_gnsImplementingGroup_apply (fun s a => hω.apply_action hβ s a)) R c) := by
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom
  have hU := α.isUnitary_gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
  have hcont := α.continuous_gnsImplementingGroup_apply (fun s a => hω.apply_action hβ s a)
  refine ⟨hU.differentiable_gaussianSmear_apply hcont R c, fun v => ?_,
    hU.locallyBounded_gaussianSmear hcont R c, ?_, hU.gaussianSmear_ofReal hcont R c⟩
  · simp only [hU.star_gaussianSmear_conj hcont R c]
    exact hU.differentiable_gaussianSmear_apply hcont (star R) c v
  · intro z
    refine f.mem_gnsVonNeumannAlgebra_commutant_iff.mpr fun a => ?_
    refine hU.commute_gaussianSmear_of_commute hcont (fun t => ?_) c z
    have hcov (r : ℝ) (x : A) :
        α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd r) * ρ x =
          ρ (α (.ofAdd r) x) *
            α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd r) := by
      ext w; simpa [ρ, mul_apply_eq_comp] using (α.gnsCovariantRepresentation
        (fun s a => hω.apply_action hβ s a)).covariance (.ofAdd r) x w
    have h1 : ρ a * α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd t) =
        α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd t) *
          ρ (α (.ofAdd (-t)) a) := by
      simpa [← CStarAction.mul_apply, ← ofAdd_add] using (hcov t (α (.ofAdd (-t)) a)).symm
    have hRa := f.mem_gnsVonNeumannAlgebra_commutant_iff.mp hR (α (.ofAdd (-t)) a)
    rw [show ρ a * (α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd t) * R *
        α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd (-t))) =
        (ρ a * α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd t)) * R *
          α.gnsImplementingGroup (fun s y => hω.apply_action hβ s y) (.ofAdd (-t)) by
        simp only [mul_assoc],
      h1, mul_assoc _ (ρ (α (.ofAdd (-t)) a)) R, hRa,
      ← mul_assoc (α.gnsImplementingGroup _ (.ofAdd t)) R _,
      mul_assoc (α.gnsImplementingGroup _ (.ofAdd t) * R) (ρ (α (.ofAdd (-t)) a)) _,
      ← hcov (-t) a]
    simp only [ρ, mul_assoc]

/-- For two analytic commutant families `R, R'`, `J₀ (R 0) J₀` commutes with `R' 0`. -/
private theorem commute_conjOperator_modularConjugation_of_isAnalyticCommutantFamily
    {hω : α.IsKMSState β ω} {hβ : β ≠ 0}
    {R R' : ℂ → (ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)}
    (hR : IsAnalyticCommutantFamily hω hβ R) (hR' : IsAnalyticCommutantFamily hω hβ R') :
    hω.modularConjugation.conjOperator (R 0) * R' 0 =
      R' 0 * hω.modularConjugation.conjOperator (R 0) := by
  -- Apply `IsAnalyticCommutantFamily.modularConjugation_apply_gnsVector` to the product family
  -- `z ↦ R z * (J₀ π(α_{conj z}(a)) J₀) * R'(conj z + iβ/2)⋆` and match both sides on `[a]`.
  let f := ω.toPositiveLinearMap; let ρ := f.gnsNonUnitalStarAlgHom; ext v
  refine (denseRange_toGNS_entireAnalytic α f).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.property
  let La : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z =>
    hω.modularConjugation.conjOperator (ρ (α.entireExtension (a : A) (conj z)))
  let S' : ℂ → (f.GNS →L[ℂ] f.GNS) := fun z => star (R' (conj z + (β / 2 : ℝ) * I))
  have hkey := ((hR.mul (isAnalyticCommutantFamily_rightMul hω hβ ha)).mul
    hR'.shiftedStar).modularConjugation_apply_gnsVector
  have hlhs : hω.modularConjugation ((R 0 * La 0 * S' 0) f.gnsVector) =
      (hω.modularConjugation.conjOperator (R 0) * R' 0) (f.toGNS (a : A)) := by
    have hS'0 : S' 0 f.gnsVector = hω.modularConjugation (R' 0 f.gnsVector) := by
      simpa only [S', map_zero, zero_add] using hR'.modularConjugation_apply_gnsVector.symm
    have hcommR' : ρ (a : A) (R' 0 f.gnsVector) = R' 0 (f.toGNS (a : A)) := by
      simpa [ρ, mul_apply_eq_comp, toGNS_apply, gnsVector_def] using
        congrArg (fun X => X f.gnsVector)
          (f.mem_gnsVonNeumannAlgebra_commutant_iff.mp (hR'.mem_commutant 0) (a : A))
    have hLa0 : La 0 = hω.modularConjugation.conjOperator (ρ (a : A)) := by
      simp [La, ha.entireExtension_apply_zero]
    simp only [mul_apply_eq_comp, hS'0, hLa0, LinearIsometryEquiv.conjOperator_apply,
      hω.modularConjugation_symm, hω.modularConjugation_modularConjugation, hcommR']
  have hrhs : (star (R ((β / 2 : ℝ) * I) * La ((β / 2 : ℝ) * I) * S' ((β / 2 : ℝ) * I)))
      f.gnsVector = (R' 0 * hω.modularConjugation.conjOperator (R 0)) (f.toGNS (a : A)) := by
    have hS'val : star (S' ((β / 2 : ℝ) * I)) = R' 0 := by
      simp only [S', star_star, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        neg_add_cancel]
    have hLaval : star (La ((β / 2 : ℝ) * I)) =
        hω.modularConjugation.conjOperator
          (ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I))) := by
      simp only [La, ← LinearIsometryEquiv.conjOperator_star, ← map_star]
      congr 2; rw [entireExtension_star]
    have hcommR : ρ (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)) (R 0 f.gnsVector) =
        R 0 (hω.modularConjugation (f.toGNS (a : A))) := by
      rw [hω.modularConjugation_apply_toGNS ha]
      simpa [ρ, mul_apply_eq_comp, toGNS_apply, gnsVector_def] using
        congrArg (fun X => X f.gnsVector)
          (f.mem_gnsVonNeumannAlgebra_commutant_iff.mp (hR.mem_commutant 0)
            (α.entireExtension (star (a : A)) ((β / 2 : ℝ) * I)))
    rw [star_mul, star_mul, hS'val, hLaval, mul_apply_eq_comp, mul_apply_eq_comp,
      hR.modularConjugation_apply_gnsVector.symm, LinearIsometryEquiv.conjOperator_apply,
      hω.modularConjugation_symm, hω.modularConjugation_modularConjugation, hcommR]
    simp only [mul_apply_eq_comp, LinearIsometryEquiv.conjOperator_apply,
      hω.modularConjugation_symm]
  rw [← hlhs, ← hrhs]; exact hkey

/-- For `β ≠ 0`, any operator `R ∈ M_ω'` commuting with the GNS implementing unitary group
satisfies `J₀ (R Ω) = R⋆ Ω`. -/
theorem IsKMSState.modularConjugation_apply_gnsVector_of_commute (hω : α.IsKMSState β ω)
    (hβ : β ≠ 0) {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant)
    (hcomm : ∀ t : Multiplicative ℝ,
      α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t * R =
        R * α.gnsImplementingGroup (fun s a => hω.apply_action hβ s a) t) :
    hω.modularConjugation (R ω.toPositiveLinearMap.gnsVector) =
      (star R) ω.toPositiveLinearMap.gnsVector :=
  IsAnalyticCommutantFamily.modularConjugation_apply_gnsVector (hβ := hβ)
    ⟨fun _ => differentiable_const _, fun _ => differentiable_const _,
      fun _ => ⟨1, one_pos, ‖R‖, fun _ _ => le_rfl⟩, fun _ => hR, fun t => by
        rw [hcomm (.ofAdd t), mul_assoc, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero,
          map_one, mul_one]⟩

/-- Tomita commutation for `β ≠ 0`: `J₀ R J₀ ∈ M_ω` for every `R ∈ M_ω'`. -/
private theorem conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra_of_ne_zero
    (hω : α.IsKMSState β ω) (hβ : β ≠ 0)
    {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant) :
    hω.modularConjugation.conjOperator R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra := by
  let f := ω.toPositiveLinearMap
  have hU := α.isUnitary_gnsImplementingGroup (fun s a => hω.apply_action hβ s a)
  have hcont := α.continuous_gnsImplementingGroup_apply (fun s a => hω.apply_action hβ s a)
  rw [← f.gnsVonNeumannAlgebra.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro R' hR'
  have hstep1 (c : ℝ) :
      hω.modularConjugation.conjOperator (hU.gaussianSmear hcont R c 0) * R' =
        R' * hω.modularConjugation.conjOperator (hU.gaussianSmear hcont R c 0) := by
    ext v; set T := hω.modularConjugation.conjOperator (hU.gaussianSmear hcont R c 0)
    refine tendsto_nhds_unique (((T.continuous.tendsto _).comp
      (hU.tendsto_gaussianSmear_apply hcont R' v)).congr fun c' => ?_)
      (hU.tendsto_gaussianSmear_apply hcont R' (T v))
    simpa [T, mul_apply_eq_comp] using congrArg (fun X => X v)
      (commute_conjOperator_modularConjugation_of_isAnalyticCommutantFamily
        (isAnalyticCommutantFamily_smearOp hω hβ hR c)
        (isAnalyticCommutantFamily_smearOp hω hβ hR' c'))
  ext v
  simp only [mul_apply_eq_comp, LinearIsometryEquiv.conjOperator_apply, hω.modularConjugation_symm]
  refine (tendsto_nhds_unique
    (((hω.modularConjugation.continuous.tendsto _).comp
        (hU.tendsto_gaussianSmear_apply hcont R (hω.modularConjugation (R' v)))).congr
      fun c => ?_)
    ((R'.continuous.tendsto _).comp ((hω.modularConjugation.continuous.tendsto _).comp
      (hU.tendsto_gaussianSmear_apply hcont R (hω.modularConjugation v))))).symm
  simpa [mul_apply_eq_comp, LinearIsometryEquiv.conjOperator_apply,
    hω.modularConjugation_symm] using congrArg (fun X => X v) (hstep1 c)

end Nonzero

/-! ### Tomita commutation for all `β` -/

/-- **Tomita commutation for KMS states (`J₀ M' J₀ ⊆ M`).** For every real `β`
(including `β = 0`), conjugating any operator in the commutant `M_ω'` by the modular conjugation
`J₀` yields an operator in the GNS von Neumann algebra `M_ω = π_ω(A)''`. -/
theorem IsKMSState.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra
    (hω : α.IsKMSState β ω) {R : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hR : R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant) :
    hω.modularConjugation.conjOperator R ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra := by
  rcases eq_or_ne β 0 with rfl | hβ
  · exact conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra_of_zero hω hR
  · exact conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra_of_ne_zero hω hβ hR

/-- Conjugation by `J₀` sends an operator into `M_ω` if and only if it lies in `M_ω'`. -/
theorem IsKMSState.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra_iff
    (hω : α.IsKMSState β ω) {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS} :
    hω.modularConjugation.conjOperator T ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra ↔
      T ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant :=
  ⟨fun h => by
    have h1 := hω.conjOperator_modularConjugation_mem_commutant h
    have hinvol : hω.modularConjugation.conjOperator (hω.modularConjugation.conjOperator T) =
        T := by
      simpa only [LinearIsometryEquiv.conjOperator_symm, hω.modularConjugation_symm] using
        hω.modularConjugation.conjOperator.symm_apply_apply T
    rwa [hinvol] at h1,
    hω.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra⟩

/-- Conjugation by `J₀` sends an operator into `M_ω'` if and only if it lies in `M_ω`. -/
theorem IsKMSState.conjOperator_modularConjugation_mem_commutant_iff
    (hω : α.IsKMSState β ω) {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS} :
    hω.modularConjugation.conjOperator T ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant ↔
      T ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra :=
  ⟨fun h => by
    have h1 := hω.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra h
    have hinvol : hω.modularConjugation.conjOperator (hω.modularConjugation.conjOperator T) =
        T := by
      simpa only [LinearIsometryEquiv.conjOperator_symm, hω.modularConjugation_symm] using
        hω.modularConjugation.conjOperator.symm_apply_apply T
    rwa [hinvol] at h1,
    hω.conjOperator_modularConjugation_mem_commutant⟩

end TauCeti.CStarAction
