/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EvolutionOperator.Invertible
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Invertibility of the stationary Floer cylinder operator

Let `F` be a finite-dimensional complex inner product space with complex structure `J₀ = I` and
symplectic form `ω₀ = Im ⟪·, ·⟫`, and let `S : AddCircle T → (F →L[ℝ] F)` be a continuous loop of
infinitesimally symplectic maps (`ω₀(S_t v, w) + ω₀(v, S_t w) = 0`). Applying
`TauCeti.Analysis.ODE.EvolutionOperator.Invertible` to `A = I • CircleSobolev.loopOperator T S`
yields the stationary Floer cylinder theory on `L²(ℝ; H¹(F)) ∩ W^{1,2}(ℝ; H⁰(F)) → L²(ℝ; H⁰(F))`:

* Pythagorean energy identity `‖∂s u‖² + ‖A u‖² = ‖(∂s + A) u‖²` without nondegeneracy:
  `norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_I_smul_loopOperator_sq`
* `isInvertible_stationaryEvolutionOperator_I_smul_loopOperator`,
  `isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_of_forall_eq_zero`,
  `isInvertible_stationaryEvolutionOperator_neg_I_smul_loopOperator`,
  `norm_inverse_stationaryEvolutionOperator_I_smul_loopOperator_le`: invertibility of
  `∂s ± J₀ (∂t - S_t)` at nondegenerate orbits and sharp inverse norm bound
  `max ‖(loopOperator T S).inverse‖ 1`.
* Uniform invertibility and inverse bounds for `∂s + J₀ (∂t - (S p - δ • J p))` on compact families:
  `exists_pos_isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_sub_smul_norm_inverse_le`

## References

* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. 7 (1999), Lecture 2.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

noncomputable section

open Complex MeasureTheory TopologicalSpace TauCeti.WeakDerivStep

namespace TauCeti.CircleSobolev

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  (T : ℝ) [Fact (0 < T)]

local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **Pythagorean energy identity for the stationary Floer cylinder operator.**
At any continuous infinitesimally symplectic loop `S` (not necessarily nondegenerate), every
`u ∈ L²(ℝ; H¹(F)) ∩ W^{1,2}(ℝ; H⁰(F))` satisfies `‖∂s u‖² + ‖A u‖² = ‖(∂s + A) u‖²`
where `A = I • loopOperator T S`. -/
theorem
  norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_I_smul_loopOperator_sq
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (u : WeakDerivStep volume ⊤ 2
      (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) :
    ‖weakFDeriv (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u‖ ^ 2 +
      ‖(I • loopOperator T S).compLp
        (prev (((inclusion (E := F) zero_le_one).restrictScalars ℝ).compLpL 2
          (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) u)‖ ^ 2 =
      ‖stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
        ((inclusion (E := F) zero_le_one).restrictScalars ℝ) (I • loopOperator T S) u‖ ^ 2 := by
  obtain ⟨δ, hδ⟩ := exists_isInvertible_loopOperator_sub_smul_const_I_id T S hS
  set S' : C(AddCircle T, F →L[ℝ] F) :=
    S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ F) with hS'_def
  have hS' : ∀ t v w, (inner ℂ (S' t v) w).im + (inner ℂ v (S' t w)).im = 0 := fun t v w ↦ by
    simp only [hS'_def, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.const_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, inner_sub_right, Complex.sub_im, ← Complex.coe_smul, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    linarith [hS t v w]
  obtain ⟨_, b, a, lam, _, _, hprop⟩ :=
    exists_hilbertBasis_I_smul_loopOperator_eq_smul T S' hS' hδ
  refine
    norm_weakFDeriv_sq_add_norm_compLp_sq_eq_norm_stationaryEvolutionOperator_sq_of_hilbertBasis
      b a (fun i ↦ lam i + δ) (real_inner_I_smul_loopOperator_comm T S hS) (fun i ↦ (hprop i).1)
      (fun i ↦ ?_) u
  have hshift := congrArg (fun L ↦ L (a i)) (I_smul_loopOperator_sub_smul_const_I_id T S δ)
  have hAi : (I • loopOperator T S) (a i) - δ • b i = lam i • b i := by
    simpa only [← hS'_def, sub_apply, smul_apply, ContinuousLinearMap.coe_restrictScalars',
      (hprop i).1] using hshift.symm.trans (hprop i).2.2
  rw [add_smul, ← hAi, sub_add_cancel]

/-- **Invertibility of the stationary Floer cylinder operator `∂s + J₀ (∂t - S_t)`.**
If `S` is a continuous loop of infinitesimally symplectic real-linear maps on `F` and
`loopOperator T S` is invertible, then `∂s + I • loopOperator T S` is invertible from
`L²(ℝ; H¹(F)) ∩ W^{1,2}(ℝ; H⁰(F))` to `L²(ℝ; H⁰(F))`. -/
theorem isInvertible_stationaryEvolutionOperator_I_smul_loopOperator
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (I • loopOperator T S)).IsInvertible :=
  isInvertible_stationaryEvolutionOperator_of_isCompactOperator
    (isCompactOperator_inclusion (E := F) zero_lt_one)
    (inclusion_injective (E := F) zero_le_one)
    (real_inner_I_smul_loopOperator_comm T S hS)
    ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).mpr hL)

/-- **Invertibility of `∂s + J₀ (∂t - S_t)` at a nondegenerate periodic orbit.**
If `S` is infinitesimally symplectic and `ζ' = S ζ` has no nonzero `T`-periodic solution, then
the stationary Floer cylinder operator `∂s + I • loopOperator T S` is invertible. -/
theorem isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_of_forall_eq_zero
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hper : ∀ ζ : C(AddCircle T, F),
      (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ) (I • loopOperator T S)).IsInvertible :=
  isInvertible_stationaryEvolutionOperator_I_smul_loopOperator T S hS
    ((isInvertible_loopOperator_iff T S).mpr hper)

/-- **Invertibility of the opposite-sign stationary Floer cylinder operator `∂s - J₀ (∂t - S_t)`.**
If `S` is a continuous loop of infinitesimally symplectic real-linear maps on `F` and
`loopOperator T S` is invertible, then `∂s - I • loopOperator T S` is invertible from
`L²(ℝ; H¹(F)) ∩ W^{1,2}(ℝ; H⁰(F))` to `L²(ℝ; H⁰(F))`. -/
theorem isInvertible_stationaryEvolutionOperator_neg_I_smul_loopOperator
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (-(I • loopOperator T S))).IsInvertible :=
  isInvertible_stationaryEvolutionOperator_neg_of_isCompactOperator
    (isCompactOperator_inclusion (E := F) zero_lt_one)
    (inclusion_injective (E := F) zero_le_one)
    (real_inner_I_smul_loopOperator_comm T S hS)
    ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).mpr hL)

/-- **Sharp inverse norm bound for the stationary Floer cylinder operator.**
At a nondegenerate infinitesimally symplectic loop `S`, the inverse of `∂s + I • loopOperator T S`
has operator norm at most `max ‖(loopOperator T S).inverse‖ 1`. -/
theorem norm_inverse_stationaryEvolutionOperator_I_smul_loopOperator_le
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ) (I • loopOperator T S)).inverse‖ ≤
      max ‖(loopOperator T S).inverse‖ 1 := by
  simpa only [ContinuousLinearMap.norm_inverse_smul, norm_I, inv_one, one_mul] using
    norm_inverse_stationaryEvolutionOperator_le_of_isCompactOperator
      (ι := (inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (isCompactOperator_inclusion (E := F) zero_lt_one)
      (inclusion_injective (E := F) zero_le_one)
      (real_inner_I_smul_loopOperator_comm T S hS)
      ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).mpr hL)

/-- **Uniform cylinder invertibility on a compact family with small loop perturbations.**
On a compact parameter set `K` where `S p` and `J p` vary continuously and each `S p` is
infinitesimally symplectic and nondegenerate, `∂s + J₀ (∂t - (S p - δ • J p))` is invertible with
uniformly bounded inverse for all `p ∈ K` and `|δ| ≤ ε`. -/
theorem
  exists_pos_isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_sub_smul_norm_inverse_le
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, F →L[ℝ] F))
    (hScont : ContinuousOn S K) (hJcont : ContinuousOn J K)
    (hS : ∀ p ∈ K, ∀ t v w, (inner ℂ (S p t v) w).im + (inner ℂ v (S p t w)).im = 0)
    (hinv : ∀ p ∈ K, (loopOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
          ((inclusion (E := F) zero_le_one).restrictScalars ℝ)
          (I • loopOperator T (S p - δ • J p))).IsInvertible ∧
        ‖(stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
          ((inclusion (E := F) zero_le_one).restrictScalars ℝ)
          (I • loopOperator T (S p - δ • J p))).inverse‖ ≤ C := by
  let A : P → CircleSobolev 1 F →L[ℝ] CircleSobolev 0 F := fun p ↦ I • loopOperator T (S p)
  let B : P → CircleSobolev 1 F →L[ℝ] CircleSobolev 0 F :=
    fun p ↦ -(I • mulLoop T (by norm_num) (J p))
  have hAB (p : P) (δ : ℝ) : A p - δ • B p = I • loopOperator T (S p - δ • J p) := by
    simp only [A, B, loopOperator_sub, mulLoop_smul, smul_add, smul_neg, sub_neg_eq_add,
      smul_comm I δ]
  obtain ⟨ε, hε, C, hC, hbound⟩ :=
    exists_pos_isInvertible_stationaryEvolutionOperator_sub_smul_norm_inverse_le
      (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ) hK A B
      (((continuous_const_smul I).comp (continuous_loopOperator T)).comp_continuousOn hScont)
      ((((continuous_const_smul I).comp (continuous_mulLoop T (by norm_num))).neg).comp_continuousOn
        hJcont)
      (fun p hp ↦ isInvertible_stationaryEvolutionOperator_I_smul_loopOperator T (S p) (hS p hp)
        (hinv p hp))
  exact ⟨ε, hε, C, hC, fun p hp δ hδ ↦ by simpa only [hAB p δ] using hbound p hp δ hδ⟩

end InnerProductSpace

end TauCeti.CircleSobolev
