/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EvolutionOperator.Invertible
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.SMul

/-!
# Invertibility of the stationary Floer cylinder operator

Let `F` be a finite-dimensional complex inner product space with standard complex structure
`J₀ = I`, Euclidean inner product `Re ⟪·, ·⟫`, and symplectic form `ω₀ = Im ⟪·, ·⟫`, and let
`S : AddCircle T → (F →L[ℝ] F)` be a continuous loop of infinitesimally symplectic real-linear
maps, `ω₀(S_t v, w) + ω₀(v, S_t w) = 0`. Its asymptotic operator
`A = J₀ (d/dt - S_t) = I • CircleSobolev.loopOperator T S : H¹(F) →L[ℝ] H⁰(F)` is symmetric with
respect to the compact Sobolev inclusion `ι : H¹(F) →L[ℝ] H⁰(F)`
(`CircleSobolev.real_inner_I_smul_loopOperator_comm`).

This file applies the abstract stationary evolution theory of
`TauCeti.Analysis.ODE.EvolutionOperator.Invertible` to the stationary linearized Floer cylinder
operator

`∂s + J₀ (∂t - S_t) : L²(ℝ; H¹(F)) ∩ W^{1,2}(ℝ; H⁰(F)) → L²(ℝ; H⁰(F))`

realized by `WeakDerivStep.stationaryEvolutionOperator ι (I • loopOperator T S)`:

* **Pythagorean energy identity**:
  `CircleSobolev.norm_weakFDeriv_sq_add_norm_compLp_sq_eq_I_smul_loopOperator` proves
  `‖∂s u‖² + ‖A u‖² = ‖(∂s + A) u‖²` for every continuous infinitesimally symplectic loop `S`
  (without assuming nondegeneracy).
* **Invertibility and sharp inverse bound**:
  `CircleSobolev.isInvertible_stationaryEvolutionOperator_I_smul_loopOperator`,
  `CircleSobolev.isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_of_forall_eq_zero`,
  `CircleSobolev.isInvertible_stationaryEvolutionOperator_neg_I_smul_loopOperator`, and
  `CircleSobolev.norm_inverse_stationaryEvolutionOperator_I_smul_loopOperator_le` establish
  invertibility of both `∂s + J₀ (∂t - S_t)` and `∂s - J₀ (∂t - S_t)` whenever `ζ' = S ζ` has no
  nonzero `T`-periodic solution, with inverse operator norm bounded by
  `max ‖(loopOperator T S).inverse‖ 1`.
* **Compact families and weighted perturbations**:
  `CircleSobolev.exists_pos_isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_sub_smul`
  gives a common positive radius `ε` and uniform inverse norm bound `C` for
  `∂s + J₀ (∂t - (S p - δ • J p))` over `p ∈ K` and `|δ| ≤ ε`, covering both loop perturbations
  and exponentially weighted cylinder operators (`J p = const J₀`, via
  `I_smul_loopOperator_sub_smul_const_I_id`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (invertibility of `∂_s + J₀ ∂_t + S` on the cylinder at a
  nondegenerate orbit).
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

/-- **Pythagorean energy identity for the stationary Floer cylinder operator.**
At any continuous infinitesimally symplectic loop `S` (not necessarily nondegenerate), every
`u ∈ L²(ℝ; H¹(F)) ∩ W^{1,2}(ℝ; H⁰(F))` satisfies `‖∂s u‖² + ‖A u‖² = ‖(∂s + A) u‖²`
where `A = I • loopOperator T S`. -/
theorem norm_weakFDeriv_sq_add_norm_compLp_sq_eq_I_smul_loopOperator
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
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨δ, hδ⟩ := exists_isInvertible_loopOperator_sub_smul_const_I_id T S hS
  set S' : C(AddCircle T, F →L[ℝ] F) :=
    S - δ • ContinuousMap.const _ (I • ContinuousLinearMap.id ℝ F) with hS'_def
  have hS' : ∀ t v w, (inner ℂ (S' t v) w).im + (inner ℂ v (S' t w)).im = 0 := by
    intro t v w
    have hI : (inner ℂ (I • v) w).im + (inner ℂ v (I • w)).im = 0 := by
      rw [inner_smul_left, inner_smul_right, Complex.conj_I]
      simp [Complex.mul_im]
    have hsub : S' t v = S t v - (δ : ℂ) • (I • v) := by
      simp [hS'_def, Complex.coe_smul]
    have hsub' : S' t w = S t w - (δ : ℂ) • (I • w) := by
      simp [hS'_def, Complex.coe_smul]
    rw [hsub, hsub', inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    simp only [Complex.conj_ofReal, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    calc (inner ℂ (S t v) w).im - δ * (inner ℂ (I • v) w).im +
          ((inner ℂ v (S t w)).im - δ * (inner ℂ v (I • w)).im)
        = ((inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im) -
          δ * ((inner ℂ (I • v) w).im + (inner ℂ v (I • w)).im) := by ring
      _ = 0 := by rw [hS t v w, hI, mul_zero, sub_zero]
  obtain ⟨s, b, a, lam, _, _, hprop⟩ :=
    exists_hilbertBasis_I_smul_loopOperator_eq_smul T S' hS' hδ
  have haι : ∀ i : s, ((inclusion (E := F) zero_le_one).restrictScalars ℝ) (a i) = b i :=
    fun i ↦ (hprop i).1
  have haA : ∀ i : s, (I • loopOperator T S) (a i) = (lam i + δ) • b i := by
    intro i
    have hshift := congrArg (fun L ↦ L (a i)) (I_smul_loopOperator_sub_smul_const_I_id T S δ)
    have hAi : (I • loopOperator T S) (a i) - δ • b i = lam i • b i := by
      simpa only [← hS'_def, sub_apply, smul_apply, ContinuousLinearMap.coe_restrictScalars',
        (hprop i).1] using hshift.symm.trans (hprop i).2.2
    rw [add_smul, ← hAi, sub_add_cancel]
  exact norm_weakFDeriv_sq_add_norm_compLp_sq_eq_of_hilbertBasis b a (fun i ↦ lam i + δ)
    (fun x y ↦ real_inner_I_smul_loopOperator_comm T S hS x y) haι haA u

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
      (I • loopOperator T S)).IsInvertible := by
  have := FiniteDimensional.completeSpace ℂ F
  exact isInvertible_stationaryEvolutionOperator_of_isCompactOperator
    (isCompactOperator_inclusion (E := F) zero_lt_one)
    (inclusion_injective (E := F) zero_le_one)
    (fun a b ↦ real_inner_I_smul_loopOperator_comm T S hS a b)
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
Follows from `isInvertible_stationaryEvolutionOperator_I_smul_loopOperator` by time reflection
`s ↦ -s`. -/
theorem isInvertible_stationaryEvolutionOperator_neg_I_smul_loopOperator
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    (stationaryEvolutionOperator (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ)
      (-(I • loopOperator T S))).IsInvertible := by
  have := FiniteDimensional.completeSpace ℂ F
  exact isInvertible_stationaryEvolutionOperator_neg_of_isCompactOperator
    (isCompactOperator_inclusion (E := F) zero_lt_one)
    (inclusion_injective (E := F) zero_le_one)
    (fun a b ↦ real_inner_I_smul_loopOperator_comm T S hS a b)
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
  have := FiniteDimensional.completeSpace ℂ F
  simpa only [ContinuousLinearMap.norm_inverse_smul, norm_I, inv_one, one_mul] using
    norm_inverse_stationaryEvolutionOperator_le_of_isCompactOperator
      (isCompactOperator_inclusion (E := F) zero_lt_one)
      (inclusion_injective (E := F) zero_le_one)
      (fun a b ↦ real_inner_I_smul_loopOperator_comm T S hS a b)
      ((ContinuousLinearMap.isInvertible_smul_iff I_ne_zero).mpr hL)

/-- **Uniform cylinder invertibility on a compact family with small loop perturbations.**
On a compact parameter set `K` where `S p` and `J p` vary continuously and each `S p` is
infinitesimally symplectic and nondegenerate, the perturbed stationary cylinder operators
`∂s + J₀ (∂t - (S p - δ • J p))` are invertible with uniformly bounded inverses for all `p ∈ K`
and `|δ| ≤ ε`. Setting `J p = const J₀` recovers uniform invertibility of exponentially weighted
cylinder operators `∂s + A_p - δ ι` via `I_smul_loopOperator_sub_smul_const_I_id`. -/
theorem exists_pos_isInvertible_stationaryEvolutionOperator_I_smul_loopOperator_sub_smul
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
  have := FiniteDimensional.completeSpace ℂ F
  let A : P → CircleSobolev 1 F →L[ℝ] CircleSobolev 0 F := fun p ↦ I • loopOperator T (S p)
  let B : P → CircleSobolev 1 F →L[ℝ] CircleSobolev 0 F :=
    fun p ↦ -(I • mulLoop T (by norm_num) (J p))
  have hAB (p : P) (δ : ℝ) : A p - δ • B p = I • loopOperator T (S p - δ • J p) := by
    simp only [A, B, loopOperator_sub, mulLoop_smul, smul_add, smul_neg, sub_neg_eq_add,
      smul_comm I δ]
  have hAcont : ContinuousOn A K :=
    ((continuous_const_smul I).comp (continuous_loopOperator T)).comp_continuousOn hScont
  have hBcont : ContinuousOn B K :=
    (((continuous_const_smul I).comp (continuous_mulLoop T (by norm_num))).neg).comp_continuousOn
      hJcont
  obtain ⟨ε, hε, C, hC, hbound⟩ :=
    exists_pos_isInvertible_stationaryEvolutionOperator_sub_smul_norm_inverse_le
      (mu := volume) (Omega := ⊤) (p := 2)
      ((inclusion (E := F) zero_le_one).restrictScalars ℝ) hK A B hAcont hBcont
      (fun p hp ↦ isInvertible_stationaryEvolutionOperator_I_smul_loopOperator T (S p) (hS p hp)
        (hinv p hp))
  refine ⟨ε, hε, C, hC, fun p hp δ hδ ↦ ?_⟩
  simpa only [hAB p δ] using hbound p hp δ hδ

end InnerProductSpace

end TauCeti.CircleSobolev
