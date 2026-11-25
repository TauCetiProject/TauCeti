/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.TaylorSeries
import TauCeti.Analysis.Calculus.FDeriv.Analytic
import TauCeti.Analysis.Calculus.FDeriv.Matrix
import TauCeti.Analysis.Complex.Taylor.Basic
import TauCeti.Analysis.ODE.Complex.LinearSystem

/-!
# Scalar complex linear differential equations at ordinary points

This module develops existence, uniqueness, solution-space dimension, and Taylor-series
representation for scalar complex linear ordinary differential equations around an ordinary point
`z₀ ∈ ℂ`, by reducing to the Banach-space first-order linear systems in
`TauCeti.Analysis.ODE.Complex.LinearSystem`:

* **Monic scalar equations** `TauCeti.LinearEquation U n`:
  - On any preconnected open domain `U`, solutions are uniquely determined by their initial `n`-jet
    (`LinearEquation.IsSolution.eqOn_of_isPreconnected`, `LinearEquation.initialJet_injective`), so
    `E.solutionSpace` has dimension at most `n`
    (`LinearEquation.finrank_solutionSpace_le_of_isPreconnected`).
  - On any open disc `(U : Set ℂ) = Metric.eball c r`, the initial-jet map at any point `a ∈ U`
    (not necessarily the disc center `c`) is a `ℂ`-linear equivalence
    `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)` (`LinearEquation.initialJetEquivOfEqEBall`, and
    `LinearEquation.initialJetEquivTop` on `⊤`), giving `Module.finrank ℂ E.solutionSpace = n`
    whenever `0 < r` (`LinearEquation.finrank_solutionSpace_of_eq_eball`,
    `LinearEquation.finrank_solutionSpace_top`).

* **Second-order scalar equations** `w'' + f(z) w' + g(z) w = h(z)`:
  - On preconnected open sets `U` (and on `ℂ`), solutions are uniquely determined by `(w z₀, w' z₀)`
    at any ordinary point `z₀ ∈ U` where `f` and `g` are analytic and the equation holds near `z₀`
    (`TauCeti.eqOn_of_deriv_deriv_add_mul_deriv_add_mul_eq`,
    `TauCeti.eq_of_differentiable_of_deriv_deriv_add_mul_deriv_add_mul_eq`).
  - On open discs `Metric.eball z₀ r` (`0 < r ≤ ∞`), `Metric.ball z₀ r`, and `ℂ`, inhomogeneous
    initial-value problems admit unique holomorphic solutions
    (`TauCeti.exists_differentiableOn_eball_deriv_deriv_add_mul_deriv_add_mul_eq`,
    `TauCeti.existsUnique_differentiable_deriv_deriv_add_mul_deriv_add_mul_eq`), and homogeneous
    solutions (`h = 0`) are represented across the full disc by the Cauchy-product recurrence
    `TauCeti.ordinaryPointCoeff` (`TauCeti.le_radius_ofScalars_ordinaryPointCoeff`,
    `TauCeti.hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff`,
    `TauCeti.exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_eball`,
    `TauCeti.exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_ball`,
    `TauCeti.exists_differentiable_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff`).

### Coefficient normalization

`TauCeti.ordinaryPointCoeff` takes and produces **factorial-scaled Taylor coefficients**
`(n ! : ℂ)⁻¹ * iteratedDeriv n f z₀` (the coefficients of `∑ₙ cₙ (z - z₀)ⁿ`), whereas
`LinearEquation.initialJet` records the **unscaled derivatives** `iteratedDeriv j y a` for `j < n`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, A K Peters, 1997, Chapter 5, §1.1.
* NIST Digital Library of Mathematical Functions, §2.7(i), <https://dlmf.nist.gov/2.7>.
* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, 1955, Ch. 3, §6.
-/

public noncomputable section

open Complex Filter Finset Metric Set TopologicalSpace Topology
open scoped BigOperators ENNReal Matrix Nat

namespace TauCeti

/-! ### Initial-jet equivalence and solution-space dimension for `TauCeti.LinearEquation` -/

namespace LinearEquation

variable {U : Opens ℂ} {n : ℕ}

private theorem differentiableOn_companionCLM (E : LinearEquation U n) :
    DifferentiableOn ℂ (fun z ↦ (Matrix.toLin' (E.companion z)).toContinuousLinearMap) U :=
  differentiableOn_toContinuousLinearMap_toLin'.mpr fun i j ↦
    (E.analyticOnNhd_companion i j).differentiableOn

private theorem analyticAt_companionCLM (E : LinearEquation U n) {a : ℂ} (ha : a ∈ U) :
    AnalyticAt ℂ (fun z ↦ (Matrix.toLin' (E.companion z)).toContinuousLinearMap) a :=
  E.differentiableOn_companionCLM.analyticOnNhd U.isOpen a ha

/-- On a preconnected open domain, scalar solutions of `E` are uniquely determined by their
initial `n`-jet at any point of the domain. -/
theorem IsSolution.eqOn_of_isPreconnected {E : LinearEquation U n} {y₁ y₂ : ℂ → ℂ}
    (hy₁ : E.IsSolution y₁) (hy₂ : E.IsSolution y₂) (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) (hjet : ∀ j < n, iteratedDeriv j y₁ a = iteratedDeriv j y₂ a) :
    EqOn y₁ y₂ U := by
  have hU_nhds := U.isOpen.mem_nhds ha
  have heq := eqOn_of_hasDerivAt_clm_apply_add (b := 0) U.isOpen hU ha
    (E.analyticAt_companionCLM ha)
    hy₁.isCompanionSolution.analyticOnNhd.differentiableOn
    hy₂.isCompanionSolution.analyticOnNhd.differentiableOn
    (Filter.eventually_of_mem hU_nhds fun z hz ↦ by
      simpa using hy₁.isCompanionSolution.hasDerivAt z hz)
    (Filter.eventually_of_mem hU_nhds fun z hz ↦ by
      simpa using hy₂.isCompanionSolution.hasDerivAt z hz)
    (funext fun j ↦ hjet j j.isLt)
  exact fun z hz ↦ by simpa using congrFun (heq hz) ⟨0, E.order_pos⟩

/-- On a preconnected open domain, the initial-jet map on `E.solutionSpace` is injective. -/
theorem initialJet_injective (E : LinearEquation U n) (hU : IsPreconnected (U : Set ℂ)) {a : ℂ}
    (ha : a ∈ U) : Function.Injective (E.initialJet ha) := by
  intro f₁ f₂ h
  have hjet : ∀ j < n, iteratedDeriv j (HolomorphicFunctions.extend f₁.val) a =
      iteratedDeriv j (HolomorphicFunctions.extend f₂.val) a := fun j hj ↦ by
    simpa [initialJet_apply] using congrFun h ⟨j, hj⟩
  have heq := IsSolution.eqOn_of_isPreconnected
    ((E.mem_solutionSpace f₁.val).mp f₁.property) ((E.mem_solutionSpace f₂.val).mp f₂.property)
    hU ha hjet
  apply Subtype.ext; apply Subtype.ext; ext ⟨z, hz⟩
  simpa [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩] using heq hz

private theorem subsingleton_solutionSpace_of_eq_empty (E : LinearEquation U n)
    (hU_empty : (U : Set ℂ) = ∅) : Subsingleton E.solutionSpace := by
  have : IsEmpty U := Set.isEmpty_coe_sort.mpr hU_empty
  have : Subsingleton C(U, ℂ) := DFunLike.coe_injective.subsingleton
  infer_instance

/-- On a preconnected open domain, the solution space of a monic order-`n` linear differential
equation is finite-dimensional. -/
theorem finiteDimensional_solutionSpace_of_isPreconnected (E : LinearEquation U n)
    (hU : IsPreconnected (U : Set ℂ)) : FiniteDimensional ℂ E.solutionSpace := by
  rcases Set.eq_empty_or_nonempty (U : Set ℂ) with hU_empty | ⟨a, ha⟩
  · have : Subsingleton E.solutionSpace := E.subsingleton_solutionSpace_of_eq_empty hU_empty
    exact Module.Finite.of_finite
  · exact FiniteDimensional.of_injective (E.initialJet ha) (E.initialJet_injective hU ha)

/-- On a preconnected open domain, `E.solutionSpace` has dimension at most `n`. -/
theorem finrank_solutionSpace_le_of_isPreconnected (E : LinearEquation U n)
    (hU : IsPreconnected (U : Set ℂ)) : Module.finrank ℂ E.solutionSpace ≤ n := by
  rcases Set.eq_empty_or_nonempty (U : Set ℂ) with hU_empty | ⟨a, ha⟩
  · have : Subsingleton E.solutionSpace := E.subsingleton_solutionSpace_of_eq_empty hU_empty
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le n
  · simpa using LinearMap.finrank_le_finrank_of_injective (E.initialJet_injective hU ha)

/-- On any open disc `(U : Set ℂ) = Metric.eball c r`, the initial-jet map `E.initialJet ha` at any
point `a ∈ U` (not necessarily the disc center `c`) is a `ℂ`-linear equivalence between
`E.solutionSpace` and `Fin n → ℂ`. -/
def initialJetEquivOfEqEBall (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJet ha)
    ⟨E.initialJet_injective (hU ▸ isPreconnected_eball) ha, by
      have ha_eball : a ∈ Metric.eball c r := by rwa [← hU, SetLike.mem_coe]
      have hr : 0 < r := zero_le.trans_lt (Metric.mem_eball.mp ha_eball)
      have hc : c ∈ U := by
        rw [← SetLike.mem_coe, hU]
        exact mem_eball_self hr
      have hsurj_c : Function.Surjective (E.initialJet hc) := fun v₀ ↦ by
        have hA : DifferentiableOn ℂ
            (fun z ↦ (Matrix.toLin' (E.companion z)).toContinuousLinearMap) (Metric.eball c r) :=
          hU ▸ E.differentiableOn_companionCLM
        obtain ⟨v, hv_ps, hv₀, hv_ode, -⟩ :=
          exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add (b := 0) hr hA
            (differentiableOn_const 0) v₀
        have hv_comp : E.IsCompanionSolution v :=
          (E.isCompanionSolution_iff v).mpr
            ⟨hU.symm ▸ hv_ps.analyticOnNhd, fun z hz ↦ by
              simpa using hv_ode z (by rwa [← hU, SetLike.mem_coe])⟩
        exact ⟨hv_comp.toSolutionSpace, (hv_comp.initialJet_toSolutionSpace hc).trans hv₀⟩
      let ec : E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
        LinearEquiv.ofBijective (E.initialJet hc)
          ⟨E.initialJet_injective (hU ▸ isPreconnected_eball) hc, hsurj_c⟩
      have : FiniteDimensional ℂ E.solutionSpace :=
        E.finiteDimensional_solutionSpace_of_isPreconnected (hU ▸ isPreconnected_eball)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ec.finrank_eq).mp
        (E.initialJet_injective (hU ▸ isPreconnected_eball) ha)⟩

/-- Applying `initialJetEquivOfEqEBall` agrees with `E.initialJet ha`. -/
@[simp]
theorem initialJetEquivOfEqEBall_apply (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) (f : E.solutionSpace) :
    E.initialJetEquivOfEqEBall hU ha f = E.initialJet ha f := by
  unfold initialJetEquivOfEqEBall
  exact LinearEquiv.ofBijective_apply _ f

/-- The underlying linear map of `initialJetEquivOfEqEBall` is `E.initialJet ha`. -/
@[simp]
theorem initialJetEquivOfEqEBall_toLinearMap (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) :
    (E.initialJetEquivOfEqEBall hU ha).toLinearMap = E.initialJet ha :=
  LinearMap.ext fun f ↦ by
    rw [LinearEquiv.coe_coe, E.initialJetEquivOfEqEBall_apply hU ha]

/-- `E.initialJet ha` is a left inverse to `(E.initialJetEquivOfEqEBall hU ha).symm`. -/
@[simp]
theorem initialJet_initialJetEquivOfEqEBall_symm (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) (v : Fin n → ℂ) :
    E.initialJet ha ((E.initialJetEquivOfEqEBall hU ha).symm v) = v := by
  rw [← E.initialJetEquivOfEqEBall_apply hU ha, LinearEquiv.apply_symm_apply]

/-- `(E.initialJetEquivOfEqEBall hU ha).symm` recovers a solution from its initial jet at `a`. -/
@[simp]
theorem initialJetEquivOfEqEBall_symm_initialJet (E : LinearEquation U n) {c a : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U) (f : E.solutionSpace) :
    (E.initialJetEquivOfEqEBall hU ha).symm (E.initialJet ha f) = f := by
  rw [← E.initialJetEquivOfEqEBall_apply hU ha, LinearEquiv.symm_apply_apply]

/-- The `j`-th derivative at `a` of the extended solution
`(E.initialJetEquivOfEqEBall hU ha).symm v` is `v j`. -/
@[simp]
theorem iteratedDeriv_extend_initialJetEquivOfEqEBall_symm (E : LinearEquation U n)
    {c a : ℂ} {r : ℝ≥0∞} (hU : (U : Set ℂ) = Metric.eball c r) (ha : a ∈ U)
    (v : Fin n → ℂ) (j : Fin n) :
    iteratedDeriv j
      (HolomorphicFunctions.extend ((E.initialJetEquivOfEqEBall hU ha).symm v).val) a = v j := by
  rw [← E.initialJet_apply ha, E.initialJet_initialJetEquivOfEqEBall_symm]

/-- On an open disc `(U : Set ℂ) = Metric.eball c r`, `E.solutionSpace` is finite-dimensional. -/
theorem finiteDimensional_solutionSpace_of_eq_eball (E : LinearEquation U n) {c : ℂ} {r : ℝ≥0∞}
    (hU : (U : Set ℂ) = Metric.eball c r) : FiniteDimensional ℂ E.solutionSpace :=
  E.finiteDimensional_solutionSpace_of_isPreconnected (hU ▸ isPreconnected_eball)

/-- On a nonempty open disc `(U : Set ℂ) = Metric.eball c r` (`0 < r`), `E.solutionSpace` has
dimension `n`. -/
theorem finrank_solutionSpace_of_eq_eball (E : LinearEquation U n) {c : ℂ} {r : ℝ≥0∞}
    (hr : 0 < r) (hU : (U : Set ℂ) = Metric.eball c r) :
    Module.finrank ℂ E.solutionSpace = n := by
  have hc : c ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact mem_eball_self hr
  simpa using (E.initialJetEquivOfEqEBall hU hc).finrank_eq

/-- On the entire complex plane `⊤ : Opens ℂ`, the initial-jet map at any point `a` is a linear
equivalence `E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ)`. -/
def initialJetEquivTop (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ) :
    E.solutionSpace ≃ₗ[ℂ] (Fin n → ℂ) :=
  E.initialJetEquivOfEqEBall (c := 0) (r := ∞) (by ext z; simp) (Set.mem_univ a)

/-- Applying `initialJetEquivTop` agrees with `E.initialJet`. -/
@[simp]
theorem initialJetEquivTop_apply (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    (f : E.solutionSpace) :
    E.initialJetEquivTop a f = E.initialJet (Set.mem_univ a) f := by
  rw [initialJetEquivTop, initialJetEquivOfEqEBall_apply]

/-- The underlying linear map of `initialJetEquivTop` is `E.initialJet`. -/
@[simp]
theorem initialJetEquivTop_toLinearMap (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ) :
    (E.initialJetEquivTop a).toLinearMap = E.initialJet (Set.mem_univ a) := by
  rw [initialJetEquivTop, initialJetEquivOfEqEBall_toLinearMap]

/-- `E.initialJet` is a left inverse to `(E.initialJetEquivTop a).symm`. -/
@[simp]
theorem initialJet_initialJetEquivTop_symm (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    {ha : a ∈ (⊤ : Opens ℂ)} (v : Fin n → ℂ) :
    E.initialJet ha ((E.initialJetEquivTop a).symm v) = v := by
  rw [initialJetEquivTop, initialJet_initialJetEquivOfEqEBall_symm]

/-- `(E.initialJetEquivTop a).symm` recovers an entire solution from its initial jet at `a`. -/
@[simp]
theorem initialJetEquivTop_symm_initialJet (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    {ha : a ∈ (⊤ : Opens ℂ)} (f : E.solutionSpace) :
    (E.initialJetEquivTop a).symm (E.initialJet ha f) = f := by
  rw [initialJetEquivTop, initialJetEquivOfEqEBall_symm_initialJet]

/-- The `j`-th derivative at `a` of the extended entire solution `(E.initialJetEquivTop a).symm v`
is `v j`. -/
@[simp]
theorem iteratedDeriv_extend_initialJetEquivTop_symm (E : LinearEquation (⊤ : Opens ℂ) n) (a : ℂ)
    (v : Fin n → ℂ) (j : Fin n) :
    iteratedDeriv j (HolomorphicFunctions.extend ((E.initialJetEquivTop a).symm v).val) a =
      v j := by
  rw [initialJetEquivTop, iteratedDeriv_extend_initialJetEquivOfEqEBall_symm]

/-- On the entire complex plane `⊤ : Opens ℂ`, `E.solutionSpace` is finite-dimensional. -/
instance instFiniteDimensionalSolutionSpaceTop (E : LinearEquation (⊤ : Opens ℂ) n) :
    FiniteDimensional ℂ E.solutionSpace :=
  E.finiteDimensional_solutionSpace_of_isPreconnected (by simpa using isPreconnected_univ)

/-- On the entire complex plane `⊤ : Opens ℂ`, `E.solutionSpace` has dimension `n`. -/
@[simp]
theorem finrank_solutionSpace_top (E : LinearEquation (⊤ : Opens ℂ) n) :
    Module.finrank ℂ E.solutionSpace = n := by
  simpa using (E.initialJetEquivTop 0).finrank_eq

end LinearEquation

/-! ### Second-order linear differential equations at an ordinary point -/

section SecondOrder

/-- Formal Taylor coefficients around `z₀` of the solution to `w'' + f(z) w' + g(z) w = 0` with
`w(z₀) = w₀` and `w'(z₀) = w₁`, given the Taylor coefficient sequences `f` and `g` around `z₀`. -/
def ordinaryPointCoeff (f g : ℕ → ℂ) (w₀ w₁ : ℂ) : ℕ → ℂ
  | 0 => w₀
  | 1 => w₁
  | n + 2 => -((((n + 2 : ℂ) * (n + 1 : ℂ))⁻¹) *
      ∑ k : Fin (n + 1), (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
        g (n - k) * ordinaryPointCoeff f g w₀ w₁ k))

/-- The constant Taylor coefficient `ordinaryPointCoeff f g w₀ w₁ 0` is `w₀`. -/
@[simp]
theorem ordinaryPointCoeff_zero (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g w₀ w₁ 0 = w₀ := by
  rw [ordinaryPointCoeff]

/-- The linear Taylor coefficient `ordinaryPointCoeff f g w₀ w₁ 1` is `w₁`. -/
@[simp]
theorem ordinaryPointCoeff_one (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g w₀ w₁ 1 = w₁ := by
  rw [ordinaryPointCoeff]

/-- Explicit Cauchy-product recurrence for `ordinaryPointCoeff` at `n + 2`. -/
theorem ordinaryPointCoeff_add_two (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ordinaryPointCoeff f g w₀ w₁ (n + 2) =
      -((((n + 2 : ℂ) * (n + 1 : ℂ))⁻¹) *
        ∑ k ∈ Finset.range (n + 1),
          (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
            g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)) := by
  rw [ordinaryPointCoeff, Fin.sum_univ_eq_sum_range (fun k ↦
    ((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
      g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)]

/-- Cleared-denominator coefficient-equating recurrence for `w'' + f(z) w' + g(z) w = 0`:
`(n + 2)(n + 1) a_{n+2} = -∑_{k=0}^n ((k + 1) f_{n-k} a_{k+1} + g_{n-k} a_k)`. -/
theorem mul_ordinaryPointCoeff_add_two (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ((n + 2 : ℂ) * (n + 1 : ℂ)) * ordinaryPointCoeff f g w₀ w₁ (n + 2) =
      -∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k) := by
  have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hn2 : (n + 2 : ℂ) ≠ 0 := mod_cast Nat.succ_ne_zero (n + 1)
  rw [ordinaryPointCoeff_add_two, mul_neg, mul_inv_cancel_left₀ (mul_ne_zero hn2 hn1)]

/-- Uniqueness characterization of `TauCeti.ordinaryPointCoeff` by its first two terms and its
cleared-denominator recurrence. -/
theorem eq_ordinaryPointCoeff_iff {f g a : ℕ → ℂ} {w₀ w₁ : ℂ} :
    a = ordinaryPointCoeff f g w₀ w₁ ↔
      a 0 = w₀ ∧ a 1 = w₁ ∧ ∀ n : ℕ, ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2) +
        ∑ k ∈ Finset.range (n + 1),
          (((k : ℂ) + 1) * f (n - k) * a (k + 1) + g (n - k) * a k) = 0 := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    refine ⟨ordinaryPointCoeff_zero f g w₀ w₁, ordinaryPointCoeff_one f g w₀ w₁, fun n ↦ ?_⟩
    rw [mul_ordinaryPointCoeff_add_two, neg_add_cancel]
  · rintro ⟨ha0, ha1, hrec⟩
    ext n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | _ | n
      · simpa using ha0
      · simpa using ha1
      · have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
        have hn2 : (n + 2 : ℂ) ≠ 0 := mod_cast Nat.succ_ne_zero (n + 1)
        rw [ordinaryPointCoeff_add_two, ← inv_mul_cancel_left₀ (mul_ne_zero hn2 hn1) (a (n + 2)),
          eq_neg_of_add_eq_zero_left (hrec n), mul_neg]
        congr 2
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ih (k + 1) (by omega), ih k (by omega)]

/-- Zero initial values produce identically zero formal Taylor coefficients. -/
@[simp]
theorem ordinaryPointCoeff_zero_zero (f g : ℕ → ℂ) :
    ordinaryPointCoeff f g 0 0 = 0 := by
  symm
  exact eq_ordinaryPointCoeff_iff.mpr ⟨rfl, rfl, fun _ ↦ by simp⟩

/-- `TauCeti.ordinaryPointCoeff` is additive in the initial data `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_add (f g : ℕ → ℂ) (w₀ w₁ u₀ u₁ : ℂ) :
    ordinaryPointCoeff f g (w₀ + u₀) (w₁ + u₁) =
      ordinaryPointCoeff f g w₀ w₁ + ordinaryPointCoeff f g u₀ u₁ := by
  symm
  refine eq_ordinaryPointCoeff_iff.mpr ⟨by simp, by simp, fun n ↦ ?_⟩
  have h1 := mul_ordinaryPointCoeff_add_two f g w₀ w₁ n
  have h2 := mul_ordinaryPointCoeff_add_two f g u₀ u₁ n
  have hsum :
      ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) *
            (ordinaryPointCoeff f g w₀ w₁ (k + 1) + ordinaryPointCoeff f g u₀ u₁ (k + 1)) +
          g (n - k) * (ordinaryPointCoeff f g w₀ w₁ k + ordinaryPointCoeff f g u₀ u₁ k)) =
      (∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k)) +
      ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g u₀ u₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g u₀ u₁ k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [Pi.add_apply]
  rw [hsum]
  linear_combination h1 + h2

/-- `TauCeti.ordinaryPointCoeff` commutes with scalar multiplication in `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_smul (f g : ℕ → ℂ) (c w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g (c * w₀) (c * w₁) = c • ordinaryPointCoeff f g w₀ w₁ := by
  symm
  refine eq_ordinaryPointCoeff_iff.mpr ⟨by simp, by simp, fun n ↦ ?_⟩
  have h := mul_ordinaryPointCoeff_add_two f g w₀ w₁ n
  have hsum :
      ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * (c * ordinaryPointCoeff f g w₀ w₁ (k + 1)) +
          g (n - k) * (c * ordinaryPointCoeff f g w₀ w₁ k)) =
      c * ∑ k ∈ Finset.range (n + 1),
        (((k : ℂ) + 1) * f (n - k) * ordinaryPointCoeff f g w₀ w₁ (k + 1) +
          g (n - k) * ordinaryPointCoeff f g w₀ w₁ k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  linear_combination c * h

/-- `TauCeti.ordinaryPointCoeff` commutes with negation in `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_neg (f g : ℕ → ℂ) (w₀ w₁ : ℂ) :
    ordinaryPointCoeff f g (-w₀) (-w₁) = -ordinaryPointCoeff f g w₀ w₁ := by
  simpa using ordinaryPointCoeff_smul f g (-1 : ℂ) w₀ w₁

/-- `TauCeti.ordinaryPointCoeff` commutes with subtraction in `(w₀, w₁)`. -/
theorem ordinaryPointCoeff_sub (f g : ℕ → ℂ) (w₀ w₁ u₀ u₁ : ℂ) :
    ordinaryPointCoeff f g (w₀ - u₀) (w₁ - u₁) =
      ordinaryPointCoeff f g w₀ w₁ - ordinaryPointCoeff f g u₀ u₁ := by
  rw [sub_eq_add_neg, sub_eq_add_neg w₁ u₁, ordinaryPointCoeff_add, ordinaryPointCoeff_neg,
    sub_eq_add_neg]

/-- Superposition of `TauCeti.ordinaryPointCoeff` into the two canonical fundamental Taylor
sequences with initial data `(1, 0)` and `(0, 1)`. -/
theorem ordinaryPointCoeff_eq_mul_add_mul (f g : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    ordinaryPointCoeff f g w₀ w₁ n =
      w₀ * ordinaryPointCoeff f g 1 0 n + w₁ * ordinaryPointCoeff f g 0 1 n := by
  have h : ordinaryPointCoeff f g w₀ w₁ =
      w₀ • ordinaryPointCoeff f g 1 0 + w₁ • ordinaryPointCoeff f g 0 1 := by
    rw [← ordinaryPointCoeff_smul, ← ordinaryPointCoeff_smul, ← ordinaryPointCoeff_add]
    simp
  simpa [Pi.add_apply, Pi.smul_apply] using congrFun h n

private def secondOrderMatrix (f g : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ if i = 0 then (if j = 0 then 0 else 1) else (if j = 0 then -g z else -f z)

private theorem secondOrderMatrix_mulVec (f g : ℂ → ℂ) (z : ℂ) (v : Fin 2 → ℂ) :
    secondOrderMatrix f g z *ᵥ v = fun i ↦ if i = 0 then v 1 else -g z * v 0 - f z * v 1 := by
  ext i
  fin_cases i <;>
    simp [secondOrderMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

private theorem differentiableOn_secondOrderCLM {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ
      (fun z ↦ (Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap) U := by
  refine differentiableOn_toContinuousLinearMap_toLin'.mpr fun i j ↦ ?_
  dsimp only [secondOrderMatrix]
  split_ifs
  · exact differentiableOn_const 0
  · exact differentiableOn_const 1
  · exact hg.neg
  · exact hf.neg

private theorem analyticAt_secondOrderCLM {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun z ↦ (Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap) z₀ := by
  obtain ⟨r, hr_pos, hr⟩ := EMetric.mem_nhds_iff.mp (hf.eventually_analyticAt.and
    hg.eventually_analyticAt)
  exact (differentiableOn_secondOrderCLM
    (fun z hz ↦ (hr hz).1.differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hr hz).2.differentiableAt.differentiableWithinAt)).analyticOnNhd
    Metric.isOpen_eball z₀ (mem_eball_self hr_pos)

private theorem hasDerivAt_secondOrder_vec_at {f g w : ℂ → ℂ} {U : Set ℂ} {z hz_val : ℂ}
    (hU : IsOpen U) (hw : DifferentiableOn ℂ w U) (hz : z ∈ U)
    (hode : deriv (deriv w) z + f z * deriv w z + g z * w z = hz_val) :
    HasDerivAt (fun z (i : Fin 2) ↦ if i = 0 then w z else deriv w z)
      ((Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap
        (fun i ↦ if i = 0 then w z else deriv w z) +
        fun i ↦ if i = 0 then 0 else hz_val) z := by
  have hwd : DifferentiableOn ℂ (deriv w) U := hw.deriv hU
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [secondOrderMatrix_mulVec] using (hw.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  · refine (hwd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.congr_deriv ?_
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
      secondOrderMatrix_mulVec, Pi.add_apply, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    linear_combination hode

private theorem secondOrder_of_hasDerivAt_vec {f g : ℂ → ℂ} {b v : ℂ → Fin 2 → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hb0 : ∀ z ∈ U, b z 0 = 0)
    (hv : ∀ z ∈ U, HasDerivAt v
      ((Matrix.toLin' (secondOrderMatrix f g z)).toContinuousLinearMap (v z) + b z) z) :
    DifferentiableOn ℂ (fun z ↦ v z 0) U ∧
      (∀ z ∈ U, deriv (fun w ↦ v w 0) z = v z 1) ∧
      ∀ z ∈ U, deriv (deriv fun w ↦ v w 0) z + f z * deriv (fun w ↦ v w 0) z +
        g z * v z 0 = b z 1 := by
  have hv_fst : ∀ z ∈ U, HasDerivAt (fun w ↦ v w 0) (v z 1) z := fun z hz ↦ by
    simpa [secondOrderMatrix_mulVec, hb0 z hz] using hasDerivAt_pi.mp (hv z hz) 0
  have hv_snd : ∀ z ∈ U, deriv (fun w ↦ v w 0) z = v z 1 := fun z hz ↦ (hv_fst z hz).deriv
  refine ⟨fun z hz ↦ (hv_fst z hz).differentiableAt.differentiableWithinAt, hv_snd, fun z hz ↦ ?_⟩
  have hd2 := (hasDerivAt_pi.mp (hv z hz) 1).deriv
  have hcongr : (fun u ↦ v u 1) =ᶠ[𝓝 z] deriv (fun w ↦ v w 0) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, fun u hu ↦ (hv_snd u hu).symm⟩
  have hddw : deriv (deriv fun w ↦ v w 0) z =
      -g z * v z 0 - f z * deriv (fun w ↦ v w 0) z + b z 1 := by
    rw [← hcongr.deriv_eq, hv_snd z hz]
    simpa [secondOrderMatrix_mulVec] using hd2
  rw [hddw]
  ring

/-- If `f` and `g` are analytic at an ordinary point `z₀ ∈ U` of an open preconnected set `U ⊆ ℂ`,
and two holomorphic functions `w₁, w₂` on `U` satisfy the same second-order equation
`w'' + f w' + g w` near `z₀` and agree to first order at `z₀`, then `EqOn w₁ w₂ U`. -/
theorem eqOn_of_deriv_deriv_add_mul_deriv_add_mul_eq {f g w₁ w₂ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hU_conn : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hw₁ : DifferentiableOn ℂ w₁ U) (hw₂ : DifferentiableOn ℂ w₂ U)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z =
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z)
    (hw₀ : w₁ z₀ = w₂ z₀) (hdw₀ : deriv w₁ z₀ = deriv w₂ z₀) :
    EqOn w₁ w₂ U := by
  let h : ℂ → ℂ := fun z ↦ deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z
  have hvec₁_diff :
      DifferentiableOn ℂ (fun z (i : Fin 2) ↦ if i = 0 then w₁ z else deriv w₁ z) U := by
    rw [differentiableOn_pi]
    intro i; fin_cases i <;> simp [hw₁, hw₁.deriv hU]
  have hvec₂_diff :
      DifferentiableOn ℂ (fun z (i : Fin 2) ↦ if i = 0 then w₂ z else deriv w₂ z) U := by
    rw [differentiableOn_pi]
    intro i; fin_cases i <;> simp [hw₂, hw₂.deriv hU]
  have hU_nhds : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
  have hvec₁_ode := ((Filter.eventually_mem_set.mpr hU_nhds).and hode).mono fun z ⟨hzU, hz_ode⟩ ↦
    hasDerivAt_secondOrder_vec_at (hz_val := h z) hU hw₁ hzU hz_ode
  have hvec₂_ode := (Filter.eventually_mem_set.mpr hU_nhds).mono fun z hzU ↦
    hasDerivAt_secondOrder_vec_at (hz_val := h z) hU hw₂ hzU rfl
  have hinit : (fun i : Fin 2 ↦ if i = 0 then w₁ z₀ else deriv w₁ z₀) =
      (fun i : Fin 2 ↦ if i = 0 then w₂ z₀ else deriv w₂ z₀) := by
    ext i; fin_cases i <;> simp [hw₀, hdw₀]
  have heq := eqOn_of_hasDerivAt_clm_apply_add
    (b := fun z i ↦ if i = 0 then 0 else h z)
    hU hU_conn hz₀ (analyticAt_secondOrderCLM hf hg) hvec₁_diff hvec₂_diff hvec₁_ode hvec₂_ode hinit
  exact fun z hz ↦ by simpa using congrFun (heq hz) 0

/-- Two entire functions `w₁, w₂` satisfying the same second-order equation `w'' + f w' + g w`
near an ordinary point `z₀` (where `f` and `g` are analytic) and agreeing to first order at `z₀`
are equal everywhere on `ℂ`. -/
theorem eq_of_differentiable_of_deriv_deriv_add_mul_deriv_add_mul_eq {f g w₁ w₂ : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hw₁ : Differentiable ℂ w₁) (hw₂ : Differentiable ℂ w₂)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w₁) z + f z * deriv w₁ z + g z * w₁ z =
      deriv (deriv w₂) z + f z * deriv w₂ z + g z * w₂ z)
    (hw₀ : w₁ z₀ = w₂ z₀) (hdw₀ : deriv w₁ z₀ = deriv w₂ z₀) :
    w₁ = w₂ := by
  ext z
  exact eqOn_of_deriv_deriv_add_mul_deriv_add_mul_eq isOpen_univ isPreconnected_univ (mem_univ z₀)
    hf hg hw₁.differentiableOn hw₂.differentiableOn hode hw₀ hdw₀ (mem_univ z)

/-- Any holomorphic function `w` on `Metric.eball z₀ r` (`0 < r ≤ ∞`) that satisfies
`w'' + f(z) w' + g(z) w = 0` eventually near `z₀`, where `f` and `g` admit scalar formal power
series `fs` and `gs` at `z₀`, is represented on `Metric.eball z₀ r` by
`FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs (w z₀) (deriv w z₀))`. -/
theorem hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff {f g w : ℂ → ℂ} {fs gs : ℕ → ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ fs) z₀)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ gs) z₀)
    (hw : DifferentiableOn ℂ w (Metric.eball z₀ r))
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) :
    HasFPowerSeriesOnBall w
      (FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs (w z₀) (deriv w z₀)))
      z₀ r := by
  let a : ℕ → ℂ := fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n w z₀
  have hw_ps : HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r :=
    hw.hasFPowerSeriesOnBall_ofScalars_eball hr
  obtain ⟨rf, hf_ball⟩ := hf
  obtain ⟨rg, hg_ball⟩ := hg
  let r₀ : ℝ≥0∞ := min r (min rf rg)
  have hr₀ : 0 < r₀ := lt_min hr (lt_min hf_ball.r_pos hg_ball.r_pos)
  have hw_r₀ := hw_ps.mono hr₀ (min_le_left _ _)
  have hf_r₀ := hf_ball.mono hr₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hg_r₀ := hg_ball.mono hr₀ ((min_le_right _ _).trans (min_le_right _ _))
  have hdw_r₀ : HasFPowerSeriesOnBall (deriv w)
      (mkPiRingSeries ℂ fun n ↦ ((n + 1 : ℂ)) * a (n + 1)) z₀ r₀ := by
    simpa [smul_eq_mul] using hw_r₀.deriv
  have hddw_r₀ : HasFPowerSeriesOnBall (deriv (deriv w))
      (mkPiRingSeries ℂ fun n ↦ ((n + 2 : ℂ) * (n + 1 : ℂ)) * a (n + 2)) z₀ r₀ := by
    convert hdw_r₀.deriv using 2
    ext n
    simp only [coeff_mkPiRingSeries, smul_eq_mul]
    push_cast
    ring
  have hsum_ps := (hddw_r₀.add (hf_r₀.fun_mul hdw_r₀)).add (hg_r₀.fun_mul hw_r₀)
  have hser_zero := hsum_ps.hasFPowerSeriesAt.eq_zero_of_eventually hode
  have ha_eq : a = ordinaryPointCoeff fs gs (w z₀) (deriv w z₀) := by
    refine eq_ordinaryPointCoeff_iff.mpr ⟨by simp [a], by simp [a], fun n ↦ ?_⟩
    have hn := congrArg (FormalMultilinearSeries.coeff · n) hser_zero
    simp only [FormalMultilinearSeries.coeff_add, FormalMultilinearSeries.coeff_zero,
      coeff_mkPiRingSeries, FormalMultilinearSeries.coeff_ofScalars] at hn
    rw [add_assoc, ← Finset.sum_add_distrib] at hn
    convert hn using 2
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rwa [ha_eq] at hw_ps

/-- If `f`, `g`, and `w` are analytic at `z₀` and `w` satisfies `w'' + f(z) w' + g(z) w = 0`
eventually near `z₀`, then the factorial-scaled iterated derivatives of `w` at `z₀` equal
`TauCeti.ordinaryPointCoeff`. -/
theorem inv_factorial_mul_iteratedDeriv_eq_ordinaryPointCoeff {f g w : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) (hw : AnalyticAt ℂ w z₀)
    (hode : ∀ᶠ z in 𝓝 z₀, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) (n : ℕ) :
    (n ! : ℂ)⁻¹ * iteratedDeriv n w z₀ =
      ordinaryPointCoeff (fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m f z₀)
        (fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m g z₀) (w z₀) (deriv w z₀) n := by
  obtain ⟨r, hw_ball⟩ := hw.hasFPowerSeriesAt
  have hf_at : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m f z₀) z₀ := by
    simpa only [div_eq_inv_mul] using hf.hasFPowerSeriesAt
  have hg_at : HasFPowerSeriesAt g
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (m ! : ℂ)⁻¹ * iteratedDeriv m g z₀) z₀ := by
    simpa only [div_eq_inv_mul] using hg.hasFPowerSeriesAt
  have hw_ps' := hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff
    hw_ball.r_pos hf_at hg_at hw_ball.differentiableOn hode
  have hser := hw_ball.hasFPowerSeriesAt.eq_formalMultilinearSeries hw_ps'.hasFPowerSeriesAt
  simpa only [FormalMultilinearSeries.coeff_ofScalars, div_eq_inv_mul] using
    congrArg (FormalMultilinearSeries.coeff · n) hser

/-- If `f`, `g`, and `h` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = h(z)` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`. -/
theorem exists_differentiableOn_eball_deriv_deriv_add_mul_deriv_add_mul_eq
    {f g h : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r))
    (hh : DifferentiableOn ℂ h (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    ∃ w : ℂ → ℂ,
      DifferentiableOn ℂ w (Metric.eball z₀ r) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = h z) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  have hb : DifferentiableOn ℂ (fun z (i : Fin 2) ↦ if i = 0 then (0 : ℂ) else h z)
      (Metric.eball z₀ r) := by
    rw [differentiableOn_pi]
    intro i; fin_cases i <;> simp [differentiableOn_const, hh]
  obtain ⟨v, -, hv₀, hv_ode, -⟩ :=
    exists_hasFPowerSeriesOnBall_hasDerivAt_clm_apply_add hr
      (differentiableOn_secondOrderCLM hf hg) hb
      (fun i : Fin 2 ↦ if i = 0 then w₀ else w₁)
  obtain ⟨hw_diff, hv_snd, hw_ode⟩ :=
    secondOrder_of_hasDerivAt_vec Metric.isOpen_eball (fun _ _ ↦ rfl) hv_ode
  let w : ℂ → ℂ := fun z ↦ v z 0
  have hw₀ : w z₀ = w₀ := by simpa [w] using congrFun hv₀ 0
  have hdw₀ : deriv w z₀ = w₁ :=
    (hv_snd z₀ (mem_eball_self hr)).trans (by simpa using congrFun hv₀ 1)
  refine ⟨w, hw_diff, hw₀, hdw₀, hw_ode, fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  have hode_ev : ∀ᶠ z in 𝓝 z₀,
      deriv (deriv u) z + f z * deriv u z + g z * u z =
        deriv (deriv w) z + f z * deriv w z + g z * w z :=
    Filter.eventually_of_mem (Metric.isOpen_eball.mem_nhds (mem_eball_self hr))
      fun z hz ↦ (hu_ode z hz).trans (hw_ode z hz).symm
  exact eqOn_of_deriv_deriv_add_mul_deriv_add_mul_eq Metric.isOpen_eball isPreconnected_eball
    (mem_eball_self hr)
    (hf.analyticOnNhd Metric.isOpen_eball z₀ (mem_eball_self hr))
    (hg.analyticOnNhd Metric.isOpen_eball z₀ (mem_eball_self hr))
    hu hw_diff hode_ev (hu₀.trans hw₀.symm) (hdu₀.trans hdw₀.symm)

/-- If `f` and `g` admit scalar power series `fs` and `gs` on `Metric.eball z₀ r`, then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, given by `ordinaryPointCoeff`. -/
theorem exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_of_hasFPowerSeriesOnBall
    {f g : ℂ → ℂ} {fs gs : ℕ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ fs) z₀ r)
    (hg : HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ gs) z₀ r) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff fs gs w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) := by
  intro a
  obtain ⟨w, hw_diff, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_differentiableOn_eball_deriv_deriv_add_mul_deriv_add_mul_eq (h := 0)
      hf.r_pos hf.differentiableOn hg.differentiableOn (differentiableOn_const 0) w₀ w₁
  have hw_ps : HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r := by
    dsimp only [a]; rw [← hw₀, ← hdw₀]
    exact hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff
      hf.r_pos hf.hasFPowerSeriesAt hg.hasFPowerSeriesAt hw_diff
      (Filter.eventually_of_mem (Metric.isOpen_eball.mem_nhds (mem_eball_self hf.r_pos)) hw_ode)
  have hw_sum : ∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z) := fun z hz ↦ by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hw_ps.hasSum_sub hz
  exact ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩

/-- **Cauchy majorant convergence bound for second-order linear ODEs at an ordinary point.** If
the scalar formal power series for `fs` and `gs` have convergence radius at least `r`, then so
does `FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs w₀ w₁)`. -/
theorem le_radius_ofScalars_ordinaryPointCoeff {fs gs : ℕ → ℂ} (w₀ w₁ : ℂ) {r : ℝ≥0∞}
    (hf : r ≤ (FormalMultilinearSeries.ofScalars ℂ fs).radius)
    (hg : r ≤ (FormalMultilinearSeries.ofScalars ℂ gs).radius) :
    r ≤ (FormalMultilinearSeries.ofScalars ℂ (ordinaryPointCoeff fs gs w₀ w₁)).radius := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact zero_le
  · have hr : 0 < r := pos_iff_ne_zero.mpr hr0
    have hf_ps : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalars ℂ fs).sum
        (FormalMultilinearSeries.ofScalars ℂ fs) 0 r :=
      ((FormalMultilinearSeries.ofScalars ℂ fs).hasFPowerSeriesOnBall (hr.trans_le hf)).mono hr hf
    have hg_ps : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalars ℂ gs).sum
        (FormalMultilinearSeries.ofScalars ℂ gs) 0 r :=
      ((FormalMultilinearSeries.ofScalars ℂ gs).hasFPowerSeriesOnBall (hr.trans_le hg)).mono hr hg
    obtain ⟨_, hw_ps, -⟩ :=
      exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_of_hasFPowerSeriesOnBall
        hf_ps hg_ps w₀ w₁
    exact hw_ps.r_le

/-- If `f` and `g` are holomorphic on `Metric.eball z₀ r` (`0 < r ≤ ∞`), then for all `w₀, w₁ : ℂ`
there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.eball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, given by `ordinaryPointCoeff`. -/
theorem exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_eball
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ≥0∞} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.eball z₀ r)) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ r ∧
      (∀ z ∈ Metric.eball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.eball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.eball z₀ r) →
        (∀ z ∈ Metric.eball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.eball z₀ r) :=
  exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_of_hasFPowerSeriesOnBall
    (hf.hasFPowerSeriesOnBall_ofScalars_eball hr)
    (hg.hasFPowerSeriesOnBall_ofScalars_eball hr) w₀ w₁

/-- If `f` and `g` are holomorphic on a finite open disc `Metric.ball z₀ r` (`0 < r`), then for all
`w₀, w₁ : ℂ` there exists a unique holomorphic solution `w` of `w'' + f(z) w' + g(z) w = 0` on
`Metric.ball z₀ r` with `w z₀ = w₀` and `deriv w z₀ = w₁`, converging on the whole disc. -/
theorem exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_ball
    {f g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ r))
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ r)) (w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      DifferentiableOn ℂ w (Metric.ball z₀ r) ∧
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ (ENNReal.ofReal r) ∧
      (∀ z ∈ Metric.ball z₀ r, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z ∈ Metric.ball z₀ r, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball z₀ r) →
        (∀ z ∈ Metric.ball z₀ r, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → EqOn u w (Metric.ball z₀ r) := by
  have heball : Metric.eball z₀ (ENNReal.ofReal r) = Metric.ball z₀ r := Metric.eball_ofReal
  have hr_enn : (0 : ℝ≥0∞) < ENNReal.ofReal r := ENNReal.ofReal_pos.mpr hr
  obtain ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_eball
      hr_enn (heball.symm ▸ hf) (heball.symm ▸ hg) w₀ w₁
  refine ⟨w, heball ▸ hw_ps.differentiableOn, hw_ps, fun z hz ↦ hw_sum z (heball.symm ▸ hz),
    hw₀, hdw₀, fun z hz ↦ hw_ode z (heball.symm ▸ hz), fun u hu hu_ode hu₀ hdu₀ ↦ ?_⟩
  simpa only [heball] using hw_uniq u (heball.symm ▸ hu)
    (fun z hz ↦ hu_ode z (heball ▸ hz)) hu₀ hdu₀

/-- For entire `f, g, h : ℂ → ℂ`, every initial-value problem `w'' + f(z) w' + g(z) w = h(z)` with
`w z₀ = w₀` and `deriv w z₀ = w₁` has a unique entire solution. -/
theorem existsUnique_differentiable_deriv_deriv_add_mul_deriv_add_mul_eq {f g h : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (z₀ w₀ w₁ : ℂ) :
    ∃! w : ℂ → ℂ, Differentiable ℂ w ∧
      (∀ z, deriv (deriv w) z + f z * deriv w z + g z * w z = h z) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ := by
  obtain ⟨w, hw_diff_on, hw₀, hdw₀, hw_ode_on, hw_uniq⟩ :=
    exists_differentiableOn_eball_deriv_deriv_add_mul_deriv_add_mul_eq (z₀ := z₀) (r := ∞)
      ENNReal.coe_lt_top hf.differentiableOn hg.differentiableOn hh.differentiableOn w₀ w₁
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  have hw_diff : Differentiable ℂ w := differentiableOn_univ.mp (by simpa using hw_diff_on)
  refine ⟨w, ⟨hw_diff, fun z ↦ hw_ode_on z (hall z), hw₀, hdw₀⟩,
    fun u ⟨hu_diff, hu_ode, hu₀, hdu₀⟩ ↦ funext fun z ↦ ?_⟩
  exact hw_uniq u hu_diff.differentiableOn (fun y _ ↦ hu_ode y) hu₀ hdu₀ (hall z)

/-- For entire `f, g : ℂ → ℂ`, every initial-value problem `w'' + f(z) w' + g(z) w = 0` with
`w z₀ = w₀` and `deriv w z₀ = w₁` has a unique entire solution `w`, and its Taylor series around
`z₀` with coefficients `ordinaryPointCoeff` converges everywhere on `ℂ`. -/
theorem exists_differentiable_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (z₀ w₀ w₁ : ℂ) :
    let a := ordinaryPointCoeff (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n f z₀)
      (fun n ↦ (n ! : ℂ)⁻¹ * iteratedDeriv n g z₀) w₀ w₁
    ∃ w : ℂ → ℂ,
      Differentiable ℂ w ∧
      HasFPowerSeriesOnBall w (FormalMultilinearSeries.ofScalars ℂ a) z₀ ∞ ∧
      (∀ z : ℂ, HasSum (fun n ↦ a n * (z - z₀) ^ n) (w z)) ∧
      w z₀ = w₀ ∧ deriv w z₀ = w₁ ∧
      (∀ z : ℂ, deriv (deriv w) z + f z * deriv w z + g z * w z = 0) ∧
      ∀ u : ℂ → ℂ, Differentiable ℂ u →
        (∀ z : ℂ, deriv (deriv u) z + f z * deriv u z + g z * u z = 0) →
        u z₀ = w₀ → deriv u z₀ = w₁ → u = w := by
  obtain ⟨w, hw_ps, hw_sum, hw₀, hdw₀, hw_ode, hw_uniq⟩ :=
    exists_hasFPowerSeriesOnBall_ofScalars_ordinaryPointCoeff_eball (z₀ := z₀) (r := ∞)
      ENNReal.coe_lt_top hf.differentiableOn hg.differentiableOn w₀ w₁
  have hall : ∀ z : ℂ, z ∈ Metric.eball z₀ ∞ := fun z ↦ by simp
  have hw_diff : Differentiable ℂ w :=
    differentiableOn_univ.mp (by simpa using hw_ps.differentiableOn)
  refine ⟨w, hw_diff, hw_ps, fun z ↦ hw_sum z (hall z), hw₀, hdw₀,
    fun z ↦ hw_ode z (hall z), fun u hu hu_ode hu₀ hdu₀ ↦ funext fun z ↦ ?_⟩
  exact hw_uniq u hu.differentiableOn (fun y _ ↦ hu_ode y) hu₀ hdu₀ (hall z)

/-! ### Sign, normalization, and recurrence checks -/

-- Check 1: `w'' = 0` produces `a₀ = w₀`, `a₁ = w₁`, and `a_{n+2} = 0`.
example (w₀ w₁ : ℂ) (n : ℕ) : ordinaryPointCoeff 0 0 w₀ w₁ (n + 2) = 0 := by
  simp [ordinaryPointCoeff_add_two]

-- Check 2: For `w'' - w = 0` (`f = 0`, `g = -1`), `a₂ = w₀ / 2`, fixing the minus sign in the
-- coefficient recurrence.
example (w₀ w₁ : ℂ) :
    ordinaryPointCoeff 0 (Pi.single 0 (-1)) w₀ w₁ 2 = w₀ / 2 := by
  rw [ordinaryPointCoeff_add_two]; norm_num; ring

-- Check 3: Airy's equation `w'' - z w = 0` around `z₀ = 0` (`f = 0`, `g(z) = -z`, so `g₁ = -1`
-- and `g_m = 0` for `m ≠ 1`) has `a₂ = 0` and `(n + 3)(n + 2) a_{n+3} = a_n` (DLMF 9.4.1).
example (w₀ w₁ : ℂ) :
    ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ 2 = 0 := by
  rw [ordinaryPointCoeff_add_two]; simp

example (w₀ w₁ : ℂ) (n : ℕ) :
    ((n + 3 : ℂ) * (n + 2 : ℂ)) *
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ (n + 3) =
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ n := by
  have h := mul_ordinaryPointCoeff_add_two 0 (Pi.single 1 (-1)) w₀ w₁ (n + 1)
  have hlhs : ((n + 3 : ℂ) * (n + 2 : ℂ)) *
      ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ (n + 3) =
      (((n + 1 : ℕ) + 2 : ℂ) * ((n + 1 : ℕ) + 1 : ℂ)) *
        ordinaryPointCoeff 0 (Pi.single 1 (-1)) w₀ w₁ ((n + 1) + 2) := by
    push_cast; ring_nf
  rw [hlhs, h, Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hne : n + 1 - k ≠ 1 := by omega
    simp [Pi.single_eq_of_ne hne]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

end SecondOrder

end TauCeti

end
