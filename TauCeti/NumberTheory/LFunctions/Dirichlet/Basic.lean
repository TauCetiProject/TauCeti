/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed

/-!
# Analytic cards of primitive Dirichlet characters

`dirichletData χ hχ` packages Mathlib's completed primitive Dirichlet L-function with its
conductor power `N^(s/2)`. This power is essential: Mathlib's completed function includes the
gamma factor but not the conductor factor. The gamma shift is zero for an even character and
one for an odd character. Only conductor one has poles, at zero and one; its card is exactly
`riemannZetaData`, including the coefficient at zero.

All three analytic-card predicates hold. The functional equation uses the conjugate card,
so non-real characters are not implicitly identified with their inverses. The analytic functions
and Gauss-sum root number come from Mathlib's Dirichlet continuation, by David Loeffler and
Michael Stoll. The normalization follows Iwaniec–Kowalski, *Analytic Number Theory*, §5.1.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

open scoped Classical in
/-- The analytic card of a primitive Dirichlet character. Its coefficients are the associated
arithmetic function (zero at index zero), its gamma shift records parity, and its completion
is Mathlib's completed function multiplied by the conductor power. -/
noncomputable def dirichletData {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : AnalyticLFunctionData where
  coeff := toArithmeticFunction (χ ·)
  conductor := ⟨χ.conductor, by rw [hχ]; exact NeZero.pos N⟩
  gammaR := {if χ.Even then 0 else 1}
  gammaC := 0
  rootNumber := χ.rootNumber
  completed s := (N : ℂ) ^ (s / 2) * χ.completedLFunction s
  polarOrder := if N = 1 then Finsupp.single 0 1 + Finsupp.single 1 1 else 0

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

@[simp]
theorem dirichletData_coeff (n : ℕ) :
    (dirichletData χ hχ).coeff n = toArithmeticFunction (χ ·) n := (rfl)

@[simp]
theorem dirichletData_conductor : (dirichletData χ hχ).conductor = ⟨N, NeZero.pos N⟩ := by
  apply Subtype.ext
  exact hχ

open scoped Classical in
@[simp]
theorem dirichletData_gammaR :
    (dirichletData χ hχ).gammaR = {if χ.Even then 0 else 1} := (rfl)

@[simp]
theorem dirichletData_gammaC : (dirichletData χ hχ).gammaC = 0 := (rfl)

@[simp]
theorem dirichletData_rootNumber : (dirichletData χ hχ).rootNumber = χ.rootNumber := (rfl)

@[simp]
theorem dirichletData_completed (s : ℂ) :
    (dirichletData χ hχ).completed s = (N : ℂ) ^ (s / 2) * χ.completedLFunction s := (rfl)

@[simp]
theorem dirichletData_polarOrder : (dirichletData χ hχ).polarOrder =
    if N = 1 then Finsupp.single 0 1 + Finsupp.single 1 1 else 0 := (rfl)

@[simp]
theorem dirichletData_degree : (dirichletData χ hχ).degree = 1 := by
  simp [AnalyticLFunctionData.degree_def]

@[simp]
theorem dirichletData_gammaFactor (s : ℂ) :
    (dirichletData χ hχ).gammaFactor s = χ.gammaFactor s := by
  classical
  simp only [AnalyticLFunctionData.gammaFactor_def, dirichletData_gammaR,
    dirichletData_gammaC, Multiset.map_singleton, Multiset.prod_singleton, Multiset.map_zero,
    Multiset.prod_zero, mul_one, DirichletCharacter.gammaFactor]
  split_ifs <;> simp

/-- The primitive conductor-one card recovers the Riemann-zeta card exactly. -/
@[simp]
theorem dirichletData_modOne (χ : DirichletCharacter ℂ 1) (hχ : χ.IsPrimitive) :
    dirichletData χ hχ = riemannZetaData := by
  have he : χ.Even := map_one χ
  ext n
  · by_cases hn : n = 0
    · subst n; simp
    · simp [toArithmeticFunction, hn, DirichletCharacter.level_one χ,
        MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]
  · simp
  · simp [he]
  · simp
  · simp [DirichletCharacter.rootNumber_modOne]
  · simp [DirichletCharacter.completedLFunction_modOne_eq]
  · simp

/-- The primitive Dirichlet card agrees with the associated Dirichlet series on `Re s > 1`. -/
theorem dirichletData_hasDirichletAgreement :
    (dirichletData χ hχ).HasDirichletAgreement where
  coeff_one := by simp [toArithmeticFunction]
  degree_pos := by simp
  completed_eq s hs := by
    have hL : LSeries (dirichletData χ hχ).coeff s = LSeries (χ ·) s :=
      LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s
    simp only [dirichletData_completed, dirichletData_conductor, PNat.mk_coe,
      dirichletData_gammaFactor, hL, χ.completedLFunction_eq_gammaFactor_mul_LSeries hs,
      mul_assoc]

/-- The completed primitive Dirichlet card is meromorphic, with precisely the two simple
poles of zeta at conductor one, and is entire at every other conductor. -/
theorem dirichletData_hasMeromorphicContinuation :
    (dirichletData χ hχ).HasMeromorphicContinuation := by
  classical
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne]
    exact riemannZetaData_hasMeromorphicContinuation
  have hc : χ ≠ 1 := fun hc ↦ hN <|
    hχ.symm.trans ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mp hc)
  have ha : ∀ s : ℂ, AnalyticAt ℂ (dirichletData χ hχ).completed s := by
    intro s
    have hL := (DirichletCharacter.differentiable_completedLFunction hc).analyticAt s
    have hbase : (N : ℂ) ∈ slitPlane := natCast_mem_slitPlane.mpr (NeZero.ne N)
    dsimp only [dirichletData]
    fun_prop (disch := assumption)
  exact ⟨fun s ↦ (ha s).meromorphicAt, by simp [hN], fun s _ ↦ ha s⟩

/-- The conductor-normalized Dirichlet completion satisfies the functional equation against
the conjugate card, with Mathlib's Gauss-sum root number. -/
theorem dirichletData_hasFunctionalEquation :
    (dirichletData χ hχ).HasFunctionalEquation := by
  classical
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne]
    exact riemannZetaData_hasFunctionalEquation
  refine ⟨hχ.norm_rootNumber, by simp [hN], ?_⟩
  intro s _ _
  have hpow : (N : ℂ) ^ (s / 2) * (N : ℂ) ^ ((1 - s) - 1 / 2) =
      (N : ℂ) ^ ((1 - s) / 2) := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
    congr 1
    ring
  have hc : χ ≠ 1 := fun hc ↦ hN <|
    hχ.symm.trans ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mp hc)
  have hconj := hχ.completedLFunction_inv (s := 1 - s) (.inr hN) (.inr hc)
  have hNconj := (TauCeti.ofReal_cpow_conj (Nat.cast_nonneg N)
    ((1 - conj s) / 2)).symm
  simp only [Complex.ofReal_natCast, map_div₀, map_ofNat, map_sub, map_one,
    Complex.conj_conj] at hNconj
  simp only [dirichletData_completed, AnalyticLFunctionData.dual_completed_apply,
    dirichletData_rootNumber, map_mul, map_sub, map_one, hNconj]
  rw [← sub_sub_cancel 1 s, hχ.completedLFunction_one_sub (1 - s), sub_sub_cancel,
    hconj]
  calc
    _ = χ.rootNumber * ((N : ℂ) ^ (s / 2) * (N : ℂ) ^ ((1 - s) - 1 / 2)) *
        conj (χ.completedLFunction (conj (1 - s))) := by ring
    _ = _ := by rw [hpow]; simp [map_sub, mul_assoc]

end TauCeti.LFunctions
