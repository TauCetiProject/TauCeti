/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
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
  conductor := ⟨χ.conductor, by
    rw [(DirichletCharacter.isPrimitive_def _).mp hχ]
    exact NeZero.pos N⟩
  gammaR := {if χ.Even then 0 else 1}
  gammaC := 0
  rootNumber := χ.rootNumber
  completed s := (N : ℂ) ^ (s / 2) * χ.completedLFunction s
  polarOrder := if N = 1 then Finsupp.single 0 1 + Finsupp.single 1 1 else 0

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

theorem dirichletData_coeff (n : ℕ) :
    (dirichletData χ hχ).coeff n = toArithmeticFunction (χ ·) n := (rfl)

/-- At every positive index, the coefficient is the value of the Dirichlet character. -/
@[simp]
theorem dirichletData_coeff_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (dirichletData χ hχ).coeff n = χ n :=
  (χ.apply_eq_toArithmeticFunction_apply hn).symm

@[simp]
theorem dirichletData_coeff_zero : (dirichletData χ hχ).coeff 0 = 0 := by
  simp only [dirichletData_coeff, ArithmeticFunction.map_zero]

@[simp]
theorem dirichletData_conductor : (dirichletData χ hχ).conductor = ⟨N, NeZero.pos N⟩ := by
  apply Subtype.ext
  exact (DirichletCharacter.isPrimitive_def _).mp hχ

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
  have he : χ.Even := χ.even_of_le_two (by decide)
  ext n
  · by_cases hn : n = 0
    · subst n; simp
    · rw [dirichletData_coeff_of_ne_zero χ hχ hn]
      simp [hn, DirichletCharacter.level_one χ,
        MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]
  · simp
  · simp [he]
  · simp
  · simp [DirichletCharacter.rootNumber_modOne]
  · simp [DirichletCharacter.completedLFunction_modOne_eq]
  · simp

/-- The dual of a primitive Dirichlet card is the card of the inverse character. -/
@[simp]
theorem dirichletData_dual : (dirichletData χ hχ).dual = dirichletData χ⁻¹ hχ.inv := by
  classical
  by_cases hN : N = 1
  · subst N
    simp
  have hc : χ ≠ 1 := mt hχ.eq_one_iff.mp hN
  ext n
  · by_cases hn : n = 0
    · subst n; simp
    · simp only [AnalyticLFunctionData.dual_coeff, dirichletData_coeff_of_ne_zero _ _ hn]
      exact MulChar.star_apply' χ (n : ZMod N)
  · apply Subtype.ext
    simp
  · simp only [AnalyticLFunctionData.dual_gammaR, dirichletData_gammaR,
      DirichletCharacter.even_inv_iff]
    split_ifs <;> simp
  · simp
  · simp [DirichletCharacter.rootNumber_inv]
  · have hp := (TauCeti.ofReal_cpow_conj (Nat.cast_nonneg N) (conj n / 2)).symm
    simp only [map_div₀, map_ofNat, Complex.conj_conj, Complex.ofReal_natCast] at hp
    simp only [AnalyticLFunctionData.dual_completed_apply, dirichletData_completed, map_mul,
      hp, χ.completedLFunction_inv_conj (.inr hN) (.inr hc)]
  · simp [hN]

/-- The primitive Dirichlet card agrees with the associated Dirichlet series on `Re s > 1`. -/
theorem dirichletData_hasDirichletAgreement :
    (dirichletData χ hχ).HasDirichletAgreement where
  coeff_one := by rw [dirichletData_coeff_of_ne_zero χ hχ one_ne_zero]; simp
  degree_pos := by simp
  completed_eq s hs := by
    have hL : LSeries (dirichletData χ hχ).coeff s = LSeries (χ ·) s :=
      LSeries_congr (fun hn ↦ dirichletData_coeff_of_ne_zero χ hχ hn) s
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
  have hc : χ ≠ 1 := mt hχ.eq_one_iff.mp hN
  have ha : ∀ s : ℂ, AnalyticAt ℂ (dirichletData χ hχ).completed s := by
    intro s
    have hL := (DirichletCharacter.differentiable_completedLFunction hc).analyticAt s
    have hbase : (N : ℂ) ∈ slitPlane := natCast_mem_slitPlane.mpr (NeZero.ne N)
    rw [funext (dirichletData_completed χ hχ)]
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
  refine ⟨DirichletCharacter.norm_rootNumber hχ, by simp [hN], ?_⟩
  intro s _ _
  have hpow : (N : ℂ) ^ (s / 2) * (N : ℂ) ^ ((1 - s) - 1 / 2) =
      (N : ℂ) ^ ((1 - s) / 2) := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
    congr 1
    ring
  rw [dirichletData_dual, dirichletData_completed, dirichletData_rootNumber,
    dirichletData_completed]
  have hfe : χ.completedLFunction s = (N : ℂ) ^ ((1 - s) - 1 / 2) * χ.rootNumber *
      χ⁻¹.completedLFunction (1 - s) := by
    simpa using hχ.completedLFunction_one_sub (1 - s)
  rw [hfe]
  calc
    (N : ℂ) ^ (s / 2) * ((N : ℂ) ^ ((1 - s) - 1 / 2) * χ.rootNumber *
        χ⁻¹.completedLFunction (1 - s)) =
      χ.rootNumber * ((N : ℂ) ^ (s / 2) * (N : ℂ) ^ ((1 - s) - 1 / 2)) *
        χ⁻¹.completedLFunction (1 - s) := by ring
    _ = χ.rootNumber * ((N : ℂ) ^ ((1 - s) / 2) * χ⁻¹.completedLFunction (1 - s)) := by
      rw [hpow, mul_assoc]

end TauCeti.LFunctions
