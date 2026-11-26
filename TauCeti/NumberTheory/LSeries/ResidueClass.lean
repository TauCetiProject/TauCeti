/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import TauCeti.Data.Nat.GCD
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Twisted von Mangoldt weights in residue classes

For a unit residue class `a` modulo `q`, character orthogonality expands the coefficients
`ψ(n) Λ(n) 1_{n ≡ a (mod q)}` using product characters. We define the corresponding weighted
sum of negative logarithmic derivatives and show it is analytic at `1` for any residue `a`
when the conductor of `ψ` does not divide `q`. This includes the quadratic character at an odd
prime not dividing `q`.

The Legendre twist at `a = 1` is used in `New.LSeries_lambdaKResidueClass_eq_add_logDerivMean`
in the shorter GRH formalization (`grh/src/New/Reduction/Zeros/PrimeError.lean` in
<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>).
-/

public section

open DirichletCharacter

namespace ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q] {d : ℕ}

section

variable [NeZero d]

/-- The weighted sum of negative logarithmic derivatives for a Dirichlet twist `ψ` in the
residue class `a` modulo `q`. This auxiliary function is defined for any `a`; the
orthogonality expansion of the twisted von Mangoldt coefficients uses `IsUnit a`. -/
noncomputable def LFunctionTwistResidueClass (a : ZMod q) (ψ : DirichletCharacter ℂ d)
    (s : ℂ) : ℂ :=
  -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * logDeriv (χ.mul ψ).LFunction s

/-- The logarithmic derivatives in the auxiliary function are those of the product characters,
weighted by character values at the inverse residue class. -/
theorem LFunctionTwistResidueClass_def (a : ZMod q) (ψ : DirichletCharacter ℂ d) (s : ℂ) :
    LFunctionTwistResidueClass a ψ s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * logDeriv (χ.mul ψ).LFunction s :=
  (rfl)

end

/-- Twisting the residue-class von Mangoldt coefficients multiplies every character in
Mathlib's orthogonality expansion by the twisting character. -/
theorem twist_residueClass_eq {a : ZMod q} (ha : IsUnit a) (ψ : DirichletCharacter ℂ d) :
    (fun n : ℕ ↦ ψ n * (residueClass a n : ℂ)) =
      (q.totient : ℂ)⁻¹ • ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ • (fun n : ℕ ↦ χ.mul ψ n * vonMangoldt n) := by
  ext n
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, residueClass_apply ha, mul_natCast]
  rw [mul_left_comm (ψ ↑n), Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun χ _ ↦ by ring

section

variable [NeZero d]

/-- The weighted sum of logarithmic derivatives is analytic wherever each product L-function
is analytic and nonzero. -/
theorem analyticAt_LFunctionTwistResidueClass (a : ZMod q) (ψ : DirichletCharacter ℂ d) {s : ℂ}
    (h : ∀ χ : DirichletCharacter ℂ q, AnalyticAt ℂ (χ.mul ψ).LFunction s ∧
      (χ.mul ψ).LFunction s ≠ 0) : AnalyticAt ℂ (LFunctionTwistResidueClass a ψ) s := by
  unfold LFunctionTwistResidueClass
  refine analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun χ _ ↦
    analyticAt_const.fun_mul ?_)
  exact (h χ).1.logDeriv (h χ).2

/-- The twisted auxiliary function is analytic at `1` for any residue `a` when the conductor
of `ψ` does not divide `q`, so no character modulo `q` can cancel the twist. -/
theorem analyticAt_LFunctionTwistResidueClass_one (a : ZMod q) (ψ : DirichletCharacter ℂ d)
    (hψ : ¬ ψ.conductor ∣ q) : AnalyticAt ℂ (LFunctionTwistResidueClass a ψ) 1 := by
  refine analyticAt_LFunctionTwistResidueClass a ψ fun χ ↦ ?_
  have hne : χ.mul ψ ≠ 1 := fun h ↦ hψ <|
    (ψ.exists_mul_eq_one_iff_conductor_dvd (q := q)).mp ⟨χ, h⟩
  exact ⟨(χ.mul ψ).analyticAt_LFunction (.inr hne),
    (χ.mul ψ).LFunction_ne_zero_of_one_le_re (.inl hne) (by simp)⟩

end

section Legendre

variable [Fact d.Prime]

local instance : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩

/-- The auxiliary function for the quadratic character at an odd prime `d` not dividing `q`
is analytic at `1` for any residue `a`. -/
theorem analyticAt_LFunctionTwistResidueClass_one_quadraticChar (hd : d ≠ 2) (hdq : ¬ d ∣ q)
    (a : ZMod q) :
    AnalyticAt ℂ (LFunctionTwistResidueClass a
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) 1 := by
  refine analyticAt_LFunctionTwistResidueClass_one a _ ?_
  have h := conductor_changeLevel_quadraticChar (p := d) (R := ℂ)
    (by simp [ringChar.eq_zero]) hd (dvd_refl d)
  rw [changeLevel_self] at h
  simpa only [h] using hdq

end Legendre

end ArithmeticFunction.vonMangoldt
