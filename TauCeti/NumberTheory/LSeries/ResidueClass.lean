/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.Data.Nat.GCD
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Twist

/-!
# Dirichlet series of twisted von Mangoldt weights in residue classes

For a unit residue class `a` modulo `q`, character orthogonality expresses the Dirichlet series
with coefficients `ψ(n) Λ(n) 1_{n ≡ a (mod q)}` as a finite sum of logarithmic derivatives. If the
conductor of `ψ` does not divide `q`, none of the products in the sum is principal. The difference
between the untwisted and twisted series then has the same principal part at `1` as the untwisted
series.

The signed combination at `a = 1` is used in `New.LSeries_lambdaKResidueClass_eq_add_logDerivMean`
in the shorter GRH formalization (`grh/src/New/Reduction/Zeros/PrimeError.lean` in
<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>).
-/

public section

open Complex DirichletCharacter
open scoped LSeries.notation

namespace ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q] {d : ℕ}

section

variable [NeZero d]

/-- The weighted sum of negative logarithmic derivatives for a Dirichlet twist `ψ` of the
von Mangoldt function restricted to `a` modulo `q`. -/
noncomputable def LFunctionTwistResidueClass (a : ZMod q) (ψ : DirichletCharacter ℂ d)
    (s : ℂ) : ℂ :=
  -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * logDeriv (χ.mul ψ).LFunction s

/-- The logarithmic derivatives in the continuation are those of the product characters,
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

/-- The twisted residue-class series equals the weighted logarithmic derivative sum in its
half-plane of absolute convergence. -/
theorem LSeries_twist_residueClass_eq {a : ZMod q} (ha : IsUnit a)
    (ψ : DirichletCharacter ℂ d) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ ψ n * (residueClass a n : ℂ)) s = LFunctionTwistResidueClass a ψ s := by
  have hsum (χ : DirichletCharacter ℂ q) :
      LSeriesSummable (χ a⁻¹ • (fun n : ℕ ↦ χ.mul ψ n * vonMangoldt n)) s :=
    (LSeriesSummable_twist_vonMangoldt (χ.mul ψ) hs).smul _
  rw [twist_residueClass_eq ha, LSeries_smul, LSeries_sum (fun χ _ ↦ hsum χ),
    LFunctionTwistResidueClass_def, neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [LSeries_smul, logDeriv_LFunction_eq_neg_LSeries _ hs, mul_neg, neg_neg]
  rfl

/-- The weighted sum of logarithmic derivatives is analytic wherever each product L-function
is analytic and nonzero. -/
theorem analyticAt_LFunctionTwistResidueClass (a : ZMod q) (ψ : DirichletCharacter ℂ d) {s : ℂ}
    (h : ∀ χ : DirichletCharacter ℂ q, AnalyticAt ℂ (χ.mul ψ).LFunction s ∧
      (χ.mul ψ).LFunction s ≠ 0) : AnalyticAt ℂ (LFunctionTwistResidueClass a ψ) s := by
  unfold LFunctionTwistResidueClass
  refine analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun χ _ ↦
    analyticAt_const.fun_mul ?_)
  exact (h χ).1.logDeriv (h χ).2

/-- The untwisted continuation after subtraction of the principal part is analytic at `1`. -/
theorem analyticAt_LFunctionResidueClassAux_one (a : ZMod q) :
    AnalyticAt ℂ (LFunctionResidueClassAux a) 1 := by
  classical
  unfold LFunctionResidueClassAux
  refine analyticAt_const.fun_mul (AnalyticAt.fun_sub ?_ ?_)
  · simpa only [logDeriv_apply, neg_div] using
      ((differentiable_LFunctionTrivChar₁ q).analyticAt 1 |>.logDeriv
        (LFunctionTrivChar₁_apply_one_ne_zero q)).fun_neg
  · refine Finset.analyticAt_fun_sum _ fun χ hχ ↦ ?_
    have hχ' : χ ≠ 1 := by simpa using hχ
    simpa only [logDeriv_apply, mul_div_assoc] using
      (analyticAt_const (v := χ a⁻¹)).fun_mul <|
        (χ.analyticAt_LFunction (.inr hχ')).logDeriv
          (χ.LFunction_ne_zero_of_one_le_re (.inl hχ') (by simp))

/-- The signed weight `(1 - ψ(n)) Λ(n) 1_{n ≡ a (mod q)}` has as its continuation, after
subtracting `s / (φ(q) (s - 1))`, the difference of the two auxiliary functions minus
`1 / φ(q)`. -/
theorem LSeries_one_sub_twist_residueClass_eq {a : ZMod q} (ha : IsUnit a)
    (ψ : DirichletCharacter ℂ d) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ (1 - ψ n) * (residueClass a n : ℂ)) s -
        s / ((q.totient : ℂ) * (s - 1)) =
      LFunctionResidueClassAux a s - LFunctionTwistResidueClass a ψ s - (q.totient : ℂ)⁻¹ := by
  have hsum : LSeriesSummable (fun n ↦ (residueClass a n : ℂ)) s := by
    exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_residueClass_le_one a).trans_lt (EReal.coe_lt_coe_iff.mpr hs))
  have htw : LSeriesSummable (fun n : ℕ ↦ ψ n * (residueClass a n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul ψ hsum
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne'
  simp only [sub_mul, one_mul]
  rw [← Pi.sub_def, LSeries_sub hsum htw, LSeries_twist_residueClass_eq ha ψ hs,
    eqOn_LFunctionResidueClassAux ha hs]
  field_simp
  ring

/-- The twist contributes no pole at `1` when no character of the residue-class modulus
can cancel it. -/
theorem analyticAt_LFunctionTwistResidueClass_one (a : ZMod q) (ψ : DirichletCharacter ℂ d)
    (hψ : ¬ ψ.conductor ∣ q) : AnalyticAt ℂ (LFunctionTwistResidueClass a ψ) 1 := by
  refine analyticAt_LFunctionTwistResidueClass a ψ fun χ ↦ ?_
  have hne : χ.mul ψ ≠ 1 := fun h ↦ hψ <|
    (ψ.exists_mul_eq_one_iff_conductor_dvd (q := q)).mp ⟨χ, h⟩
  exact ⟨(χ.mul ψ).analyticAt_LFunction (.inr hne),
    (χ.mul ψ).LFunction_ne_zero_of_one_le_re (.inl hne) (by simp)⟩

/-- The compensated signed series has a holomorphic continuation at `1` if the conductor of
the twist does not divide the residue-class modulus. -/
theorem analyticAt_one_sub_twist_residueClass (a : ZMod q) (ψ : DirichletCharacter ℂ d)
    (hψ : ¬ ψ.conductor ∣ q) :
    AnalyticAt ℂ (fun s ↦ LFunctionResidueClassAux a s - LFunctionTwistResidueClass a ψ s -
      (q.totient : ℂ)⁻¹) 1 :=
  ((analyticAt_LFunctionResidueClassAux_one a).fun_sub
    (analyticAt_LFunctionTwistResidueClass_one a ψ hψ)).fun_sub analyticAt_const

end

section Legendre

variable [Fact d.Prime]

local instance : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩

/-- The half-plane formula for the signed Legendre weight in the class `1` modulo `q`. -/
theorem LSeries_one_sub_legendreSym_residueClass_one_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ (1 - (legendreSym d n : ℂ)) * (residueClass (1 : ZMod q) n : ℂ)) s -
        s / ((q.totient : ℂ) * (s - 1)) =
      LFunctionResidueClassAux (1 : ZMod q) s -
        LFunctionTwistResidueClass (1 : ZMod q)
          ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) s - (q.totient : ℂ)⁻¹ := by
  simpa only [legendreSym, MulChar.ringHomComp_apply, Int.cast_natCast,
    Int.coe_castRingHom] using
    LSeries_one_sub_twist_residueClass_eq (isUnit_one (M := ZMod q))
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) hs

/-- For the Legendre twist at an odd prime `d` not dividing `q`, the compensated
continuation of the signed series is holomorphic at `1`. -/
theorem analyticAt_one_sub_legendreSym_residueClass (hd : d ≠ 2) (hdq : ¬ d ∣ q)
    (a : ZMod q) :
    AnalyticAt ℂ (fun s ↦ LFunctionResidueClassAux a s - LFunctionTwistResidueClass a
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) s - (q.totient : ℂ)⁻¹) 1 := by
  refine analyticAt_one_sub_twist_residueClass a _ ?_
  have h := conductor_changeLevel_quadraticChar (p := d) (R := ℂ)
    (by simp [ringChar.eq_zero]) hd (dvd_refl d)
  rw [changeLevel_self] at h
  simpa only [h] using hdq

end Legendre

end ArithmeticFunction.vonMangoldt
