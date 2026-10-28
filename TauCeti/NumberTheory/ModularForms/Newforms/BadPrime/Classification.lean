/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.PrimeToPart
public import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.AtkinLehner
public import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Ramified
public import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Vanishing

/-!
# The bad-prime eigenvalues of a newform, by the conductor of its nebentypus

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ`, and let `p ∣ N` be prime. By
the Atkin–Lehner–Li theorem `a_p(f)` is the `U_p`-eigenvalue of `f`. Write `v = v_p(N)` and
`c = v_p(cond χ)`, so that `c ≤ v`, and let `χ⁽ᵖ⁾` be the prime-to-`p` part of `χ`
(`TauCeti.primeToPart`). Li's classification (Miyake, Theorem 4.6.17) reads:

* if `v = 1` and `c = 0`, then `a_p(f) ² = χ⁽ᵖ⁾(p) · p ^ (k - 2)`;
* if `c = v`, then `|a_p(f)| = p ^ ((k - 1) / 2)`;
* otherwise, that is if `c < v` and `v ≥ 2`, then `a_p(f) = 0`.

In particular `a_p(f) ≠ 0` if and only if `v = max(1, c)`.

The three cases are proved in `Newforms/BadPrime/AtkinLehner.lean`,
`Newforms/BadPrime/Ramified.lean` and `Newforms/BadPrime/Vanishing.lean`, where they are
distinguished by whether `χ` is defined modulo `N / p`. This file restates them in terms of `c`
and `χ⁽ᵖ⁾`. The translation rests on
`DirichletCharacter.factorsThrough_div_iff_factorization_conductor_lt` (`χ` is defined modulo
`N / p` exactly when `c < v`) and, in the first case, on the identification of the value at `p` of
the lowered character modulo `N / p` with `χ⁽ᵖ⁾(p)`.

## Main results

* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq_of_factorization_eq_one`: the case `v = 1`,
  `c = 0`.
* `HeckeRing.GL2.Newform.norm_qExpansion_coeff_prime_of_factorization_conductor_eq`: the case
  `c = v`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt`: the case
  `c < v`, `v ≥ 2`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_ne_zero_iff`: `a_p(f) ≠ 0 ↔ v = max(1, c)`.

## References

* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315,
  Theorem 3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.17.
-/

public section

open UpperHalfPlane TauCeti

open scoped TauCeti.ExactDivisor

namespace HeckeRing.GL2.Newform

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-- **The bad-prime eigenvalue when `v_p(N) = 1` and `p ∤ cond χ`** (Li, Theorem 3): a newform `f`
of nebentypus `χ` has `a_p(f) ² = χ⁽ᵖ⁾(p) · p ^ (k - 2)`, where `χ⁽ᵖ⁾` is the prime-to-`p` part of
`χ`. -/
theorem qExpansion_coeff_prime_sq_of_factorization_eq_one (f : Newform N k) (hp : p.Prime)
    (hN : N.factorization p = 1) (hc : f.dirichletLift.conductor.factorization p = 0) :
    (qExpansion 1 f.toCuspForm).coeff p ^ 2 =
      primeToPart p f.dirichletLift p * (p : ℂ) ^ (k - 2) := by
  have hpN : p ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h : p ∥ N := .of_not_sq_dvd hp hpN fun h2 ↦ by
    have := (hp.pow_dvd_iff_le_factorization (NeZero.ne N)).mp h2
    omega
  have hfac : f.dirichletLift.FactorsThrough (N / p) :=
    (DirichletCharacter.factorsThrough_div_iff_factorization_conductor_lt hp hpN _).mpr (by omega)
  -- the nebentypus is the pull-back of the lowered character `hfac.χ₀`
  have hcomp : f.χ = hfac.χ₀.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)) := by
    rw [← f.dirichletLift_equivToUnitHom, ← MulChar.toUnitHom_eq]
    conv_lhs => rw [hfac.eq_changeLevel]
    rw [DirichletCharacter.changeLevel_toUnitHom]
  -- `p` is prime to `N / p`, so the lowered character and the primitive character agree at `p`
  have hprim : f.dirichletLift.primitiveCharacter (p : ZMod f.dirichletLift.conductor) =
      hfac.χ₀ p := by
    have h₁ := congrArg (fun ψ : DirichletCharacter ℂ N ↦ ψ.primitiveCharacter (p : ℤ))
      hfac.eq_changeLevel
    have h₂ := DirichletCharacter.primitiveCharacter_changeLevel_apply hfac.dvd hfac.χ₀ p
    have h₃ := hfac.χ₀.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr h.coprime)
    simp only [Int.cast_natCast] at h₁ h₂ h₃
    rw [h₁, h₂, h₃]
  rw [f.qExpansion_coeff_prime_sq_of_isExactDivisor hp h hcomp, MulChar.coe_toUnitHom,
    ZMod.coe_unitOfCoprime, primeToPart_apply_prime_of_not_dvd hp _ fun hd ↦
      (hp.factorization_pos_of_dvd f.dirichletLift.conductor_ne_zero hd).ne' hc, hprim]

/-- **The bad-prime eigenvalue when `v_p(cond χ) = v_p(N)`** (Li, Theorem 3): for a prime `p ∣ N`
whose full power in `N` divides the conductor of the nebentypus, a newform `f` has
`|a_p(f)| = p ^ ((k - 1) / 2)`. -/
theorem norm_qExpansion_coeff_prime_of_factorization_conductor_eq (f : Newform N k)
    (hp : p.Prime) (hpN : p ∣ N)
    (hc : f.dirichletLift.conductor.factorization p = N.factorization p) :
    ‖(qExpansion 1 f.toCuspForm).coeff p‖ = Real.sqrt p ^ (k - 1) := by
  refine f.norm_qExpansion_coeff_prime_of_not_exists_eq_comp hp hpN ?_
  rintro ⟨χ₀, hχ₀⟩
  -- a nebentypus pulled back from `N / p` is defined modulo `N / p`, so `c < v`
  have hfac : f.dirichletLift.FactorsThrough (N / p) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap
      (Nat.div_dvd_of_dvd hpN)).mpr fun u hu ↦ ?_
    rw [MonoidHom.mem_ker, MulChar.toUnitHom_eq, dirichletLift_equivToUnitHom, hχ₀,
      MonoidHom.comp_apply, MonoidHom.mem_ker.mp hu, map_one]
  exact ((DirichletCharacter.factorsThrough_div_iff_factorization_conductor_lt hp hpN _).mp
    hfac).ne hc

/-- **The bad-prime eigenvalue vanishes when `v_p(cond χ) < v_p(N)` and `v_p(N) ≥ 2`**
(Atkin–Lehner for trivial nebentypus; Li, Theorem 3). -/
theorem qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt (f : Newform N k)
    (hp : p.Prime) (hN : 2 ≤ N.factorization p)
    (hc : f.dirichletLift.conductor.factorization p < N.factorization p) :
    (qExpansion 1 f.toCuspForm).coeff p = 0 := by
  have hpsq : p ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization (NeZero.ne N)).mpr hN
  exact f.qExpansion_coeff_prime_eq_zero_of_sq_dvd hp hpsq
    ((DirichletCharacter.factorsThrough_div_iff_factorization_conductor_lt hp
      ((dvd_pow_self p two_ne_zero).trans hpsq) _).mpr hc)

/-- **The nonvanishing criterion for the bad-prime eigenvalues** (Li, Theorem 3; Miyake,
Theorem 4.6.17): for a prime `p ∣ N`, a newform `f` of nebentypus `χ` has `a_p(f) ≠ 0` if and
only if `v_p(N) = max(1, v_p(cond χ))`. -/
theorem qExpansion_coeff_prime_ne_zero_iff (f : Newform N k) (hp : p.Prime) (hpN : p ∣ N) :
    (qExpansion 1 f.toCuspForm).coeff p ≠ 0 ↔
      N.factorization p = max 1 (f.dirichletLift.conductor.factorization p) := by
  have hpos := hp.factorization_pos_of_dvd (NeZero.ne N) hpN
  have hle : f.dirichletLift.conductor.factorization p ≤ N.factorization p :=
    (Nat.factorization_le_iff_dvd f.dirichletLift.conductor_ne_zero (NeZero.ne N)).mpr
      f.dirichletLift.conductor_dvd_level p
  rcases hle.lt_or_eq with hc | hc
  · by_cases hN : N.factorization p = 1
    · -- `v = 1`, `c = 0`: `a_p ²` is the nonzero `χ⁽ᵖ⁾(p) · p ^ (k - 2)`
      refine iff_of_true (fun h0 ↦ ?_) (by omega)
      have hsq := f.qExpansion_coeff_prime_sq_of_factorization_eq_one hp hN (by omega)
      rw [h0, zero_pow two_ne_zero] at hsq
      exact mul_ne_zero (primeToPart_apply_prime_ne_zero hp _)
        (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)) hsq.symm
    · -- `c < v`, `v ≥ 2`: `a_p = 0`
      exact iff_of_false (not_not.mpr
        (f.qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt hp (by omega) hc))
        (by omega)
  · -- `c = v`: `|a_p| = p ^ ((k - 1) / 2) ≠ 0`
    refine iff_of_true (fun h0 ↦ ?_) (by omega)
    have hnorm := f.norm_qExpansion_coeff_prime_of_factorization_conductor_eq hp hpN hc
    rw [h0, norm_zero] at hnorm
    exact zpow_ne_zero _ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hp.pos)) hnorm.symm

end HeckeRing.GL2.Newform
