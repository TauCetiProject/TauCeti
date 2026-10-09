/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign
public import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Descent
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# The bad-prime eigenvalue of a newform when `p` exactly divides the level

For a newform `f` of trivial nebentypus and a prime `p ∥ N`, the descent relation
`U_p f + W_p f ∈ S_old` combines with newness and the Atkin–Lehner sign to give

`a_p(f) = -ε_p(f) · (√p) ^ (k - 2)`.

In particular `a_p(f) ≠ 0` and `a_p(f) ² = p ^ (k - 2)`. Here `ε_p(f) = ±1` is the
eigenvalue of the normalized operator `𝒲_p = (√p) ^ (2 - k) • W_p`.
The descent identity, valid whenever the nebentypus descends to `N/p`, is in
`Newforms/BadPrime/Descent.lean`.

## Main results

* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul`: the eigenvalue formula.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_ne_zero_of_isExactDivisor`: nonvanishing.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq_of_isExactDivisor`: the square of `a_p`.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on Γ₀(m)*, Math. Ann. **185** (1970),
  134–160, Theorem 3.
* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14 and Theorem 4.6.17.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace HeckeRing.GL2.Newform

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-- **The bad-prime eigenvalue at `p ∥ N`** (Atkin–Lehner, Theorem 3): a newform `f` of trivial
nebentypus has `a_p(f) = -ε_p(f) · (√p) ^ (k - 2)` at every prime `p` exactly dividing the
level, where `ε_p(f) = ±1` is its Atkin–Lehner sign at `p`. With
`Newform.heckeUCuspNat_eq_qExpansion_coeff_smul` this is the eigenvalue of `U_p` on `f`.

The hypothesis `p ∥ N` is stated as `p ∣ N` and `¬ p ^ 2 ∣ N`, which characterize it for a prime
`p` (`TauCeti.Nat.IsExactDivisor.of_not_sq_dvd`). -/
@[simp]
theorem qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul (f : Newform N k) (hχ : f.χ = 1)
    (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) :
    (qExpansion 1 f.toCuspForm).coeff p =
      -(f.atkinLehnerSign hχ (.of_not_sq_dvd hp hpN hpsq) * ((Real.sqrt p : ℝ) : ℂ) ^ (k - 2)) := by
  have h : p ∥ N := .of_not_sq_dvd hp hpN hpsq
  set c : ℂ := ((Real.sqrt p : ℝ) : ℂ) ^ (k - 2) with hc
  -- `W_p f = c • ε_p • f`, undoing the normalization of `𝒲_p f = ε_p • f`.
  have hW : h.atkinLehnerOperatorCusp k (f.toCuspFormGamma0 hχ) =
      (c * f.atkinLehnerSign hχ h) • f.toCuspFormGamma0 hχ := by
    have hε := f.normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul hχ h
    rw [Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp_def, LinearMap.smul_apply] at hε
    have hinv : c * atkinLehnerNormalizer p k = 1 := by
      rw [hc, atkinLehnerNormalizer_def, ← zpow_add₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hp.pos)))]
      simp
    rw [mul_smul, ← hε, smul_smul, hinv, one_smul]
  have hcomp : (1 : (ZMod N)ˣ →* ℂˣ) =
      (1 : (ZMod (N / p))ˣ →* ℂˣ).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)) :=
    (MonoidHom.one_comp _).symm
  have hold :=
    (heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld_inf_cuspFormCharSpace
      k hp hpN hpsq hcomp (hχ ▸ f.mem_charSpace)).1
  have hW₁ : atkinLehnerOperatorGamma1Cusp hp.pos hpN
      (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) k f.toCuspForm =
      (c * f.atkinLehnerSign hχ h) • f.toCuspForm := by
    have heq : atkinLehnerOperatorGamma1Cusp hp.pos hpN
        (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) k f.toCuspForm =
        CuspForm.ofLe (Gamma1_map_le_Gamma0_map N)
          (h.atkinLehnerOperatorCusp k (f.toCuspFormGamma0 hχ)) := by
      refine DFunLike.coe_injective ?_
      rw [coe_atkinLehnerOperatorGamma1Cusp, CuspForm.coe_ofLe,
        h.atkinLehnerOperatorCusp_eq (isAtkinLehnerMatrix_descendExtra hp hpN hpsq),
        coe_atkinLehnerOperatorCusp, coe_toCuspFormGamma0]
    rw [heq, hW]
    exact CuspForm.ext fun τ ↦ by simp
  -- The scalar multiple is both old and new, hence zero.
  rw [hW₁, f.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN, ← add_smul] at hold
  have h0 := Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k) _ hold
    (Submodule.smul_mem _ _ f.isNew)
  exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h0).resolve_right f.ne_zero) |>.trans
    (by rw [mul_comm])

/-- **The bad-prime eigenvalue at `p ∥ N` is nonzero**, for a newform of trivial nebentypus:
it is `±(√p) ^ (k - 2)` (`qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul`). -/
theorem qExpansion_coeff_prime_ne_zero_of_isExactDivisor (f : Newform N k) (hχ : f.χ = 1)
    (hp : p.Prime) (h : p ∥ N) : (qExpansion 1 f.toCuspForm).coeff p ≠ 0 := by
  rw [f.qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul hχ hp h.dvd (h.not_sq_dvd hp.one_lt.ne'),
    neg_ne_zero]
  refine mul_ne_zero ?_ (zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hp.pos))))
  rcases f.atkinLehnerSign_eq_one_or_neg_one hχ h with hε | hε <;> simp [hε]

/-- The square of `ε_p(f) · (√p) ^ (k - 2)` is `p ^ (k - 2)`, since the Atkin–Lehner sign
`ε_p(f)` at an exact divisor `p ∥ N` is `±1`. By `qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul`
this is the square of the eigenvalue `a_p(f)`. -/
@[simp]
theorem atkinLehnerSign_mul_sqrt_zpow_sq (f : Newform N k) (hχ : f.χ = 1) (h : p ∥ N) :
    (f.atkinLehnerSign hχ h * ((Real.sqrt p : ℝ) : ℂ) ^ (k - 2)) ^ 2 = (p : ℂ) ^ (k - 2) := by
  have hε : f.atkinLehnerSign hχ h ^ 2 = 1 := by
    rcases f.atkinLehnerSign_eq_one_or_neg_one hχ h with hε | hε <;> simp [hε]
  have hs : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]
  rw [mul_pow, hε, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs]

/-- **The square of the bad-prime eigenvalue at `p ∥ N` is `p ^ (k - 2)`**, for a newform of
trivial nebentypus: `a_p(f) = ±(√p) ^ (k - 2)` by
`qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul`, and the sign squares to `1`
(`atkinLehnerSign_mul_sqrt_zpow_sq`). -/
theorem qExpansion_coeff_prime_sq_of_isExactDivisor (f : Newform N k) (hχ : f.χ = 1)
    (hp : p.Prime) (h : p ∥ N) : (qExpansion 1 f.toCuspForm).coeff p ^ 2 = (p : ℂ) ^ (k - 2) := by
  have hpsq := h.not_sq_dvd hp.one_lt.ne'
  simp [hχ, hp, h.dvd, hpsq]

end HeckeRing.GL2.Newform
