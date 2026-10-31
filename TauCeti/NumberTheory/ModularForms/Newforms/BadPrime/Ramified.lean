/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Fricke
import TauCeti.NumberTheory.ModularForms.Newforms.Fricke

/-!
# The bad-prime eigenvalue of a newform when the nebentypus is not defined modulo `N / p`

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ`, and let `p` be a prime dividing
`N` such that `χ` is not defined modulo `N / p`, that is, the `p`-part of the conductor of `χ` is
the full `p`-part of `N`. Then the `U_p`-eigenvalue `a_p(f)` satisfies

`|a_p(f)| = p ^ ((k - 1) / 2)`,

and in particular `a_p(f) ≠ 0` (Li, Theorem 3; Miyake, Theorem 4.6.17). Note the exponent
`(k - 1) / 2`, rather than the exponent `(k - 2) / 2` of the case `p ∥ N` with `χ` defined modulo
`N / p` (`HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq_of_isExactDivisor`).

The proof combines `U_p 𝒲_N U_p = p ^ (k - 1) 𝒲_N` on `S_k(N, χ)`
(`HeckeRing.GL2.heckeUCuspNat_normalizedFrickeOperatorCusp_heckeUCuspNat`) with the Fricke
relation `𝒲_N f = λ_N(f) • f_ρ`, where `λ_N(f) ≠ 0` and the conjugate newform `f_ρ` is a
`U_p`-eigenvector with eigenvalue `conj (a_p(f))`. Applying both sides to `f` gives
`a_p(f) · conj (a_p(f)) · λ_N(f) = p ^ (k - 1) · λ_N(f)`.

Together with `HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq_of_isExactDivisor` (`p ∥ N`, `χ`
defined modulo `N / p`) and `HeckeRing.GL2.Newform.qExpansion_coeff_prime_eq_zero_of_sq_dvd`
(`p ^ 2 ∣ N`, `χ` defined modulo `N / p`), this covers every prime dividing the level.

## Main results

* `HeckeRing.GL2.Newform.norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp`:
  `‖a_p(f)‖ ^ 2 = p ^ (k - 1)`.
* `HeckeRing.GL2.Newform.norm_qExpansion_coeff_prime_of_not_exists_eq_comp`:
  `‖a_p(f)‖ = (√p) ^ (k - 1)`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_ne_zero_of_not_exists_eq_comp`: `a_p(f) ≠ 0`.

## References

* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315,
  Theorem 3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.17.
-/

public section

open UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2.Newform

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-- **The bad-prime eigenvalue when the nebentypus is not defined modulo `N / p`** (Li,
Theorem 3): for a newform `f` and a prime `p ∣ N` such that the nebentypus of `f` is not of the
form `χ₀ ∘ (ZMod N → ZMod (N / p))`, `‖a_p(f)‖ ^ 2 = p ^ (k - 1)`. -/
theorem norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp (f : Newform N k) (hp : p.Prime)
    (hpN : p ∣ N)
    (hχ : ¬ ∃ χ₀ : (ZMod (N / p))ˣ →* ℂˣ, f.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    ‖(qExpansion 1 f.toCuspForm).coeff p‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
  set a := (qExpansion 1 f.toCuspForm).coeff p
  set c := f.frickePseudoEigenvalue
  have hU : heckeUCuspNat k p hp hpN f.toCuspForm = a • f.toCuspForm :=
    f.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN
  have hW : normalizedFrickeOperatorCusp k f.toCuspForm = c • f.conj.toCuspForm :=
    f.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul
  -- `f_ρ` is a `U_p`-eigenvector with eigenvalue `conj a`
  have hUc : heckeUCuspNat k p hp hpN f.conj.toCuspForm = starRingEnd ℂ a • f.conj.toCuspForm := by
    rw [f.conj.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN, qExpansion_conj,
      PowerSeries.coeff_map]
  have hc : c ≠ 0 := norm_ne_zero_iff.mp (f.norm_frickePseudoEigenvalue.symm ▸ one_ne_zero)
  -- both sides of `U_p 𝒲_N U_p f = p ^ (k - 1) 𝒲_N f` are multiples of `f_ρ`
  have hlhs : heckeUCuspNat k p hp hpN (normalizedFrickeOperatorCusp k
      (heckeUCuspNat k p hp hpN f.toCuspForm)) = (a * c * starRingEnd ℂ a) • f.conj.toCuspForm := by
    simp only [hU, hW, hUc, map_smul, smul_smul]
  have hrhs : (p : ℂ) ^ (k - 1) • normalizedFrickeOperatorCusp k f.toCuspForm =
      ((p : ℂ) ^ (k - 1) * c) • f.conj.toCuspForm := by
    rw [hW, smul_smul]
  have h := heckeUCuspNat_normalizedFrickeOperatorCusp_heckeUCuspNat hp hpN hχ f.mem_charSpace
  rw [hlhs, hrhs] at h
  have hmul : a * starRingEnd ℂ a = (p : ℂ) ^ (k - 1) :=
    mul_right_cancel₀ hc (by linear_combination smul_left_injective ℂ f.conj.ne_zero h)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hmul
  exact Complex.ofReal_injective (by rw [hmul, Complex.ofReal_zpow, Complex.ofReal_natCast])

/-- **The absolute value of the bad-prime eigenvalue when the nebentypus is not defined modulo
`N / p`**: `‖a_p(f)‖ = (√p) ^ (k - 1)`, that is `|a_p(f)| = p ^ ((k - 1) / 2)`. -/
theorem norm_qExpansion_coeff_prime_of_not_exists_eq_comp (f : Newform N k) (hp : p.Prime)
    (hpN : p ∣ N)
    (hχ : ¬ ∃ χ₀ : (ZMod (N / p))ˣ →* ℂˣ, f.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    ‖(qExpansion 1 f.toCuspForm).coeff p‖ = Real.sqrt p ^ (k - 1) := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  refine (sq_eq_sq₀ (norm_nonneg _) (zpow_nonneg (Real.sqrt_nonneg _) _)).mp ?_
  rw [f.norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp hp hpN hχ, ← zpow_natCast,
    ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs]

/-- **The bad-prime eigenvalue is nonzero when the nebentypus is not defined modulo `N / p`**:
its absolute value is `p ^ ((k - 1) / 2)`
(`HeckeRing.GL2.Newform.norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp`). -/
theorem qExpansion_coeff_prime_ne_zero_of_not_exists_eq_comp (f : Newform N k) (hp : p.Prime)
    (hpN : p ∣ N)
    (hχ : ¬ ∃ χ₀ : (ZMod (N / p))ˣ →* ℂˣ, f.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    (qExpansion 1 f.toCuspForm).coeff p ≠ 0 := by
  intro h0
  have hsq := f.norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp hp hpN hχ
  rw [h0, norm_zero, zero_pow two_ne_zero] at hsq
  exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero) hsq.symm

end HeckeRing.GL2.Newform
