/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.NewSpace
public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign
public import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Descent
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# The bad-prime eigenvalue of a newform when `p` exactly divides the level

Let `f` be a newform of level `N` and `p ∥ N` a prime whose nebentypus `χ` is defined modulo
`N / p`, that is `χ = χ₀ ∘ (ZMod N → ZMod (N / p))` for a character `χ₀` modulo `N / p`. Let
`W_p` be the slash by the Atkin–Lehner matrix `diag(1, p) γ_p` of Miyake's descent family. The
descent relation puts `U_p f + W_p f` in the old subspace
(`Newforms/BadPrime/Descent.lean`). Both summands are new: `U_p f = a_p(f) f`, and `W_p`
preserves the new subspace. So the sum vanishes and

`W_p f = -a_p(f) · f`.

The square `W_p ∘ W_p` is `p ^ (k - 2)` times the diamond operator of a unit that is `p` modulo
`N / p`, and it acts on `f` by `p ^ (k - 2) χ₀(p)`. Hence

`a_p(f) ² = χ₀(p) · p ^ (k - 2)`,

and in particular `a_p(f) ≠ 0` (Li, Theorem 3; Miyake, Theorem 4.6.17). For trivial nebentypus
`W_p` acts on `f` through its Atkin–Lehner sign, and the eigenvalue is
`a_p(f) = -ε_p(f) · (√p) ^ (k - 2)` (Atkin–Lehner, Theorem 3), where `ε_p(f) = ±1` is the
eigenvalue of the normalized operator `𝒲_p = (√p) ^ (2 - k) • W_p`.

## Main results

* `HeckeRing.GL2.Newform.atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul`:
  `W_p f = -a_p(f) • f`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq_of_isExactDivisor`: the square of `a_p`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_ne_zero_of_isExactDivisor`: nonvanishing.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul`: the eigenvalue formula
  for trivial nebentypus.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on Γ₀(m)*, Math. Ann. **185** (1970),
  134–160, Theorem 3.
* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315,
  Theorem 3.
* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14 and Theorem 4.6.17.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace HeckeRing.GL2.Newform

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-! ### Nebentypus defined modulo `N / p` -/

/-- **A newform is a `W_p`-eigenvector with eigenvalue `-a_p` at `p ∥ N`**, when its nebentypus
is defined modulo `N / p`. Here `W_p` is the unnormalized slash by the Atkin–Lehner matrix
`diag(1, p) γ_p` of Miyake's descent family.

The hypothesis `p ∥ N` is stated as `p ∣ N` and `¬ p ^ 2 ∣ N`, the form the descent matrix
takes. -/
theorem atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul (f : Newform N k)
    (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hχ : f.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    atkinLehnerOperatorGamma1Cusp hp.pos hpN (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) k
        f.toCuspForm =
      -(qExpansion 1 f.toCuspForm).coeff p • f.toCuspForm := by
  -- `U_p f + W_p f` is old by the descent relation, and new since `U_p f = a_p(f) • f` and
  -- `W_p f` are new, so it is zero
  have hold :=
    (heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld_inf_cuspFormCharSpace
      k hp hpN hpsq hχ f.mem_charSpace).1
  rw [f.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN] at hold
  have h0 := Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k) _ hold
    (Submodule.add_mem _ (Submodule.smul_mem _ _ f.isNew)
      (atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hp.pos hpN _ f.isNew))
  exact (eq_neg_of_add_eq_zero_right h0).trans (_root_.neg_smul _ _).symm

/-- **The square of the bad-prime eigenvalue at `p ∥ N`** (Li, Theorem 3): a newform `f` whose
nebentypus is the pull-back of a character `χ₀` modulo `N / p` has `a_p(f) ² = χ₀(p) p ^ (k - 2)`.
In particular `a_p(f) ² = p ^ (k - 2)` for trivial nebentypus. -/
theorem qExpansion_coeff_prime_sq_of_isExactDivisor (f : Newform N k) (hp : p.Prime) (h : p ∥ N)
    {χ₀ : (ZMod (N / p))ˣ →* ℂˣ} (hχ : f.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    (qExpansion 1 f.toCuspForm).coeff p ^ 2 =
      χ₀ (ZMod.unitOfCoprime p h.coprime) * (p : ℂ) ^ (k - 2) := by
  have hpsq := h.not_sq_dvd hp.one_lt.ne'
  have hW := isAtkinLehnerMatrix_descendExtra hp h.dvd hpsq
  obtain ⟨γ, hγ, hsq⟩ := hW.exists_mem_Gamma0_mul_self hp.ne_zero h.dvd
  have hu := hW.unitsMap_toHomUnits_gamma0Map_of_mul_self_eq hp.ne_zero h.dvd hγ hsq
  have hu' := hW.natCast_mul_toHomUnits_gamma0Map_of_mul_self_eq hγ hsq
  -- the diamond label of `W_p ∘ W_p` is `p` modulo `N / p`
  have hup : ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) =
      ZMod.unitOfCoprime p h.coprime := by
    have hγ₁₁ : ((descendExtraGamma p N 1 1 : ℤ) : ZMod (N / p)) = 1 := by
      simpa using congr_fun₂ (congrArg Subtype.val
        (descendExtraGamma_map_intCast_zmod_div_eq_one hp h.dvd hpsq)) 1 1
    -- reduce `p u = W₁₁ ^ 2` modulo `N / p`, where `W₁₁ = p (γ_p)₁₁` and `(γ_p)₁₁ ≡ 1`
    have hcast := congrArg (ZMod.castHom (Nat.div_dvd_of_dvd h.dvd) (ZMod (N / p))) hu'
    simp only [map_mul, map_pow, map_natCast, map_intCast] at hcast
    refine Units.ext ((ZMod.unitOfCoprime p h.coprime).isUnit.mul_left_cancel ?_)
    simpa [ZMod.unitsMap_val, Matrix.mul_apply, Fin.sum_univ_two, hγ₁₁, sq] using hcast
  -- `W_p ∘ W_p = p ^ (k - 2) ⟨u⟩` acts on `f` by `p ^ (k - 2) χ₀(p)`, and by `a_p(f) ^ 2` since
  -- `W_p f = -a_p(f) • f`
  have hWW := atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp hp.pos h.dvd hW hu hu'
    f.toCuspForm
  rw [diamondOpCusp_apply_of_mem_cuspFormCharSpace k f.χ _ f.mem_charSpace, hχ,
    MonoidHom.comp_apply, hup,
    f.atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul hp h.dvd hpsq hχ, map_smul,
    f.atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul hp h.dvd hpsq hχ, smul_smul,
    smul_smul] at hWW
  linear_combination smul_left_injective ℂ f.ne_zero hWW

/-- **The bad-prime eigenvalue at `p ∥ N` is nonzero**, for a newform whose nebentypus is defined
modulo `N / p`: its square is `χ₀(p) p ^ (k - 2)` (`qExpansion_coeff_prime_sq_of_isExactDivisor`).
-/
theorem qExpansion_coeff_prime_ne_zero_of_isExactDivisor (f : Newform N k) (hp : p.Prime)
    (h : p ∥ N) {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hχ : f.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    (qExpansion 1 f.toCuspForm).coeff p ≠ 0 := by
  intro h0
  have hsq := f.qExpansion_coeff_prime_sq_of_isExactDivisor hp h hχ
  rw [h0, zero_pow two_ne_zero] at hsq
  exact mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)) hsq.symm

/-! ### Trivial nebentypus -/

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
  -- `W_p f = -a_p(f) • f` for every nebentypus defined modulo `N / p`, here the trivial one.
  rw [f.atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul hp hpN hpsq
    (hχ.trans (MonoidHom.one_comp _).symm)] at hW₁
  linear_combination -smul_left_injective ℂ f.ne_zero hW₁

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

end HeckeRing.GL2.Newform
