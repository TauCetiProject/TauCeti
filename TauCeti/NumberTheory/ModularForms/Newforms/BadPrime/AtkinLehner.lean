/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# The bad-prime eigenvalue of a newform when `p` exactly divides the level

Let `p` be a prime exactly dividing `N`. Miyake's descent family at `p`
(`TauCeti.descendMatrix`) consists of the `p` upper-triangular matrices `[1, j; 0, p]` that define
`U_p`, together with one extra member `[1, 0; 0, p] γ_p`, where `γ_p ∈ Γ₀(N / p)` reduces to
`S = [0, -1; 1, 0]` modulo `p`. That extra member is an Atkin–Lehner matrix for `p` at level `N`
(`TauCeti.isAtkinLehnerMatrix_descendExtra`), so on underlying functions the descent is

`descendSlash f = U_p f + f ∣[k] W_p`

(`TauCeti.descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL`). For a cusp form `F` on
`Γ₀(N)` the descent is a cusp form of the lower level `Γ₁(N / p)`, so `U_p F + W_p F` is old at
level `N` (`HeckeRing.GL2.heckeUCuspNat_ofLe_add_ofLe_atkinLehnerOperatorCusp_mem_cuspFormsOld`).
This is Atkin and Lehner's relation `U_p ≡ -W_p` modulo old forms.

For a newform `f` of trivial nebentypus both operators act by scalars: `U_p f = a_p(f) • f` and
`𝒲_p f = ε_p(f) • f` for the normalized operator `𝒲_p = (√p) ^ (2 - k) • W_p` and the
Atkin–Lehner sign `ε_p(f) = ±1`. The form `(a_p(f) + ε_p(f) (√p) ^ (k - 2)) • f` is then both
old and new, hence zero, and so

`a_p(f) = -ε_p(f) · (√p) ^ (k - 2)`.

In particular `a_p(f) ≠ 0` and `a_p(f) ² = p ^ (k - 2)`. This is the case `v_p(N) = 1` of the
classification of the bad-prime eigenvalues of a newform, at trivial nebentypus.

## Main results

* `TauCeti.isAtkinLehnerMatrix_descendExtra`: the extra descent matrix is an Atkin–Lehner matrix
  for `p`, and `TauCeti.descendMatrix_eq_atkinLehnerGL` reads it in `GL (Fin 2) ℝ`.
* `TauCeti.descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL`: the descent slash sum is
  `U_p f + f ∣[k] W_p` when `p ∥ N`.
* `HeckeRing.GL2.heckeUCuspNat_ofLe_add_ofLe_atkinLehnerOperatorCusp_mem_cuspFormsOld`: for a
  cusp form `F` on `Γ₀(N)`, `U_p F + W_p F` is old.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul`: a newform of trivial
  nebentypus has `a_p = -ε_p · (√p) ^ (k - 2)` at every prime `p ∥ N`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_ne_zero_of_isExactDivisor` and
  `HeckeRing.GL2.Newform.qExpansion_coeff_prime_sq_of_isExactDivisor`: so `a_p ≠ 0` and
  `a_p ^ 2 = p ^ (k - 2)`, the latter from
  `HeckeRing.GL2.Newform.atkinLehnerSign_mul_sqrt_zpow_sq`: `(ε_p · (√p) ^ (k - 2)) ^ 2 =
  p ^ (k - 2)`.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. **185** (1970),
  134–160, Theorem 3.
* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14 and Theorem 4.6.17.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace TauCeti

variable {p N : ℕ}

/-! ### The extra descent matrix is an Atkin–Lehner matrix -/

/-- **The extra descent matrix is an Atkin–Lehner matrix for `p`.** For a prime `p` exactly
dividing `N`, the matrix `[1, 0; 0, p] γ_p` with `γ_p = descendExtraGamma p N` has upper-left
entry divisible by `p` and lower-right entry divisible by `p`, since `γ_p` reduces to
`S = [0, -1; 1, 0]` modulo `p`; lower-left entry divisible by `N`, since `γ_p ∈ Γ₀(N / p)`; and
determinant `p`. -/
theorem isAtkinLehnerMatrix_descendExtra (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N) :
    IsAtkinLehnerMatrix N p
      (!![1, 0; 0, (p : ℤ)] * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have h : ∀ i j,
      ((descendExtraGamma p N i j : ℤ) : ZMod p) = ((ModularGroup.S i j : ℤ) : ZMod p) :=
    fun i j ↦ by
      simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast] using
        congr_fun₂ (congrArg Subtype.val (descendExtraGamma_map_intCast_zmod_eq_S hp hpN hpsq)) i j
  have h00 : ((descendExtraGamma p N 0 0 : ℤ) : ZMod p) = 0 := by
    simp [h 0 0, ModularGroup.coe_S]
  set γ := descendExtraGamma p N
  obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h00
  obtain ⟨c, hc⟩ : ((N / p : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (N / p)).mp
    (Gamma0_mem.mp (descendExtraGamma_mem_Gamma0 hp hpN hpsq))
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two, ha, hc] at hdet
  have hM : !![1, 0; 0, (p : ℤ)] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(p : ℤ) * a, γ 0 1; (p : ℤ) * (N / p : ℕ) * c, (p : ℤ) * γ 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hc, mul_assoc]
  rw [hM]
  exact isAtkinLehnerMatrix_of_entries (Nat.mul_div_cancel' hpN).symm _ _ _ _ <| by
    linear_combination hdet

/-- **The extra descent matrix, read in `GL (Fin 2) ℝ`, is the Atkin–Lehner matrix
`[1, 0; 0, p] γ_p`.** This is the member of the descent family at the index `p`, present because
`p ∥ N`. -/
theorem descendMatrix_eq_atkinLehnerGL (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N)
    {v : Fin (descendMatrixCount p N)} (hv : p ≤ v.val) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    descendMatrix p N v = atkinLehnerGL hp.pos (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine Units.ext ?_
  rw [descendMatrix_of_le hv, coe_atkinLehnerGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.val_map_apply,
      Matrix.vecMul, dotProduct]

/-! ### The descent is `U_p + W_p` -/

variable (k : ℤ) in
/-- **When `p ∥ N`, the descent slash sum is `U_p f + f ∣[k] W_p`.** The family consists of the
`p` upper-triangular matrices of `U_p` and the Atkin–Lehner matrix `[1, 0; 0, p] γ_p`
(`descendMatrix_eq_atkinLehnerGL`). -/
theorem descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL (hp : p.Prime) (hpN : p ∣ N)
    (hpsq : ¬ p ^ 2 ∣ N) (f : ℍ → ℂ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    descendSlash k p N f = heckeSlashUpperTri k p f +
      f ∣[k] atkinLehnerGL hp.pos (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hc := descendMatrixCount_of_not_sq_dvd (p := p) hpsq
  rw [descendSlash_def, heckeSlashUpperTri_def,
    ← Fintype.sum_equiv (finCongr hc.symm) (fun v ↦ f ∣[k] descendMatrix p N (finCongr hc.symm v))
      _ fun _ ↦ rfl, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [descendMatrix_of_lt (by simp), ModularForm.rat_slash]
    -- `Fin.castSucc b` read through `finCongr` is `⟨b.val, _⟩`, the index `upperTriRep` takes
    rfl
  · rw [descendMatrix_eq_atkinLehnerGL hp hpN hpsq (by simp)]

end TauCeti

namespace HeckeRing.GL2

open TauCeti

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-! ### `U_p + W_p` is old -/

variable (k) in
/-- **`U_p + W_p` maps into the old subspace when `p ∥ N`** (Atkin–Lehner). For a cusp form `F`
on `Γ₀(N)`, the sum of `U_p F` and the Atkin–Lehner image `W_p F`, both read at level `Γ₁(N)`,
is the descent of `F` (`descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL`), a cusp
form of the proper divisor level `Γ₁(N / p)`. -/
theorem heckeUCuspNat_ofLe_add_ofLe_atkinLehnerOperatorCusp_mem_cuspFormsOld (hp : p.Prime)
    (h : p ∥ N) (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    heckeUCuspNat k p hp h.dvd (CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) F) +
        CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) (h.atkinLehnerOperatorCusp k F) ∈
      cuspFormsOld N k := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpsq := h.not_sq_dvd hp.one_lt.ne'
  have hcomp : (1 : (ZMod N)ˣ →* ℂˣ) =
      (1 : (ZMod (N / p))ˣ →* ℂˣ).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd)) :=
    (MonoidHom.one_comp _).symm
  have hdesc : heckeUCuspNat k p hp h.dvd (CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) F) +
      CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) (h.atkinLehnerOperatorCusp k F) =
      CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (Nat.div_dvd_of_dvd h.dvd))
        (descendCuspForm k hp h.dvd hcomp (ofLe_mem_cuspFormCharSpace_one F)) := by
    refine DFunLike.coe_injective ?_
    rw [FunLike.coe_add, CuspForm.coe_ofLe, CuspForm.coe_ofLe,
      coe_descendCuspForm, descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL k hp h.dvd
        hpsq, heckeUCuspNat_eq_heckeTCuspNat, heckeTCuspNat_eq_upperTri k h.dvd,
      coe_heckeSlashUpperTriCuspFormEnd, h.atkinLehnerOperatorCusp_eq
        (isAtkinLehnerMatrix_descendExtra hp h.dvd hpsq), coe_atkinLehnerOperatorCusp,
      CuspForm.coe_ofLe]
  rw [hdesc]
  exact ofLe_mem_cuspFormsOld (Nat.div_dvd_of_dvd h.dvd)
    (Nat.div_lt_self (NeZero.pos N) hp.one_lt).ne k _

/-! ### The eigenvalue `a_p` -/

namespace Newform

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
  -- `W_p f = c • ε_p • f`, undoing the normalization of `𝒲_p f = ε_p • f`
  have hW : h.atkinLehnerOperatorCusp k (f.toCuspFormGamma0 hχ) =
      (c * f.atkinLehnerSign hχ h) • f.toCuspFormGamma0 hχ := by
    have hε := f.normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul hχ h
    rw [Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp_def, LinearMap.smul_apply] at hε
    have hinv : c * atkinLehnerNormalizer p k = 1 := by
      rw [hc, atkinLehnerNormalizer_def, ← zpow_add₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hp.pos)))]
      simp
    rw [mul_smul, ← hε, smul_smul, hinv, one_smul]
  -- `U_p f + W_p f = (a_p + c ε_p) • f` is old, and it is new, so it vanishes
  have hold := heckeUCuspNat_ofLe_add_ofLe_atkinLehnerOperatorCusp_mem_cuspFormsOld k hp h
    (f.toCuspFormGamma0 hχ)
  have hsmul : CuspForm.ofLe (Gamma1_map_le_Gamma0_map N)
      ((c * f.atkinLehnerSign hχ h) • f.toCuspFormGamma0 hχ) =
      (c * f.atkinLehnerSign hχ h) • f.toCuspForm :=
    CuspForm.ext fun τ ↦ by simp
  rw [hW, hsmul, ofLe_toCuspFormGamma0,
    f.heckeUCuspNat_eq_qExpansion_coeff_smul hp h.dvd, ← add_smul] at hold
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

end Newform

end HeckeRing.GL2

