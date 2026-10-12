/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Gamma1
public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
public import TauCeti.NumberTheory.ModularForms.Newforms.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Basic

/-!
# The unramified bad-prime descent relation

Let `p` exactly divide `N`, and let the nebentypus of a cusp form `f` of level `Γ₁(N)`
descend to `N / p`. Miyake's descent family consists of the `p` upper-triangular matrices
for `U_p` and one extra matrix `W = diag(1,p) γ_p`. The latter is an Atkin–Lehner matrix
for `p`, so the descent is `U_p f + W f`. This is a cusp form of level `Γ₁(N/p)`;
its restriction to level `N` is therefore old.

The identity is stated for the unnormalized arithmetic slash operator and the particular
matrix supplied by the descent family. No trivial-nebentypus assumption is needed.
It gives the relation between `U_p` and `W_p` modulo old forms in the unramified-character
case of the bad-prime eigenvalue classification.

## Main results

* `isAtkinLehnerMatrix_descendExtra`: the extra descent matrix is an Atkin–Lehner matrix.
* `descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL`: the identity on functions.
* `ofLe_descendCuspForm_eq_heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp`: the bundled identity.
* `heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld_inf_cuspFormCharSpace`:
  the sum is old and has the original nebentypus.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14 and Theorem 4.6.17.
* A. O. L. Atkin and J. Lehner, *Hecke operators on Γ₀(m)*, Math. Ann. **185** (1970),
  134–160, Theorem 3, for the trivial-nebentypus specialization.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace TauCeti

variable {p N : ℕ}

/-- The extra descent matrix `diag(1,p) γ_p` is an Atkin–Lehner matrix for `p` at level `N`
when `p` exactly divides `N`. -/
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

/-- The extra member of the descent family, read in `GL₂(ℝ)`, is the Atkin–Lehner matrix
`diag(1,p) γ_p`. -/
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

variable (k : ℤ) in
/-- When `p` exactly divides `N`, the descent slash sum is `U_p f + f ∣[k] W_p`,
with `W_p = diag(1,p) γ_p` the extra descent matrix. -/
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
    -- `Fin.castSucc b` read through `finCongr` is the index `upperTriRep` takes.
    rfl
  · rw [descendMatrix_eq_atkinLehnerGL hp hpN hpsq (by simp)]

variable [NeZero N] (k : ℤ)

/-- For a nebentypus descending to `N/p`, the restriction of Miyake's descent is exactly
`U_p f + W_p f` as a cusp form of level `Γ₁(N)`. -/
theorem ofLe_descendCuspForm_eq_heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp
    (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (Nat.div_dvd_of_dvd hpN))
        (descendCuspForm k hp hpN hcomp hf) =
      heckeUCuspNat k p hp hpN f +
        atkinLehnerOperatorGamma1Cusp hp.pos hpN
          (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) k f := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine DFunLike.coe_injective ?_
  rw [CuspForm.coe_ofLe, coe_descendCuspForm,
    descendSlash_eq_heckeSlashUpperTri_add_slash_atkinLehnerGL k hp hpN hpsq,
    FunLike.coe_add, heckeUCuspNat_eq_heckeTCuspNat, heckeTCuspNat_eq_upperTri k hpN,
    coe_heckeSlashUpperTriCuspFormEnd, coe_atkinLehnerOperatorGamma1Cusp]

/-- At `p ∥ N`, `U_p f + W_p f` is old with nebentypus `χ` whenever `χ` descends to
`N/p`. The operator `W_p` uses the extra matrix in Miyake's descent family; it is not normalized.
This is the unramified-character trace relation in the fixed-character old subspace. -/
theorem heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld_inf_cuspFormCharSpace
    (hp : p.Prime) (hpN : p ∣ N) (hpsq : ¬ p ^ 2 ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeUCuspNat k p hp hpN f +
        atkinLehnerOperatorGamma1Cusp hp.pos hpN
          (isAtkinLehnerMatrix_descendExtra hp hpN hpsq) k f ∈
      cuspFormsOld N k ⊓ cuspFormCharSpace k χ := by
  subst χ
  rw [← ofLe_descendCuspForm_eq_heckeUCuspNat_add_atkinLehnerOperatorGamma1Cusp
    k hp hpN hpsq rfl hf]
  exact ⟨ofLe_mem_cuspFormsOld (Nat.div_dvd_of_dvd hpN)
      (Nat.div_lt_self (NeZero.pos N) hp.one_lt).ne k _,
    CuspForm.ofLe_mem_cuspFormCharSpace χ₀ (Nat.div_dvd_of_dvd hpN)
      (descendCuspForm_mem_cuspFormCharSpace k hp hpN rfl hf)⟩

end TauCeti
