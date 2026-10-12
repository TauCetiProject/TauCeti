/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Constant terms under level raising

At the cusp represented by `γ = [a,b;c,d]`, the degeneracy map `V_t f(z) = f(tz)`
multiplies the constant term at the reduced cusp `ta/c` by `(gcd(c,t)/t)^k`.
The formula uses any integral determinant-one representative whose first column is
`(ta/g, c/g)`, where `g = gcd(c,t)`; hence it involves no choice of a preferred representative.
It applies to modular forms for arbitrary arithmetic determinant-one subgroups with the
level-raising inclusion. This transports constant-term vectors of Eisenstein series to
higher levels.

The two matrix reductions also apply to functions with a transformation law, such as the
quasimodular weight-two Eisenstein series.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.1 and 4.5.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Filter Complex ModularForm
open scoped MatrixGroups Topology Pointwise

open TauCeti

namespace Matrix.SpecialLinearGroup

/-- A representative of the scaled cusp with primitive first column. -/
lemma exists_scaled_cusp_reduction (γ : SL(2, ℤ)) {t : ℕ} [NeZero t] :
    ∃ δ : SL(2, ℤ), (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t ∧
      γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t := by
  have hcop := Int.isCoprime_iff_gcd_eq_one.mp (γ.isCoprime_col 0)
  have hgcd : Int.gcd ((t : ℤ) * γ 0 0) (γ 1 0) = Int.gcd (γ 1 0) t := by
    rw [Int.gcd_mul_left_left_of_gcd_eq_one hcop, Int.gcd_comm]
  have hpos : 0 < Int.gcd ((t : ℤ) * γ 0 0) (γ 1 0) := by
    rw [hgcd]
    exact Int.gcd_pos_of_ne_zero_right _ (Nat.cast_ne_zero.mpr (NeZero.ne t))
  obtain ⟨a, c, hac, ha, hc⟩ := Int.exists_gcd_one hpos
  obtain ⟨δ, hδa, hδc⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hac).exists_SL2_col 0
  exact ⟨δ, by simpa [hδa, hgcd] using ha, by simpa [hδc, hgcd] using hc⟩

/-- Reducing the scaled cusp leaves an upper-triangular factor with lower-right entry
`t / gcd(c,t)`. -/
lemma scaled_cusp_upperTriangular (γ δ : SL(2, ℤ)) {t : ℕ} [NeZero t]
    (ha : (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t)
    (hc : γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t) :
    let β := (mapGL ℝ δ)⁻¹ * (scaleGL t * mapGL ℝ γ)
    β 1 0 = 0 ∧ β 1 1 = (t : ℝ) / Int.gcd (γ 1 0) t := by
  intro β
  have ha' : (t : ℝ) * γ 0 0 = (δ 0 0 : ℝ) * Int.gcd (γ 1 0) t := by
    exact_mod_cast ha
  have hc' : (γ 1 0 : ℝ) = (δ 1 0 : ℝ) * Int.gcd (γ 1 0) t := by
    exact_mod_cast hc
  have hentries : β 0 0 = (δ 1 1 : ℝ) * ((t : ℝ) * γ 0 0) - δ 0 1 * γ 1 0 ∧
      β 1 0 = -(δ 1 0 : ℝ) * ((t : ℝ) * γ 0 0) + δ 0 0 * γ 1 0 := by
    simp [β, ← map_inv, mapGL_coe_matrix,
      adjugate_fin_two, coe_scaleGL, Matrix.mul_apply,
      Fin.sum_univ_two, vecMul, dotProduct, sub_eq_add_neg]
  have hδ : (δ 0 0 : ℝ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    exact_mod_cast (δ.det_coe ▸ Matrix.det_fin_two (δ : Matrix (Fin 2) (Fin 2) ℤ)).symm
  have h00 : β 0 0 = (Int.gcd (γ 1 0) t : ℝ) := by
    rw [hentries.1, ha', hc']
    nlinarith [hδ]
  have h10 : β 1 0 = 0 := by rw [hentries.2, ha', hc']; ring
  have hdet : (β.det : ℝ) = t := by
    simp [β]
  have hprod : (Int.gcd (γ 1 0) t : ℝ) * β 1 1 = t := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h10] at hdet
    simpa using hdet
  have hg : (Int.gcd (γ 1 0) t : ℝ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right (γ 1 0)
      (Nat.cast_ne_zero.mpr (NeZero.ne t))).ne'
  exact ⟨h10, (eq_div_iff hg).mpr (by simpa [mul_comm] using hprod)⟩

end Matrix.SpecialLinearGroup

namespace ModularForm

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] [Γ.IsArithmetic]
  [Γ'.HasDetOne] [Γ'.IsArithmetic] {k : ℤ} {t : ℕ} [NeZero t]

/-- **Constant-term transport under level raising.** If `δ` represents the reduced cusp
`ta/c`, then the constant term of `V_t f` at `a/c` is `(gcd(c,t)/t)^k` times that of `f` at `δ`.
The first-column equations fix the sign of the representative, including in odd weight. -/
theorem constantTermAt_levelRaise (f : ModularForm Γ k)
    (h : Γ' ≤ ConjAct.toConjAct (TauCeti.scaleGL t)⁻¹ • Γ) (γ δ : SL(2, ℤ))
    (ha : (t : ℤ) * γ 0 0 = δ 0 0 * Int.gcd (γ 1 0) t)
    (hc : γ 1 0 = δ 1 0 * Int.gcd (γ 1 0) t) :
    constantTermAt γ (TauCeti.ModularForm.levelRaise t h f) =
      ((Int.gcd (γ 1 0) t : ℂ) / t) ^ k * constantTermAt δ f := by
  let β := (mapGL ℝ δ)⁻¹ * (TauCeti.scaleGL t * mapGL ℝ γ)
  obtain ⟨h10, h11⟩ := γ.scaled_cusp_upperTriangular δ ha hc
  have hdet : (β.det : ℝ) = t := by simp [β]
  have hdetpos : 0 < (β : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← GeneralLinearGroup.val_det_apply, hdet]
    exact_mod_cast NeZero.pos t
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  have hlim := TauCeti.tendsto_slash_atImInfty_of_upperTriangular k β h10
    (tendsto_translate_constantTermAt δ f)
  rw [coe_translate, ← SlashAction.slash_mul, mul_inv_cancel_left] at hlim
  have hlim' := hlim.const_mul ((t : ℂ) ^ (1 - k))
  have hfun : ⇑(translate (TauCeti.ModularForm.levelRaise t h f) (mapGL ℝ γ)) =
      fun z ↦ (t : ℂ) ^ (1 - k) * (⇑f ∣[k] (TauCeti.scaleGL t * mapGL ℝ γ)) z := by
    rw [coe_translate, TauCeti.ModularForm.coe_levelRaise, smul_slash,
      σ_eq_refl_of_det_pos (by
        rw [← GeneralLinearGroup.val_det_apply, det_mapGL]
        norm_num), ContinuousAlgEquiv.refl_apply,
      ← SlashAction.slash_mul]
    rfl
  rw [constantTermAt_eq_valueAtInfty, hfun]
  refine hlim'.limUnder_eq.trans ?_
  rw [σ_eq_refl_of_det_pos hdetpos, ContinuousAlgEquiv.refl_apply,
    hdet, abs_of_pos (by exact_mod_cast NeZero.pos t), h11]
  -- The normalization of `V_t` cancels the determinant power in the arithmetic slash.
  push_cast
  rw [div_zpow, div_zpow]
  simp only [zpow_neg, div_eq_mul_inv, inv_inv]
  have hp : (t : ℂ) ^ (1 - k) * (t : ℂ) ^ (k - 1) = 1 := by
    rw [← zpow_add₀ ht]
    simp
  linear_combination hp * (Int.gcd (γ 1 0) t : ℂ) ^ k *
    ((t : ℂ) ^ k)⁻¹ * constantTermAt δ f

end ModularForm
