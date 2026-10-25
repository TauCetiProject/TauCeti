/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Fourier parity and orders at irregular cusps

If the negative translation `-[1,h;0,1]` belongs to the group of a weight-`k`
modular form, then `f(z+h) = (-1)^k f(z)`. Its expansion in `q₂ₕ` therefore
has coefficients only in degrees of the same parity as `k`.

At an irregular cusp the negative translation by the projective width belongs
to the group. For a nonzero odd-weight form, its leading `q₂ₕ` degree is odd,
so the width-normalized order is `m + 1/2` for a nonnegative integer `m`.
In particular the form vanishes at that cusp. In even weight the same convention
gives integral order, including for the zero form. The period in these statements
is twice the projective width, independently of the weight.

The statements are at infinity; applying them to an integral slash of a form
gives the corresponding statements at the represented cusp.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§2.4 and 3.6,
  with the corrected irregular-cusp order convention in the errata to pp. 74–75.

The order is the existing `TauCeti.orderAtCusp`; coefficient uniqueness uses
Mathlib's `ModularFormClass.qExpansion_coeff_unique`.
-/

public noncomputable section

open Matrix.GeneralLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace TauCeti.ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ}
variable {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]

/-- A negative translation forces the `q₂ₕ` coefficients to transform by the
same sign as the weight. -/
theorem neg_one_pow_mul_qExpansion_coeff_eq_neg_one_zpow_mul (f : F) (hh : 0 < h)
    (hΓ : -upperRightHom h ∈ Γ) (n : ℕ) :
    (-1 : ℂ) ^ n * (qExpansion (2 * h) f).coeff n =
      (-1 : ℂ) ^ k * (qExpansion (2 * h) f).coeff n := by
  have hperiod : 2 * h ∈ Γ.strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    -- Squaring the negative translation gives the positive translation by twice the width.
    have hs := Γ.pow_mem hΓ 2
    rw [neg_sq, ← AddChar.map_nsmul_eq_pow, two_nsmul, ← two_mul] at hs
    exact hs
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods (by positivity) hperiod⟩
  have hq (z : ℍ) : Function.Periodic.qParam (2 * h) (h +ᵥ z : ℍ) =
      -Function.Periodic.qParam (2 * h) z := by
    have hhalf : ((2 * h : ℝ) : ℂ) / 2 = (h : ℂ) := by push_cast; ring
    have H := TauCeti.Periodic.qParam_add_half (h := 2 * h) (by positivity) (z : ℂ)
    rw [hhalf, add_comm] at H
    simpa only [coe_vadd] using H
  have hsign : (-1 : ℂ) ^ k ≠ 0 := zpow_ne_zero k (by norm_num)
  have hsum (z : ℍ) : HasSum (fun m : ℕ ↦
      (((-1 : ℂ) ^ k)⁻¹ * ((-1 : ℂ) ^ m * (qExpansion (2 * h) f).coeff m)) •
        Function.Periodic.qParam (2 * h) z ^ m) (f z) := by
    have H := (_root_.ModularForm.hasSum_qExpansion f (by positivity : 0 < 2 * h)
      hperiod (h +ᵥ z)).mul_left (((-1 : ℂ) ^ k)⁻¹)
    rw [SlashInvariantForm.vadd_apply_of_neg_upperRightHom_mem f hΓ, hq,
      inv_mul_cancel_left₀ hsign] at H
    refine H.congr_fun fun m ↦ ?_
    simp only [smul_eq_mul]
    rw [neg_pow (Function.Periodic.qParam (2 * h) z)]
    ring
  exact (inv_mul_eq_iff_eq_mul₀ hsign).mp
    (ModularFormClass.qExpansion_coeff_unique (f := f)
      (by positivity : 0 < 2 * h) hperiod hsum n)

/-- Nonzero `q₂ₕ` coefficients have the same parity as the weight when a negative
translation by `h` belongs to the group. -/
theorem even_qExpansion_index_iff_even_weight (f : F) (hh : 0 < h)
    (hΓ : -upperRightHom h ∈ Γ) {n : ℕ} (hn : (qExpansion (2 * h) f).coeff n ≠ 0) :
    Even n ↔ Even k := by
  have hs := mul_right_cancel₀ hn
    (neg_one_pow_mul_qExpansion_coeff_eq_neg_one_zpow_mul f hh hΓ n)
  rw [← neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1), hs,
    neg_one_zpow_eq_ite]
  by_cases hk : Even k <;> norm_num [hk]

/-- Coefficients whose parity differs from the weight vanish in the doubled-period
expansion at a negative translation. -/
theorem qExpansion_coeff_eq_zero_of_parity_ne (f : F) (hh : 0 < h)
    (hΓ : -upperRightHom h ∈ Γ) {n : ℕ} (hn : ¬(Even n ↔ Even k)) :
    (qExpansion (2 * h) f).coeff n = 0 := by
  by_contra hc
  exact hn (even_qExpansion_index_iff_even_weight f hh hΓ hc)

/-- Every odd-weight modular form vanishes at an irregular cusp, including the
zero form. -/
theorem isZeroAtImInfty_of_odd_of_not_isRegularAtInfty [Γ.IsArithmetic]
    (f : F) (hk : Odd k) (hΓ : ¬Γ.IsRegularAtInfty) :
    IsZeroAtImInfty f := by
  have hzero : (qExpansion (2 * Γ.widthInfty) f).coeff 0 = 0 :=
    qExpansion_coeff_eq_zero_of_parity_ne f Γ.widthInfty_pos
      (neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γ hΓ)
      (by simpa using Int.not_even_iff_odd.mpr hk)
  simpa only [IsZeroAtImInfty, Filter.ZeroAtFilter, hzero] using
    ModularFormClass.tendsto_atImInfty f
    (mul_pos (by norm_num) Γ.widthInfty_pos) Γ.two_mul_widthInfty_mem_strictPeriods

/-- The nonzero leading coefficient at an irregular cusp has the parity of the weight. -/
theorem even_qExpansion_order_toNat_iff_even_weight [Γ.IsArithmetic]
    (f : F) (hf : (f : ℍ → ℂ) ≠ 0) (hΓ : ¬Γ.IsRegularAtInfty) :
    Even (qExpansion (2 * Γ.widthInfty) f).order.toNat ↔ Even k := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods
    (mul_pos (by norm_num) Γ.widthInfty_pos) Γ.two_mul_widthInfty_mem_strictPeriods⟩
  have hq : qExpansion (2 * Γ.widthInfty) f ≠ 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff (mul_pos (by norm_num) Γ.widthInfty_pos)
      (SlashInvariantFormClass.periodic_comp_ofComplex f Γ.two_mul_widthInfty_mem_strictPeriods)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)).not.mpr hf
  exact even_qExpansion_index_iff_even_weight f Γ.widthInfty_pos
    (neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γ hΓ)
    (PowerSeries.coeff_order hq)

/-- A nonzero odd-weight form at an irregular cusp has odd leading degree in
the expansion of period twice the projective width. -/
theorem odd_qExpansion_order_of_not_isRegularAtInfty [Γ.IsArithmetic]
    (f : F) (hf : (f : ℍ → ℂ) ≠ 0) (hk : Odd k) (hΓ : ¬Γ.IsRegularAtInfty) :
    Odd (qExpansion (2 * Γ.widthInfty) f).order.toNat := by
  exact Nat.not_even_iff_odd.mp fun he ↦ (Int.not_even_iff_odd.mpr hk)
    ((even_qExpansion_order_toNat_iff_even_weight f hf hΓ).mp he)

/-- The order of a nonzero odd-weight form at an irregular cusp is a strictly
half-integral nonnegative number, with the doubled-width convention. -/
theorem exists_orderAtCusp_eq_natCast_add_half_of_odd_of_not_isRegularAtInfty [Γ.IsArithmetic]
    (f : F) (hf : (f : ℍ → ℂ) ≠ 0) (hk : Odd k) (hΓ : ¬Γ.IsRegularAtInfty) :
    ∃ m : ℕ, TauCeti.orderAtCusp Γ.widthInfty f = (m : ℚ) + 1 / 2 := by
  obtain ⟨m, hm⟩ := odd_qExpansion_order_of_not_isRegularAtInfty f hf hk hΓ
  refine ⟨m, ?_⟩
  rw [TauCeti.orderAtCusp_def, TauCeti.qExpansionOrderAtCusp_def, hm]
  push_cast
  ring

/-- In even weight the cusp order is integral at every cusp, using its projective width. -/
theorem exists_orderAtCusp_eq_natCast_of_even [Γ.IsArithmetic]
    (f : F) (hk : Even k) :
    ∃ m : ℕ, TauCeti.orderAtCusp Γ.widthInfty f = m := by
  have hper : Function.Periodic (f ∘ ofComplex) Γ.widthInfty := by
    by_cases hΓ : Γ.IsRegularAtInfty
    · exact SlashInvariantFormClass.periodic_comp_ofComplex f (Γ.isRegularAtInfty_iff.mp hΓ)
    · apply UpperHalfPlane.periodic_comp_ofComplex
      intro z
      rw [SlashInvariantForm.vadd_apply_of_neg_upperRightHom_mem f
        (neg_upperRightHom_widthInfty_mem_of_not_isRegularAtInfty Γ hΓ),
        hk.neg_one_zpow, one_mul]
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods
    (mul_pos (by norm_num) Γ.widthInfty_pos) Γ.two_mul_widthInfty_mem_strictPeriods⟩
  refine ⟨(qExpansion Γ.widthInfty f).order.toNat, ?_⟩
  simpa only [TauCeti.qExpansionOrderAtCusp_def, Int.cast_natCast] using
    TauCeti.orderAtCusp_eq_qExpansionOrderAtCusp Γ.widthInfty_pos hper
      (ModularFormClass.bdd_at_infty f) (ModularFormClass.holo f)

end TauCeti.ModularForm
