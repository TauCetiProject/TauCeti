/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.MulDiscriminant

import TauCeti.Analysis.Complex.Periodic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

/-!
# `q`-expansions of multiples of the discriminant

Let `Γ(N) ≤ Γ ≤ SL₂(ℤ)`. Since `Δ` is invariant under `SL₂(ℤ)`, at every cusp the expansion of
`f Δ` at the common period `N` is that of `f` times that of `Δ`
(`ModularForm.qExpansion_translate_mulDiscriminant`). At period `N` the expansion of `Δ` is
`qᴺ + ⋯`, so the range of multiplication by `Δ` is cut out by the vanishing of the first `N`
coefficients at every cusp (`ModularForm.mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero`),
linear conditions with integer coefficients.

## Main results

* `ModularForm.qExpansion_translate_mulDiscriminant`: at every cusp, the expansion of `f Δ` is
  that of `f` times that of `Δ`.
* `ModularForm.mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero`: a form of weight
  `k + 12` is divisible by `Δ` exactly when its first `N` coefficients at period `N` vanish at
  every cusp.
-/

public section

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup Filter Asymptotics
open scoped MatrixGroups

namespace ModularForm

open TauCeti TauCeti.ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {N : ℕ} [NeZero N]

/-- At every cusp, the expansion of `f Δ` at period `N` is that of `f` times that of `Δ`. -/
theorem qExpansion_translate_mulDiscriminant
    (hΓN : (Γ(N) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ) (hΓ : Γ ≤ 𝒮ℒ) (f : ModularForm Γ k)
    (γ : SL(2, ℤ)) :
    qExpansion N (translate (mulDiscriminant hΓ f) (mapGL ℝ γ)) =
      qExpansion N (translate f (mapGL ℝ γ)) * qExpansion N discriminant := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hslash : ⇑(translate (mulDiscriminant hΓ f) (mapGL ℝ γ)) =
      ⇑(translate f (mapGL ℝ γ)) * discriminant := by
    rw [coe_translate, coe_translate, coe_mulDiscriminant]
    exact (mul_slash_SL2 k 12 γ _ _).trans (by rw [discriminant_slash]; rfl)
  rw [hslash]
  exact qExpansion_mul
    (ModularFormClass.analyticAt_cuspFunction_zero _ hN
      (natCast_mem_strictPeriods_conjAct_of_Gamma_le hΓN γ))
    (ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant hN
      (by rw [Subgroup.strictPeriods_SL2Z]; exact ⟨N, by simp⟩))

variable [Γ.IsArithmetic]

/-- **The forms divisible by `Δ`.** For `Γ(N) ≤ Γ ≤ SL₂(ℤ)`, a form of weight `k + 12` is `Δ`
times a form of weight `k` exactly when, at every cusp, the first `N` coefficients of its
expansion at period `N` vanish. -/
theorem mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero
    (hΓN : (Γ(N) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ) (hΓ : Γ ≤ 𝒮ℒ) {g : ModularForm Γ (k + 12)} :
    g ∈ LinearMap.range (mulDiscriminant hΓ) ↔
      ∀ (γ : SL(2, ℤ)), ∀ n < N, (qExpansion N (translate g (mapGL ℝ γ))).coeff n = 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  constructor
  · rintro ⟨f, rfl⟩ γ n hn
    rw [qExpansion_translate_mulDiscriminant hΓN hΓ, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have := Finset.mem_antidiagonal.mp hp
    rw [qExpansion_natCast_discriminant_coeff_of_lt (by omega), mul_zero]
  · refine fun hg ↦ (mem_range_mulDiscriminant_iff hΓ).mpr fun γ ↦ ?_
    have hNγ := natCast_mem_strictPeriods_conjAct_of_Gamma_le hΓN γ
    let G := translate g (mapGL ℝ γ)
    -- `G = O(‖q_N‖ ^ N) = O(‖q‖)` at `i∞`, and `‖q‖ = O(Δ)`.
    have hG : ⇑G =O[atImInfty] fun τ : ℍ ↦ ‖Function.Periodic.qParam N τ‖ ^ N :=
      ((TauCeti.ModularFormClass.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero G hN hNγ N
        (hg γ)).comp_tendsto (qParam_tendsto_atImInfty hN)).congr_left fun τ ↦
          eq_cuspFunction τ hN.ne' (SlashInvariantFormClass.periodic_comp_ofComplex G hNγ)
    have hq : (fun τ : ℍ ↦ ‖Function.Periodic.qParam N τ‖ ^ N) =
        fun τ ↦ Real.exp (-2 * Real.pi * τ.im) := by
      funext τ
      rw [← norm_pow, ← mul_one (N : ℝ), TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne N),
        Function.Periodic.norm_qParam]
      simp
    exact hG.trans (hq ▸ exp_isBigO_discriminant)

end ModularForm
