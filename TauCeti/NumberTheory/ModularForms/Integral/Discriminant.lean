/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.MulDiscriminant

import TauCeti.Analysis.Complex.Periodic
import TauCeti.LinearAlgebra.Span.CommonKernel
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
import TauCeti.NumberTheory.ModularForms.QExpansion.Order
import TauCeti.RingTheory.PowerSeries.SubringCoeff

/-!
# Integral forms and division by the discriminant

Let `Γ(N) ≤ Γ ≤ SL₂(ℤ)` and let `R ⊆ ℂ` be a subring. The discriminant `Δ` has integer
`q`-expansion `q + ⋯` and is invariant under `SL₂(ℤ)`, so at every cusp, read at the common
period `N`, its expansion is `qᴺ` times a unit power series over `ℤ`. Multiplying by `Δ` therefore
neither creates nor destroys integrality: `f Δ` is integral at every cusp exactly when `f` is
(`TauCeti.ModularForm.mulDiscriminant_mem_integralAtCusps_iff`). Its image is cut out by the
vanishing of the first `N` coefficients at every cusp
(`ModularForm.mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero`), linear conditions
with integer coefficients.

Together these show that if the forms of weight `k + 12` integral at every cusp span
`M_{k+12}(Γ)` over `ℂ`, then the forms of weight `k` integral at every cusp span `M_k(Γ)`
(`TauCeti.ModularForm.span_integralAtCusps_eq_top_of_add_twelve`). Deligne–Serre's lattice of
forms integral at every cusp needs this spanning statement to carry the Hecke eigenvalues; the
descent reduces it in weight one to the same statement in weight `13`.

## Main results

* `TauCeti.ModularForm.mulDiscriminant_mem_integralAtCusps_iff`: `f Δ` is integral at every cusp
  if and only if `f` is.
* `ModularForm.mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero`: a form of weight
  `k + 12` is divisible by `Δ` exactly when its first `N` coefficients at period `N` vanish at
  every cusp.
* `TauCeti.ModularForm.span_integralAtCusps_eq_top_of_add_twelve`: spanning by integral forms
  descends from weight `k + 12` to weight `k`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, §2.7.
-/

public section

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup Filter Asymptotics
open scoped MatrixGroups Topology

namespace ModularForm

open TauCeti TauCeti.ModularForm

variable {R : Subring ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {N : ℕ} [NeZero N]

/-- The expansion of `Δ` at period `N` is its expansion at period `1` in the variable `qᴺ`. -/
private theorem qExpansion_natCast_discriminant :
    qExpansion N discriminant =
      PowerSeries.expand N (NeZero.ne N) (qExpansion 1 discriminant) := by
  simpa using TauCeti.qExpansion_nat_mul one_pos (Nat.pos_of_ne_zero (NeZero.ne N))
    (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL)
    (ModularFormClass.bdd_at_infty CuspForm.discriminant) CuspForm.discriminant.holo'

/-- The coefficients of `Δ` at period `N` vanish below `N`. -/
private theorem qExpansion_natCast_discriminant_coeff_of_lt {i : ℕ} (hi : i < N) :
    (qExpansion N discriminant).coeff i = 0 := by
  rw [qExpansion_natCast_discriminant, PowerSeries.coeff_expand]
  split_ifs with h
  · obtain rfl : i = 0 := Nat.eq_zero_of_dvd_of_lt h hi
    simpa using discriminant_qExpansion_coeff_zero
  · rfl

/-- The coefficient of `qᴺ` in the expansion of `Δ` at period `N` is `1`. -/
private theorem qExpansion_natCast_discriminant_coeff_self :
    (qExpansion N discriminant).coeff N = 1 := by
  simpa [qExpansion_natCast_discriminant, discriminant_qExpansion_coeff_one] using
    PowerSeries.coeff_expand_mul N (NeZero.ne N) (qExpansion 1 discriminant) 1

/-- The coefficients of `Δ` at period `N` lie in every subring of `ℂ`. -/
private theorem qExpansion_natCast_discriminant_coeff_mem (i : ℕ) :
    (qExpansion N discriminant).coeff i ∈ R := by
  rw [qExpansion_natCast_discriminant, PowerSeries.coeff_expand]
  split_ifs
  · obtain ⟨m, hm⟩ := exists_discriminant_qExpansion_coeff_eq_intCast (i / N)
    rw [hm]
    exact intCast_mem R m
  · exact R.zero_mem

/-- At every cusp, the expansion of `f Δ` at period `N` is that of `f` times that of `Δ`. -/
private theorem qExpansion_translate_mulDiscriminant
    (hΓN : (Γ(N) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ) (hΓ : Γ ≤ 𝒮ℒ) (f : ModularForm Γ k)
    (γ : SL(2, ℤ)) :
    qExpansion N (translate (mulDiscriminant hΓ f) (mapGL ℝ γ)) =
      qExpansion N (translate f (mapGL ℝ γ)) * qExpansion N discriminant := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hslash : ⇑(translate (mulDiscriminant hΓ f) (mapGL ℝ γ)) =
      ⇑(translate f (mapGL ℝ γ)) * discriminant := by
    have hΔ : discriminant ∣[(12 : ℤ)] γ = discriminant :=
      CuspForm.discriminant.slash_action_eq' _ ⟨γ, rfl⟩
    rw [coe_translate, coe_translate, coe_mulDiscriminant]
    exact (mul_slash_SL2 k 12 γ _ _).trans (by rw [hΔ]; rfl)
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

namespace TauCeti.ModularForm

variable {R : Subring ℂ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] [Γ.IsArithmetic] {k : ℤ}
  {N : ℕ} [NeZero N]

/-- **Multiplication by `Δ` preserves and reflects integrality at every cusp.** For
`Γ(N) ≤ Γ ≤ SL₂(ℤ)`, the form `f Δ` has coefficients in `R` at every cusp exactly when `f` does. -/
theorem mulDiscriminant_mem_integralAtCusps_iff (hΓN : (Γ(N) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ)
    (hΓ : Γ ≤ 𝒮ℒ) {f : ModularForm Γ k} :
    mulDiscriminant hΓ f ∈ integralAtCusps R Γ (k + 12) ↔ f ∈ integralAtCusps R Γ k := by
  rw [mem_integralAtCusps_iff_qExpansion_coeff_mem hΓN,
    mem_integralAtCusps_iff_qExpansion_coeff_mem hΓN]
  simp only [qExpansion_translate_mulDiscriminant hΓN hΓ]
  refine ⟨fun h γ ↦ PowerSeries.coeff_mem_of_coeff_mul_mem
    (fun _ ↦ qExpansion_natCast_discriminant_coeff_of_lt)
    qExpansion_natCast_discriminant_coeff_self qExpansion_natCast_discriminant_coeff_mem (h γ),
    fun h γ n ↦ ?_⟩
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem fun p _ ↦ R.mul_mem (h γ _) (qExpansion_natCast_discriminant_coeff_mem _)

/-- **Spanning by integral forms descends from weight `k + 12` to weight `k`.** For
`Γ(N) ≤ Γ ≤ SL₂(ℤ)`, if the forms of weight `k + 12` whose expansions at every cusp have
coefficients in `R` span `M_{k+12}(Γ)` over `ℂ`, then the forms of weight `k` with this property
span `M_k(Γ)`. -/
theorem span_integralAtCusps_eq_top_of_add_twelve (hΓN : (Γ(N) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ)
    (hΓ : Γ ≤ 𝒮ℒ)
    (h : Submodule.span ℂ (integralAtCusps R Γ (k + 12) : Set (ModularForm Γ (k + 12))) = ⊤) :
    Submodule.span ℂ (integralAtCusps R Γ k : Set (ModularForm Γ k)) = ⊤ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  -- The coefficients below `N` at period `N` after each translate: these cut out the range of
  -- multiplication by `Δ`, and they are `R`-valued on the integral forms.
  let φ : SL(2, ℤ) × Fin N → ModularForm Γ (k + 12) →ₗ[ℂ] ℂ := fun i ↦
    (PowerSeries.coeff (i.2 : ℕ)).comp ((ModularForm.qExpansionLinearMap hN
      (natCast_mem_strictPeriods_conjAct_of_Gamma_le hΓN i.1) (k + 12)).comp
        (translateₗ (mapGL ℝ i.1) (by simp)))
  have hφ (i : SL(2, ℤ) × Fin N) (g : ModularForm Γ (k + 12)) :
      φ i g = (qExpansion N (translate g (mapGL ℝ i.1))).coeff i.2 := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, translateₗ_apply,
      ModularForm.qExpansionLinearMap_apply]
  have hrange : LinearMap.range (mulDiscriminant (k := k) hΓ) = ⨅ i, LinearMap.ker (φ i) := by
    ext g
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, hφ,
      mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero hΓN]
    exact ⟨fun h i ↦ h i.1 i.2 i.2.2, fun h γ n hn ↦ h (γ, ⟨n, hn⟩)⟩
  have hspan := iInf_ker_eq_span_inter (fun _ hr _ hv ↦ smul_mem_integralAtCusps hr hv) h φ
    fun i g hg ↦ hφ i g ▸ (mem_integralAtCusps_iff_qExpansion_coeff_mem hΓN).mp hg i.1 i.2
  rw [← hrange] at hspan
  have hle : LinearMap.range (mulDiscriminant hΓ) ≤
      (Submodule.span ℂ (integralAtCusps R Γ k : Set (ModularForm Γ k))).map
        (mulDiscriminant hΓ) := by
    rw [hspan, Submodule.span_le]
    rintro _ ⟨hgL, f, rfl⟩
    exact ⟨f, Submodule.subset_span ((mulDiscriminant_mem_integralAtCusps_iff hΓN hΓ).mp hgL),
      rfl⟩
  refine eq_top_iff.mpr fun f _ ↦ ?_
  obtain ⟨f', hf', hff'⟩ := hle ⟨f, rfl⟩
  rwa [← mulDiscriminant_injective hΓ hff']

end TauCeti.ModularForm
