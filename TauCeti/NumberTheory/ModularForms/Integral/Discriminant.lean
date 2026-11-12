/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Integral.Basic
public import TauCeti.NumberTheory.ModularForms.MulDiscriminant

import TauCeti.LinearAlgebra.Span.CommonKernel
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.MulDiscriminant
import TauCeti.RingTheory.PowerSeries.SubringCoeff

/-!
# Integral forms and division by the discriminant

Let `Γ(N) ≤ Γ ≤ SL₂(ℤ)` and let `R ⊆ ℂ` be a subring. The discriminant `Δ` has integer
`q`-expansion `q + ⋯` and is invariant under `SL₂(ℤ)`, so at every cusp, read at the common
period `N`, its expansion is `qᴺ` times a unit power series over `ℤ`. Multiplying by `Δ` therefore
neither creates nor destroys integrality: `f Δ` is integral at every cusp exactly when `f` is
(`TauCeti.ModularForm.mulDiscriminant_mem_integralAtCusps_iff`). Its image is cut out by the
vanishing of the first `N` coefficients at every cusp
(`ModularForm.mem_range_mulDiscriminant_iff_qExpansion_coeff_eq_zero`, in
`TauCeti.NumberTheory.ModularForms.QExpansion.MulDiscriminant`), linear conditions with integer
coefficients.

Together these show that if the forms of weight `k + 12` integral at every cusp span
`M_{k+12}(Γ)` over `ℂ`, then the forms of weight `k` integral at every cusp span `M_k(Γ)`
(`TauCeti.ModularForm.span_integralAtCusps_eq_top_of_add_twelve`). Deligne–Serre's lattice of
forms integral at every cusp needs this spanning statement to carry the Hecke eigenvalues; the
descent reduces it in weight one to the same statement in weight `13`.

## Main results

* `TauCeti.ModularForm.mulDiscriminant_mem_integralAtCusps_iff`: `f Δ` is integral at every cusp
  if and only if `f` is.
* `TauCeti.ModularForm.span_integralAtCusps_eq_top_of_add_twelve`: spanning by integral forms
  descends from weight `k + 12` to weight `k`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, §2.7.
-/

public section

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

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
