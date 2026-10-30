/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Multiplication by the discriminant at general level

For a subgroup `Γ ≤ SL₂(ℤ)` (inside `GL₂(ℝ)`), multiplication by the discriminant `Δ` is an
injective linear map `M_k(Γ) → M_{k+12}(Γ)` (`ModularForm.mulDiscriminant`). Since `Δ`
vanishes nowhere on `ℍ` and is invariant under `SL₂(ℤ)`, its image consists exactly of the forms
that are `O(Δ)` at every cusp, that is, `O(q)` after every translate by `SL₂(ℤ)`
(`ModularForm.mem_range_mulDiscriminant_iff`).

This generalises Mathlib's level-one isomorphism `CuspForm.discriminantEquiv` (Chris Birkbeck)
to arbitrary level, and the construction of the quotient `g / Δ` follows it. Dividing by `Δ`
lowers the weight by `12` while keeping a modular form, which is how statements about forms of
low weight, such as weight one, are reduced to higher weight.

## Main declarations

* `ModularForm.mulDiscriminant`: multiplication by `Δ`, from weight `k` to `k + 12`.
* `ModularForm.mulDiscriminant_injective`: it is injective.
* `ModularForm.discriminant_slash`: `Δ` is invariant under slashing by `SL₂(ℤ)` in weight `12`.
* `ModularForm.div_discriminant_slash`: slashing `g / Δ` in weight `k` slashes `g` in weight
  `k + 12`.
* `ModularForm.mem_range_mulDiscriminant_iff`: its range consists of the forms that are
  `O(Δ)` at every cusp.
-/

public section

open UpperHalfPlane ModularForm SlashInvariantFormClass Filter Asymptotics
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ}

/-- Multiplication by the discriminant `Δ`, as a linear map from forms of weight `k` on
`Γ ≤ SL₂(ℤ)` to forms of weight `k + 12`. -/
noncomputable def mulDiscriminant (hΓ : Γ ≤ 𝒮ℒ) :
    ModularForm Γ k →ₗ[ℂ] ModularForm Γ (k + 12) where
  toFun f := f.mul (ModularForm.restrict hΓ (CuspForm.toModularFormₗ CuspForm.discriminant))
  map_add' f g := by
    ext τ
    simp [add_mul]
  map_smul' c f := by
    ext τ
    simp [mul_assoc]

/-- The product of `f` with the discriminant, as a function. -/
@[simp]
theorem coe_mulDiscriminant (hΓ : Γ ≤ 𝒮ℒ) (f : ModularForm Γ k) :
    ⇑(mulDiscriminant hΓ f) = ⇑f * discriminant :=
  (rfl)

/-- Multiplication by the discriminant is injective, since `Δ` vanishes nowhere on `ℍ`. -/
theorem mulDiscriminant_injective (hΓ : Γ ≤ 𝒮ℒ) :
    Function.Injective (mulDiscriminant (k := k) hΓ) := fun f g h ↦ by
  ext τ
  simpa [discriminant_ne_zero τ] using congr($h τ)

/-- The discriminant is invariant under slashing by `SL₂(ℤ)` in weight `12`. -/
theorem discriminant_slash (γ : SL(2, ℤ)) : discriminant ∣[(12 : ℤ)] γ = discriminant :=
  CuspForm.discriminant.slash_action_eq' _ ⟨γ, rfl⟩

/-- Slashing `g / Δ` in weight `k` by `γ ∈ SL₂(ℤ)` slashes `g` in weight `k + 12`. -/
theorem div_discriminant_slash (g : ℍ → ℂ) (γ : SL(2, ℤ)) :
    (g / discriminant) ∣[k] γ = (g ∣[k + 12] γ) / discriminant := by
  simpa [discriminant_slash] using div_slash_SL2 (k + 12) 12 γ g discriminant

variable [Γ.IsArithmetic]

/-- **The range of multiplication by the discriminant.** A form of weight `k + 12` on
`Γ ≤ SL₂(ℤ)` is `Δ` times a form of weight `k` exactly when it is `O(Δ)` at every cusp, that is,
when each of its translates by `SL₂(ℤ)` is `O(Δ)` at `i∞`. -/
theorem mem_range_mulDiscriminant_iff (hΓ : Γ ≤ 𝒮ℒ) {g : ModularForm Γ (k + 12)} :
    g ∈ LinearMap.range (mulDiscriminant hΓ) ↔
      ∀ γ : SL(2, ℤ), (⇑g ∣[k + 12] γ) =O[atImInfty] discriminant := by
  constructor
  · rintro ⟨f, rfl⟩ γ
    rw [coe_mulDiscriminant, mul_slash_SL2, discriminant_slash]
    have hc : IsCusp (mapGL ℝ γ • OnePoint.infty) 𝒮ℒ := isCusp_SL2Z_iff'.mpr ⟨γ, rfl⟩
    have hf : IsBoundedAtImInfty (⇑f ∣[k] γ) :=
      (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mp (ModularFormClass.bdd_at_cusps f
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mpr hc)) γ rfl
    have hf' : (⇑f ∣[k] γ) =O[atImInfty] fun _ ↦ (1 : ℂ) :=
      hf.trans (isBigO_of_le _ fun _ ↦ by simp)
    exact (hf'.mul (isBigO_refl discriminant atImInfty)).congr (fun _ ↦ rfl) fun _ ↦ one_mul _
  · intro hg
    let f : ModularForm Γ k :=
      { toFun := ⇑g / discriminant
        slash_action_eq' γ hγ := by
          obtain ⟨γ, rfl⟩ := hΓ hγ
          have hg : ⇑g ∣[k + 12] γ = ⇑g := SlashInvariantFormClass.slash_action_eq g _ hγ
          exact (div_discriminant_slash _ γ).trans (by rw [hg])
        holo' := g.holo'.div CuspForm.discriminant.holo' discriminant_ne_zero
        bdd_at_cusps' {c} hc := by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [div_discriminant_slash, IsBoundedAtImInfty, BoundedAtFilter]
          exact (div_isBoundedUnder_of_isBigO (hg γ)).isBigO_one ℝ }
    refine ⟨f, ?_⟩
    ext τ
    exact div_mul_cancel₀ (g τ) (discriminant_ne_zero τ)

end ModularForm
