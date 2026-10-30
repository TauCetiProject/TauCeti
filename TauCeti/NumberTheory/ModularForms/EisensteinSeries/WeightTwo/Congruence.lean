/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Primitive
public import TauCeti.NumberTheory.ModularForms.CuspComplementDescent

/-!
# The weight-two cusp–Eisenstein decomposition for congruence subgroups

At level `Γ(N)` the weight-two series `G₂^W` (`TauCeti.EisensteinSeries.weightedG2MF`) with weights
`W ∈ TauCeti.EisensteinSeries.primitiveG2Weights N`, supported on the residues of coprime pairs
and of total mass zero, span a complement of the cusp forms in `M₂(Γ(N))`
(`TauCeti.EisensteinSeries.isCompl_primitiveG2Subspace_cuspFormSubmodule`). This file descends
that decomposition to every subgroup `Γ` of `SL(2, ℤ)` containing `Γ(N)`, such as `Γ₁(N)` and
`Γ₀(N)`, and to each nebentypus space `M₂(N, χ)`.

Slashing by `γ ∈ SL(2, ℤ)` replaces the weight `W` of `G₂^W` by `a ↦ W(a γ⁻¹)`
(`TauCeti.EisensteinSeries.weightedG2_slash_apply`). Right multiplication by `SL(2, ℤ)` permutes
the residues of coprime pairs, so it preserves both conditions on `W`, and the subspace of
`M₂(Γ(N))` is stable under slashing. The descent is then
`ModularForm.isCompl_comap_restrictₗ_cuspFormSubmodule` and its nebentypus form.

## Main definitions

* `TauCeti.EisensteinSeries.congruenceG2Subspace`: the weight-two Eisenstein subspace of
  `M₂(Γ)`, the forms whose restriction to `Γ(N)` lies in the primitive weight-two Eisenstein
  subspace.

## Main results

* `TauCeti.EisensteinSeries.gammaSlashₗ_weightedG2MF`: slashing `G₂^W` by `γ ∈ SL(2, ℤ)`.
* `TauCeti.EisensteinSeries.gammaSlashₗ_mem_primitiveG2Subspace`: the primitive weight-two
  Eisenstein subspace of `M₂(Γ(N))` is stable under slashing by `SL(2, ℤ)`.
* `TauCeti.EisensteinSeries.isCompl_congruenceG2Subspace_cuspFormSubmodule`: the weight-two
  cusp–Eisenstein decomposition of `M₂(Γ)` for `Γ ⊇ Γ(N)`.
* `TauCeti.EisensteinSeries.isCompl_congruenceG2Subspace_charSpace_range_cuspToModFormCharSpace`:
  the weight-two cusp–Eisenstein decomposition of `M₂(N, χ)`, with Eisenstein part the forms of
  nebentypus `χ` in the weight-two Eisenstein subspace of `M₂(Γ₁(N))`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.2 and
  §4.6.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}

/-- Slashing the weight-two series `G₂^W` of level `Γ(N)` by `γ ∈ SL(2, ℤ)` replaces the weight
`W` by `a ↦ W(a γ⁻¹)`. -/
theorem gammaSlashₗ_weightedG2MF (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    gammaSlashₗ γ (weightedG2MF W) = weightedG2MF (fun a ↦
      W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) := by
  apply DFunLike.coe_injective
  rw [coe_gammaSlashₗ, coe_weightedG2MF, coe_weightedG2MF]
  exact (ModularForm.SL_slash _ γ).symm.trans (weightedG2_slash_apply W γ)

/-- The primitive weight-two Eisenstein subspace of `M₂(Γ(N))` is stable under slashing by
`SL(2, ℤ)`. -/
theorem gammaSlashₗ_mem_primitiveG2Subspace (γ : SL(2, ℤ))
    {f : ModularForm ((Gamma N).map (mapGL ℝ)) 2} (hf : f ∈ primitiveG2Subspace N) :
    gammaSlashₗ γ f ∈ primitiveG2Subspace N := by
  obtain ⟨W, hW, rfl⟩ := mem_primitiveG2Subspace_iff.mp hf
  rw [gammaSlashₗ_weightedG2MF]
  exact mem_primitiveG2Subspace_iff.mpr ⟨_, comp_vecMul_mem_primitiveG2Weights hW γ⁻¹, rfl⟩

/-- The weight-two Eisenstein subspace of `M₂(Γ)`, for a subgroup `Γ` of `SL(2, ℤ)` containing
`Γ(N)`: a form belongs to it exactly when its restriction to `Γ(N)` lies in the primitive
weight-two Eisenstein subspace. -/
def congruenceG2Subspace (hΓ : Gamma N ≤ Γ) : Submodule ℂ (ModularForm (Γ.map (mapGL ℝ)) 2) :=
  (primitiveG2Subspace N).comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono hΓ))

/-- The defining pullback of the primitive weight-two Eisenstein subspace along restriction to
`Γ(N)`. -/
theorem congruenceG2Subspace_def (hΓ : Gamma N ≤ Γ) :
    congruenceG2Subspace hΓ =
      (primitiveG2Subspace N).comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono hΓ)) :=
  (rfl)

/-- Membership in the weight-two Eisenstein subspace of `M₂(Γ)` is detected after restriction to
`Γ(N)`. -/
theorem mem_congruenceG2Subspace_iff (hΓ : Gamma N ≤ Γ) (f : ModularForm (Γ.map (mapGL ℝ)) 2) :
    f ∈ congruenceG2Subspace hΓ ↔
      ModularForm.restrict (Subgroup.map_mono hΓ) f ∈ primitiveG2Subspace N := by
  rw [congruenceG2Subspace_def, Submodule.mem_comap, ModularForm.restrictₗ_apply]

/-- **The weight-two cusp–Eisenstein decomposition on a congruence subgroup**: for a subgroup
`Γ` of `SL(2, ℤ)` containing `Γ(N)`, the weight-two Eisenstein subspace is a complement of the
cusp forms in `M₂(Γ)`. For `Γ₁(N)`, take `hΓ := CongruenceSubgroup.Gamma_le_Gamma1 N`. -/
theorem isCompl_congruenceG2Subspace_cuspFormSubmodule (hΓ : Gamma N ≤ Γ) :
    IsCompl (congruenceG2Subspace hΓ) (cuspFormSubmodule (Γ.map (mapGL ℝ)) 2) :=
  isCompl_comap_restrictₗ_cuspFormSubmodule isCompl_primitiveG2Subspace_cuspFormSubmodule
    (fun γ _ _ hf ↦ gammaSlashₗ_mem_primitiveG2Subspace γ hf) hΓ

/-- **The weight-two cusp–Eisenstein decomposition with nebentypus**: the forms of nebentypus `χ`
in the weight-two Eisenstein subspace of `M₂(Γ₁(N))` form a complement of the image of
`S₂(N, χ)` in `M₂(N, χ)`. -/
theorem isCompl_congruenceG2Subspace_charSpace_range_cuspToModFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) :
    IsCompl ((congruenceG2Subspace (Gamma_le_Gamma1 N)).comap (modFormCharSpace 2 χ).subtype)
      (LinearMap.range (cuspToModFormCharSpace 2 χ)) :=
  isCompl_comap_restrictₗ_charSpace_range_cuspToModFormCharSpace
    isCompl_primitiveG2Subspace_cuspFormSubmodule
    (fun γ _ _ hf ↦ gammaSlashₗ_mem_primitiveG2Subspace γ hf) χ

end TauCeti.EisensteinSeries
