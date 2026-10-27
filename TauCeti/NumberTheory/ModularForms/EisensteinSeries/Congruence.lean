/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Primitive
public import TauCeti.NumberTheory.ModularForms.CuspComplementDescent

/-!
# The cusp--Eisenstein decomposition for congruence subgroups

Let `Γ` be a subgroup of `SL(2, ℤ)` containing the principal congruence subgroup `Γ(N)`, such as
`Γ₁(N)` (via `CongruenceSubgroup.Gamma_le_Gamma1`) or `Γ₀(N)`. In weight at least three, the
Eisenstein subspace for `Γ` is the space of forms whose restriction to `Γ(N)` belongs to the span
of the primitive residue-class Eisenstein series. This file proves that it is complementary to
the cusp forms.

The decomposition descends from the corresponding decomposition for `Γ(N)` by
`TauCeti.ModularForm.isCompl_comap_restrictₗ_cuspFormSubmodule`, since the primitive
Eisenstein span is stable under slashing by `SL(2, ℤ)`: the slash transformation formula sends the
series with residue `a` to the series whose residue is the right translate of `a`.

## Main results

* `TauCeti.EisensteinSeries.gammaSlashₗ_eisensteinSeriesMF`: integral slash operators permute
  the primitive residue-class Eisenstein generators.
* `TauCeti.EisensteinSeries.congruenceEisensteinSubspace`: the Eisenstein subspace of `M_k(Γ)`
  detected after restriction to `Γ(N)`.
* `TauCeti.EisensteinSeries.isCompl_congruenceEisensteinSubspace_cuspFormSubmodule`: the
  cusp--Eisenstein decomposition of `M_k(Γ)` in weight at least three.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Section 4.2.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open TauCeti.ModularForm
open UpperHalfPlane
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

/-- Slashing a primitive residue-class Eisenstein series by an integral determinant-one matrix
permutes its residue class, with the matrix viewed in the real general linear group. -/
theorem eisensteinSeries_slash_mapGL {N : ℕ} (a : Fin 2 → ZMod N) (k : ℤ)
    (γ : SL(2, ℤ)) :
    eisensteinSeries a k ∣[k] mapGL ℝ γ =
      eisensteinSeries (a ᵥ* SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) k := by
  exact (ModularForm.SL_slash (eisensteinSeries a k) γ).symm.trans
    (eisensteinSeries_slash_apply a k γ)

variable {N : ℕ} {k : ℤ} [NeZero N] {Γ : Subgroup SL(2, ℤ)}

/-- The principal-level slash operator sends a bundled primitive Eisenstein generator to the
generator with right-translated residue. -/
theorem gammaSlashₗ_eisensteinSeriesMF (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    gammaSlashₗ γ (eisensteinSeriesMF hk a) =
      eisensteinSeriesMF hk (a ᵥ* SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) := by
  apply DFunLike.coe_injective
  rw [coe_gammaSlashₗ, coe_eisensteinSeriesMF, coe_eisensteinSeriesMF,
    eisensteinSeries_slash_mapGL]

/-- The primitive Eisenstein span of `M_k(Γ(N))` is stable under slashing by `SL(2, ℤ)`. -/
theorem gammaSlashₗ_mem_primitiveEisensteinSubspace (hk : 3 ≤ k) (γ : SL(2, ℤ))
    {f : ModularForm ((Gamma N).map (mapGL ℝ)) k} (hf : f ∈ primitiveEisensteinSubspace N hk) :
    gammaSlashₗ γ f ∈ primitiveEisensteinSubspace N hk := by
  have hle : primitiveEisensteinSubspace N hk ≤
      (primitiveEisensteinSubspace N hk).comap (gammaSlashₗ γ) := by
    apply primitiveEisensteinSubspace_le hk
    intro a
    rw [Submodule.mem_comap, gammaSlashₗ_eisensteinSeriesMF]
    exact mem_primitiveEisensteinSubspace hk _
  exact hle hf

/-- The Eisenstein subspace of `M_k(Γ)`, for a subgroup `Γ` of `SL(2, ℤ)` containing `Γ(N)`, in
weight at least three: a form belongs to it exactly when its restriction to `Γ(N)` belongs to the
primitive residue-class Eisenstein span. -/
def congruenceEisensteinSubspace (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    Submodule ℂ (ModularForm (Γ.map (mapGL ℝ)) k) :=
  (primitiveEisensteinSubspace N hk).comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono hΓ))

/-- The defining pullback of the primitive Eisenstein span along restriction to `Γ(N)`. -/
theorem congruenceEisensteinSubspace_def (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k) :
    congruenceEisensteinSubspace hΓ hk =
      (primitiveEisensteinSubspace N hk).comap (ModularForm.restrictₗ _ ℂ (Subgroup.map_mono hΓ)) :=
  (rfl)

/-- Membership in the Eisenstein subspace of `M_k(Γ)` is detected after restriction to the
principal congruence subgroup. -/
theorem mem_congruenceEisensteinSubspace_iff (hΓ : Gamma N ≤ Γ) (hk : 3 ≤ k)
    (f : ModularForm (Γ.map (mapGL ℝ)) k) :
    f ∈ congruenceEisensteinSubspace hΓ hk ↔
      ModularForm.restrict (Subgroup.map_mono hΓ) f ∈ primitiveEisensteinSubspace N hk := by
  rw [congruenceEisensteinSubspace_def, Submodule.mem_comap, ModularForm.restrictₗ_apply]

/-- The cusp--Eisenstein decomposition on a subgroup `Γ` of `SL(2, ℤ)` containing `Γ(N)`, in
weight at least three. For `Γ₁(N)`, take `hΓ := CongruenceSubgroup.Gamma_le_Gamma1 N`. -/
theorem isCompl_congruenceEisensteinSubspace_cuspFormSubmodule (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) :
    IsCompl (congruenceEisensteinSubspace hΓ hk) (cuspFormSubmodule (Γ.map (mapGL ℝ)) k) :=
  isCompl_comap_restrictₗ_cuspFormSubmodule
    (isCompl_primitiveEisensteinSubspace_cuspFormSubmodule hk)
    (fun γ _ _ hf ↦ gammaSlashₗ_mem_primitiveEisensteinSubspace hk γ hf) hΓ

/-- The Eisenstein subspace of `M_k(Γ)` and the cusp-form submodule have zero intersection in
weight at least three. -/
theorem disjoint_congruenceEisensteinSubspace_cuspFormSubmodule (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) :
    Disjoint (congruenceEisensteinSubspace hΓ hk)
      (cuspFormSubmodule (Γ.map (mapGL ℝ)) k) :=
  (isCompl_congruenceEisensteinSubspace_cuspFormSubmodule hΓ hk).disjoint

/-- In weight at least three, the Eisenstein subspace of `M_k(Γ)` and the cusp forms together
span all modular forms on `Γ`. -/
theorem sup_congruenceEisensteinSubspace_cuspFormSubmodule_eq_top (hΓ : Gamma N ≤ Γ)
    (hk : 3 ≤ k) :
    congruenceEisensteinSubspace hΓ hk ⊔ cuspFormSubmodule (Γ.map (mapGL ℝ)) k = ⊤ :=
  codisjoint_iff.mp (isCompl_congruenceEisensteinSubspace_cuspFormSubmodule hΓ hk).codisjoint

end TauCeti.EisensteinSeries
