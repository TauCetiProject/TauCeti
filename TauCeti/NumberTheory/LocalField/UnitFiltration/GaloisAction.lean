/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# The Galois action on the unit filtration

Every automorphism of a finite extension of a nonarchimedean local field preserves its valuation.
It therefore preserves every step of the unit filtration. This gives an action on each filtered
unit group, compatible with its inclusion in the units of the field.

The stability is stated both elementwise and as equality of the image subgroup. The elementwise
form installs the restricted action on `unitFiltration L i`; the image form is convenient when
passing to successive quotients in ramification theory.

## Main results

* `TauCeti.unitsMap_algEquiv_mem_unitFiltration_iff`: membership in `U(L,i)` is invariant under an
  extension automorphism.
* `TauCeti.smul_unitFiltration`: an extension automorphism maps `U(L,i)` onto itself.
* `TauCeti.coe_smul_unitFiltration`: the restricted action agrees with the action on `Lˣ`.
* `TauCeti.val_coe_smul_unitFiltration`: the restricted action agrees with applying the
  automorphism on `L`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
-/

public section
noncomputable section

open ValuativeRel
open scoped Pointwise

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- Membership in the unit filtration is invariant under every automorphism of a finite extension
of a nonarchimedean local field. The action of `σ` on `Lˣ` is `Units.map σ`, so this is also the
statement that `σ • x ∈ unitFiltration L i ↔ x ∈ unitFiltration L i`. -/
@[simp]
theorem unitsMap_algEquiv_mem_unitFiltration_iff (σ : L ≃ₐ[K] L) {i : ℕ} {x : Lˣ} :
    Units.map (σ : L →* L) x ∈ unitFiltration L i ↔ x ∈ unitFiltration L i := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  have hsub : valuation L (σ (x : L) - 1) = valuation L ((x : L) - 1) := by
    simpa only [map_sub, map_one] using σ.valuation_eq ((x : L) - 1)
  rw [mem_unitFiltration_iff_valuation_le hπ, mem_unitFiltration_iff_valuation_le hπ]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [σ.valuation_eq, hsub]

/-- Every automorphism of a finite extension of a nonarchimedean local field maps each step of
the unit filtration onto itself. -/
@[simp]
theorem smul_unitFiltration (σ : L ≃ₐ[K] L) (i : ℕ) :
    σ • unitFiltration L i = unitFiltration L i := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_units_def,
    unitsMap_algEquiv_mem_unitFiltration_iff]

/-- The action of extension automorphisms on `Lˣ` restricts to every step `U(L,i)` of the unit
filtration. -/
noncomputable instance unitFiltrationMulDistribMulAction (i : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L i) := by
  letI : SMul (L ≃ₐ[K] L) (unitFiltration L i) :=
    ⟨fun σ x ↦ ⟨σ • (x : Lˣ), by
      simpa only [AlgEquiv.smul_units_def] using
        (unitsMap_algEquiv_mem_unitFiltration_iff σ).2 x.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction (unitFiltration L i).subtype fun _ _ ↦ rfl

/-- The action on a step of the unit filtration agrees with the ambient action on `Lˣ`. -/
@[simp]
theorem coe_smul_unitFiltration (σ : L ≃ₐ[K] L) {i : ℕ} (x : unitFiltration L i) :
    ((σ • x : unitFiltration L i) : Lˣ) = σ • (x : Lˣ) :=
  (rfl)

/-- The value in `L` of the action on a step of the unit filtration is obtained by applying the
automorphism. -/
theorem val_coe_smul_unitFiltration (σ : L ≃ₐ[K] L) {i : ℕ} (x : unitFiltration L i) :
    (((σ • x : unitFiltration L i) : Lˣ) : L) = σ ((x : Lˣ) : L) :=
  (rfl)

end TauCeti
