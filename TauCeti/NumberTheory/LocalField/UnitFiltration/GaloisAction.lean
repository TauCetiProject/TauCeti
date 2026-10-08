/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.Logarithm
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# The Galois action on the unit filtration

Every automorphism of a finite extension of a nonarchimedean local field preserves its valuation.
It therefore preserves every step of the unit filtration. This gives an action on each filtered
unit group, compatible with its inclusion in the units of the field.

The stability is stated both elementwise and as equality of the image subgroup. The elementwise
form installs the restricted action on `unitFiltration L i`; the image form is convenient when
passing to successive quotients in ramification theory.

## Main results

* `AlgEquiv.unitsMap_mem_unitFiltration_iff`: membership in `U(L,i)` is invariant under an
  extension automorphism.
* `AlgEquiv.smul_unitFiltration`: an extension automorphism maps `U(L,i)` onto itself.
* `AlgEquiv.coe_smul_unitFiltration`: the restricted action agrees with the action on `Lˣ`.
* `AlgEquiv.val_coe_smul_unitFiltration`: the restricted action agrees with applying the
  automorphism on `L`.
* `AlgEquiv.map_log_of_mem_unitFiltration_one`: on a finite extension of `ℚ_[p]`, the logarithm of
  principal units commutes with every extension automorphism.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
-/

public section
noncomputable section

open ValuativeRel
open scoped Pointwise

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- Membership in the unit filtration is invariant under every automorphism of a finite extension
of a nonarchimedean local field. The action of `σ` on `Lˣ` is `Units.map σ`, so this is also the
statement that `σ • x ∈ unitFiltration L i ↔ x ∈ unitFiltration L i`. -/
@[simp]
theorem unitsMap_mem_unitFiltration_iff (σ : L ≃ₐ[K] L) {i : ℕ} {x : Lˣ} :
    Units.map (σ : L →* L) x ∈ unitFiltration L i ↔ x ∈ unitFiltration L i := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  have hsub : valuation L (σ (x : L) - 1) = valuation L ((x : L) - 1) := by
    simpa only [map_sub, map_one] using σ.valuation_eq ((x : L) - 1)
  rw [mem_unitFiltration_iff_valuation_le hπ, mem_unitFiltration_iff_valuation_le hπ]
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  rw [σ.valuation_eq, hsub]

/-- Every automorphism of a finite extension of a nonarchimedean local field maps each step of
the unit filtration onto itself. -/
@[simp]
theorem smul_unitFiltration (σ : L ≃ₐ[K] L) (i : ℕ) :
    σ • unitFiltration L i = unitFiltration L i := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_units_def,
    unitsMap_mem_unitFiltration_iff]

end AlgEquiv

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- The action of extension automorphisms on `Lˣ` restricts to every step `U(L,i)` of the unit
filtration. -/
noncomputable instance unitFiltrationMulDistribMulAction (i : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L i) := by
  letI : SMul (L ≃ₐ[K] L) (unitFiltration L i) :=
    ⟨fun σ x ↦ ⟨σ • (x : Lˣ), by
      simpa only [AlgEquiv.smul_units_def] using
        (AlgEquiv.unitsMap_mem_unitFiltration_iff σ).2 x.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction (unitFiltration L i).subtype fun _ _ ↦ rfl

end TauCeti

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

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

/-- **The logarithm is Galois-equivariant.** On a finite extension `L` of `ℚ_[p]`, every
automorphism of `L/K` commutes with the logarithm of a principal unit: `σ (log u) = log (σ u)`.
The logarithm series of `u` converges on `U(L,1)`, and `σ` is continuous and maps it termwise to
the logarithm series of `σ u`. -/
theorem map_log_of_mem_unitFiltration_one (σ : L ≃ₐ[K] L) (p : ℕ) [Fact p.Prime]
    [FinitePadicExtension L p] {u : Lˣ} (hu : u ∈ unitFiltration L 1) :
    σ (NormedSpace.log (u : L)) = NormedSpace.log (σ (u : L)) := by
  have h := (hasSum_log_of_mem_unitFiltration_one p hu).map σ.toAddMonoidHom
    σ.continuous_of_valuativeExtension
  have h' := hasSum_log_of_mem_unitFiltration_one p (σ.unitsMap_mem_unitFiltration_iff.mpr hu)
  rw [Units.coe_map, MonoidHom.coe_ofClass] at h'
  refine h.unique (h'.congr_fun fun n ↦ ?_)
  simp

end AlgEquiv

namespace TauCeti

open CategoryTheory

universe u

variable (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- Inclusion of the valuation-zero units in the multiplicative group, as a morphism of
integral Galois representations. -/
def unitFiltrationZeroIncl :
    Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (unitFiltration L 0) ⟶
      Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (unitFiltration L 0).subtype.toAdditive.toIntLinearMap fun σ x ↦
      congrArg Additive.ofMul (AlgEquiv.coe_smul_unitFiltration σ x.toMul)

/-- The inclusion is the subgroup inclusion, written additively. -/
@[simp]
theorem unitFiltrationZeroIncl_apply (x : Additive (unitFiltration L 0)) :
    (unitFiltrationZeroIncl K L).hom x = Additive.ofMul (x.toMul : Lˣ) := (rfl)

/-- The inclusion of the valuation-zero units in the multiplicative group is injective. -/
theorem unitFiltrationZeroIncl_injective : Function.Injective (unitFiltrationZeroIncl K L).hom :=
  fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul h))

end TauCeti
