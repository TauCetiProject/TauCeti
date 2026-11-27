/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.Matrix

/-!
# The model `ℂⁿ` of a unitary representation

For a topological group `G` and a continuous homomorphism `ρ : G →ₜ* U(n)` into the unitary
matrices, `TauCeti.UnitaryModel ρ` is the space `ℂⁿ` on which `G` acts by `g • z = ρ g *ᵥ z`. It is
the model fibre of the complex vector bundles associated to principal `G`-bundles by `ρ`
(`TauCeti.AssociatedBundle`). It is a type synonym carrying the action, so that different
representations on `ℂⁿ` give different associated bundles.

## Main definitions

* `TauCeti.UnitaryModel ρ`: the space `ℂⁿ` on which `G` acts by the unitary matrices `ρ g`.
* `TauCeti.UnitaryModel.coords`: the model as `ℂⁿ`, on which `g` acts by `ρ g`
  (`TauCeti.UnitaryModel.coords_smul`).
-/

public section

noncomputable section

open Module
open scoped Matrix

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- The space `ℂⁿ` of complex coordinates, on which a topological group `G` acts through a
continuous homomorphism `ρ : G →ₜ* U(n)` into the unitary matrices, `g • z = ρ g *ᵥ z`
(`TauCeti.UnitaryModel.coords_smul`). It is the model fibre of the complex vector bundles
associated to principal `G`-bundles by `ρ`. -/
@[expose] def UnitaryModel (_ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ) : Type := Fin n → ℂ

namespace UnitaryModel

variable (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ)

instance instNormedAddCommGroup : NormedAddCommGroup (UnitaryModel ρ) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → ℂ))

instance instNormedSpace : NormedSpace ℂ (UnitaryModel ρ) :=
  inferInstanceAs (NormedSpace ℂ (Fin n → ℂ))

instance instFiniteDimensional : FiniteDimensional ℂ (UnitaryModel ρ) :=
  inferInstanceAs (FiniteDimensional ℂ (Fin n → ℂ))

/-- `G` acts on the model by the unitary matrices `ρ g`. -/
instance instDistribMulAction : DistribMulAction G (UnitaryModel ρ) where
  smul g z := (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ (show Fin n → ℂ from z)
  -- The action `g • z` is `ρ g *ᵥ z` by the `smul` field above; `change` states it in that form so
  -- that the matrix lemmas apply.
  one_smul z := by
    change (ρ 1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ (show Fin n → ℂ from z) = z
    rw [map_one, Matrix.UnitaryGroup.one_val, Matrix.one_mulVec]
  mul_smul g h z := by
    change (ρ (g * h) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (show Fin n → ℂ from z) =
      (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ ((ρ h : Matrix (Fin n) (Fin n) ℂ) *ᵥ
        (show Fin n → ℂ from z))
    rw [map_mul, Matrix.UnitaryGroup.mul_val, Matrix.mulVec_mulVec]
  smul_zero g := Matrix.mulVec_zero _
  smul_add g z w := Matrix.mulVec_add _ (show Fin n → ℂ from z) (show Fin n → ℂ from w)

variable {ρ} in
/-- The model as `ℂⁿ`. -/
def coords : UnitaryModel ρ ≃L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearEquiv.refl ℂ (Fin n → ℂ)

/-- `g` acts on the coordinates by the unitary matrix `ρ g`. -/
@[simp]
theorem coords_smul (g : G) (z : UnitaryModel ρ) :
    coords (g • z) = (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ coords z :=
  (rfl)

instance instSMulCommClass : SMulCommClass G ℂ (UnitaryModel ρ) where
  smul_comm g c z := coords.injective <| by
    rw [coords_smul, map_smul, map_smul, coords_smul, Matrix.mulVec_smul]

instance instContinuousSMul : ContinuousSMul G (UnitaryModel ρ) where
  continuous_smul :=
    (((continuous_subtypeVal.comp ρ.continuous).comp continuous_fst).matrix_mulVec
      continuous_snd).congr fun _ ↦ (rfl)

/-- The model has complex dimension `n`. -/
theorem finrank_eq : finrank ℂ (UnitaryModel ρ) = n :=
  coords.toLinearEquiv.finrank_eq.trans (finrank_fin_fun ℂ)

/-- A real vector space of dimension four has twice the complex dimension of the model `ℂ²`, the
dimension condition under which a continuous complex structure on a real bundle with that model
fibre is a complex vector bundle with model `ℂ²`. -/
instance instFactFinrank {ρ : G →ₜ* Matrix.unitaryGroup (Fin 2) ℂ} {F : Type*} [AddCommGroup F]
    [Module ℝ F] [Fact (finrank ℝ F = 4)] : Fact (finrank ℝ F = 2 * finrank ℂ (UnitaryModel ρ)) :=
  ⟨by rw [finrank_eq ρ, (Fact.out : finrank ℝ F = 4)]⟩

end UnitaryModel

end TauCeti
