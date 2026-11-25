/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Determinant.Projective.Basic
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep

/-!
# The determinant character of a continuous representation

Let `ρ` be a continuous representation of a group `Γ` on a finite projective module `M` over a
commutative topological ring `A`, of possibly varying rank. Its **determinant character**
`ContinuousRep.det ρ : Γ →* Aˣ` sends `g` to the determinant `LinearMap.projectiveDet (ρ g)` of the
operator `ρ g`, a unit because `ρ g` is invertible. When `M` carries its module topology and
inversion on `Γ` is continuous, the determinant character is continuous
(`ContinuousRep.continuous_det`). Through a splitting `π ∘ σ = id` of `M` off a free module
`Aⁿ`, `det ρ(g)` is the determinant of the matrix of `σ ∘ ρ(g) ∘ π + (1 − σ ∘ π)`, whose entries
are continuous in `g`.

On a free carrier the determinant character is the usual determinant `LinearMap.det (ρ g)`
(`ContinuousRep.coe_det_apply_eq_linearMap_det`). It is an isomorphism invariant
(`ContinuousRep.Iso.det_eq`), it is trivial on the zero module and on trivial representations, it
recovers a character from its rank-one representation (`ContinuousRep.det_ofCharacter`), and it
commutes with extension of scalars (`ContinuousRep.coe_det_baseChange_apply`).

## Main definitions

* `TauCeti.ContinuousRep.det`: the determinant character `g ↦ det ρ(g)`.
* `TauCeti.ContinuousRep.continuousDet`: the determinant character as a continuous homomorphism.

## Main results

* `TauCeti.ContinuousRep.continuous_det`: the determinant character is continuous.
* `TauCeti.ContinuousRep.coe_det_apply_eq_linearMap_det`: on a free carrier it is
  `LinearMap.det (ρ g)`.
* `TauCeti.ContinuousRep.Iso.det_eq`: isomorphic representations have the same determinant
  character.
* `TauCeti.ContinuousRep.det_of_subsingleton`: on the zero module it is trivial.
* `TauCeti.ContinuousRep.det_trivial`: the trivial representation has trivial determinant
  character.
* `TauCeti.ContinuousRep.det_ofCharacter`: the determinant of a character line is the character.
* `TauCeti.ContinuousRep.coe_det_baseChange_apply`: it commutes with extension of scalars.
-/

public section

open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [CommRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [Module.Finite A M] [Module.Projective A M]

/-- The **determinant character** of a continuous representation on a finite projective module:
`g ↦ det ρ(g)`, the determinant `LinearMap.projectiveDet` of the operator `ρ g`. It is a unit
because `ρ g` is invertible. -/
noncomputable def det (ρ : ContinuousRep Γ A M) : Γ →* Aˣ :=
  (LinearMap.projectiveDet.comp ρ.toRepresentation).toHomUnits

/-- The determinant character at `g` is the determinant of `ρ g`. -/
@[simp]
theorem coe_det_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.det g : A) = LinearMap.projectiveDet (ρ g) :=
  (rfl)

/-- On a free carrier the determinant character is the determinant of `ρ g`. -/
theorem coe_det_apply_eq_linearMap_det [Module.Free A M] (ρ : ContinuousRep Γ A M) (g : Γ) :
    (ρ.det g : A) = LinearMap.det (ρ g) := by
  rw [coe_det_apply, LinearMap.projectiveDet_eq_det]

/-- On the zero module the determinant character is trivial. -/
theorem det_of_subsingleton [Subsingleton M] (ρ : ContinuousRep Γ A M) : ρ.det = 1 := by
  ext g
  rw [coe_det_apply_eq_linearMap_det, MonoidHom.one_apply, Units.val_one,
    Subsingleton.elim (ρ g) LinearMap.id, LinearMap.det_id]

/-- The determinant character of the trivial representation is trivial. -/
@[simp]
theorem det_trivial : (trivial Γ A M).det = 1 := by
  ext g
  rw [coe_det_apply, trivial_apply_eq_id, LinearMap.projectiveDet_id, MonoidHom.one_apply,
    Units.val_one]

/-- **Isomorphic continuous representations have the same determinant character.** -/
theorem Iso.det_eq {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [Module.Finite A N] [Module.Projective A N] {ρ : ContinuousRep Γ A M}
    {σ : ContinuousRep Γ A N} (e : Iso ρ σ) : ρ.det = σ.det := by
  ext g
  rw [coe_det_apply, coe_det_apply, ← coe_toRepresentation σ,
    ← e.toRepresentationEquiv.conj_apply_self g, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.projectiveDet_conj, coe_toRepresentation]

section Continuity

variable [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology A M]

/-- For the module topology on `M`, the determinant of `ρ g` is continuous in `g`. -/
theorem continuous_projectiveDet_apply (ρ : ContinuousRep Γ A M) :
    Continuous fun g => LinearMap.projectiveDet (ρ g) := by
  classical
  -- Through a splitting `π ∘ σ = id` of `M` off `Aⁿ`, `projectiveDet (ρ g)` is the determinant
  -- of a matrix whose entries are continuous in `g`.
  obtain ⟨n, π, σ, -, -, h⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  simp_rw [LinearMap.projectiveDet_eq_det_of_comp_eq_id π σ h, ← LinearMap.det_toMatrix']
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp only [LinearMap.toMatrix'_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, Pi.add_apply]
  have hσ : Continuous σ := IsModuleTopology.continuous_of_linearMap σ
  exact ((_root_.continuous_apply i).comp (hσ.comp (ρ.continuous_orbit (π (Pi.single j 1))))).add
    continuous_const

/-- **The determinant character is continuous**, for the module topology on `M` and a group `Γ`
with continuous inversion. -/
theorem continuous_det [ContinuousInv Γ] (ρ : ContinuousRep Γ A M) : Continuous ρ.det :=
  Units.continuous_iff.2 ⟨ρ.continuous_projectiveDet_apply,
    (ρ.continuous_projectiveDet_apply.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, ← coe_det_apply, map_inv]⟩

/-- The determinant character as a continuous homomorphism `Γ →ₜ* Aˣ`. -/
noncomputable def continuousDet [ContinuousInv Γ] (ρ : ContinuousRep Γ A M) : Γ →ₜ* Aˣ :=
  ⟨ρ.det, ρ.continuous_det⟩

@[simp]
theorem coe_continuousDet [ContinuousInv Γ] (ρ : ContinuousRep Γ A M) :
    ⇑ρ.continuousDet = ρ.det :=
  (rfl)

end Continuity

/-- **The determinant of a character line is the character.** -/
@[simp]
theorem det_ofCharacter [TopologicalSpace A] [ContinuousMul A] (χ : Γ →ₜ* Aˣ) :
    (ofCharacter χ).det = χ := by
  ext g
  rw [coe_det_apply_eq_linearMap_det, LinearMap.det_ring, ofCharacter_apply, mul_one,
    MonoidHom.coe_ofClass]

/-- **The determinant character commutes with extension of scalars**: the determinant of the
base-changed operator is the image of the determinant under `A → B`. -/
theorem coe_det_baseChange_apply [TopologicalSpace A] [IsModuleTopology A M] (B : Type*)
    [CommRing B] [TopologicalSpace B]
    [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)]
    [IsModuleTopology B (B ⊗[A] M)] (ρ : ContinuousRep Γ A M) (g : Γ) :
    ((ρ.baseChange B).det g : B) = algebraMap A B (ρ.det g) := by
  rw [coe_det_apply, baseChange_apply, LinearMap.projectiveDet_baseChange, coe_det_apply]

end TauCeti.ContinuousRep
