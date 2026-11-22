/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Lattice
public import TauCeti.RepresentationTheory.Continuous.IntegralModel.Basic

/-!
# Dual integral models

Let `O` be a principal ideal domain with fraction field `E`, such as a discrete valuation ring,
and let `Λ` be an integral model over `O` of a continuous representation `ρ` of a group `Γ` on a
finite-dimensional `E`-vector space `V`. The *dual lattice*
`Λ^∨ = {λ ∈ V^∨ : λ(Λ) ⊆ O}` (`Submodule.dualLattice`) is an integral model of the contragredient
representation `TauCeti.ContinuousRep.dual` on `V^∨ = Module.Dual E V`. Duality reverses
inclusion, sends the homothetic model `c • Λ` to `c⁻¹ • Λ^∨` for `c ∈ Eˣ`, and is an involution
up to the biduality isomorphism: evaluation `V → V^∨∨` carries `Λ` onto `Λ^∨∨`.

## Main definitions

* `TauCeti.GaloisLattice.IntegralModel.dual`: the dual integral model of the contragredient
  representation.

## Main results

* `TauCeti.GaloisLattice.IntegralModel.lattice_dual_dual`: evaluation carries `Λ` onto `Λ^∨∨`.
* `TauCeti.GaloisLattice.IntegralModel.dual_le_dual_iff`: duality reverses inclusion.
* `TauCeti.GaloisLattice.IntegralModel.dual_smul`: the dual of `c • Λ` is `c⁻¹ • Λ^∨`.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open scoped Pointwise

namespace TauCeti.GaloisLattice.IntegralModel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {E : Type*} [Field E] [Algebra O E] [IsFractionRing O E] [TopologicalSpace E]
  [IsTopologicalRing E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]
  [TopologicalSpace (Module.Dual E V)] [IsModuleTopology E (Module.Dual E V)]
  {ρ : ContinuousRep Γ E V}

/-- **The dual integral model** `Λ^∨ = {λ ∈ V^∨ : λ(Λ) ⊆ O}` of the contragredient
representation. -/
def dual (Λ : IntegralModel O ρ) : IntegralModel O ρ.dual where
  lattice := Λ.lattice.dualLattice E
  isFullLattice := by
    have := Submodule.IsLattice.free E Λ.lattice
    infer_instance
  stable g φ hφ := (Submodule.mem_dualLattice _ _).mpr fun x hx ↦ by
    simpa using (Submodule.mem_dualLattice _ φ).mp hφ _ (Λ.stable g⁻¹ x hx)

@[simp]
theorem lattice_dual (Λ : IntegralModel O ρ) : Λ.dual.lattice = Λ.lattice.dualLattice E :=
  (rfl)

/-- Duality reverses inclusion of integral models. -/
theorem dual_antitone : Antitone (dual : IntegralModel O ρ → IntegralModel O ρ.dual) :=
  fun _ _ h ↦ Submodule.dualLattice_antitone E h

/-- The dual of a homothetic model `c • Λ` is `c⁻¹ • Λ^∨`. -/
@[simp]
theorem dual_smul (c : Eˣ) (Λ : IntegralModel O ρ) : (c • Λ).dual = c⁻¹ • Λ.dual :=
  IntegralModel.ext (Submodule.dualLattice_smul c Λ.lattice)

/-- Duality reverses inclusion of integral models, and detects it. -/
@[simp]
theorem dual_le_dual_iff {Λ Λ' : IntegralModel O ρ} : Λ.dual ≤ Λ'.dual ↔ Λ' ≤ Λ := by
  refine ⟨fun h ↦ ?_, fun h ↦ dual_antitone h⟩
  have := Submodule.IsLattice.free E Λ.lattice
  have := Submodule.IsLattice.free E Λ'.lattice
  have h' := Submodule.dualLattice_antitone E (lattice_le_lattice.mpr h)
  rw [lattice_dual, lattice_dual, Submodule.dualLattice_dualLattice,
    Submodule.dualLattice_dualLattice] at h'
  exact (Submodule.map_le_map_iff_of_injective (f := (Module.Dual.eval E V).restrictScalars O)
    (Module.eval_apply_injective E) _ _).mp h'

/-- Duality of integral models is injective. -/
theorem dual_injective : Function.Injective (dual : IntegralModel O ρ → IntegralModel O ρ.dual) :=
  fun _ _ h ↦ le_antisymm (dual_le_dual_iff.mp h.ge) (dual_le_dual_iff.mp h.le)

variable [TopologicalSpace (Module.Dual E (Module.Dual E V))]
  [IsModuleTopology E (Module.Dual E (Module.Dual E V))]

/-- **Biduality for integral models.** The biduality isomorphism `V ≅ V^∨∨`, evaluation, carries
`Λ` onto the double dual model `Λ^∨∨`. -/
theorem lattice_dual_dual (Λ : IntegralModel O ρ) :
    Λ.dual.dual.lattice = Λ.lattice.map ((Module.Dual.eval E V).restrictScalars O) :=
  have := Submodule.IsLattice.free E Λ.lattice
  Λ.lattice.dualLattice_dualLattice

end TauCeti.GaloisLattice.IntegralModel
