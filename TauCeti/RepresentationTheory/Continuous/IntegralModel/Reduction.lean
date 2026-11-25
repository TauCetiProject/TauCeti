/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.IntegralModel.Basic
public import TauCeti.RepresentationTheory.Continuous.Reduction

/-!
# Reductions of integral models of characters

If `g` acts on a module `M` over a topological local ring `A` by a scalar `c`, it acts on the raw
reduction `k_A ⊗[A] M` by the residue of `c`
(`TauCeti.ContinuousRep.reduction_apply_of_forall_apply_eq_smul`).

For a continuous character `χ : Γ → Eˣ` with values in the image of a coefficient ring `O`, every
integral model `Λ` of the line `ofCharacter χ` is acted on by the scalars `c` with
`algebraMap O E c = χ g` (`TauCeti.GaloisLattice.IntegralModel.toContinuousRep_ofCharacter_apply`),
so when `O` is local the reduction of any model is the character `g ↦ residue c`
(`TauCeti.GaloisLattice.IntegralModel.reduction_toContinuousRep_ofCharacter_apply`). For instance,
any model of `ℚ_ℓ(1)` reduces to the mod `ℓ` cyclotomic character.

## Main results

* `TauCeti.ContinuousRep.reduction_apply_of_forall_apply_eq_smul`: scalars reduce to their
  residues.
* `TauCeti.GaloisLattice.IntegralModel.reduction_toContinuousRep_ofCharacter_apply`: every model
  of a character line reduces to the residue of the character.
-/

public section

open IsLocalRing
open scoped TensorProduct

namespace TauCeti

namespace ContinuousRep

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [IsLocalRing A]
  [TopologicalSpace A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [TopologicalSpace (ResidueField A)] [IsTopologicalRing (ResidueField A)]
  [ContinuousSMul A (ResidueField A)] [TopologicalSpace (ResidueField A ⊗[A] M)]
  [IsModuleTopology (ResidueField A) (ResidueField A ⊗[A] M)]

/-- If `g` acts on `M` by the scalar `c`, it acts on the reduction by the residue of `c`. -/
theorem reduction_apply_of_forall_apply_eq_smul (ρ : ContinuousRep Γ A M) {g : Γ} {c : A}
    (h : ∀ x, ρ g x = c • x) (y : ResidueField A ⊗[A] M) :
    ρ.reduction g y = residue A c • y := by
  rw [baseChange_apply]
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => rw [map_add, hy, hz, smul_add]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, h, TensorProduct.tmul_smul, ← ResidueField.algebraMap_eq,
      algebraMap_smul]

end ContinuousRep

namespace GaloisLattice.IntegralModel

variable {Γ O E : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing O] [CommRing E] [Algebra O E]
  [TopologicalSpace E] [ContinuousMul E]

/-- On an integral model of the line of a character `χ`, an element `g` acts by any scalar `c`
of the coefficient ring with `algebraMap O E c = χ g`. -/
theorem toContinuousRep_ofCharacter_apply {χ : Γ →ₜ* Eˣ}
    (Λ : IntegralModel O (ContinuousRep.ofCharacter χ)) {g : Γ} {c : O}
    (hc : algebraMap O E c = χ g) (x : Λ.lattice) : Λ.toContinuousRep g x = c • x :=
  Subtype.ext <| by
    rw [coe_toContinuousRep_apply, ContinuousRep.ofCharacter_apply, ← hc, Submodule.coe_smul,
      Algebra.smul_def]

variable [IsLocalRing O] [TopologicalSpace O] {χ : Γ →ₜ* Eˣ}
  (Λ : IntegralModel O (ContinuousRep.ofCharacter χ)) [IsModuleTopology O Λ.lattice]
  [TopologicalSpace (ResidueField O)] [IsTopologicalRing (ResidueField O)]
  [ContinuousSMul O (ResidueField O)] [TopologicalSpace (ResidueField O ⊗[O] Λ.lattice)]
  [IsModuleTopology (ResidueField O) (ResidueField O ⊗[O] Λ.lattice)]

/-- **Every model of a character line reduces to the residue of the character.** If
`algebraMap O E c = χ g`, then `g` acts on the reduction of any integral model of
`ofCharacter χ` by the residue of `c`. -/
theorem reduction_toContinuousRep_ofCharacter_apply {g : Γ} {c : O}
    (hc : algebraMap O E c = χ g) (y : ResidueField O ⊗[O] Λ.lattice) :
    Λ.toContinuousRep.reduction g y = residue O c • y :=
  Λ.toContinuousRep.reduction_apply_of_forall_apply_eq_smul
    (Λ.toContinuousRep_ofCharacter_apply hc) y

end GaloisLattice.IntegralModel

end TauCeti
