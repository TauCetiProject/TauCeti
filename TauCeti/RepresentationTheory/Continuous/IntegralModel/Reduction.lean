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

For a continuous character `χ : Γ → Eˣ` with values in the image of a local coefficient ring
`O`, every integral model `Λ` of the line `ofCharacter χ` is acted on by the scalars `c` with
`algebraMap O E c = χ g` (`TauCeti.GaloisLattice.IntegralModel.toContinuousRep_ofCharacter_apply`),
so the reduction of any model is the character `g ↦ residue c`. For instance, any model of
`ℚ_ℓ(1)` reduces to the mod `ℓ` cyclotomic character.

## Main results

* `TauCeti.GaloisLattice.IntegralModel.reduction_toContinuousRep_ofCharacter_apply`: every model
  of a character line reduces to the residue of the character.
-/

public section

open IsLocalRing
open scoped TensorProduct

namespace TauCeti.GaloisLattice.IntegralModel

variable {Γ O E : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing O] [CommRing E] [Algebra O E]
  [TopologicalSpace E] [ContinuousMul E] [IsLocalRing O] [TopologicalSpace O] {χ : Γ →ₜ* Eˣ}
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

end TauCeti.GaloisLattice.IntegralModel
