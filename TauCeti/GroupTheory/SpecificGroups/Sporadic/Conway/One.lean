/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Isometry
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Action.Hom

/-!
# The lattice Conway quotient and its faithful pair action

`Co0` is the full isometry group of the canonical Leech lattice. The quotient `Co1` by
negation is finite and acts faithfully on the 98280 antipodal pairs of minimal vectors.
The kernel calculation uses the actual lattice action, rather than a presumed Conway
generating set. No identification with a sporadic presentation, order formula or simplicity
result is asserted here.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti.Sporadic

open IntegralLattice

/-- The full isometry group of the canonical Leech lattice. -/
abbrev Co0 := Isometry leechLattice leechLattice

/-- The first Conway lattice group, the quotient of the full Leech isometry group by negation.
This definition does not identify it with any abstract presentation. -/
abbrev Co1 := Co0 ⧸ Subgroup.zpowers (Isometry.neg leechLattice)

/-- The first Conway lattice group's permutation representation on Leech minimal pairs. -/
noncomputable def Co1.antipodalPairsHom : Co1 →* Equiv.Perm (leechLattice.antipodalPairs 4) :=
  QuotientGroup.lift _ (Isometry.antipodalPairsHom leechLattice 4)
    ker_antipodalPairsHom_leechLattice.symm.le

/-- On a quotient representative, the pair action is the original lattice-isometry action. -/
@[simp]
theorem Co1.antipodalPairsHom_mk (e : Co0) :
    Co1.antipodalPairsHom (e : Co1) = Isometry.antipodalPairsHom leechLattice 4 e :=
  QuotientGroup.lift_mk _ _ e

/-- The permutation representation of the first Conway lattice group is faithful. -/
theorem Co1.antipodalPairsHom_injective : Function.Injective Co1.antipodalPairsHom :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr ker_antipodalPairsHom_leechLattice.symm

/-- The first Conway lattice group acts on the antipodal pairs of Leech minimal vectors. -/
noncomputable instance Co1.instMulAction : MulAction Co1 (leechLattice.antipodalPairs 4) :=
  MulAction.compHom _ Co1.antipodalPairsHom

/-- The Conway action on minimal pairs is given by the pair permutation representation. -/
theorem Co1.smul_def (g : Co1) (p : leechLattice.antipodalPairs 4) :
    g • p = Co1.antipodalPairsHom g p := (rfl)

/-- A quotient representative acts by its lattice-isometry permutation of minimal pairs. -/
@[simp]
theorem Co1.mk_smul (e : Co0) (p : leechLattice.antipodalPairs 4) :
    (e : Co1) • p = Isometry.antipodalPairsHom leechLattice 4 e p := (rfl)

/-- The inverse of a quotient representative acts by the inverse pair permutation. -/
@[simp]
theorem Co1.mk_inv_smul (e : Co0) (p : leechLattice.antipodalPairs 4) :
    (e : Co1)⁻¹ • p = (Isometry.antipodalPairsHom leechLattice 4 e).symm p := by
  rw [Co1.smul_def, map_inv, Co1.antipodalPairsHom_mk]
  rfl

/-- The action of the first Conway lattice group on minimal pairs is faithful. -/
instance Co1.instFaithfulSMul : FaithfulSMul Co1 (leechLattice.antipodalPairs 4) where
  eq_of_smul_eq_smul h := Co1.antipodalPairsHom_injective (Equiv.ext h)

end TauCeti.Sporadic
