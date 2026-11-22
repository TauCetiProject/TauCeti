/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.ModTwo
public import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Action.Hom

/-!
# The lattice Conway quotient and its faithful actions

`Co0` is the full isometry group of the canonical Leech lattice. The quotient `Co1` by
negation is finite and acts faithfully on the 98280 antipodal pairs of minimal vectors.
The kernel calculation uses the actual lattice action, rather than a presumed Conway
generating set. No identification with a sporadic presentation, order formula or simplicity
result is asserted here.

Reduction modulo two induces an action of `Co1` on the mod-two Leech module `Λ / 2Λ`, since
negation acts trivially there. This action is faithful as well: by
`TauCeti.congruenceSubgroup_two_leechLattice`, only identity and negation act trivially on
`Λ / 2Λ`. The action permutes the type-2 classes, and the identification
`TauCeti.leechAntipodalPairsEquivModTwo` of minimal pairs with type-2 classes is
`Co1`-equivariant, so a minimal pair and its type-2 class have the same stabilizer in `Co1`.
Irreducibility of `Λ / 2Λ` is not proved here.

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
    (e : Co1) • p = Isometry.antipodalPairsHom leechLattice 4 e p := by
  rw [Co1.smul_def, Co1.antipodalPairsHom_mk]

/-- The inverse of a quotient representative acts by the inverse pair permutation. -/
@[simp]
theorem Co1.mk_inv_smul (e : Co0) (p : leechLattice.antipodalPairs 4) :
    (e : Co1)⁻¹ • p = (Isometry.antipodalPairsHom leechLattice 4 e).symm p := by
  rw [Co1.smul_def, map_inv, Co1.antipodalPairsHom_mk, Equiv.Perm.inv_def]

/-- The action of the first Conway lattice group on minimal pairs is faithful. -/
instance Co1.instFaithfulSMul : FaithfulSMul Co1 (leechLattice.antipodalPairs 4) where
  eq_of_smul_eq_smul h := Co1.antipodalPairsHom_injective (Equiv.ext h)

/-! ### The action on the mod-two Leech module -/

/-- The first Conway lattice group's action on the mod-two Leech module `Λ / 2Λ`, induced by
reduction of lattice isometries modulo two. -/
noncomputable def Co1.reductionHom : Co1 →* Module.End ℤ (QuotSMulTop (2 : ℤ) leechLattice) :=
  QuotientGroup.lift _ (Isometry.reductionHom leechLattice 2)
    ((Isometry.zpowers_neg_le_congruenceSubgroup_two leechLattice).trans_eq
      (Isometry.ker_reductionHom leechLattice 2).symm)

/-- On a quotient representative, the mod-two action is the reduction of the lattice isometry. -/
@[simp]
theorem Co1.reductionHom_mk (e : Co0) :
    Co1.reductionHom (e : Co1) = Isometry.reductionHom leechLattice 2 e :=
  QuotientGroup.lift_mk _ _ e

/-- The action of the first Conway lattice group on `Λ / 2Λ` is faithful. -/
theorem Co1.reductionHom_injective : Function.Injective Co1.reductionHom :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr <|
    congruenceSubgroup_two_leechLattice.symm.trans (Isometry.ker_reductionHom leechLattice 2).symm

/-- The first Conway lattice group acts additively on the mod-two Leech module. -/
noncomputable instance Co1.instDistribMulActionModTwo :
    DistribMulAction Co1 (QuotSMulTop (2 : ℤ) leechLattice) :=
  DistribMulAction.compHom _ Co1.reductionHom

/-- The Conway action on `Λ / 2Λ` is given by the mod-two representation. -/
theorem Co1.smul_modTwo_def (g : Co1) (c : QuotSMulTop (2 : ℤ) leechLattice) :
    g • c = Co1.reductionHom g c := (rfl)

/-- A quotient representative acts on `Λ / 2Λ` by the reduction of its lattice isometry. -/
@[simp]
theorem Co1.mk_smul_modTwo (e : Co0) (c : QuotSMulTop (2 : ℤ) leechLattice) :
    (e : Co1) • c = Isometry.reductionHom leechLattice 2 e c := by
  rw [Co1.smul_modTwo_def, Co1.reductionHom_mk]

/-- The action of the first Conway lattice group on `Λ / 2Λ` preserves the type-2 classes. -/
@[simp]
theorem Co1.smul_mem_normClassesModTwo_four_iff (g : Co1) (c : QuotSMulTop (2 : ℤ) leechLattice) :
    g • c ∈ leechLattice.normClassesModTwo 4 ↔ c ∈ leechLattice.normClassesModTwo 4 := by
  induction g using QuotientGroup.induction_on with
  | H e => rw [Co1.mk_smul_modTwo, Isometry.reductionHom_mem_normClassesModTwo_iff]

/-- The action of the first Conway lattice group on `Λ / 2Λ` is faithful. -/
instance Co1.instFaithfulSMulModTwo : FaithfulSMul Co1 (QuotSMulTop (2 : ℤ) leechLattice) where
  eq_of_smul_eq_smul h := Co1.reductionHom_injective (LinearMap.ext h)

/-- The identification of minimal pairs with type-2 classes intertwines the two actions of the
first Conway lattice group. -/
theorem Co1.coe_leechAntipodalPairsEquivModTwo_smul (g : Co1)
    (p : leechLattice.antipodalPairs 4) :
    (leechAntipodalPairsEquivModTwo (g • p) : QuotSMulTop (2 : ℤ) leechLattice) =
      g • (leechAntipodalPairsEquivModTwo p : QuotSMulTop (2 : ℤ) leechLattice) := by
  induction g using QuotientGroup.induction_on with
  | H e =>
    rw [Co1.mk_smul, Co1.mk_smul_modTwo, Isometry.antipodalPairsHom_apply]
    exact coe_leechAntipodalPairsEquivModTwo_antipodalPairsEquiv e p

/-- A minimal pair and its type-2 class in `Λ / 2Λ` have the same stabilizer in the first Conway
lattice group. -/
theorem Co1.stabilizer_leechAntipodalPairsEquivModTwo (p : leechLattice.antipodalPairs 4) :
    MulAction.stabilizer Co1
        (leechAntipodalPairsEquivModTwo p : QuotSMulTop (2 : ℤ) leechLattice) =
      MulAction.stabilizer Co1 p := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    ← Co1.coe_leechAntipodalPairsEquivModTwo_smul, ← Subtype.ext_iff,
    leechAntipodalPairsEquivModTwo.apply_eq_iff_eq]

end TauCeti.Sporadic
