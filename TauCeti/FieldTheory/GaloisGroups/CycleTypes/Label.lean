/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.CycleTypes.Basic
public import TauCeti.FieldTheory.GaloisGroups.Label
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.CycleTypes

/-!
# Galois cycle types from transitive-group labels

A Galois label identifies the root action with a conjugate of a reference permutation group.
Consequently `Polynomial.Gal.cycleTypes` is exactly the full cycle-type set of that reference,
independently of the numbering of the roots. The reference-group calculations in degree five
then give the complete cycle-type set of every labelled quintic, including fixed points.

The comparison uses `Polynomial.Gal.mem_cycleTypes_iff_exists_mem_range`, transport of full
cycle types along an equivalence, and `TauCeti.TransitiveGroupLabel.image_fullCycleType_eq`.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] {p : F[X]}

/-- A Galois label determines all the cycle types of the polynomial, including fixed roots.
This compares the intrinsic invariant directly with the reference subgroup, independently of
the numbering used to exhibit the label. -/
theorem HasGaloisLabel.cycleTypes_eq {n : ℕ} {j : TransitiveGroupIndex n}
    (h : HasGaloisLabel p j) :
    Gal.cycleTypes p = Equiv.Perm.fullCycleType ''
      (referenceSubgroup n j : Set (Equiv.Perm (Fin n))) := by
  classical
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  let e : p.rootSet p.SplittingField ≃ Fin n :=
    Fintype.equivFinOfCardEq
      ((card_rootSet_eq_natDegree h.separable (SplittingField.splits p)).trans h.natDegree_eq)
  have he := h.transitiveGroupLabel e
  calc
    Gal.cycleTypes p = Equiv.Perm.fullCycleType ''
        ((Gal.galActionHom p p.SplittingField).range :
          Set (Equiv.Perm (p.rootSet p.SplittingField))) := by
      ext t
      exact Gal.mem_cycleTypes_iff_exists_mem_range p p.SplittingField
    _ = Equiv.Perm.fullCycleType ''
        ((Gal.galActionHom p p.SplittingField).range.map e.permCongrHom.toMonoidHom :
          Set (Equiv.Perm (Fin n))) :=
      (Equiv.image_fullCycleType_map_permCongrHom e _).symm
    _ = Equiv.Perm.fullCycleType '' (referenceSubgroup n j : Set (Equiv.Perm (Fin n))) :=
      he.image_fullCycleType_eq

end TauCeti
