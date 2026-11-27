/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# The homology class map of an opposite short complex

For a short complex `S` with homology, Mathlib identifies the homology of the opposite short
complex `S.op` with the opposite of the homology of `S` (`ShortComplex.homologyOpIso`), and the
cycles of `S.op` with the opposite of the opcycles of `S` (`ShortComplex.cyclesOpIso`). This file
records that, under these identifications, the projection `S.op.homologyπ` of the cycles of `S.op`
onto its homology is the opposite of the inclusion `S.homologyι` of the homology of `S` into its
opcycles (`CategoryTheory.ShortComplex.op_homologyπ_homologyOpIso_hom`). It also records the
`hom` form `CategoryTheory.ShortComplex.cyclesOpIso_hom_pOpcycles_op` of Mathlib's
`CategoryTheory.ShortComplex.cyclesOpIso_inv_op_iCycles`.
-/

public section

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] (S : ShortComplex C)

/-- Under the identification `cyclesOpIso`, the opposite of the projection `S.pOpcycles` onto the
opcycles is the inclusion of the cycles of the opposite short complex. -/
@[reassoc (attr := simp)]
lemma cyclesOpIso_hom_pOpcycles_op [S.HasRightHomology] :
    S.cyclesOpIso.hom ≫ S.pOpcycles.op = S.op.iCycles := by
  rw [← cyclesOpIso_inv_op_iCycles, Iso.hom_inv_id_assoc]

variable [S.HasHomology]

/-- Under the identifications `homologyOpIso` and `cyclesOpIso`, the projection of the cycles of
the opposite short complex onto its homology is the opposite of `S.homologyι`. -/
@[reassoc (attr := simp)]
lemma op_homologyπ_homologyOpIso_hom :
    S.op.homologyπ ≫ S.homologyOpIso.hom = S.cyclesOpIso.hom ≫ S.homologyι.op := by
  -- `leftHomologyOpIso` is the left homology isomorphism of the opposite right homology data.
  have h : S.op.leftHomologyπ ≫ S.leftHomologyOpIso.hom =
      S.cyclesOpIso.hom ≫ S.rightHomologyι.op :=
    S.rightHomologyData.op.leftHomologyπ_comp_leftHomologyIso_hom
  simp [homologyOpIso, homologyπ, homologyι, reassoc_of% h]

end CategoryTheory.ShortComplex
