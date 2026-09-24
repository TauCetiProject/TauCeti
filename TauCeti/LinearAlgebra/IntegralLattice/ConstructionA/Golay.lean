/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Binary.Golay.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Even

/-!
# The Construction A lattice of the extended binary Golay code

Construction A applied to the extended binary Golay code produces the rank-`24` lattice of
integer vectors in `ℚ^(Fin 24)` whose reduction modulo two is a Golay codeword, carrying the
halved dot product. Because the Golay code is doubly even and Euclidean self-dual, this lattice
is positive definite, even, and unimodular.

## References

* W. Ebeling, *Lattices and Codes*, §§1.3 and 2.8, for Construction A applied to the Golay
  code.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11 and
  Chapter 7, §6.
-/

public section

namespace TauCeti.BinaryGolay

/-- The extended binary Golay code is Euclidean self-dual, phrased for the submodule over
`ZMod 2` that Construction A consumes. -/
theorem toZModSubmodule_code_eq_euclideanDual :
    AddSubgroup.toZModSubmodule 2 code.toAddSubgroup =
      (AddSubgroup.toZModSubmodule 2 code.toAddSubgroup).euclideanDual := by
  rw [Submodule.toAddSubgroup_toZModSubmodule, euclideanDual_code]

/-- **The Construction A lattice of the extended binary Golay code**: the integer vectors of
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two, with the dot product halved. -/
noncomputable def constructionALattice : IntegralLattice (Fin 24 → ℚ) :=
  ConstructionA.integralLattice 2 code.toAddSubgroup toZModSubmodule_code_eq_euclideanDual.le

/-- The Golay lattice is Construction A applied to the explicit extended binary Golay code. -/
@[simp]
theorem constructionALattice_eq_integralLattice :
    constructionALattice = ConstructionA.integralLattice 2 code.toAddSubgroup
      toZModSubmodule_code_eq_euclideanDual.le := by
  rw [constructionALattice]

/-- The Golay Construction A lattice has rank `24`. -/
theorem finrank_constructionALattice : Module.finrank ℤ constructionALattice = 24 := by
  rw [IntegralLattice.finrank_carrier]
  simp

/-- The Golay Construction A lattice is positive definite. -/
theorem isPosDef_constructionALattice : constructionALattice.IsPosDef :=
  ConstructionA.isPosDef_integralLattice 2 code.toAddSubgroup
    toZModSubmodule_code_eq_euclideanDual.le

/-- **The Golay Construction A lattice is even.** -/
theorem isEven_constructionALattice : constructionALattice.IsEven :=
  (ConstructionA.isEven_integralLattice_two_iff_isDoublyEven code
    toZModSubmodule_code_eq_euclideanDual.le).mpr isDoublyEven_code

/-- **The Golay Construction A lattice is unimodular.** -/
theorem isUnimodular_constructionALattice : constructionALattice.IsUnimodular :=
  (ConstructionA.isUnimodular_integralLattice_iff 2 code.toAddSubgroup
    toZModSubmodule_code_eq_euclideanDual.le).mpr toZModSubmodule_code_eq_euclideanDual

end TauCeti.BinaryGolay
