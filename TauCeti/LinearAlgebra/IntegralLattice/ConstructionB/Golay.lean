/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Golay.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionB.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality

/-!
# The Construction B lattice of the extended binary Golay code

Construction B applied to the extended binary Golay code is the lattice of integer vectors in
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two and having coordinate sum divisible by four,
with the halved dot product. It is the kernel of half the coordinate sum modulo two on the
unimodular Golay Construction A lattice, so it has index two there and discriminant four. It is
positive definite, even, and of rank `24`.

This is the half-lattice of the Construction B model of the Leech lattice: the Leech lattice is
the union of it and one odd shifted coset.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti.BinaryGolay

/-- **The Construction B lattice of the extended binary Golay code**: the integer vectors of
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two whose coordinate sum is divisible by four,
with the dot product halved. -/
noncomputable def constructionBLattice : IntegralLattice (Fin 24 → ℚ) :=
  ConstructionB.integralLattice code isDoublyEven_code.isSelfOrthogonal

/-- The Golay Construction B carrier is the Construction B carrier of the Golay code. -/
@[simp]
theorem constructionBLattice_carrier :
    constructionBLattice.carrier = ConstructionB.lattice code :=
  ConstructionB.integralLattice_carrier _ _

/-- The Golay Construction B form is the halved coordinate dot product. -/
@[simp]
theorem constructionBLattice_form : constructionBLattice.form = ConstructionA.form 2 :=
  ConstructionB.integralLattice_form _ _

/-- The Golay Construction B lattice is a sublattice of the Golay Construction A lattice. -/
theorem constructionBLattice_carrier_le :
    constructionBLattice.carrier ≤ constructionALattice.carrier := by
  rw [constructionBLattice_carrier, constructionALattice_carrier]
  exact ConstructionB.lattice_le code

/-- **The Golay Construction B lattice has index two in the Golay Construction A lattice.** -/
theorem relIndex_constructionBLattice :
    constructionBLattice.carrier.toAddSubgroup.relIndex
      constructionALattice.carrier.toAddSubgroup = 2 := by
  rw [constructionBLattice_carrier, constructionALattice_carrier]
  exact ConstructionB.relIndex_lattice code isDoublyEven_code.isEven

/-- The Golay Construction B lattice is nondegenerate. -/
instance instIsNondegenerateConstructionBLattice : constructionBLattice.IsNondegenerate :=
  ConstructionB.isNondegenerate_integralLattice _ _

/-- The Golay Construction B lattice has rank `24`. -/
@[simp]
theorem finrank_constructionBLattice : Module.finrank ℤ constructionBLattice = 24 := by
  rw [constructionBLattice, ConstructionB.finrank_integralLattice, Fintype.card_fin]

/-- The Golay Construction B lattice is positive definite. -/
theorem isPosDef_constructionBLattice : constructionBLattice.IsPosDef :=
  ConstructionB.isPosDef_integralLattice _ _

/-- **The Golay Construction B lattice is even.** -/
theorem isEven_constructionBLattice : constructionBLattice.IsEven :=
  ConstructionB.isEven_integralLattice isDoublyEven_code

/-- **The Golay Construction B lattice has discriminant four**, being of index two in the
unimodular Golay Construction A lattice. -/
@[simp]
theorem discriminant_constructionBLattice : constructionBLattice.discriminant = 4 := by
  rw [constructionBLattice, ConstructionB.discriminant_integralLattice,
    ← constructionALattice_eq_integralLattice,
    constructionALattice.isUnimodular_iff_discriminant_eq_one.mp
      isUnimodular_constructionALattice]

/-- The discriminant group of the Golay Construction B lattice has order four. -/
@[simp]
theorem natCard_discriminantGroup_constructionBLattice :
    Nat.card constructionBLattice.DiscriminantGroup = 4 := by
  rw [IntegralLattice.natCard_discriminantGroup, discriminant_constructionBLattice]

end TauCeti.BinaryGolay
