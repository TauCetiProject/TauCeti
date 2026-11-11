/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.A1TwentyFour.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.CodeAutomorphism

/-!
# Binary Golay permutations on the table lattice `A₁²⁴`

A permutation preserving the extended binary Golay code acts on the canonical table lattice
`RootfulNiemeierType.a1TwentyFourth.lattice`. Transport the isometry
`TauCeti.a1TwentyFourthGolayAutIsometry` through the coordinate-preserving identification with
`TauCeti.a1TwentyFourthLattice`.

The table coordinates are not the systematic Golay coordinates. The intertwining theorem
`a1TwentyFourthLatticeConstructionAIsometry_golayAut_apply` shows that the explicit isometry
onto Golay Construction A cancels this coordinate change: in Construction-A coordinates the
induced lattice isometry is precisely the original permutation. Thus the code action and the
table-lattice action are related by the specified coordinate map, not an abstract equivalence.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.,
  Chapter 4 §3, Chapter 7 §6, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti.RootfulNiemeierType

open IntegralLattice

variable (e : Equiv.Perm (Fin 24))
  (he : LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm ∈ permutationAut BinaryGolay.code)

/-- A binary Golay coordinate permutation acts on the canonical `A₁²⁴` table lattice,
through its identification with the lattice glued along the binary Golay subgroup. -/
noncomputable def a1TwentyFourthLatticeGolayAutIsometry :
    Isometry a1TwentyFourth.lattice a1TwentyFourth.lattice :=
  a1TwentyFourthLatticeIsometry.conjMulEquiv.symm (a1TwentyFourthGolayAutIsometry e he)

/-- The identification with the constant-family gluing intertwines the two lattice actions. -/
-- Not `@[simp]`: `simp` normalizes `(A 1).rank` in the codomain of the comparison isometry.
theorem a1TwentyFourthLatticeIsometry_golayAut_apply
    (x : ∀ i, Fin (a1TwentyFourth.componentType i).rank → ℚ) :
    a1TwentyFourthLatticeIsometry (a1TwentyFourthLatticeGolayAutIsometry e he x) =
      a1TwentyFourthGolayAutIsometry e he (a1TwentyFourthLatticeIsometry x) := by
  rw [a1TwentyFourthLatticeGolayAutIsometry, Isometry.conjMulEquiv_symm_apply,
    Isometry.apply_symm_apply]

/-- In Golay Construction-A coordinates the table-lattice action moves coordinate `i` to
`e i`: the table-to-Golay coordinate change cancels the conjugating permutation. -/
@[simp]
theorem a1TwentyFourthLatticeConstructionAIsometry_golayAut_apply
    (x : ∀ i, Fin (a1TwentyFourth.componentType i).rank → ℚ) (j : Fin 24) :
    a1TwentyFourthLatticeConstructionAIsometry (a1TwentyFourthLatticeGolayAutIsometry e he x) j =
      a1TwentyFourthLatticeConstructionAIsometry x (e.symm j) := by
  -- Evaluate the two factors of the table-to-Construction-A isometry in turn.
  simp only [a1TwentyFourthLatticeConstructionAIsometry_def, Isometry.trans_apply,
    a1TwentyFourthLatticeIsometry_golayAut_apply,
    a1TwentyFourthConstructionAIsometry_apply, a1TwentyFourthGolayAutIsometry_apply,
    Equiv.symm_apply_apply]

end TauCeti.RootfulNiemeierType
