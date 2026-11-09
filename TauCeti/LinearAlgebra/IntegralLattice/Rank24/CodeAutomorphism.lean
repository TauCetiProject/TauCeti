/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.A1TwentyFour
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.A2Twelfth

/-!
# Golay code automorphisms act on the Niemeier lattices `A₁²⁴` and `A₂¹²`

The Niemeier lattices `A₁²⁴` and `A₂¹²` are glued along subgroups of glue words identified, after
explicit coordinate changes, with the extended binary and ternary Golay codes.  This file shows
that a symmetry of the code induces an isometry of the lattice, through that identification.

* A coordinate permutation `e` of `Fin 24` preserving `BinaryGolay.code` moves Golay coordinate `i`
  to `e i`.  The table coordinate read by Golay coordinate `i` is `p i`, for the permutation
  `p = a1TableToGolayPerm`, so in table coordinates the code automorphism is the permutation
  `p * e * p⁻¹`.  It preserves the glue subgroup, and permuting the twenty-four `A₁` components
  accordingly is an isometry `a1TwentyFourthGolayAutIsometry` of `a1TwentyFourthLattice`.
* A signed permutation `signedEquiv v e` of `Fin 12` preserving `TernaryGolay.code` scales
  coordinate `i` by `v i` and moves it to `e i`; since the units of `ℤ/3` are `±1`, these are all
  the monomial automorphisms of the code.  The comparison `a2TwelfthGolayIsometry` is itself a
  signed permutation, with signs `s = a2TwelfthSign`, so conjugating by it gives a signed
  permutation of the table coordinates: for `p = a2TwelfthDestinationToSource`, table coordinate
  `p a` is multiplied by the sign `a2TwelfthGolayAutSign v e (p a) = s (e a) * v a * s a` and
  moved to `p (e a)`.  Negating and permuting the twelve `A₂` components accordingly is an
  isometry `a2TwelfthGolayAutIsometry` of `a2TwelfthLattice`.

Both isometries come from the general mechanism
`TauCeti.DynkinType.gluedLatticeSignedPermIsometry`: a signed permutation of identical components
which preserves the glue subgroup restricts to an isometry of the glued lattice.  The code
automorphisms, the coordinate changes of glue words and the lattice isometries are kept distinct,
and the evaluation lemmas record how they are related.  The preservation of the glue subgroups is
`mem_a1TwentyFourGlueSubgroup_golayAut_iff` and `mem_a2TwelfthGlueSubgroup_golayAut_iff`; the
ternary case rests on the conjugation identity `signedEquiv_a2TwelfthSign_conj`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §3, Chapter 7, §§6 and 8, and Chapter 16, §1.
-/

public section

namespace TauCeti

open DynkinType IntegralLattice

/-! ### `A₁²⁴` and the binary Golay code -/

/-- **A permutation automorphism of the binary Golay code preserves the glue subgroup of
`A₁²⁴`.**  For a coordinate permutation `e` of the Golay coordinates preserving
`BinaryGolay.code`, permuting the labels of a glue word by `p * e * p⁻¹`, with
`p = a1TableToGolayPerm`, maps `a1TwentyFourGlueSubgroup` onto itself. -/
theorem mem_a1TwentyFourGlueSubgroup_golayAut_iff (e : Equiv.Perm (Fin 24))
    (he : LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm ∈ permutationAut BinaryGolay.code)
    (w : a1TwentyFourGlueModule) :
    (fun j ↦ w ((a1TableToGolayPerm * e * a1TableToGolayPerm⁻¹).symm j) :
        a1TwentyFourGlueModule) ∈ a1TwentyFourGlueSubgroup ↔ w ∈ a1TwentyFourGlueSubgroup := by
  rw [mem_a1TwentyFourGlueSubgroup_iff, mem_a1TwentyFourGlueSubgroup_iff]
  conv_lhs => rw [← (mem_permutationAut.mp he).2, Submodule.mem_map_equiv]
  refine iff_of_eq (congrArg (· ∈ BinaryGolay.code) (funext fun j ↦ ?_))
  simp only [LinearEquiv.funCongrLeft_symm, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply]
  rw [a1TableToGolayIsometry_apply, a1TableToGolayIsometry_apply]
  exact congrArg (fun k ↦ typeA1GlueAlphabetZModStandardIsometry (w k))
    (by simp [Equiv.Perm.mul_def, Equiv.Perm.inv_def])

/-- **A permutation automorphism of the binary Golay code induces an isometry of `A₁²⁴`.**  For a
coordinate permutation `e` of the Golay coordinates preserving `BinaryGolay.code`, the
permutation `p * e * p⁻¹` of the twenty-four `A₁` components, with `p = a1TableToGolayPerm`,
restricts to a self-isometry of the Niemeier lattice `A₁²⁴`. -/
noncomputable def a1TwentyFourthGolayAutIsometry (e : Equiv.Perm (Fin 24))
    (he : LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm ∈ permutationAut BinaryGolay.code) :
    Isometry a1TwentyFourthLattice a1TwentyFourthLattice :=
  (Isometry.ofEq a1TwentyFourthLattice_def).trans <|
    (gluedLatticeSignedPermIsometry _ _ 1 (a1TableToGolayPerm * e * a1TableToGolayPerm⁻¹)
      fun w ↦ by
        simpa only [Pi.one_apply, one_smul] using
          mem_a1TwentyFourGlueSubgroup_golayAut_iff e he w).trans
      (Isometry.ofEq a1TwentyFourthLattice_def.symm)

/-- The isometry of `A₁²⁴` induced by a Golay code automorphism `e` moves the component in table
position `p i` to table position `p (e i)`, for `p = a1TableToGolayPerm`. -/
-- Not `@[simp]`: `simp` rewrites `(A 1).rank` inside the left-hand side by `rank_A`.
theorem a1TwentyFourthGolayAutIsometry_apply (e : Equiv.Perm (Fin 24))
    (he : LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm ∈ permutationAut BinaryGolay.code)
    (x : Fin 24 → Fin (A 1).rank → ℚ) (j : Fin 24) :
    a1TwentyFourthGolayAutIsometry e he x j =
      x (a1TableToGolayPerm (e.symm (a1TableToGolayPerm.symm j))) := by
  rw [a1TwentyFourthGolayAutIsometry, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticeSignedPermIsometry_apply, Pi.one_apply,
    one_smul]
  exact congrArg x (by simp [Equiv.Perm.mul_def, Equiv.Perm.inv_def])

/-! ### `A₂¹²` and the ternary Golay code -/

/-- **The table-coordinate signs of a ternary Golay code automorphism.**  For the signed
permutation `signedEquiv v e` of the Golay coordinates, write `p = a2TwelfthDestinationToSource`
and `s = a2TwelfthSign`.  The sign attached to table coordinate `p a` is `s (e a) * v a * s a`:
conjugating by the coordinate change of `a2TwelfthGolayIsometry` turns `signedEquiv v e` into
the signed permutation of table coordinates with these signs and the permutation `p * e * p⁻¹`. -/
def a2TwelfthGolayAutSign (v : Fin 12 → ℤˣ) (e : Equiv.Perm (Fin 12)) : Fin 12 → ℤˣ :=
  fun k ↦ a2TwelfthSign (e (a2TwelfthDestinationToSource.symm k)) *
    v (a2TwelfthDestinationToSource.symm k) * a2TwelfthSign (a2TwelfthDestinationToSource.symm k)

/-- The sign `a2TwelfthGolayAutSign v e` attaches to table coordinate `k`. -/
@[simp]
theorem a2TwelfthGolayAutSign_apply (v : Fin 12 → ℤˣ) (e : Equiv.Perm (Fin 12)) (k : Fin 12) :
    a2TwelfthGolayAutSign v e k =
      a2TwelfthSign (e (a2TwelfthDestinationToSource.symm k)) *
        v (a2TwelfthDestinationToSource.symm k) *
          a2TwelfthSign (a2TwelfthDestinationToSource.symm k) := by
  rw [a2TwelfthGolayAutSign]

/-- **The ternary comparison conjugates a Golay code automorphism to a signed permutation of the
table coordinates.**  Write `p = a2TwelfthDestinationToSource`, `s = a2TwelfthSign`, and
`signedEquiv (s ∘ p.symm) p.symm` for the coordinate change of `a2TwelfthGolayIsometry` on
ternary words.  Multiplying table coordinate `p a` by `s (e a) * v a * s a` and moving it to
`p (e a)`, followed by the coordinate change, agrees with the coordinate change followed by
`signedEquiv v e`. -/
theorem signedEquiv_a2TwelfthSign_conj (v : Fin 12 → ℤˣ) (e : Equiv.Perm (Fin 12))
    (x : Fin 12 → ZMod 3) :
    signedEquiv (fun i ↦ a2TwelfthSign (a2TwelfthDestinationToSource.symm i))
        a2TwelfthDestinationToSource.symm
        (signedEquiv (a2TwelfthGolayAutSign v e)
          (a2TwelfthDestinationToSource * e * a2TwelfthDestinationToSource⁻¹) x) =
      signedEquiv v e (signedEquiv (fun i ↦ a2TwelfthSign (a2TwelfthDestinationToSource.symm i))
        a2TwelfthDestinationToSource.symm x) := by
  funext j
  obtain ⟨a, rfl⟩ := e.surjective j
  simp only [signedEquiv_apply, a2TwelfthGolayAutSign_apply, Equiv.Perm.mul_def,
    Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Units.val_mul, Int.cast_mul]
  set p := a2TwelfthDestinationToSource
  -- Each sign squares to one.
  have hsq : ((a2TwelfthSign (e a) : ℤ) : ZMod 3) * (a2TwelfthSign (e a) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (a2TwelfthSign (e a)) with h | h <;> simp [h]
  linear_combination ((v a : ℤ) * (a2TwelfthSign a : ℤ) * x (p a) : ZMod 3) * hsq

/-- **A monomial automorphism of the ternary Golay code preserves the glue subgroup of
`A₂¹²`.**  If the signed permutation `signedEquiv v e` preserves `TernaryGolay.code`, then, for
`p = a2TwelfthDestinationToSource` and `s = a2TwelfthSign`, multiplying the label in table
position `p a` by `s (e a) * v a * s a` and moving it to table position `p (e a)` maps
`a2TwelfthGlueSubgroup` onto itself. -/
theorem mem_a2TwelfthGlueSubgroup_golayAut_iff (v : Fin 12 → ℤˣ) (e : Equiv.Perm (Fin 12))
    (he : signedEquiv (R := ZMod 3) v e ∈ monomialAut TernaryGolay.code)
    (w : a2TwelfthGlueModule) :
    (fun j ↦ a2TwelfthGolayAutSign v e
          ((a2TwelfthDestinationToSource * e * a2TwelfthDestinationToSource⁻¹).symm j) •
        w ((a2TwelfthDestinationToSource * e * a2TwelfthDestinationToSource⁻¹).symm j) :
        a2TwelfthGlueModule) ∈ a2TwelfthGlueSubgroup ↔ w ∈ a2TwelfthGlueSubgroup := by
  rw [mem_a2TwelfthGlueSubgroup_iff, mem_a2TwelfthGlueSubgroup_iff]
  set p := a2TwelfthDestinationToSource
  set u := a2TwelfthGolayAutSign v e
  -- The glue words of `A₂` are ternary words, on which signs act by multiplication.
  have hw : (fun j ↦ u ((p * e * p⁻¹).symm j) • w ((p * e * p⁻¹).symm j) :
      Fin 12 → ZMod 3) = signedEquiv (R := ZMod 3) u (p * e * p⁻¹) w :=
    funext fun j ↦ by
      simp only [signedEquiv_apply (R := ZMod 3) u _ w j, Units.smul_def]
      exact zsmul_eq_mul (_ : ZMod 3) _
  refine (iff_of_eq (congrArg (· ∈ TernaryGolay.code)
    (((a2TwelfthGolayIsometry_eq_signedEquiv _).trans (congrArg _ hw)).trans
      (signedEquiv_a2TwelfthSign_conj v e w)))).trans ?_
  conv_lhs => rw [← (mem_monomialAut.mp he).2, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]
  exact iff_of_eq (congrArg (· ∈ TernaryGolay.code)
    (a2TwelfthGolayIsometry_eq_signedEquiv w).symm)

/-- **A monomial automorphism of the ternary Golay code induces an isometry of `A₂¹²`.**  Let the
signed permutation `signedEquiv v e`, scaling Golay coordinate `a` by `v a` and moving it to
`e a`, preserve `TernaryGolay.code`.  Write `p = a2TwelfthDestinationToSource` and
`s = a2TwelfthSign` for the coordinate change of `a2TwelfthGolayIsometry`.  Then multiplying the
`A₂` component in table position `p a` by the sign `s (e a) * v a * s a` and moving it to table
position `p (e a)` restricts to a self-isometry of the Niemeier lattice `A₂¹²`. -/
noncomputable def a2TwelfthGolayAutIsometry (v : Fin 12 → ℤˣ) (e : Equiv.Perm (Fin 12))
    (he : signedEquiv (R := ZMod 3) v e ∈ monomialAut TernaryGolay.code) :
    Isometry a2TwelfthLattice a2TwelfthLattice :=
  (Isometry.ofEq a2TwelfthLattice_def).trans <|
    (gluedLatticeSignedPermIsometry _ _ (a2TwelfthGolayAutSign v e)
      (a2TwelfthDestinationToSource * e * a2TwelfthDestinationToSource⁻¹)
      (mem_a2TwelfthGlueSubgroup_golayAut_iff v e he)).trans
      (Isometry.ofEq a2TwelfthLattice_def.symm)

/-- The isometry of `A₂¹²` induced by a ternary Golay code automorphism `signedEquiv v e` moves
the component in table position `p a` to table position `p (e a)`, multiplied by the sign
`s (e a) * v a * s a`, for `p = a2TwelfthDestinationToSource` and `s = a2TwelfthSign`.  At table
position `j` this is stated with `a = e.symm (p.symm j)`, so that `j = p (e a)` and
`s (e a) = s (p.symm j)`. -/
-- Not `@[simp]`: `simp` rewrites `(A 2).rank` inside the left-hand side by `rank_A`.
theorem a2TwelfthGolayAutIsometry_apply (v : Fin 12 → ℤˣ) (e : Equiv.Perm (Fin 12))
    (he : signedEquiv (R := ZMod 3) v e ∈ monomialAut TernaryGolay.code)
    (x : Fin 12 → Fin (A 2).rank → ℚ) (j : Fin 12) :
    a2TwelfthGolayAutIsometry v e he x j =
      (a2TwelfthSign (a2TwelfthDestinationToSource.symm j) *
          v (e.symm (a2TwelfthDestinationToSource.symm j)) *
            a2TwelfthSign (e.symm (a2TwelfthDestinationToSource.symm j))) •
        x (a2TwelfthDestinationToSource (e.symm (a2TwelfthDestinationToSource.symm j))) := by
  rw [a2TwelfthGolayAutIsometry, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply, gluedLatticeSignedPermIsometry_apply]
  simp [Equiv.Perm.mul_def, Equiv.Perm.inv_def]

end TauCeti
