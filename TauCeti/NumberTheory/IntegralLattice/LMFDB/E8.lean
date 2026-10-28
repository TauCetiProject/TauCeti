/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.LMFDB.StoredGenusCertificate
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.WeylGroup

/-!
# The stored columns of the LMFDB record of `E₈`

The LMFDB lattice record `8.1.1.1.1` is the root lattice `E₈`, with determinant `1`, level `1`,
minimum `2`, kissing number `240`, automorphism group order `696729600`, and a single genus
representative. This file certifies these columns as a
`TauCeti.IntegralLattice.StoredGenusCertificate` whose Gram matrix, and whose one genus
representative, is the Cartan matrix of type `E₈`, with the theta series prefix `1, 0, 240`.
The certificate does not assert that the genus has a single class.

## Main definitions

* `TauCeti.IntegralLattice.typeE₈StoredGenusCertificate`: the certificate of the stored columns
  of the LMFDB record of `E₈`.

## References

* The LMFDB Collaboration, *The L-functions and modular forms database*, lattice `8.1.1.1.1`,
  https://www.lmfdb.org/Lattice/8.1.1.1.1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.1.
-/

public section

namespace TauCeti.IntegralLattice

/-- **The certificate of the stored columns of the LMFDB record of `E₈`.** The stored Gram matrix
is the Cartan matrix of type `E₈`, with determinant `1`, level `1`, minimum `2`, kissing number
`240`, automorphism group order `696729600`, theta series prefix `1, 0, 240`, and the single genus
representative given by the same Cartan matrix. -/
noncomputable def typeE₈StoredGenusCertificate : StoredGenusCertificate 8 where
  gram := CartanMatrix.E 8
  gram_isSymm := CartanMatrix.E_isSymm 8
  isPosDef := typeE₈RootLattice_def ▸ isPosDef_typeE₈RootLattice
  determinant := 1
  determinant_eq := by rw [← typeE₈RootLattice_def, determinant_typeE₈RootLattice]
  level := 1
  level_eq := by rw [← typeE₈RootLattice_def, level_typeE₈RootLattice]
  minimum := 2
  minimum_eq := by rw [← typeE₈RootLattice_def, minimum_typeE₈RootLattice]
  kissingNumber := 240
  kissingNumber_eq := by rw [← typeE₈RootLattice_def, kissingNumber_typeE₈RootLattice]
  autOrder := 696729600
  autOrder_eq := by rw [← typeE₈RootLattice_def, card_isometry_typeE₈RootLattice]
  thetaSeries := [1, 0, 240]
  thetaSeries_eq := by
    rw [← typeE₈RootLattice_def]
    intro k hk
    match k, hk with
    | 0, _ =>
      exact (representationNumber_zero_of_anisotropic
        (by rw [norm_def]; exact isPosDef_typeE₈RootLattice.anisotropic)).symm
    | 1, _ =>
      rw [representationNumber_def, Nat.cast_one, ← Int.cast_one,
        IsEven.vectorsOfNorm_eq_empty_of_not_even _ isEven_typeE₈RootLattice (by decide),
        Set.ncard_empty]
      rfl
    | 2, _ => exact representationNumber_typeE₈RootLattice_two.symm
  reps := [⟨CartanMatrix.E 8, CartanMatrix.E_isSymm 8⟩]
  sameGenus_reps H hH := by
    obtain rfl := List.mem_singleton.mp hH
    exact SameGenus.refl _
  pairwise_isEmpty_isometry_reps := List.pairwise_singleton _ _

/-- The lattice of the stored Gram matrix of the `E₈` record is the root lattice `E₈`. -/
@[simp]
theorem lattice_typeE₈StoredGenusCertificate :
    typeE₈StoredGenusCertificate.lattice = typeE₈RootLattice :=
  typeE₈RootLattice_def.symm

end TauCeti.IntegralLattice
