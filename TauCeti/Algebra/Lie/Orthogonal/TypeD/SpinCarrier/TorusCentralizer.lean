/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic

/-!
# The centralizer of the type-D spin weight torus

Over an infinite field, a point of the full-weight type-`Dₙ` spin carrier centralizes the weight
torus exactly when its matrix in the exterior basis is diagonal. The spin weights of the sign sets
are distinct, also across the two half-spin summands, and over an infinite field distinct weights
are distinct characters of the split torus, so the torus separates every pair of basis vectors.
The centralizer is therefore the inverse image of the diagonal torus of `GL_(2^n)`.

This does not identify the diagonal carrier points with the image of the weight torus, so it is
not the statement that the weight torus is its own centralizer, nor its maximality.

## Main results

* `TauCeti.TypeDSpinCarrier.mem_centralizer_range_weightTorusPoints_iff_isDiag`: a carrier
  point centralizes the weight torus exactly when its matrix is diagonal.
* `TauCeti.TypeDSpinCarrier.centralizer_range_weightTorusPoints_eq_comap_diagonalTorus`: the
  centralizer is the inverse image of the diagonal torus.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.TorusCentralizer`, whose character-separation
  argument for the short-root `F₄` weight torus is the source of the general criterion
  `TauCeti.mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL` applied here.
-/

public section

namespace TauCeti.TypeDSpinCarrier

variable (n : ℕ) (hn : 4 ≤ n) {k : Type*} [Field k] [Infinite k]

/-- Over an infinite field, a point of the type-`Dₙ` spin carrier centralizes the weight torus
exactly when its matrix is diagonal. -/
@[simp]
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag (g : points n hn k) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints n hn k)) ↔
      ((g : GL (Fin (dimension n)) k) : Matrix (Fin (dimension n)) (Fin (dimension n)) k).IsDiag :=
  mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL
    (fun s ↦ (coe_weightTorusPoints n hn k s).trans
      (UniversalEnvelopingAlgebra.kostantTorusMatrix_apply _ _ _ s))
    (fun _ _ hij ↦ exists_torusCharacter_ne fun h ↦
      hij ((Fintype.equivFin (Finset (Fin n))).symm.injective
        (DynkinType.typeDSpinWeight_injective h))) g

/-- Over an infinite field, the centralizer of the type-`Dₙ` spin weight torus is the inverse
image of the diagonal torus of `GL_(2^n)`. -/
theorem centralizer_range_weightTorusPoints_eq_comap_diagonalTorus :
    Subgroup.centralizer (Set.range (weightTorusPoints n hn k)) =
      (diagonalTorus k (dimension n)).comap (points n hn k).subtype := by
  ext g
  simp only [mem_centralizer_range_weightTorusPoints_iff_isDiag, Subgroup.mem_comap,
    Subgroup.subtype_apply, mem_diagonalTorus_iff]

end TauCeti.TypeDSpinCarrier
