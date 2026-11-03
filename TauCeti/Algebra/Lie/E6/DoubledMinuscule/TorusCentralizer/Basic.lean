/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GroupScheme

/-!
# The centralizer of the doubled type-E₆ minuscule weight torus

Over an infinite field, a point of the doubled type-`E₆` minuscule carrier centralizes the weight
torus exactly when its matrix in the fifty-four matrix coordinates is diagonal. The weights of
`V(ϖ₁)` and of `V(ϖ₆)` are distinct, also across the two blocks, and over an infinite field
distinct weights are distinct characters of the split torus, so the torus separates every pair of
basis vectors. The centralizer is therefore the inverse image of the diagonal torus of `GL₅₄`.

This does not identify the diagonal carrier points with the image of the weight torus, so it is
not the statement that the weight torus is its own centralizer, nor its maximality.

## Main results

* `TauCeti.E6DoubledMinuscule.mem_centralizer_range_weightTorusPoints_iff_isDiag`: a carrier
  point centralizes the weight torus exactly when its matrix is diagonal.
* `TauCeti.E6DoubledMinuscule.centralizer_range_weightTorusPoints_eq_comap_diagonalTorus`: the
  centralizer is the inverse image of the diagonal torus.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.TorusCentralizer`, whose character-separation
  argument for the short-root `F₄` weight torus is the source of the general criterion
  `TauCeti.mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL` applied here.
-/

public section

namespace TauCeti.E6DoubledMinuscule

variable {k : Type*} [Field k] [Infinite k]

/-- Over an infinite field, a point of the doubled type-`E₆` minuscule carrier centralizes the
weight torus exactly when its matrix is diagonal. -/
@[simp]
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag (g : points k) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints k)) ↔
      ((g : GL (Fin 54) k) : Matrix (Fin 54) (Fin 54) k).IsDiag :=
  mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL
    (fun s ↦ (coe_weightTorusPoints k s).trans
      (UniversalEnvelopingAlgebra.kostantTorusMatrix_apply _ _ _ s))
    (fun _ _ hij ↦ exists_torusCharacter_ne fun h ↦
      hij (matrixIndexEquiv.symm.injective (DynkinType.e6DoubledMinusculeWeight_injective
        (by rwa [matrixWeight_apply, matrixWeight_apply] at h)))) g

/-- Over an infinite field, the centralizer of the doubled type-`E₆` minuscule weight torus is the
inverse image of the diagonal torus of `GL₅₄`. -/
theorem centralizer_range_weightTorusPoints_eq_comap_diagonalTorus :
    Subgroup.centralizer (Set.range (weightTorusPoints k)) =
      (diagonalTorus k 54).comap (points k).subtype := by
  ext g
  simp only [mem_centralizer_range_weightTorusPoints_iff_isDiag, Subgroup.mem_comap,
    Subgroup.subtype_apply, mem_diagonalTorus_iff]

end TauCeti.E6DoubledMinuscule
