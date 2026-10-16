/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The centralizer of the type-B spin weight torus

Over an infinite field, a point of the integral type-`Bₙ₊₁` spin carrier centralizes its
weight torus exactly when its spin matrix is diagonal. The spin weights are distinct, so
characters separate every pair of exterior-basis vectors, including in characteristic two.
The centralizer is therefore the intersection of the carrier with the ambient diagonal torus.
This subgroup of diagonal carrier points is self-centralizing, hence maximal among commutative
subgroups of the point group.

This is the matrix reduction needed to identify the carrier's torus centralizer. It does not
identify the diagonal carrier points with the weight-torus image, prove maximality of that
image, or identify the carrier with an independently pinned simply connected group scheme.

## Main declarations

* `TauCeti.TypeBSpinCarrier.diagonalPoints`: the diagonal points of the spin carrier.
* `TauCeti.TypeBSpinCarrier.centralizer_range_weightTorusPoints_eq_diagonalPoints`: over an
  infinite field, the weight-torus centralizer is the subgroup of diagonal carrier points.
* `TauCeti.TypeBSpinCarrier.centralizer_diagonalPoints_eq_diagonalPoints`: over an infinite field,
  the diagonal carrier points are self-centralizing.
* `TauCeti.TypeBSpinCarrier.eq_diagonalPoints_of_le_of_isMulCommutative`: no commutative subgroup
  properly contains all diagonal carrier points.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* The character-separation argument follows
  `TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.TorusCentralizer`. Unlike that representation,
  the spin representation has no repeated weights.
* The diagonal-point API follows
  `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.TorusCentralizer`.
-/

public section

open Matrix

namespace TauCeti.TypeBSpinCarrier

universe u

noncomputable section

variable (n : ℕ) {A : Type u} [CommRing A] [IsLeftCancelMulZero A]

/-! ## Diagonal carrier points -/

/-- The subgroup of type-`Bₙ₊₁` spin-carrier points whose ambient matrices are diagonal. -/
def diagonalPoints (K : Type u) [CommRing K] : Subgroup (points n K) :=
  (diagonalTorus K (dimension n)).comap (points n K).subtype

/-- A spin-carrier point belongs to `diagonalPoints` exactly when its ambient matrix is diagonal. -/
@[simp]
theorem mem_diagonalPoints_iff {K : Type u} [CommRing K] {g : points n K} :
    g ∈ diagonalPoints n K ↔ g.1.1.IsDiag := by
  rw [diagonalPoints, Subgroup.mem_comap, mem_diagonalTorus_iff]
  rfl

/-- Every point of the spin weight torus is diagonal in the ambient general linear group. -/
theorem coe_weightTorusPoints_mem_diagonalTorus (K : Type u) [CommRing K]
    (s : Fin (n + 1) → Kˣ) :
    (weightTorusPoints n K s : GL (Fin (dimension n)) K) ∈
      diagonalTorus K (dimension n) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
  exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩

/-- The spin weight torus is contained in the subgroup of diagonal carrier points. -/
theorem range_weightTorusPoints_le_diagonalPoints (K : Type u) [CommRing K] :
    (weightTorusPoints n K).range ≤ diagonalPoints n K := by
  rintro _ ⟨s, rfl⟩
  rw [diagonalPoints, Subgroup.mem_comap]
  exact coe_weightTorusPoints_mem_diagonalTorus n K s

/-- The diagonal carrier points form a commutative group. -/
instance instIsMulCommutativeDiagonalPoints (K : Type u) [CommRing K] :
    IsMulCommutative (diagonalPoints n K) :=
  (diagonalTorus K (dimension n)).comap_injective_isMulCommutative
    (points n K).subtype_injective

/-! ## The centralizer -/

/-- If the spin weights define distinct characters on torus points, a carrier point
centralizes the weight torus exactly when its spin matrix is diagonal. -/
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_basisWeight_injective
    (hchar : Function.Injective fun i : Fin (dimension n) ↦ weightChar A (basisWeight n i))
    (g : points n A) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints n A)) ↔
      ((g : GL (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A).IsDiag := by
  constructor
  · intro hg i j hij
    obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp (hchar.ne hij)
    simp only [weightChar_apply] at hs
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (weightTorusPoints n A s) ⟨s, rfl⟩
    have hmatrix := congrArg (fun x : points n A ↦
      ((x : GL (Fin (dimension n)) A) : Matrix (Fin (dimension n)) (Fin (dimension n)) A)) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe] at hmatrix
    exact apply_eq_zero_of_commute_diagonal hmatrix (fun h ↦ hs (Units.ext h))
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    rintro d ⟨s, rfl⟩
    apply (points n A).subtype_injective
    apply Units.ext
    simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    rw [← hg.diagonal_diag]
    exact (Matrix.commute_diagonal _ _).eq

/-- If the spin weight characters remain distinct over a ring without zero divisors, the
centralizer of the weight torus is exactly the diagonal carrier subgroup, the inverse image of
the ambient diagonal torus under the carrier inclusion. -/
theorem centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective
    (hchar : Function.Injective fun i : Fin (dimension n) ↦ weightChar A (basisWeight n i)) :
    Subgroup.centralizer (Set.range (weightTorusPoints n A)) = diagonalPoints n A := by
  ext g
  rw [mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_basisWeight_injective
    n hchar, mem_diagonalPoints_iff]

/-- If the spin weight characters remain distinct over a ring without zero divisors, the diagonal
spin-carrier points are self-centralizing. -/
theorem centralizer_diagonalPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective
    (hchar : Function.Injective fun i : Fin (dimension n) ↦ weightChar A (basisWeight n i)) :
    Subgroup.centralizer (diagonalPoints n A : Set (points n A)) = diagonalPoints n A := by
  apply le_antisymm
  · calc
      Subgroup.centralizer (diagonalPoints n A : Set (points n A)) ≤
          Subgroup.centralizer (Set.range (weightTorusPoints n A)) :=
        Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr (range_weightTorusPoints_le_diagonalPoints n A))
      _ = diagonalPoints n A :=
        centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective
          n hchar
  · exact Subgroup.le_centralizer _

/-- If the spin weight characters remain distinct over a ring without zero divisors, no
commutative subgroup of the spin carrier properly contains all diagonal carrier points. -/
theorem eq_diagonalPoints_of_weightChar_basisWeight_injective_of_le_of_isMulCommutative
    (hchar : Function.Injective fun i : Fin (dimension n) ↦ weightChar A (basisWeight n i))
    (H : Subgroup (points n A)) [IsMulCommutative H] (hH : diagonalPoints n A ≤ H) :
    H = diagonalPoints n A :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    (centralizer_diagonalPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective n hchar) hH

variable {k : Type u} [Field k] [Infinite k]

/-- Over an infinite field, distinct spin-basis indices have distinct weight characters. -/
theorem weightChar_comp_basisWeight_injective :
    Function.Injective (weightChar k ∘ basisWeight n) := by
  intro i j h
  exact (Fintype.equivFin (Finset (Fin (n + 1)))).symm.injective
    (DynkinType.typeBSpinWeight_injective (weightChar_injective h))

/-- Over an infinite field in any characteristic, the spin weight-torus centralizer consists
exactly of the carrier points whose spin matrices are diagonal. -/
@[simp]
theorem mem_centralizer_range_weightTorusPoints_iff_isDiag (g : points n k) :
    g ∈ Subgroup.centralizer (Set.range (weightTorusPoints n k)) ↔
      ((g : GL (Fin (dimension n)) k) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) k).IsDiag := by
  exact mem_centralizer_range_weightTorusPoints_iff_isDiag_of_weightChar_basisWeight_injective n
    (weightChar_comp_basisWeight_injective n) g

/-- Over an infinite field, the weight-torus centralizer is the diagonal carrier subgroup, the
inverse image of the ambient diagonal torus under the carrier's matrix inclusion. This is not an
assertion that the weight torus is its own centralizer. -/
theorem centralizer_range_weightTorusPoints_eq_diagonalPoints :
    Subgroup.centralizer (Set.range (weightTorusPoints n k)) = diagonalPoints n k :=
  centralizer_range_weightTorusPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective n
    (weightChar_comp_basisWeight_injective n)

/-- Over an infinite field, the diagonal spin-carrier points are self-centralizing. -/
theorem centralizer_diagonalPoints_eq_diagonalPoints :
    Subgroup.centralizer (diagonalPoints n k : Set (points n k)) = diagonalPoints n k :=
  centralizer_diagonalPoints_eq_diagonalPoints_of_weightChar_basisWeight_injective n
    (weightChar_comp_basisWeight_injective n)

/-- Over an infinite field, no commutative subgroup of the spin carrier properly contains all
diagonal carrier points. -/
theorem eq_diagonalPoints_of_le_of_isMulCommutative (H : Subgroup (points n k))
    [IsMulCommutative H] (hH : diagonalPoints n k ≤ H) : H = diagonalPoints n k :=
  eq_diagonalPoints_of_weightChar_basisWeight_injective_of_le_of_isMulCommutative n
    (weightChar_comp_basisWeight_injective n) H hH

end

end TauCeti.TypeBSpinCarrier
