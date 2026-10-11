/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors
public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Diagonal
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The centralizer of the short-root G₂ weight torus

The diagonal points of the prime-field short-root carrier are exactly its weight-torus
points, over every commutative `𝔽₃`-algebra. Over an infinite field, this
torus is its own centralizer in the carrier's point group. Consequently no larger
commutative subgroup of points contains it.

The seven distinct weights force a commuting matrix to be diagonal; preservation of
the cross product then restricts its diagonal to the rank-two weight torus. The pointwise
centralizer calculation is the input for maximality of the torus as a closed subgroup
scheme. No identification with a pinned simply connected group is asserted here.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §16.1 and §26.3.
* The point-group argument follows
  `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Centralizer`.
* Tensor invariance comes from
  `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors`.
* Character separation uses `TauCeti.weightChar_injective` from
  `TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic`.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot.PrimeField

universe v

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

/-- A point of the short-root carrier lies in the weight torus exactly when its matrix
is diagonal. This characterization also holds over nonreduced value algebras. -/
@[simp]
theorem exists_weightTorusPoints_eq_iff_isDiag (g : points A) :
    (∃ s, weightTorusPoints A s = g) ↔
      ((g : GL (Fin 7) A) : Matrix (Fin 7) (Fin 7) A).IsDiag := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [coe_weightTorusPoints, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal]
    exact isDiag_diagonal _
  · intro hg
    obtain ⟨d, hd⟩ := mem_diagonalTorus_iff_exists_diagGL.mp
      (mem_diagonalTorus_iff.mpr hg)
    have hcross := preservesG2Cross_of_mem_points g.property
    rw [← hd, diagGL_coe] at hcross
    have h2 : IsUnit (2 : A) := by
      have h : IsUnit ((algebraMap (ZMod 3) A) 2) :=
        ((ZMod.isUnit_iff_coprime 2 3).mpr (by decide)).map
          (algebraMap (ZMod 3) A).toMonoidHom
      rwa [map_ofNat] at h
    obtain ⟨s, hs⟩ := (preservesG2Cross_diagonal_iff h2.isRegular d).mp hcross
    refine ⟨s, Subtype.ext (Units.ext ?_)⟩
    rw [coe_weightTorusPoints, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
      ← hd, diagGL_coe]
    simp_rw [hs]

variable {k : Type v} [Field k] [Algebra (ZMod 3) k] [Infinite k]

/-- Over an infinite field of characteristic three, the weight torus is
its own centralizer in the short-root carrier's point group. -/
theorem centralizer_range_weightTorusPoints :
    Subgroup.centralizer ((weightTorusPoints k).range : Set (points k)) =
      (weightTorusPoints k).range := by
  refine le_antisymm (fun g hg => ?_) (Subgroup.le_centralizer _)
  rw [MonoidHom.mem_range, exists_weightTorusPoints_eq_iff_isDiag]
  intro i j hij
  have hne : weightChar k (weight i) ≠ weightChar k (weight j) :=
    (weightChar_injective.comp weight_injective).ne hij
  obtain ⟨s, hs⟩ := DFunLike.ne_iff.mp hne
  simp only [weightChar_apply] at hs
  have hcomm := Subgroup.mem_centralizer_iff.mp hg (weightTorusPoints k s)
    ⟨s, rfl⟩
  have hm := congrArg (fun g : points k =>
    ((g : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k)) hcomm
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal] at hm
  exact apply_eq_zero_of_commute_diagonal hm (fun h => hs (Units.ext h))

/-- No commutative subgroup of short-root carrier points over an infinite field
properly contains the weight torus. -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative
    (H : Subgroup (points k)) [IsMulCommutative H]
    (hH : (weightTorusPoints k).range ≤ H) : H = (weightTorusPoints k).range :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    centralizer_range_weightTorusPoints hH

end TauCeti.G2ShortRoot.PrimeField
