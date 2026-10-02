/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel

/-!
# Triangularizing connected solvable subgroups of `SLₙ`

Over an algebraically closed field, every reduced, connected, solvable closed subgroup of `SLₙ`
is contained in a conjugate, by a rational point of `SLₙ`, of the upper-triangular subgroup. In
Hopf coordinates containment of closed subgroups is reversed, so the conclusion reads
`(definingHopfIdeal k n).conjugate g ≤ I`.

The proof views the subgroup inside `GLₙ`, where the Lie--Kolchin argument
`TauCeti.GeneralLinear.exists_map_inv_mul_mul_map_mem_upperTriangularGroup` supplies a rational
matrix `P` triangularizing the generic point of the subgroup. Rescaling one column of `P` by the
inverse of its determinant keeps it triangularizing and makes it a rational point of `SLₙ`.

This is the conjugacy input for classifying the Borel subgroups of `SLₙ`; the upper-triangular
subgroup is smooth with solvable geometric points by
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Basic`.

## Main declaration

* `TauCeti.SpecialLinear.UpperTriangular.exists_conjugate_definingHopfIdeal_le`: a reduced,
  connected, solvable closed subgroup of `SLₙ` is contained in a conjugate of the
  upper-triangular subgroup.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Corollary 10.5 and Theorem 11.1.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30 and Section 17.a.
* The argument generalizes the rank-two case in
  `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Borel.Conjugacy`, and follows the general-linear
  case `TauCeti.GeneralLinear.UpperTriangular.exists_conjugate_definingHopfIdeal_le`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear.UpperTriangular

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- **Every reduced, connected, solvable closed subgroup of `SLₙ` is contained in a conjugate of
the upper-triangular subgroup**, over an algebraically closed field. The inequality of Hopf
ideals reverses subgroup containment. -/
theorem exists_conjugate_definingHopfIdeal_le
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k n))
    [IsReduced (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k n) I)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k n) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k n) I)) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k),
      (definingHopfIdeal k n).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k n) I
  let πS : SpecialLinear.coordinateHopfAlgebra k n →ₐc[k] Q :=
    (CommHopfAlgCat.mkQuotient _ I).hom
  let π : GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] Q :=
    πS.comp (SpecialLinear.coordinateMap k n).hom
  obtain ⟨P₀, hP₀⟩ :=
    GeneralLinear.exists_map_inv_mul_mul_map_mem_upperTriangularGroup hconn hsolv π
  obtain ⟨P, hdet, hP⟩ := UpperTriangularGroup.exists_det_eq_one_map_inv_mul_mul_map_mem
    (algebraMap k Q) _ P₀ hP₀
  let g : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k) :=
    (SpecialLinear.pointsMulEquiv (R := k) (A := k) n).symm
      (Matrix.SpecialLinearGroup.toGLKerEquiv.symm ⟨P, hdet⟩)⁻¹
  -- Conjugating the quotient's generic `SLₙ` point by `g` is ordinary matrix conjugation by the
  -- determinant-one triangularizing matrix `P`.
  have hmatrix : Matrix.SpecialLinearGroup.toGL
      (SpecialLinear.pointsMulEquiv (R := k) (A := Q) n
        (toConv ((πS : SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] Q).comp
          (HopfAlgebra.pointConjugationAlgHom g)))) =
      (Matrix.GeneralLinearGroup.map (algebraMap k Q) P)⁻¹ *
        GeneralLinear.pointsMulEquiv n (toConv (π : _ →ₐ[k] Q)) *
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P := by
    simpa only [g, π, BialgHom.comp_toAlgHom] using
      SpecialLinear.pointsMulEquiv_comp_pointConjugationAlgHom_symm_toGLKerEquiv_symm
        (R := k) (n := n) P hdet
        (πS : SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] Q)
  have hmem : toConv ((πS : SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] Q).comp
      (HopfAlgebra.pointConjugationAlgHom g)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (SpecialLinear.coordinateHopfAlgebra k n)
        (definingHopfIdeal k n) (CommAlgCat.of k Q) := by
    rw [mem_definingPointsSubgroup_iff, hmatrix]
    exact hP
  -- Vanishing of the upper-triangular ideal on this conjugated generic point gives the
  -- scheme-theoretic containment, rather than only containment on `k`-points.
  exact ⟨g⁻¹, HopfIdeal.conjugate_inv_le_of_mem_quotientPointsSubgroup_mkQuotient
    I (definingHopfIdeal k n) g hmem⟩

end

end TauCeti.SpecialLinear.UpperTriangular
