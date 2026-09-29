/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Borel.Geometry
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

/-!
# Conjugacy of Borel subgroups of `SL₂`

Over an algebraically closed field, a reduced connected solvable closed subgroup of `SL₂` acts on
the standard two-dimensional module with an invariant flag. Lie--Kolchin triangularizes its
generic matrix. Rescaling one column of the change-of-basis matrix makes its determinant one
without changing the flag. Thus the subgroup is contained in an `SL₂`-conjugate of the standard
upper-triangular subgroup. Maximality identifies every Borel with such a conjugate.

## Main results

* `TauCeti.SpecialLinear.Borel.exists_conjugate_definingHopfIdeal_le`: containment of a reduced,
  connected, solvable closed subgroup in a conjugate of the standard Borel.
* `TauCeti.SpecialLinear.Borel.isBorelOverAlgClosed_iff_exists_eq_conjugate`: classification of
  Borel subgroups of `SL₂` by conjugacy.
* `TauCeti.SpecialLinear.Borel.exists_conjugate_eq_of_isBorelOverAlgClosed`: geometric conjugacy
  of any two Borel subgroups of `SL₂`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

The proof uses the triangularization of a generic matrix from
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel` and follows the coordinate
conjugation argument for split maximal tori in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Conjugacy`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear.Borel

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every reduced, connected, solvable closed subgroup of `SL₂` is contained in a conjugate of
the standard upper-triangular subgroup. The inequality of Hopf ideals reverses subgroup
containment. -/
theorem exists_conjugate_definingHopfIdeal_le
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k 2))
    [IsReduced (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k 2) I)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k 2) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k 2) I)) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k),
      (definingHopfIdeal k).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k 2) I
  let πS : SpecialLinear.coordinateHopfAlgebra k 2 →ₐc[k] Q :=
    (CommHopfAlgCat.mkQuotient _ I).hom
  let π : GeneralLinear.coordinateHopfAlgebra k 2 →ₐc[k] Q :=
    πS.comp (SpecialLinear.coordinateMap k 2).hom
  obtain ⟨P₀, hP₀⟩ :=
    GeneralLinear.exists_map_inv_mul_mul_map_mem_upperTriangularGroup
      (n := 2) hconn hsolv π
  obtain ⟨P, hdet, hP⟩ := UpperTriangularGroup.exists_det_eq_one_conjugate_mem
    (algebraMap k Q) _ P₀ hP₀
  let s : Matrix.SpecialLinearGroup (Fin 2) k :=
    ⟨P, by rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  let g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k) :=
    (SpecialLinear.pointsMulEquiv (R := k) (A := k) 2).symm s⁻¹
  -- Identify conjugation of the quotient's generic `SL₂` point with ordinary matrix
  -- conjugation by the determinant-one triangularizing matrix.
  have hmatrix : Matrix.SpecialLinearGroup.toGL
      (SpecialLinear.pointsMulEquiv (R := k) (A := Q) 2
        (toConv ((πS : SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] Q).comp
          (HopfAlgebra.pointConjugationAlgHom g)))) =
      (Matrix.GeneralLinearGroup.map (algebraMap k Q) P)⁻¹ *
        GeneralLinear.pointsMulEquiv 2 (toConv (π : _ →ₐ[k] Q)) *
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P := by
    have hπ : Matrix.SpecialLinearGroup.toGL
        (SpecialLinear.pointsMulEquiv (R := k) (A := Q) 2
          (toConv (πS : SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] Q))) =
        GeneralLinear.pointsMulEquiv 2 (toConv (π : _ →ₐ[k] Q)) :=
      (SpecialLinear.pointsMulEquiv_toGL k 2 _).symm
    have hg : Matrix.SpecialLinearGroup.toGL
        (SpecialLinear.pointsMulEquiv (R := k) (A := Q) 2
          (AlgHom.mapValue (H := SpecialLinear.coordinateHopfAlgebra k 2)
            (Algebra.ofId k Q) g)) =
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ := by
      rw [SpecialLinear.pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply,
        map_inv, map_inv, map_inv]
      congr 1
      ext i j
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, Matrix.GeneralLinearGroup.map_apply]
      rfl
    calc
      _ = Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ *
          Matrix.SpecialLinearGroup.toGL
            (SpecialLinear.pointsMulEquiv (R := k) (A := Q) 2
              (toConv (πS : SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] Q))) *
          (Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹)⁻¹ := by
        rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
          map_mul, map_mul, map_inv, hg]
      _ = _ := by rw [hπ, map_inv, inv_inv]
  have hmem : toConv ((πS : SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] Q).comp
      (HopfAlgebra.pointConjugationAlgHom g)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (SpecialLinear.coordinateHopfAlgebra k 2)
        (definingHopfIdeal k) (CommAlgCat.of k Q) := by
    rw [mem_definingPointsSubgroup_iff]
    have htri : Matrix.SpecialLinearGroup.toGL
        (SpecialLinear.pointsMulEquiv (R := k) (A := Q) 2
          (toConv ((πS : SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] Q).comp
            (HopfAlgebra.pointConjugationAlgHom g)))) ∈ upperTriangularGroup (Fin 2) Q := by
      rwa [hmatrix]
    exact SL2Borel.mem_iff.mpr
      (TauCeti.blockTriangular_id_iff.mp (UpperTriangularGroup.mem_iff.mp htri))
  -- Vanishing of the standard Borel ideal on this conjugated generic point gives the
  -- scheme-theoretic containment, rather than only containment on `k`-points.
  have hle : definingHopfIdeal k ≤ I.conjugate g := by
    intro x hx
    rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal,
      ← CommHopfAlgCat.mkQuotient_eq_zero_iff]
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hmem x hx
  exact ⟨g⁻¹, by simpa using HopfIdeal.conjugate_mono g⁻¹ hle⟩

/-- Over an algebraically closed field, the Borel subgroups of `SL₂` are precisely the
conjugates of its standard upper-triangular Borel. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k 2)) :
    HopfIdeal.IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) I ↔
      ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k),
        I = (definingHopfIdeal k).conjugate g := by
  apply HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate _ ?_ ?_ I
  · exact (HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp
      (isBorelOverAlgClosed_definingHopfIdeal (k := k)) |>.2.1
  · intro J hJ
    have hcandidate := ((HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp hJ).2.1
    let _ : IsReduced (CommHopfAlgCat.quotient
        (SpecialLinear.coordinateHopfAlgebra k 2) J) :=
      ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp
        hcandidate.smooth).isReduced
    exact exists_conjugate_definingHopfIdeal_le J
      hcandidate.geometricallyConnected hcandidate.geometricallySolvable

/-- Any two Borel subgroups of `SL₂` over an algebraically closed field are conjugate by an
`SL₂`-point. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed
    {I J : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k 2)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) I)
    (hJ : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) J) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] k),
      I.conjugate g = J := by
  apply HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed
    (definingHopfIdeal k) ?_ ?_ hI hJ
  · exact (HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp
      (isBorelOverAlgClosed_definingHopfIdeal (k := k)) |>.2.1
  · intro K hK
    obtain ⟨g, hg⟩ := (isBorelOverAlgClosed_iff_exists_eq_conjugate K).mp hK
    exact ⟨g, le_of_eq hg.symm⟩

end

end TauCeti.SpecialLinear.Borel
