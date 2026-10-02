/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Connected
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel

/-!
# Borel subgroups of `SLₙ`

Over an algebraically closed field, every reduced, connected, solvable closed subgroup of `SLₙ`
is contained in a conjugate, by a rational point of `SLₙ`, of the upper-triangular subgroup. In
Hopf coordinates containment of closed subgroups is reversed, so the conclusion reads
`(definingHopfIdeal k n).conjugate g ≤ I`.

The proof views the subgroup inside `GLₙ`, where the Lie--Kolchin argument
`TauCeti.GeneralLinear.exists_map_inv_mul_mul_map_mem_upperTriangularGroup` supplies a rational
matrix `P` triangularizing the generic point of the subgroup. Rescaling one column of `P` by the
inverse of its determinant keeps it triangularizing and makes it a rational point of `SLₙ`.

The upper-triangular subgroup is smooth, geometrically connected, and has solvable geometric
points, so it is a Borel candidate. Combined with the containment above, it is a Borel subgroup,
the Borel subgroups of `SLₙ` over an algebraically closed field are exactly its conjugates, and
any two of them are conjugate. Its defining ideal commutes with base change, so it is a Borel
subgroup over every field.

## Main declarations

* `TauCeti.SpecialLinear.UpperTriangular.exists_conjugate_definingHopfIdeal_le`: a reduced,
  connected, solvable closed subgroup of `SLₙ` is contained in a conjugate of the
  upper-triangular subgroup.
* `TauCeti.SpecialLinear.UpperTriangular.isBorelCandidate_definingHopfIdeal`: the
  upper-triangular subgroup is smooth, geometrically connected, and geometrically solvable.
* `TauCeti.SpecialLinear.UpperTriangular.isBorelOverAlgClosed_iff_exists_eq_conjugate`: over an
  algebraically closed field, the Borel subgroups of `SLₙ` are exactly the conjugates of the
  upper-triangular subgroup.
* `TauCeti.SpecialLinear.UpperTriangular.exists_conjugate_eq_of_isBorelOverAlgClosed`: any two
  Borel subgroups of `SLₙ` over an algebraically closed field are conjugate.
* `TauCeti.SpecialLinear.UpperTriangular.map_baseChangeHopfIdeal_definingHopfIdeal`: the
  upper-triangular ideal commutes with base change.
* `TauCeti.SpecialLinear.UpperTriangular.isBorel_definingHopfIdeal`: the upper-triangular
  subgroup is a Borel subgroup of `SLₙ` over every field.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Corollary 10.5 and Theorem 11.1.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30 and Section 17.a.
* The argument follows the general-linear case in
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Borel`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear.UpperTriangular

open scoped TensorProduct

universe u v

noncomputable section

section Triangularization

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

end Triangularization

section Borel

variable (k : Type u) [Field k] (n : ℕ)

/-- The upper-triangular subgroup of `SLₙ` is a Borel candidate over every field: it is smooth,
geometrically connected, and geometrically solvable. -/
theorem isBorelCandidate_definingHopfIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n))
      (definingHopfIdeal k n) :=
  HopfIdeal.IsBorelCandidate.mk (smoothCommHopfAlgProperty_coordinateHopfAlgebra n k)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra n k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra n k)

variable {k n}

/-- Over an algebraically closed field, every Borel subgroup of `SLₙ` is contained in a
conjugate of the upper-triangular subgroup. -/
private theorem exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed [IsAlgClosed k]
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k n))
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n)) I) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k),
      (definingHopfIdeal k n).conjugate g ≤ I := by
  have hIcandidate := ((HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp hI).2.prop
  let _ : IsReduced (CommHopfAlgCat.quotient (SpecialLinear.coordinateHopfAlgebra k n) I) :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp hIcandidate.smooth).isReduced
  exact exists_conjugate_definingHopfIdeal_le I hIcandidate.geometricallyConnected
    hIcandidate.geometricallySolvable

variable (k n) in
/-- **The upper-triangular subgroup of `SLₙ` is a Borel subgroup over an algebraically closed
field**: it is maximal among smooth, connected, solvable closed subgroups. -/
theorem isBorelOverAlgClosed_definingHopfIdeal [IsAlgClosed k] :
    HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n))
      (definingHopfIdeal k n) :=
  HopfIdeal.isBorelOverAlgClosed_of_forall_exists_conjugate_le _
    (isBorelCandidate_definingHopfIdeal k n)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed

/-- **The Borel subgroups of `SLₙ` over an algebraically closed field are exactly the conjugates
of the upper-triangular subgroup.** The equality is an equality of defining Hopf ideals, hence of
closed subgroup schemes, rather than only of their rational points. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate [IsAlgClosed k]
    (I : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k n)) :
    HopfIdeal.IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n)) I ↔
      ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k),
        I = (definingHopfIdeal k n).conjugate g :=
  HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate _
    (isBorelCandidate_definingHopfIdeal k n)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed I

/-- **Any two Borel subgroups of `SLₙ` over an algebraically closed field are conjugate** by a
rational point of `SLₙ`. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed [IsAlgClosed k]
    {I J : HopfIdeal k (SpecialLinear.coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n)) I)
    (hJ : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n)) J) :
    ∃ g : WithConv (SpecialLinear.coordinateHopfAlgebra k n →ₐ[k] k), I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed _
    (isBorelCandidate_definingHopfIdeal k n)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed hI hJ

end Borel

section BaseChange

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ)

/-- The special-linear base-change isomorphism carries the scalar extension of the
upper-triangular defining ideal to the upper-triangular defining ideal over the new base. -/
@[simp]
theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R n)).map
        (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom =
      definingHopfIdeal K n := by
  -- The special-linear base-change isomorphism is induced by the general-linear one.
  have hcoord (x : GeneralLinear.coordinateHopfAlgebra R n) :
      (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
          (1 ⊗ₜ[R] (SpecialLinear.coordinateMap R n).hom x) =
        (SpecialLinear.coordinateMap K n).hom
          ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom (1 ⊗ₜ[R] x)) := by
    have h := congrArg (fun f ↦ f.hom (1 ⊗ₜ[R] x))
      (SpecialLinear.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom
        R K n)
    rwa [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
      CommHopfAlgCat.baseChangeMap_apply_tmul] at h
  -- The general-linear base-change isomorphism matches the matrix coordinates.
  have hentry (i j : Fin n) :
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
          (1 ⊗ₜ[R] GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
            (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
        GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j))) := by
    simpa using GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v}
      R K n 1 (MvPolynomial.X (i, j))
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R n) (definingHopfIdeal K n)
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (definingHopfIdeal_toIdeal R n) (definingHopfIdeal_toIdeal K n) ?_
  rw [Set.image_image]
  ext x
  simp only [Set.mem_image, hcoord, GeneralLinear.UpperTriangular.mem_definingRelationSet_iff]
  constructor
  · rintro ⟨y, ⟨i, j, hji, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, j, hji, rfl⟩, by rw [hentry]⟩
  · rintro ⟨y, ⟨i, j, hji, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, j, hji, rfl⟩, by rw [hentry]⟩

end BaseChange

variable (k : Type u) [Field k] (n : ℕ) in
/-- **The upper-triangular subgroup of `SLₙ` is a Borel subgroup over every field.** Its base
change to an algebraic closure is smooth, connected, solvable, and maximal among closed
subgroups with those properties. -/
theorem isBorel_definingHopfIdeal :
    HopfIdeal.IsBorel k (SpecialLinear.coordinateHopfAlgebra k n) (definingHopfIdeal k n) := by
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    (FiniteTypeCommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k n))
  let L := FiniteTypeCommHopfAlgCat.of K (SpecialLinear.coordinateHopfAlgebra K n)
  let e : H' ≅ L := ObjectProperty.isoMk _
    (SpecialLinear.coordinateHopfAlgebraBaseChangeIso k K n)
  have hpull := HopfIdeal.IsBorelOverAlgClosed.of_map_eq e
    (map_baseChangeHopfIdeal_definingHopfIdeal k K n)
    (isBorelOverAlgClosed_definingHopfIdeal K n)
  exact (HopfIdeal.isBorel_iff_isBorelOverAlgClosed_baseChange
    k (SpecialLinear.coordinateHopfAlgebra k n) (definingHopfIdeal k n)).2 hpull

end

end TauCeti.SpecialLinear.UpperTriangular
