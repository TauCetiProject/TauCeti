/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Borel subgroups of `GLₙ`

Over an algebraically closed field `k`, every smooth (indeed every reduced), connected, solvable
closed subgroup of `GLₙ` is conjugate, by a rational point, into the upper-triangular subgroup.
In Hopf coordinates containment of closed subgroups is reversed, so the conclusion reads
`(UpperTriangular.definingHopfIdeal k n).conjugate g ≤ I`.

The proof restricts the standard representation of `GLₙ` to the subgroup and applies the
Lie--Kolchin theorem: the restricted comodule has a basis `b` in which its coefficient matrix `C`
is upper triangular. If `P` is the matrix with columns `bⱼ` and `M` is the generic point of the
subgroup, the change of basis formula for the action of `M` on `kⁿ` reads `P⁻¹ M P = C`. Hence
conjugating the generic point by `P⁻¹` lands in the upper-triangular subgroup, which is the
inclusion of closed subgroups to be proved.

Since the upper-triangular subgroup is itself smooth, connected, and solvable, the generic
conjugacy results for Borel subgroups then show that it is a Borel subgroup, that the Borel
subgroups of `GLₙ` over an algebraically closed field are exactly its conjugates, and that any
two of them are conjugate. Base change to an algebraic closure shows that the upper-triangular
subgroup is a Borel subgroup of `GLₙ` over every field.

## Main declarations

* `TauCeti.GeneralLinear.exists_map_inv_mul_mul_map_mem_upperTriangularGroup`: a point of `GLₙ`
  with values in the coordinate algebra of a reduced connected solvable group is triangularized
  by a rational matrix.
* `TauCeti.GeneralLinear.UpperTriangular.exists_conjugate_definingHopfIdeal_le`: a reduced,
  connected, solvable closed subgroup of `GLₙ` is contained in a conjugate of the
  upper-triangular subgroup.
* `TauCeti.GeneralLinear.UpperTriangular.isBorelOverAlgClosed_definingHopfIdeal` and
  `TauCeti.GeneralLinear.UpperTriangular.isBorel_definingHopfIdeal`: the upper-triangular
  subgroup is a Borel subgroup of `GLₙ`, over an algebraically closed field and over every field.
* `TauCeti.GeneralLinear.UpperTriangular.isBorelOverAlgClosed_iff_exists_eq_conjugate`: over an
  algebraically closed field, the Borel subgroups of `GLₙ` are exactly the conjugates of the
  upper-triangular subgroup.
* `TauCeti.GeneralLinear.UpperTriangular.exists_conjugate_eq_of_isBorelOverAlgClosed`: any two
  Borel subgroups of `GLₙ` over an algebraically closed field are conjugate.
* `TauCeti.GeneralLinear.UpperTriangular.map_baseChangeHopfIdeal_definingHopfIdeal`: scalar
  extension preserves the upper-triangular defining ideal under the coordinate isomorphism.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Corollary 10.5 and Theorem 11.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 17.6 and 21.3.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30 and Section 17.a.
* `TauCeti/Algebra/AlgebraicGroup/GeneralLinear/DiagonalTorus/Conjugacy.lean`, for the
  analogous Hopf-coordinate proof of conjugacy in `GLₙ`.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}

attribute [local instance] standardComodule

/-- **Lie--Kolchin for `GLₙ`-valued points.**

Let `Q` be the coordinate algebra of a reduced, geometrically connected, geometrically solvable
affine group of finite type over an algebraically closed field `k`. For every bialgebra morphism
`π : O(GLₙ) → Q` some rational matrix `P` triangularizes the `Q`-valued point `π`: the matrix
`P⁻¹ π P` is upper triangular. The columns of `P` form a Lie--Kolchin basis of the standard
comodule corestricted along `π`. -/
theorem exists_map_inv_mul_mul_map_mem_upperTriangularGroup [IsAlgClosed k]
    {Q : Type v} [CommRing Q] [HopfAlgebra k Q] [Algebra.FiniteType k Q] [IsReduced Q]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (π : coordinateHopfAlgebra k n →ₐc[k] Q) :
    ∃ P : GL (Fin n) k,
      Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ *
          pointsMulEquiv n (toConv (π : coordinateHopfAlgebra k n →ₐ[k] Q)) *
          Matrix.GeneralLinearGroup.map (algebraMap k Q) P ∈
        upperTriangularGroup (Fin n) Q := by
  let _ : Comodule k Q (Fin n → k) :=
    Comodule.Corestrict (π : coordinateHopfAlgebra k n →ₗc[k] Q)
  obtain ⟨m, b, hb, -⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (H := Q) (M := Fin n → k) hconn hsolv
  obtain rfl : m = n := by simpa using (Module.finrank_eq_card_basis b).symm
  let e := Pi.basisFun k (Fin m)
  let _ := e.invertibleToMatrix b
  refine ⟨unitOfInvertible (e.toMatrix b), ?_⟩
  -- The universal `Q`-point acts on `Q ⊗ kᵐ` by the generic matrix `π(X)` in the standard basis
  -- and by the coefficient matrix of `b` in the basis `b`; compare the two by change of basis.
  let f := Comodule.endOfPoint (Fin m → k) (AlgHom.id k Q)
  have he : LinearMap.toMatrix (e.baseChange Q) (e.baseChange Q) f =
      (genericMatrix k m).map π := by
    rw [Comodule.toMatrix_endOfPoint, Comodule.coefficientMatrix_corestrict,
      coefficientMatrix_basisFun]
    ext i j
    simp
  have hbasis := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (b.baseChange Q) (e.baseChange Q) (b.baseChange Q) (e.baseChange Q) f
  rw [he, Comodule.toMatrix_endOfPoint, Module.Basis.baseChange_toMatrix_baseChange,
    Module.Basis.baseChange_toMatrix_baseChange] at hbasis
  have hinv : (e.toMatrix b)⁻¹ = b.toMatrix e :=
    Matrix.inv_eq_left_inv (b.toMatrix_mul_toMatrix_flip e)
  have hmap (g : GL (Fin m) k) :
      ((Matrix.GeneralLinearGroup.map (algebraMap k Q) g : GL (Fin m) Q) :
        Matrix (Fin m) (Fin m) Q) = (g : Matrix (Fin m) (Fin m) k).map (algebraMap k Q) := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply _ i j g
  have hpoint : ((pointsMulEquiv m (toConv (π : coordinateHopfAlgebra k m →ₐ[k] Q)) :
      GL (Fin m) Q) : Matrix (Fin m) (Fin m) Q) = (genericMatrix k m).map π := by
    ext i j
    simp [pointsMulEquiv_apply, pointToGeneralLinear_apply, genericMatrix_apply]
  rw [UpperTriangularGroup.mem_iff, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, hmap, hmap, hpoint, Matrix.GeneralLinearGroup.coe_inv,
    val_unitOfInvertible, hinv, hbasis]
  simpa using hb

namespace UpperTriangular

/-- **A reduced connected solvable closed subgroup of `GLₙ` is conjugate into the
upper-triangular subgroup.**

Over an algebraically closed field, if the quotient coordinate Hopf algebra of `I` is reduced,
geometrically connected, and geometrically solvable, then some rational point `g` conjugates the
upper-triangular subgroup to a closed subgroup containing the one cut out by `I`. Containment of
closed subgroups is the reversed inequality of Hopf ideals. -/
theorem exists_conjugate_definingHopfIdeal_le [IsAlgClosed k]
    (I : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k n))
    [IsReduced (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k n) I)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k n) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k n) I)) :
    ∃ g : WithConv (GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k),
      (definingHopfIdeal k n).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k n) I
  let π : GeneralLinear.coordinateHopfAlgebra k n →ₐc[k] Q :=
    (CommHopfAlgCat.mkQuotient _ I).hom
  obtain ⟨P, hP⟩ := exists_map_inv_mul_mul_map_mem_upperTriangularGroup hconn hsolv π
  let g : WithConv (GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k) :=
    (GeneralLinear.pointsMulEquiv (R := k) (A := k) n).symm P⁻¹
  have hkey : GeneralLinear.pointsMulEquiv n
      (toConv ((π : GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] Q).comp
        (HopfAlgebra.pointConjugationAlgHom g))) =
      Matrix.GeneralLinearGroup.map (algebraMap k Q) P⁻¹ *
        GeneralLinear.pointsMulEquiv n
          (toConv (π : GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] Q)) *
        Matrix.GeneralLinearGroup.map (algebraMap k Q) P := by
    rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
      GeneralLinear.pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, map_inv, inv_inv,
      map_inv, Algebra.toRingHom_ofId]
  have hle : definingHopfIdeal k n ≤ I.conjugate g := by
    intro x hx
    rw [HopfIdeal.mem_conjugate, ← HopfIdeal.mem_toIdeal,
      ← CommHopfAlgCat.mkQuotient_eq_zero_iff]
    refine definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular k n
      ((π : GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] Q).comp
        (HopfAlgebra.pointConjugationAlgHom g)) ?_ hx
    rw [← GeneralLinear.pointsMulEquiv_apply, hkey]
    exact UpperTriangularGroup.mem_iff.mp hP
  refine ⟨g⁻¹, ?_⟩
  simpa using HopfIdeal.conjugate_mono g⁻¹ hle

variable (k n)

/-- The upper-triangular subgroup of `GLₙ` is a Borel candidate over every field: it is smooth,
geometrically connected, and geometrically solvable. -/
theorem isBorelCandidate_definingHopfIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n))
      (definingHopfIdeal k n) :=
  HopfIdeal.IsBorelCandidate.mk (smoothCommHopfAlgProperty_coordinateHopfAlgebra n k)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra n k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k n)

variable {k n}

/-- Over an algebraically closed field, every Borel subgroup of `GLₙ` is contained in a
conjugate of the upper-triangular subgroup. -/
private theorem exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed [IsAlgClosed k]
    (I : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k n))
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n)) I) :
    ∃ g : WithConv (GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k),
      (definingHopfIdeal k n).conjugate g ≤ I := by
  have hIcandidate := ((HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp hI).2.prop
  let _ : IsReduced (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra k n) I) :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp hIcandidate.smooth).isReduced
  exact exists_conjugate_definingHopfIdeal_le I hIcandidate.geometricallyConnected
    hIcandidate.geometricallySolvable

variable (k n) in
/-- **The upper-triangular subgroup of `GLₙ` is a Borel subgroup over an algebraically closed
field**: it is maximal among smooth, connected, solvable closed subgroups. -/
theorem isBorelOverAlgClosed_definingHopfIdeal [IsAlgClosed k] :
    HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n))
      (definingHopfIdeal k n) :=
  HopfIdeal.isBorelOverAlgClosed_of_forall_exists_conjugate_le _
    (isBorelCandidate_definingHopfIdeal k n)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed

/-- **The Borel subgroups of `GLₙ` over an algebraically closed field are exactly the conjugates
of the upper-triangular subgroup.** The equality is an equality of defining Hopf ideals, hence of
closed subgroup schemes, rather than only of their rational points. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate [IsAlgClosed k]
    (I : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k n)) :
    HopfIdeal.IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n)) I ↔
      ∃ g : WithConv (GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k),
        I = (definingHopfIdeal k n).conjugate g :=
  HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate _
    (isBorelCandidate_definingHopfIdeal k n)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed I

/-- **Any two Borel subgroups of `GLₙ` over an algebraically closed field are conjugate** by a
rational point of `GLₙ`. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed [IsAlgClosed k]
    {I J : HopfIdeal k (GeneralLinear.coordinateHopfAlgebra k n)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n)) I)
    (hJ : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n)) J) :
    ∃ g : WithConv (GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] k), I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed _
    (isBorelCandidate_definingHopfIdeal k n)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed hI hJ

/-- The general-linear base-change isomorphism carries the scalar extension of the
upper-triangular defining ideal to the upper-triangular defining ideal over the new field. -/
theorem map_baseChangeHopfIdeal_definingHopfIdeal
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal k n)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K n).hom.hom =
      definingHopfIdeal K n := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal k n) (definingHopfIdeal K n)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K n)
    (definingHopfIdeal_toIdeal k n) (definingHopfIdeal_toIdeal K n) ?_
  have hentry (i j : Fin n) :
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K n).hom.hom
          (1 ⊗ₜ[k] GeneralLinear.coordinateHopfAlgebraAlgEquiv k n
            (GeneralLinear.coordinateRingMap k n (MvPolynomial.X (i, j)))) =
        GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j))) := by
    simpa using GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, u}
      k K n 1 (MvPolynomial.X (i, j))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, j, hji, rfl⟩ := (mem_definingRelationSet_iff k n y).mp hy
    exact (mem_definingRelationSet_iff K n _).mpr ⟨i, j, hji, hentry i j⟩
  · intro hx
    obtain ⟨i, j, hji, rfl⟩ := (mem_definingRelationSet_iff K n x).mp hx
    exact ⟨_, (mem_definingRelationSet_iff k n _).mpr ⟨i, j, hji, rfl⟩, hentry i j⟩

variable (k n) in
/-- **The upper-triangular subgroup of `GLₙ` is a Borel subgroup over every field.** Its base
change to an algebraic closure is smooth, connected, solvable, and maximal among closed
subgroups with those properties. -/
theorem isBorel_definingHopfIdeal :
    HopfIdeal.IsBorel k (GeneralLinear.coordinateHopfAlgebra k n) (definingHopfIdeal k n) := by
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    (FiniteTypeCommHopfAlgCat.of k (GeneralLinear.coordinateHopfAlgebra k n))
  let L := FiniteTypeCommHopfAlgCat.of K (GeneralLinear.coordinateHopfAlgebra K n)
  let e : H' ≅ L := ObjectProperty.isoMk _
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K n)
  have hpull := HopfIdeal.IsBorelOverAlgClosed.of_map_eq e
    (map_baseChangeHopfIdeal_definingHopfIdeal k K)
    (isBorelOverAlgClosed_definingHopfIdeal K n)
  exact (HopfIdeal.isBorel_iff_isBorelOverAlgClosed_baseChange
    k (GeneralLinear.coordinateHopfAlgebra k n) (definingHopfIdeal k n)).2 hpull

end UpperTriangular

end

end TauCeti.GeneralLinear
