/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Borel.Over
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Connected
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Smooth
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Solvable.Lagrangian
import TauCeti.Algebra.Coalgebra.Comodule.Flag.Extension
import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic

/-!
# Borel subgroups of `Sp₂ₘ`

Over an algebraically closed field, every reduced, connected, solvable closed subgroup of `Sp₂ₘ`
is contained in a conjugate, by a rational point of `Sp₂ₘ`, of the stabilizer of the standard
complete isotropic flag. In Hopf coordinates containment of closed subgroups is reversed, so the
conclusion reads `(definingHopfIdeal k m).conjugate g ≤ I`.

The proof restricts the standard representation `k^(2m)` to the subgroup. The standard
alternating form is invariant, so the subgroup preserves a Lagrangian subspace `L`
(`LinearMap.BilinForm.IsAlt.exists_subcomodule_eq_orthogonal_of_isSolvable`), and the
Lie--Kolchin theorem gives a basis of `L` in which the subgroup acts by upper-triangular
matrices. That basis extends to a symplectic basis of `k^(2m)`
(`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq`). In the extended basis the
generic point of the subgroup has upper-triangular upper-left block and vanishing lower-left
block, and a symplectic matrix of this shape preserves the whole standard isotropic flag
(`TauCeti.GLSymplecticFin.IsotropicFlag.mem_matrixSubgroup_iff_castAdd`). The change of basis
matrix is symplectic, so it is a rational point of `Sp₂ₘ`.

The flag stabilizer is smooth, geometrically connected, and has solvable geometric points, so
it is a Borel candidate. Combined with the containment above, it is a Borel subgroup, the Borel
subgroups of `Sp₂ₘ` over an algebraically closed field are exactly its conjugates, and any two of
them are conjugate. Its defining ideal commutes with base change, so it is a Borel subgroup of
`Sp₂ₘ` over every commutative ring, and in particular over every field. All of this holds in
every characteristic, including two.

## Main declarations

* `TauCeti.Symplectic.IsotropicFlag.exists_map_inv_mul_mul_map_mem_matrixSubgroup`: a point of
  `Sp₂ₘ` with values in the coordinate algebra of a reduced connected solvable group is
  conjugated into the flag stabilizer by a rational symplectic matrix.
* `TauCeti.Symplectic.IsotropicFlag.exists_conjugate_definingHopfIdeal_le`: a reduced,
  connected, solvable closed subgroup of `Sp₂ₘ` is contained in a conjugate of the flag
  stabilizer.
* `TauCeti.Symplectic.IsotropicFlag.isBorelCandidate_definingHopfIdeal`: the flag stabilizer is
  smooth, geometrically connected, and geometrically solvable.
* `TauCeti.Symplectic.IsotropicFlag.isBorelOverAlgClosed_iff_exists_eq_conjugate`: over an
  algebraically closed field, the Borel subgroups of `Sp₂ₘ` are exactly the conjugates of the
  flag stabilizer.
* `TauCeti.Symplectic.IsotropicFlag.exists_conjugate_eq_of_isBorelOverAlgClosed`: any two Borel
  subgroups of `Sp₂ₘ` over an algebraically closed field are conjugate.
* `TauCeti.Symplectic.IsotropicFlag.isBorelOver_definingHopfIdeal`: the flag stabilizer is a
  Borel subgroup of `Sp₂ₘ` over every commutative ring.
* `TauCeti.Symplectic.IsotropicFlag.isBorel_definingHopfIdeal`: the flag stabilizer is a Borel
  subgroup of `Sp₂ₘ` over every field.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 11.1 and §23.
* J. S. Milne, *Algebraic Groups* (2017), Section 17.a and §24.6.
* The argument follows the special-linear case in
  `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Borel`.
-/

public section

open CategoryTheory WithConv Module
open scoped Matrix

namespace TauCeti.Symplectic.IsotropicFlag

universe u v

noncomputable section

section Triangularization

variable {k : Type u} [Field k] {m : ℕ}

/-- The transported alternating form is `Matrix.J` reindexed along `finSumFinEquiv`. -/
private theorem JFin_eq_submatrix :
    JFin m k = (Matrix.J (Fin m) k).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [← JFin_submatrix m (R := k), Matrix.submatrix_submatrix]
  simp

/-- In `Fin (m + m)` coordinates, the form `x ↦ y ↦ xᵀ J y` is the standard symplectic form
transported along `finSumFinEquiv`. -/
private theorem toBilin'_JFin_eq_congr :
    Matrix.toBilin' (JFin m k) = LinearMap.BilinForm.congr
      (LinearEquiv.funCongrLeft k k finSumFinEquiv.symm) (stdSymplecticBilinForm k m) := by
  refine LinearMap.ext₂ fun x y ↦ ?_
  rw [LinearMap.BilinForm.congr_apply, LinearEquiv.funCongrLeft_symm, Equiv.symm_symm,
    stdSymplecticBilinForm_apply, Matrix.toBilin'_apply', JFin_eq_submatrix,
    Matrix.submatrix_mulVec_equiv, dotProduct_comp_equiv_symm]
  rfl

/-- The standard symplectic form in `Fin (m + m)` coordinates is alternating. -/
private theorem isAlt_toBilin'_JFin : (Matrix.toBilin' (JFin m k)).IsAlt := by
  intro v
  rw [toBilin'_JFin_eq_congr, LinearMap.BilinForm.congr_apply]
  exact isAlt_stdSymplecticBilinForm k m _

/-- The standard symplectic form in `Fin (m + m)` coordinates is nondegenerate. -/
private theorem nondegenerate_toBilin'_JFin : (Matrix.toBilin' (JFin m k)).Nondegenerate := by
  rw [toBilin'_JFin_eq_congr]
  exact (stdSymplecticBilinForm_nondegenerate k m).congr _

/-- Read through the symplectic coordinate morphism, the general-linear matrix of a point of
`Sp₂ₘ` is its symplectic matrix. -/
private theorem pointsMulEquiv_comp_coordinateMap {A : Type v} [CommRing A] [Algebra k A]
    (ψ : Symplectic.coordinateHopfAlgebra k m →ₐ[k] A) :
    GeneralLinear.pointsMulEquiv (m + m)
        (toConv (ψ.comp ((Symplectic.coordinateMap k m).hom :
          GeneralLinear.coordinateHopfAlgebra k (m + m) →ₐ[k]
            Symplectic.coordinateHopfAlgebra k m))) =
      (Symplectic.pointsMulEquiv k m (A := A) (toConv ψ) : GL (Fin (m + m)) A) := by
  rw [← Symplectic.pointsMulEquiv_coe, CommHopfAlgCat.quotientPointsHom_apply,
    Symplectic.coordinateMap_def, ofConv_toConv]

variable {Q : Type v} [CommRing Q] [HopfAlgebra k Q]

/-- The standard alternating form is invariant under the rational points of a group `Q` mapping
to `Sp₂ₘ`, acting on the standard representation corestricted along `π`. -/
private theorem isInvariantForm_toBilin'_JFin (π : Symplectic.coordinateHopfAlgebra k m →ₐc[k] Q) :
    let _ := GeneralLinear.corestrictStandardComodule k (m + m)
      (π.comp (Symplectic.coordinateMap k m).hom)
    Representation.IsInvariantForm (Comodule.basePointsRepresentation (H := Q) (Fin (m + m) → k))
      (Matrix.toBilin' (JFin m k)) := by
  let _ := GeneralLinear.corestrictStandardComodule k (m + m)
    (π.comp (Symplectic.coordinateMap k m).hom)
  dsimp only
  rw [Representation.isInvariantForm_iff]
  intro g x y
  let S := Symplectic.pointsMulEquiv k m (A := k) (AlgHom.mapDomain π g)
  have hact (w : Fin (m + m) → k) :
      Comodule.basePointsRepresentation (H := Q) (Fin (m + m) → k) g w =
        (S.val : Matrix (Fin (m + m)) (Fin (m + m)) k) *ᵥ w := by
    let _ := GeneralLinear.standardComodule k (m + m)
    rw [Comodule.basePointsRepresentation_corestrict,
      GeneralLinear.basePointsRepresentation_eq_mulVec, ← GeneralLinear.pointsMulEquiv_apply,
      AlgHom.mapDomain_apply, ← pointsMulEquiv_comp_coordinateMap, BialgHom.comp_toAlgHom,
      AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_assoc]
  have hS := GLSymplecticFin.mem_iff'.mp S.2
  rw [hact, hact, Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  conv_rhs => rw [← hS, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The matrix whose columns form a basis of `k^(2m)` in which the standard alternating form has
Gram matrix `J` is symplectic. -/
private theorem toMatrix_mem_GLSymplecticFin (b : Basis (Fin (m + m)) k (Fin (m + m) → k))
    (hb : LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (JFin m k)) = JFin m k)
    [Invertible ((Pi.basisFun k (Fin (m + m))).toMatrix b)] :
    unitOfInvertible ((Pi.basisFun k (Fin (m + m))).toMatrix b) ∈ GLSymplecticFin m k := by
  have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun k (Fin (m + m))) b
    (Matrix.toBilin' (JFin m k))
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin', hb] at h
  rwa [GLSymplecticFin.mem_iff', val_unitOfInvertible]

/-- **Adapted symplectic bases.** Let `π : O(Sp₂ₘ) → Q` be a point with values in the
coordinate algebra of a reduced, geometrically connected, geometrically solvable group over an
algebraically closed field. The standard representation corestricted along `π` has a symplectic
basis `b` whose first half is a Lie--Kolchin basis `e` of an invariant Lagrangian subspace `N`. -/
private theorem exists_basis_castAdd_eq [IsAlgClosed k] [Algebra.FiniteType k Q] [IsReduced Q]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (π : Symplectic.coordinateHopfAlgebra k m →ₐc[k] Q) :
    let _ := GeneralLinear.corestrictStandardComodule k (m + m)
      (π.comp (Symplectic.coordinateMap k m).hom)
    ∃ (N : Subcomodule k Q (Fin (m + m) → k)) (e : Basis (Fin m) k N)
      (b : Basis (Fin (m + m)) k (Fin (m + m) → k)),
      (Comodule.coefficientMatrix (C := Q) e).IsUpperTriangular ∧
        (∀ j, b (Fin.castAdd m j) = e j) ∧
        LinearMap.BilinForm.toMatrix b (Matrix.toBilin' (JFin m k)) = JFin m k := by
  let _ := GeneralLinear.corestrictStandardComodule k (m + m)
    (π.comp (Symplectic.coordinateMap k m).hom)
  dsimp only
  let _ : ConnectedSpace (PrimeSpectrum Q) :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mp hconn
  let _ : Group.IsSolvable (WithConv (Q →ₐ[k] AlgebraicClosure k)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff k _).mp hsolv
  let _ : Group.IsSolvable (WithConv (Q →ₐ[k] k)) :=
    Group.isSolvable_of_isSolvable_injective
      (AlgHom.mapValue_injective (Algebra.ofId k (AlgebraicClosure k)).injective)
  obtain ⟨N, hN⟩ := isAlt_toBilin'_JFin.exists_subcomodule_eq_orthogonal_of_isSolvable
    (isInvariantForm_toBilin'_JFin π)
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have : Module.Finite k N := N.finite
  obtain ⟨r, e, he, -⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_geometricallySolvable
      (k := k) (H := Q) (M := N) hconn hsolv
  -- The basis `e` of `N` is also a basis of the submodule `N.toSubmodule`, with the same
  -- underlying vectors.
  obtain ⟨b, hbJ, hbe⟩ := isAlt_toBilin'_JFin.exists_basis_toMatrix_eq_J_inl_eq
    nondegenerate_toBilin'_JFin (U := N.toSubmodule) e hN
  obtain rfl : r = m := by
    have h := Module.finrank_eq_card_basis b
    simp only [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h
    omega
  refine ⟨N, e, b.reindex finSumFinEquiv, he, fun j ↦ ?_, ?_⟩
  · rw [Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, hbe]
    rfl
  · ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply,
      ← LinearMap.BilinForm.toMatrix_apply, hbJ, JFin_eq_submatrix, Matrix.submatrix_apply]

/-- **Lie--Kolchin for `Sp₂ₘ`-valued points.**

Let `Q` be the coordinate algebra of a reduced, geometrically connected, geometrically solvable
affine group of finite type over an algebraically closed field `k`. For every bialgebra morphism
`π : O(Sp₂ₘ) → Q` some rational symplectic matrix `P` conjugates the `Q`-valued point `π` into the
stabilizer of the standard complete isotropic flag. The columns of `P` form a symplectic basis
whose isotropic half is a Lie--Kolchin basis of an invariant Lagrangian subspace. -/
theorem exists_map_inv_mul_mul_map_mem_matrixSubgroup [IsAlgClosed k] [Algebra.FiniteType k Q]
    [IsReduced Q]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k Q))
    (π : Symplectic.coordinateHopfAlgebra k m →ₐc[k] Q) :
    ∃ P : GLSymplecticFin m k,
      GLSymplecticFin.map m k (algebraMap k Q) P⁻¹ *
          Symplectic.pointsMulEquiv k m (A := Q)
            (toConv (π : Symplectic.coordinateHopfAlgebra k m →ₐ[k] Q)) *
          GLSymplecticFin.map m k (algebraMap k Q) P ∈
        GLSymplecticFin.IsotropicFlag.matrixSubgroup m := by
  let πGL := π.comp (Symplectic.coordinateMap k m).hom
  let _ := GeneralLinear.corestrictStandardComodule k (m + m) πGL
  obtain ⟨N, e, b, he, hbe, hbJ⟩ := exists_basis_castAdd_eq hconn hsolv π
  let _ := (Pi.basisFun k (Fin (m + m))).invertibleToMatrix b
  let P₀ : GL (Fin (m + m)) k := unitOfInvertible ((Pi.basisFun k (Fin (m + m))).toMatrix b)
  refine ⟨⟨P₀, toMatrix_mem_GLSymplecticFin b hbJ⟩, ?_⟩
  -- Conjugating the generic point by the change-of-basis matrix gives the coefficient matrix
  -- of `b`.
  let U := Matrix.GeneralLinearGroup.mk'' (Comodule.coefficientMatrix (C := Q) b)
    (Comodule.isUnit_det_coefficientMatrix b)
  have hmat : (Symplectic.pointsMulEquiv k m (A := Q)
        (toConv (π : Symplectic.coordinateHopfAlgebra k m →ₐ[k] Q)) : GL (Fin (m + m)) Q) *
      Matrix.GeneralLinearGroup.map (algebraMap k Q) P₀ =
      Matrix.GeneralLinearGroup.map (algebraMap k Q) P₀ * U := by
    ext : 1
    rw [← pointsMulEquiv_comp_coordinateMap]
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_map_apply,
      val_unitOfInvertible, Matrix.GeneralLinearGroup.val_mk'', P₀, U, πGL,
      BialgHom.comp_toAlgHom, GeneralLinear.pointsMulEquiv_apply] using
      GeneralLinear.pointToGeneralLinear_mul_map_toMatrix k (m + m) πGL b
  rw [GLSymplecticFin.IsotropicFlag.mem_matrixSubgroup_iff_castAdd, Subgroup.coe_mul,
    Subgroup.coe_mul, map_inv, Subgroup.coe_inv, GLSymplecticFin.coe_map, mul_assoc, hmat,
    inv_mul_cancel_left]
  -- The first half of `b` spans the subcomodule `N` and is triangular there.
  refine ⟨fun i j hji ↦ ?_, fun i j ↦ ?_⟩
  · rw [Matrix.GeneralLinearGroup.val_mk'',
      Comodule.coefficientMatrix_castAdd_castAdd_of_castAdd_eq N e b hbe]
    exact he hji
  · rw [Matrix.GeneralLinearGroup.val_mk'', ← Fin.natAdd_eq_addNat,
      Comodule.coefficientMatrix_natAdd_castAdd_of_castAdd_eq N e b hbe]

/-- **Every reduced, connected, solvable closed subgroup of `Sp₂ₘ` is contained in a conjugate of
the stabilizer of the standard complete isotropic flag**, over an algebraically closed field. The
inequality of Hopf ideals reverses subgroup containment. -/
theorem exists_conjugate_definingHopfIdeal_le [IsAlgClosed k]
    (I : HopfIdeal k (Symplectic.coordinateHopfAlgebra k m))
    [IsReduced (CommHopfAlgCat.quotient (Symplectic.coordinateHopfAlgebra k m) I)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (Symplectic.coordinateHopfAlgebra k m) I))
    (hsolv : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (Symplectic.coordinateHopfAlgebra k m) I)) :
    ∃ g : WithConv (Symplectic.coordinateHopfAlgebra k m →ₐ[k] k),
      (definingHopfIdeal k m).conjugate g ≤ I := by
  let Q := CommHopfAlgCat.quotient (Symplectic.coordinateHopfAlgebra k m) I
  let π : Symplectic.coordinateHopfAlgebra k m →ₐc[k] Q :=
    (CommHopfAlgCat.mkQuotient _ I).hom
  obtain ⟨P, hP⟩ := exists_map_inv_mul_mul_map_mem_matrixSubgroup hconn hsolv π
  let g : WithConv (Symplectic.coordinateHopfAlgebra k m →ₐ[k] k) :=
    (Symplectic.pointsMulEquiv k m (A := k)).symm P⁻¹
  -- Conjugating the quotient's generic `Sp₂ₘ` point by `g` is ordinary matrix conjugation by
  -- the symplectic matrix `P`.
  have hkey : Symplectic.pointsMulEquiv k m (A := Q)
      (toConv ((π : Symplectic.coordinateHopfAlgebra k m →ₐ[k] Q).comp
        (HopfAlgebra.pointConjugationAlgHom g))) =
      GLSymplecticFin.map m k (algebraMap k Q) P⁻¹ *
        Symplectic.pointsMulEquiv k m (A := Q)
          (toConv (π : Symplectic.coordinateHopfAlgebra k m →ₐ[k] Q)) *
        GLSymplecticFin.map m k (algebraMap k Q) P := by
    rw [HopfAlgebra.comp_pointConjugationAlgHom, map_mul, map_mul, map_inv,
      Symplectic.pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, map_inv, inv_inv,
      map_inv, Algebra.toRingHom_ofId]
  -- Vanishing of the flag ideal on this conjugated generic point gives the scheme-theoretic
  -- containment, rather than only containment on `k`-points.
  exact ⟨g⁻¹, HopfIdeal.conjugate_inv_le_of_mem_quotientPointsSubgroup_mkQuotient
    I (definingHopfIdeal k m) g
    ((mem_definingPointsSubgroup_iff k m _).mpr (by rw [hkey]; exact hP))⟩

end Triangularization

section Borel

variable (k : Type u) [Field k] (m : ℕ)

/-- The stabilizer of the standard complete isotropic flag in `Sp₂ₘ` is a Borel candidate over
every field: it is smooth, geometrically connected, and geometrically solvable. -/
theorem isBorelCandidate_definingHopfIdeal :
    HopfIdeal.IsBorelCandidate k
      (FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m))
      (definingHopfIdeal k m) :=
  HopfIdeal.IsBorelCandidate.mk (smoothCommHopfAlgProperty_coordinateHopfAlgebra k m)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra m k)
    (geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra m k)

variable {k m}

/-- Over an algebraically closed field, every Borel subgroup of `Sp₂ₘ` is contained in a
conjugate of the flag stabilizer. -/
private theorem exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed [IsAlgClosed k]
    (I : HopfIdeal k (Symplectic.coordinateHopfAlgebra k m))
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m)) I) :
    ∃ g : WithConv (Symplectic.coordinateHopfAlgebra k m →ₐ[k] k),
      (definingHopfIdeal k m).conjugate g ≤ I := by
  have hIcandidate := ((HopfIdeal.isBorelOverAlgClosed_iff _ _ _).mp hI).2.prop
  let _ : IsReduced (CommHopfAlgCat.quotient (Symplectic.coordinateHopfAlgebra k m) I) :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k _).mp hIcandidate.smooth).isReduced
  exact exists_conjugate_definingHopfIdeal_le I hIcandidate.geometricallyConnected
    hIcandidate.geometricallySolvable

variable (k m) in
/-- **The stabilizer of the standard complete isotropic flag is a Borel subgroup of `Sp₂ₘ` over
an algebraically closed field**: it is maximal among smooth, connected, solvable closed
subgroups. -/
theorem isBorelOverAlgClosed_definingHopfIdeal [IsAlgClosed k] :
    HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m))
      (definingHopfIdeal k m) :=
  HopfIdeal.isBorelOverAlgClosed_of_forall_exists_conjugate_le _
    (isBorelCandidate_definingHopfIdeal k m)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed

/-- **The Borel subgroups of `Sp₂ₘ` over an algebraically closed field are exactly the conjugates
of the stabilizer of the standard complete isotropic flag.** The equality is an equality of
defining Hopf ideals, hence of closed subgroup schemes, rather than only of their rational
points. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate [IsAlgClosed k]
    (I : HopfIdeal k (Symplectic.coordinateHopfAlgebra k m)) :
    HopfIdeal.IsBorelOverAlgClosed k
        (FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m)) I ↔
      ∃ g : WithConv (Symplectic.coordinateHopfAlgebra k m →ₐ[k] k),
        I = (definingHopfIdeal k m).conjugate g :=
  HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate _
    (isBorelCandidate_definingHopfIdeal k m)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed I

/-- **Any two Borel subgroups of `Sp₂ₘ` over an algebraically closed field are conjugate** by a
rational point of `Sp₂ₘ`. -/
theorem exists_conjugate_eq_of_isBorelOverAlgClosed [IsAlgClosed k]
    {I J : HopfIdeal k (Symplectic.coordinateHopfAlgebra k m)}
    (hI : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m)) I)
    (hJ : HopfIdeal.IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m)) J) :
    ∃ g : WithConv (Symplectic.coordinateHopfAlgebra k m →ₐ[k] k), I.conjugate g = J :=
  HopfIdeal.exists_conjugate_eq_of_isBorelOverAlgClosed _
    (isBorelCandidate_definingHopfIdeal k m)
    exists_conjugate_definingHopfIdeal_le_of_isBorelOverAlgClosed hI hJ

end Borel

variable (R : Type u) [CommRing R] (m : ℕ) in
/-- **The stabilizer of the standard complete isotropic flag is a Borel subgroup of `Sp₂ₘ` over
every commutative ring**: it is smooth over the base, and on every geometric fiber it is the
flag stabilizer, a Borel subgroup. -/
theorem isBorelOver_definingHopfIdeal :
    HopfIdeal.IsBorelOver R (Symplectic.coordinateHopfAlgebra R m) (definingHopfIdeal R m) := by
  refine HopfIdeal.IsBorelOver.mk inferInstance fun k _ _ _ ↦ ?_
  let e : FiniteTypeCommHopfAlgCat.baseChange (K := k)
        (FiniteTypeCommHopfAlgCat.of R (Symplectic.coordinateHopfAlgebra R m)) ≅
      FiniteTypeCommHopfAlgCat.of k (Symplectic.coordinateHopfAlgebra k m) :=
    ObjectProperty.isoMk _ (Symplectic.coordinateHopfAlgebraBaseChangeIso R k m)
  exact HopfIdeal.IsBorelOverAlgClosed.of_map_eq e
    (map_baseChangeHopfIdeal_definingHopfIdeal R k m)
    (isBorelOverAlgClosed_definingHopfIdeal k m)

variable (k : Type u) [Field k] (m : ℕ) in
/-- **The stabilizer of the standard complete isotropic flag is a Borel subgroup of `Sp₂ₘ` over
every field.** Its base change to an algebraic closure is smooth, connected, solvable, and
maximal among closed subgroups with those properties. -/
theorem isBorel_definingHopfIdeal :
    HopfIdeal.IsBorel k (Symplectic.coordinateHopfAlgebra k m) (definingHopfIdeal k m) :=
  (isBorelOver_definingHopfIdeal k m).isBorel

end

end TauCeti.Symplectic.IsotropicFlag
