/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Tangent

/-!
# Differentials of symplectic root subgroups

The differential of each represented root map `𝔾ₐ → Sp₂ₘ` sends an additive
tangent parameter to the corresponding single matrix unit (long roots) or signed
pair of matrix units (short roots). This identifies its image with the line spanned
by its normalized unit tangent vector, and proves injectivity over arbitrary
commutative coefficient algebras, including nonreduced rings and characteristic two.
These are the Lie vectors used to normalize the type-C root subgroups in a pinning.

The coordinate calculation uses `Symplectic.rootSubgroupCoordinateMap_apply_X`,
the quotient tangent map, and `Symplectic.tangentLieEquivSp`. Its organization follows
`SpecialLinear.Root.Differential`, with all five symplectic root families treated
uniformly through `GLSymplecticFin.RootSubgroupIndex.tangentMatrix`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21 and 24.6.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

namespace TauCeti.Symplectic

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {m : ℕ}

/-- The represented root-subgroup differential has the standard normalized symplectic
matrix: a single entry for a long root and a signed pair for a short root. -/
@[simp]
theorem tangentMatrix_derivationComp_rootSubgroup (root : GLSymplecticFin.RootSubgroupIndex m)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    (tangentMatrix m (derivationComp (B := B)
      (rootSubgroupCoordinateMap (R := R) root).hom d) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) =
      root.tangentMatrix (AdditiveGroup.gaTangentLinearEquiv d) := by
  ext a b
  rw [tangentMatrix_apply_coe, Matrix.submatrix_apply,
    GeneralLinear.tangentMatrix_apply, HopfIdeal.quotientLieHom_apply,
    algEquivSelf_derivationComp_apply, algEquivSelf_derivationComp_apply]
  have hcoord := rootSubgroupCoordinateMap_apply_X (R := R) root a b
  simp only [coordinateMap_def, CommHopfAlgCat.hom_mkQuotient] at hcoord
  refine (congrArg (fun x => Bialgebra.CounitAlgebra.algEquivSelf R
    (AdditiveGroup.coordinateHopfAlgebra R) B (d x)) hcoord).trans ?_
  have hconst : d ((1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
      (AdditiveGroup.coordinateHopfAlgebra R)) a b) = 0 := by
    classical
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [Matrix.add_apply, map_add, hconst, zero_add]
  let f : AdditiveGroup.coordinateHopfAlgebra R →+ B :=
    ((Bialgebra.CounitAlgebra.algEquivSelf R
      (AdditiveGroup.coordinateHopfAlgebra R) B).toAddMonoidHom).comp
        d.toLinearMap.toAddMonoidHom
  have hf_apply (x : AdditiveGroup.coordinateHopfAlgebra R) :
      f x = Bialgebra.CounitAlgebra.algEquivSelf R
        (AdditiveGroup.coordinateHopfAlgebra R) B (d x) := rfl
  have hf := congrFun (congrFun (root.map_tangentMatrix f (SymmetricAlgebra.ι R R 1)) a) b
  simpa only [Matrix.map_apply, hf_apply,
    AdditiveGroup.gaTangentLinearEquiv_apply] using hf

/-- Every root-subgroup differential is injective over every commutative
coefficient algebra. -/
theorem derivationComp_rootSubgroup_injective (root : GLSymplecticFin.RootSubgroupIndex m) :
    Function.Injective
      (derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) root).hom) := by
  intro d e h
  apply (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).injective
  apply root.tangentMatrix_injective
  simpa only [tangentMatrix_derivationComp_rootSubgroup (R := R) (B := B)] using
    congrArg (fun x => (tangentMatrix m x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B)) h

/-- The normalized root vector is the image of the additive unit tangent vector
under the represented root-subgroup differential. -/
noncomputable def rootVector (root : GLSymplecticFin.RootSubgroupIndex m) :
    Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B) :=
  derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) root).hom
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- The matrix of the normalized root vector has parameter one. -/
@[simp]
theorem tangentMatrix_rootVector (root : GLSymplecticFin.RootSubgroupIndex m) :
    (tangentMatrix m (rootVector (R := R) (B := B) root) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) = root.tangentMatrix 1 := by
  rw [rootVector, tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply]

/-- The differential sends a tangent parameter to that scalar times the
normalized root vector. -/
theorem derivationComp_rootSubgroup_eq_smul_rootVector
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) B)) :
    derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) root).hom d =
      AdditiveGroup.gaTangentLinearEquiv d • rootVector (R := R) (B := B) root := by
  let c : B := AdditiveGroup.gaTangentLinearEquiv d
  have hunit : root.tangentMatrix c = c • root.tangentMatrix 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hright : (tangentMatrix m (c • rootVector (R := R) (B := B) root) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) = c • root.tangentMatrix 1 := by
    calc
      _ = ((c • tangentMatrix m (rootVector (R := R) (B := B) root) :
          LieAlgebra.Symplectic.sp (Fin m) B) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) :=
        congrArg Subtype.val ((tangentMatrix (R := R) (B := B) m).map_smul c _)
      _ = c • (tangentMatrix m (rootVector (R := R) (B := B) root) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) :=
        -- Scalar multiplication on the Lie-subalgebra subtype is inherited from matrices.
        rfl
      _ = c • root.tangentMatrix 1 :=
        congrArg (c • ·) (tangentMatrix_rootVector (R := R) (B := B) root)
  apply (tangentLieEquivSp (R := R) (B := B) m).injective
  apply Subtype.ext
  simpa only [LieEquiv.coe_toLieHom, tangentLieEquivSp_apply (R := R) (B := B)] using
    (tangentMatrix_derivationComp_rootSubgroup (R := R) (B := B) root d).trans
      (hunit.trans hright.symm)

/-- The image of a root-subgroup differential is exactly its normalized root line. -/
theorem range_derivationCompLieHom_rootSubgroup_eq_span
    (root : GLSymplecticFin.RootSubgroupIndex m) :
    (derivationCompLieHom (B := B)
      (rootSubgroupCoordinateMap (R := R) root).hom).range.toSubmodule =
      Submodule.span B {rootVector (R := R) (B := B) root} := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨AdditiveGroup.gaTangentLinearEquiv e, by
      rw [derivationCompLieHom_apply, derivationComp_rootSubgroup_eq_smul_rootVector]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨(AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm c, ?_⟩
    rw [derivationCompLieHom_apply, derivationComp_rootSubgroup_eq_smul_rootVector,
      LinearEquiv.apply_symm_apply]

/-- Extension from the base ring to a coefficient algebra preserves the normalized
root-subgroup tangent vector. -/
@[simp]
theorem mapValue_rootVector (root : GLSymplecticFin.RootSubgroupIndex m) :
    Derivation.mapValue (Algebra.ofId R B) (rootVector (R := R) (B := R) root) =
      rootVector (R := R) (B := B) root := by
  have hga : Derivation.mapValue (Algebra.ofId R B)
      ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1) =
        (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1 := by
    apply (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).injective
    simp only [AdditiveGroup.gaTangentLinearEquiv_apply, Derivation.mapValue_apply,
      AdditiveGroup.gaTangentLinearEquiv_symm_apply_ι, map_one]
  rw [rootVector, rootVector]
  ext a
  rw [Derivation.mapValue_apply, derivationComp_apply, derivationComp_apply]
  have ha := DFunLike.congr_fun hga ((rootSubgroupCoordinateMap (R := R) root).hom a)
  rw [Derivation.mapValue_apply] at ha
  -- Precomposition changes the counit-algebra index. Both equalities are in the same
  -- value ring, but rewriting cannot cross the temporarily ill-typed synonym coercion.
  change (Algebra.ofId R B)
      ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1
        ((rootSubgroupCoordinateMap (R := R) root).hom a)) =
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1
      ((rootSubgroupCoordinateMap (R := R) root).hom a) : B) at ha ⊢
  exact ha

/-- The normalized root vector is nonzero whenever the coefficient algebra is nontrivial. -/
theorem rootVector_ne_zero [Nontrivial B] (root : GLSymplecticFin.RootSubgroupIndex m) :
    rootVector (R := R) (B := B) root ≠ 0 := by
  intro h
  have h' : root.tangentMatrix (1 : B) = root.tangentMatrix 0 := by
    simpa only [tangentMatrix_rootVector (R := R) (B := B), map_zero,
      ZeroMemClass.coe_zero] using congrArg
      (fun d => (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B)) h
  exact one_ne_zero (root.tangentMatrix_injective h')

end TauCeti.Symplectic
