/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Lie.F4.ModularLattice
import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Matrix
import TauCeti.Algebra.Lie.F4.ShortRoot.TorusAction

/-!
# Numbered root differentials of the short-root F₄ carrier over 𝔽₂

The differentials of the eight numbered signed-simple-root subgroups (four positive and four
negative) send the additive unit tangent vector to the corresponding integral Chevalley matrix
reduced modulo two. The quadratic terms in the short-root parametrizations have zero differential
at the identity. The vectors are nonzero and have their prescribed integral torus characters,
even though characteristic two makes the short simple-root matrices square to zero.

These normalized vectors are the differential data needed for a pinning. Membership in the
prescribed adjoint weight space does not assert that the vector spans that entire space.
Neither maximality of the weight torus nor an identification with an independently pinned
simply connected group scheme is asserted.

## Main declarations

* `tangentMatrix`: the injective matrix realization of the carrier's tangent space.
* `tangentMatrix_derivationComp_generator_inl`: the numbered differential on matrices,
  with coefficients in any commutative 𝔽₂-algebra.
* `rootVector` and `tangentMatrix_rootVector`: the normalized unit tangent vectors.
* `rootVector_mem_adjointWeightSpace`: each vector has the numbered signed-simple-root character.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.

The differential calculation follows
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`, using the existing integral F₄
root matrices and their quadratic parametrizations.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator
local notation "Q" => CommHopfAlgCat.quotient H₂₆ J

/-- The tangent matrix of a vector of the prime-field carrier: the differential of its closed
embedding in `GL₂₆`, after cotangent duality. -/
def tangentMatrix : Module.Dual (ZMod 2) (Bialgebra.CotangentSpace (ZMod 2) Q) →ₗ[ZMod 2]
    Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  (GeneralLinear.tangentMatrix 26).comp
    ((HopfIdeal.quotientLieHom (B := ZMod 2) J).toLinearMap.comp
      (Derivation.cotangentLinearEquiv (B := ZMod 2)).toLinearMap)

/-- The carrier's tangent matrix is the ambient matrix of its included derivation. -/
theorem tangentMatrix_apply (x : Module.Dual (ZMod 2) (Bialgebra.CotangentSpace (ZMod 2) Q)) :
    tangentMatrix x = GeneralLinear.tangentMatrix 26
      (HopfIdeal.quotientLieHom J (Derivation.cotangentLinearEquiv (B := ZMod 2) x)) :=
  (rfl)

/-- A tangent vector of the carrier is determined by its matrix. -/
theorem tangentMatrix_injective : Function.Injective tangentMatrix := by
  intro x y h
  rw [tangentMatrix_apply, tangentMatrix_apply,
    ← GeneralLinear.tangentLinearEquivMatrix_apply,
    ← GeneralLinear.tangentLinearEquivMatrix_apply] at h
  exact (Derivation.cotangentLinearEquiv (B := ZMod 2)).injective
    (HopfIdeal.quotientLieHom_injective J
      ((GeneralLinear.tangentLinearEquivMatrix 26).injective h))

/-- Restricting the ambient generic matrix to a numbered root subgroup gives its matrix at
the universal additive coordinate. -/
theorem map_genericMatrix_generator_inl (k : Fin 4 ⊕ Fin 4) :
    (GeneralLinear.genericMatrix (ZMod 2) 26).map (generator (.inl k)).hom.toAlgHom =
      ((rootSubgroupPoints k (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
        (Multiplicative.ofAdd (SymmetricAlgebra.ι (ZMod 2) (ZMod 2) 1)) :
        Matrix.GeneralLinearGroup (Fin 26) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))) :
        Matrix (Fin 26) (Fin 26) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))) := by
  let A := CommAlgCat.of (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
  let q : HopfAlgebra.points (R := ZMod 2)
      (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 2)) A :=
    toConv (AlgHom.id (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2)))
  have hid : (CommHopfAlgCat.mapPointsFunctor (generator (.inl k))).app A q =
      toConv (generator (.inl k)).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
    simp only [q, AlgHom.id_comp]
    -- The categorical point has the same algebra map after erasing its object wrapper.
    rfl
  have hu : AdditiveGroup.gaPointsMulEquiv (R := ZMod 2) q =
      Multiplicative.ofAdd (SymmetricAlgebra.ι (ZMod 2) (ZMod 2) 1) := by
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv (R := ZMod 2) q),
      AdditiveGroup.toAdd_gaPointsMulEquiv]
    simp [q]
  rw [← hu, coe_rootSubgroupPoints_gaPointsMulEquiv, hid,
    GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    GeneralLinear.pointsMulEquiv_apply]

/-- The differential of a numbered root subgroup, read in the ambient matrix group, is the
additive tangent parameter times its Chevalley matrix. This holds over every commutative
coefficient algebra, including nonreduced ones. -/
theorem tangentMatrix_derivationComp_generator_inl
    {B : Type*} [CommRing B] [Algebra (ZMod 2) B] (k : Fin 4 ⊕ Fin 4)
    (d : Derivation (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
      (Bialgebra.CounitAlgebra (ZMod 2) (AdditiveGroup.coordinateHopfAlgebra (ZMod 2)) B)) :
    GeneralLinear.tangentMatrix 26 (derivationComp (B := B) (generator (.inl k)).hom d) =
      AdditiveGroup.gaTangentLinearEquiv d • (rootMatrix k).map (Int.cast : ℤ → B) := by
  ext a b
  rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply,
    ← GeneralLinear.genericMatrix_apply]
  have hentry := congrFun (congrFun (map_genericMatrix_generator_inl k) a) b
  rw [Matrix.map_apply] at hentry
  rw [hentry, coe_rootSubgroupPoints, F4ShortRoot.coe_rootSubgroupPoints_eq]
  have hone : d ((1 : Matrix (Fin 26) (Fin 26)
      (SymmetricAlgebra (ZMod 2) (ZMod 2))) a b) = 0 := by
    classical
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  simp only [toAdd_ofAdd, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    map_add, Derivation.leibniz, Derivation.map_intCast, smul_zero, zero_add, hone,
    AdditiveGroup.tangent_ι_pow_eq_zero d 1 (by norm_num : 2 ≠ 1), Int.cast_smul_eq_zsmul,
    add_zero, zsmul_eq_mul, map_mul, map_intCast, AdditiveGroup.gaTangentLinearEquiv_apply]
  ring

/-- The tangent vector obtained by differentiating the numbered root subgroup at additive
parameter one. -/
def rootVector (k : Fin 4 ⊕ Fin 4) :
    Module.Dual (ZMod 2) (Bialgebra.CotangentSpace (ZMod 2) Q) :=
  (Derivation.cotangentLinearEquiv (B := ZMod 2)).symm
    (derivationComp (B := ZMod 2) (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom
      ((AdditiveGroup.gaTangentLinearEquiv (R := ZMod 2) (B := ZMod 2)).symm 1))

/-- Cotangent duality sends a root vector to the differential of its root parametrization. -/
@[simp↓]
theorem cotangentLinearEquiv_rootVector (k : Fin 4 ⊕ Fin 4) :
    Derivation.cotangentLinearEquiv (B := ZMod 2) (rootVector k) =
      derivationComp (B := ZMod 2) (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := ZMod 2) (B := ZMod 2)).symm 1) := by
  simp [rootVector]

/-- The matrix of a normalized numbered root vector is its integral Chevalley matrix
reduced modulo two. -/
-- Match the bundled quotient tangent space before simplification changes its presentation.
@[simp↓]
theorem tangentMatrix_rootVector (k : Fin 4 ⊕ Fin 4) :
    tangentMatrix (rootVector k) = (rootMatrix k).map (Int.cast : ℤ → ZMod 2) := by
  have hcomp : (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom.comp
      (Bialgebra.Quotient.mkBialgHom (J).toIdeal) = (generator (.inl k)).hom := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift]
  rw [tangentMatrix_apply, cotangentLinearEquiv_rootVector,
    HopfIdeal.quotientLieHom_apply, ← LinearMap.comp_apply, ← derivationComp_comp, hcomp,
    tangentMatrix_derivationComp_generator_inl, LinearEquiv.apply_symm_apply, one_smul]

/-- Every numbered root vector is nonzero, since its root subgroup is a closed immersion. -/
@[simp↓]
theorem rootVector_ne_zero (k : Fin 4 ⊕ Fin 4) : rootVector k ≠ 0 := by
  intro h
  have hd := congrArg (Derivation.cotangentLinearEquiv (B := ZMod 2)) h
  rw [cotangentLinearEquiv_rootVector, map_zero] at hd
  have hinj := derivationComp_injective_of_surjective (B := ZMod 2)
    (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom
    (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl k)
      (generator_surjective (.inl k)))
  have hz := hinj (hd.trans (map_zero _).symm)
  have hu := congrArg AdditiveGroup.gaTangentLinearEquiv hz
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
    (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hu)

/-- The weight-space criterion for the carrier's weight torus: a tangent matrix has only
entries whose integral weight difference is the prescribed character. -/
theorem mem_adjointWeightSpace_iff (α : Multiplicative (Fin 4 →₀ ℤ))
    (x : Module.Dual (ZMod 2) (Bialgebra.CotangentSpace (ZMod 2) Q)) :
    x ∈ Derivation.adjointWeightSpace
        (CommHopfAlgCat.commonKernelLift generator (.inr ())).hom α ↔
      ∀ i j, SplitTorus.weightCharacter (f4ShortRootWeight i - f4ShortRootWeight j) ≠ α →
        tangentMatrix x i j = 0 := by
  have hπ : (CommHopfAlgCat.commonKernelLift generator (.inr ())).hom.comp
      (Bialgebra.Quotient.mkBialgHom (J).toIdeal) =
        (GeneralLinear.weightTorusCoordinateMap (R := ZMod 2) f4ShortRootWeight).hom := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      CommHopfAlgCat.mkQuotient_comp_commonKernelLift, generator_inr,
      GeneralLinear.weightTorusBaseChangeCoordinateMap_eq]
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus J f4ShortRootWeight _ hπ α x

/-- Each numbered root vector has its prescribed signed-simple-root torus character. The integral
character is retained, rather than reducing the weight lattice modulo two. -/
theorem rootVector_mem_adjointWeightSpace (k : Fin 4 ⊕ Fin 4) :
    rootVector k ∈ Derivation.adjointWeightSpace
      (CommHopfAlgCat.commonKernelLift generator (.inr ())).hom
      (SplitTorus.weightCharacter (f4Root (f4SignedSimpleRootIndex k))) := by
  rw [mem_adjointWeightSpace_iff]
  intro i j h
  rw [tangentMatrix_rootVector]
  by_contra hne
  have hm : f4ShortRootAdjointMatrix (f4ModularRootVector (f4SignedSimpleRootIndex k)) i j ≠ 0 := by
    rw [← f4ShortRootSignedSimpleAdjointMatrix_eq_rootMatrix_map] at hne
    simpa only [f4ShortRootSignedSimpleAdjointMatrix_apply,
      f4ShortRootSignedSimpleAdjoint_apply, f4ShortRootLieIdealBasis_repr_apply,
      coe_f4ShortRootAdjoint_apply, f4ShortRootAdjointMatrix_apply] using hne
  have hw := f4ShortRootAdjointMatrix_root_weight_support (f4SignedSimpleRootIndex k) i j hm
  apply h
  congr 1
  rw [hw, add_sub_cancel_left]

end

end TauCeti.F4ShortRoot.PrimeField
