/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Differential
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.ClosedGenerators

/-!
# Root-subgroup differentials of the short-root G₂ carrier

For every numbered positive or negative simple root, the root-subgroup differential identifies
`Lie(𝔾ₐ)` with the corresponding adjoint root line of the short-root carrier over `𝔽₃`.
The unit additive tangent vector maps to the normalized root vector. After extension to every
commutative `𝔽₃`-algebra, the differential remains injective and its image is exactly the scalar
extension of that root line. Thus the root-space generators and root-subgroup parameters have
compatible normalizations, including over nonreduced coefficient algebras.

These results concern the explicit carrier, not an identification with the pinned simply connected
group scheme of type `G₂`. They supply the differential normalization for such a comparison;
no Borel subgroup or pinning is constructed here.

The comparison uses the root lines of
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space` and the general additive differential
API. Its interface follows `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Adjoint`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open scoped TensorProduct

universe u

noncomputable section

/-- The numbered root-subgroup differential identifies the additive tangent module with its
adjoint root space over `𝔽₃`. -/
def rootDifferentialEquiv (k : Fin 2 ⊕ Fin 2) :
    Derivation (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
        (Bialgebra.CounitAlgebra (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
          (ZMod 3)) ≃ₗ[ZMod 3]
      Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
        (SplitTorus.weightCharacter (DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 k)) :=
  AdditiveGroup.gaTangentLinearEquiv.trans (rootSpaceEquiv k)

/-- Forgetting the root-space restriction gives the actual numbered root-subgroup differential,
expressed through cotangent duality. Use this for rewriting: simplification of the rank-indexed
root character prevents `simp` from matching the bundled subtype coercion. -/
theorem rootDifferentialEquiv_apply_coe (k : Fin 2 ⊕ Fin 2)
    (d : Derivation (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
      (Bialgebra.CounitAlgebra (ZMod 3) (AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
        (ZMod 3))) :
    (rootDifferentialEquiv k d : Module.Dual (ZMod 3)
      (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra)) =
      (Derivation.cotangentLinearEquiv (B := ZMod 3)).symm
        (derivationComp (B := ZMod 3)
          (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom d) := by
  apply (Derivation.cotangentLinearEquiv (B := ZMod 3)).injective
  rw [rootDifferentialEquiv]
  -- The root character uses the definitionally rank-two index of the G₂ diagram.
  erw [LinearEquiv.trans_apply, rootSpaceEquiv_apply_coe]
  rw [map_smul, cotangentLinearEquiv_rootVector, LinearEquiv.apply_symm_apply]
  have hd : d = AdditiveGroup.gaTangentLinearEquiv d •
      (AdditiveGroup.gaTangentLinearEquiv (R := ZMod 3) (B := ZMod 3)).symm 1 := by
    apply AdditiveGroup.gaTangentLinearEquiv.injective
    -- The additive coordinate algebra is the bundled symmetric algebra.
    erw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  conv_rhs => rw [hd]
  rw [map_smul]

/-- The inverse differential reads the root-space coordinate as an additive tangent parameter.
Use this for rewriting; leaving the inverse bundled preserves cancellation by `simp`. -/
theorem rootDifferentialEquiv_symm_apply (k : Fin 2 ⊕ Fin 2)
    (x : Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
      (SplitTorus.weightCharacter (DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 k))) :
    (rootDifferentialEquiv k).symm x =
      AdditiveGroup.gaTangentLinearEquiv.symm ((rootSpaceEquiv k).symm x) := by
  rw [rootDifferentialEquiv]
  -- The root character uses the definitionally rank-two index of the G₂ diagram.
  erw [LinearEquiv.symm_trans_apply]

variable {B : Type u} [CommRing B] [Algebra (ZMod 3) B]

/-- The root-subgroup differential remains injective over every commutative coefficient algebra,
including algebras with nilpotents. -/
theorem derivationComp_rootSubgroup_injective (k : Fin 2 ⊕ Fin 2) :
    Function.Injective (derivationComp (B := B)
      (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom) :=
  derivationComp_injective_of_surjective _
    (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl k)
      (generator_surjective (.inl k)))

/-- Coefficient extension carries the normalized root vector to the root-subgroup differential
with the same parameter. This is for rewriting; the general tensor simp rule is
`Derivation.tangentScalarExtensionEquiv_tmul`. -/
theorem tangentScalarExtensionEquiv_tmul_rootVector (k : Fin 2 ⊕ Fin 2) (c : B) :
    Derivation.tangentScalarExtensionEquiv (R := ZMod 3) (A := carrierAlgebra) (B := B)
        (c ⊗ₜ[ZMod 3] rootVector k) =
      derivationComp (B := B) (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := ZMod 3) (B := B)).symm c) := by
  have hroot := congrArg (Derivation.cotangentLinearEquiv (B := ZMod 3)).symm
    (cotangentLinearEquiv_rootVector k)
  rw [LinearEquiv.symm_apply_apply] at hroot
  rw [hroot]
  exact AdditiveGroup.tangentScalarExtensionEquiv_tmul_derivationComp c _

/-- The image of a numbered root-subgroup differential over every coefficient algebra is exactly
the scalar extension of its prime-field adjoint root line. -/
theorem range_derivationCompLieHom_rootSubgroup_eq_adjointWeightSpace_baseChange
    (k : Fin 2 ⊕ Fin 2) :
    (derivationCompLieHom (B := B)
        (CommHopfAlgCat.commonKernelLift generator (.inl k)).hom).range.toSubmodule =
      ((Derivation.adjointWeightSpace weightTorusCoordinateMap.hom
        (SplitTorus.weightCharacter
          (DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 k))).baseChange B).map
            (Derivation.tangentScalarExtensionEquiv
              (R := ZMod 3) (A := carrierAlgebra) (B := B)).toLinearMap := by
  rw [AdditiveGroup.range_derivationCompLieHom_eq_span,
    adjointWeightSpace_rootGeneratorWeight_eq_span,
    Submodule.baseChange_span, Set.image_singleton, Submodule.map_span, Set.image_singleton]
  simp only [LinearEquiv.coe_coe]
  -- `Submodule.map_span` prints the quotient presentation of the carrier's cotangent space.
  erw [tangentScalarExtensionEquiv_tmul_rootVector]

end

end TauCeti.G2ShortRoot.PrimeField
