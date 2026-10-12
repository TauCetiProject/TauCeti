/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Adjoint.Classification
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Differential

/-!
# Adjoint roots, root spaces, and root-subgroup differentials of `SLₙ`

The differential of the elementary root subgroup `xᵢⱼ : 𝔾ₐ → SLₙ` identifies
`Lie(𝔾ₐ)` with the corresponding weight space of the integral adjoint comodule.
The additive unit tangent vector maps to the normalized root vector `Eᵢⱼ`.
This connects the root subgroup and root-vector normalizations used in a pinning.

The identification persists after extension to every commutative coefficient algebra:
the differential's image is the scalar extension of the adjoint root line. The base
ring and coefficient algebra may have nilpotents or zero divisors.

Over every nontrivial commutative base ring, the nontrivial adjoint weights of
`SL_{r+1}` are exactly the roots of `diagonalRootDatum`. The root indices are
canonically equivalent to the full nontrivial weight set, identifying the root
lines to which a pinning assigns generators.

The calculation combines `tangentMatrix_derivationComp_rootSubgroup` with
`adjointWeightSpace_root_eq_span` and the existing cotangent-duality and tangent
scalar-extension equivalences.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
* B. Conrad, *Reductive Group Schemes*, §5.1 (root subgroups and pinnings).
* The root-index API follows
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Adjoint`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The root-subgroup differential sends the additive tangent parameter to that
multiple of the normalized adjoint root vector, in the cotangent-dual model. -/
@[simp]
theorem cotangentLinearEquiv_symm_derivationComp_rootSubgroup
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) R)) :
    (Derivation.cotangentLinearEquiv (R := R)
      (A := coordinateHopfAlgebra R (r + 1)) (B := R)).symm
        (derivationComp (B := R) (rootSubgroupCoordinateMap (R := R) p.2).hom d) =
      AdditiveGroup.gaTangentLinearEquiv d • rootVector (R := R) p := by
  apply (Derivation.cotangentLinearEquiv (R := R)
    (A := coordinateHopfAlgebra R (r + 1)) (B := R)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (tangentLieEquivSl (R := R) (B := R) (r + 1)).injective
  simp only [LieEquiv.coe_toLieHom]
  -- Both Lie equivalences have the quotient-indexed coordinate presentation.
  erw [tangentLieEquivSl_apply (R := R) (B := R),
    tangentLieEquivSl_apply (R := R) (B := R)]
  -- Cotangent duality uses the quotient-indexed scalar structure.
  erw [map_smul]
  rw [map_smul, tangentMatrix_cotangentLinearEquiv_rootVector,
    tangentMatrix_derivationComp_rootSubgroup]
  simpa only [smul_eq_mul, mul_one] using
    ((LieAlgebra.SpecialLinear.single p.1.1 p.1.2 p.2).map_smul
      (AdditiveGroup.gaTangentLinearEquiv d) 1)

/-- The differential of the root subgroup, as an isomorphism onto the adjoint
root space over the base ring. -/
def rootDifferentialEquiv (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) R) ≃ₗ[R]
      Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
        (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) :=
  (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).trans (rootSpaceEquiv p)

/-- Forgetting the weight-space restriction recovers the actual root-subgroup
differential, expressed by cotangent duality. -/
@[simp]
theorem rootDifferentialEquiv_apply_coe
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) R)) :
    (rootDifferentialEquiv (R := R) p d :
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R (r + 1)))) =
      (Derivation.cotangentLinearEquiv (R := R)
        (A := coordinateHopfAlgebra R (r + 1)) (B := R)).symm
          (derivationComp (B := R) (rootSubgroupCoordinateMap (R := R) p.2).hom d) := by
  rw [rootDifferentialEquiv]
  -- The character lattice is represented by the indexed exponent module.
  erw [LinearEquiv.trans_apply, rootSpaceEquiv_apply_coe]
  rw [cotangentLinearEquiv_symm_derivationComp_rootSubgroup]

/-- The inverse differential recovers the additive tangent parameter of a root
vector from its root-space coordinate. -/
@[simp]
theorem rootDifferentialEquiv_symm_apply
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (x : Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))) :
    (rootDifferentialEquiv (R := R) p).symm x =
      (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm
        ((rootSpaceEquiv (R := R) p).symm x) := by
  rw [rootDifferentialEquiv]
  -- The character lattice is represented by the indexed exponent module.
  erw [LinearEquiv.symm_trans_apply]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- After coefficient extension, the root vector with parameter `c` is the
root-subgroup differential of the additive tangent vector with parameter `c`.
For simplification, `Derivation.tangentScalarExtensionEquiv_tmul` is the general
pure-tensor normal form; this identity is for explicit rewriting. -/
theorem tangentScalarExtensionEquiv_tmul_rootVector
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) (c : B) :
    Derivation.tangentScalarExtensionEquiv
        (R := R) (A := coordinateHopfAlgebra R (r + 1)) (B := B)
        (c ⊗ₜ[R] rootVector (R := R) p) =
      derivationComp (B := B) (rootSubgroupCoordinateMap (R := R) p.2).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm c) := by
  apply (tangentLieEquivSl (R := R) (B := B) (r + 1)).injective
  simp only [LieEquiv.coe_toLieHom]
  -- Both Lie equivalences have the quotient-indexed coordinate presentation.
  erw [tangentLieEquivSl_apply (R := R) (B := B),
    tangentLieEquivSl_apply (R := R) (B := B)]
  -- Expose the quotient-indexed coordinate presentation for tangent scalar extension.
  erw [Derivation.tangentScalarExtensionEquiv_tmul]
  rw [map_smul, tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [Submodule.coe_smul, tangentMatrix_mapValue_coe,
    tangentMatrix_cotangentLinearEquiv_rootVector, LieAlgebra.SpecialLinear.val_single]
  simp only [LieAlgebra.SpecialLinear.val_single, Matrix.map_single, map_one,
    Matrix.smul_single, smul_eq_mul, mul_one]

/-- Over every commutative coefficient algebra, the image of the root-subgroup
differential is exactly the scalar extension of its integral adjoint root space. -/
theorem range_derivationCompLieHom_rootSubgroup_eq_adjointWeightSpace_baseChange
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (derivationCompLieHom (B := B)
        (rootSubgroupCoordinateMap (R := R) p.2).hom).range.toSubmodule =
      ((Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
          (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))).baseChange B).map
        (Derivation.tangentScalarExtensionEquiv
          (R := R) (A := coordinateHopfAlgebra R (r + 1)) (B := B)).toLinearMap := by
  rw [range_derivationCompLieHom_rootSubgroup_eq_span,
    adjointWeightSpace_root_eq_span]
  rw [Submodule.baseChange_span, Set.image_singleton, Submodule.map_span, Set.image_singleton]
  congr 1
  exact congrArg (fun d => ({d} : Set _))
    (tangentScalarExtensionEquiv_tmul_rootVector (R := R) p (1 : B)).symm

variable [Nontrivial R]

/-- Every root of the diagonal root datum occurs as a nontrivial adjoint weight of
`SL_{r+1}`. -/
@[simp↓ 1100]
theorem ofAdd_root_mem_nontrivialAdjointWeights
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) ∈
      Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom := by
  rw [Derivation.mem_nontrivialAdjointWeights]
  refine ⟨?_, ?_⟩
  · intro h
    exact (diagonalRootDatum.{u} r).ne_zero p (congrArg Multiplicative.toAdd h)
  · -- The torus characters are stored as the indexed copy of the exponent lattice.
    erw [adjointWeightSpace_root_eq_span]
    exact (Submodule.ne_bot_iff _).mpr
      ⟨rootVector p, Submodule.mem_span_singleton_self _, rootVector_ne_zero p⟩

/-- The nontrivial adjoint weights of `SL_{r+1}` relative to its diagonal torus are
exactly the roots of its diagonal root datum. No field or reducedness assumption is needed. -/
theorem mem_nontrivialAdjointWeights_iff_exists_diagonalRoot
    (α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) :
    α ∈ Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom ↔
      ∃ p : SplitTorus.CoordinateRootIndex (Fin (r + 1)),
        α = Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) := by
  constructor
  · rw [Derivation.mem_nontrivialAdjointWeights]
    rintro ⟨hα, hspace⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hspace
    have hmatrix : (tangentMatrix (r + 1) (Derivation.cotangentLinearEquiv (B := R) x) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) R) ≠ 0 := by
      intro hzero
      apply hx0
      apply (Derivation.cotangentLinearEquiv (R := R)
        (A := coordinateHopfAlgebra R (r + 1)) (B := R)).injective
      apply (tangentLieEquivSl (R := R) (B := R) (r + 1)).injective
      simp only [map_zero, LieEquiv.coe_toLieHom]
      -- The Lie equivalence stores the quotient-indexed coordinate presentation.
      erw [tangentLieEquivSl_apply]
      exact Subtype.ext hzero
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hmatrix
    obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
    have hweight := weightCharacter_eq_of_mem_adjointWeightSpace_of_apply_ne_zero hx hij
    have hne : i ≠ j := by
      rintro rfl
      apply hα
      rw [← hweight]
      apply Multiplicative.toAdd.injective
      ext k
      simp
    refine ⟨⟨(i, j), hne⟩, ?_⟩
    exact hweight.symm.trans
      ((weightCharacter_diagonalTorusWeight_sub_eq_root_iff ⟨(i, j), hne⟩ i j).mpr
        ⟨rfl, rfl⟩)
  · rintro ⟨p, rfl⟩
    exact ofAdd_root_mem_nontrivialAdjointWeights p

/-- The root set of the diagonal root datum is the entire nontrivial adjoint weight
set of the special linear group. -/
theorem range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights :
    Set.range (fun p : SplitTorus.CoordinateRootIndex (Fin (r + 1)) ↦
        Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) =
      Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom := by
  ext α
  rw [Set.mem_range, mem_nontrivialAdjointWeights_iff_exists_diagonalRoot]
  exact exists_congr fun p ↦ eq_comm

/-- Ordered pairs of distinct matrix indices canonically index all nontrivial adjoint
weights of `SL_{r+1}`. -/
def diagonalRootIndexEquivNontrivialAdjointWeights :
    SplitTorus.CoordinateRootIndex (Fin (r + 1)) ≃
      {α // α ∈ Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom} :=
  (Equiv.ofInjective
    (fun p ↦ Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))
    (Multiplicative.ofAdd.injective.comp (diagonalRootDatum.{u} r).root.injective)).trans
    (Set.equivOfEq range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights)

/-- The root-index equivalence sends an index to its root character. -/
@[simp]
theorem diagonalRootIndexEquivNontrivialAdjointWeights_apply
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    (diagonalRootIndexEquivNontrivialAdjointWeights (R := R) p :
      Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) =
      Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) :=
  (rfl)

end

end TauCeti.SpecialLinear
