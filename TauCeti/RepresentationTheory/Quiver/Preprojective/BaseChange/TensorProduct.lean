/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor-product scalar extension of preprojective algebras

For a finite quiver and an algebra of commutative rings `k → l`, the additive preprojective
algebra commutes with scalar extension:
`l ⊗[k] Π_k(Q) ≃ₐ[l] Π_l(Q)`. The equivalence sends `a ⊗ x` to `a` times the coefficient
image of `x`, and its inverse sends each path class to the corresponding unit pure tensor.
No flatness or injectivity hypothesis is needed, and loops and multiple arrows are retained.

The universal-property construction is adapted from
`Zigzag.BaseChange.TensorProduct`: extend the existing coefficient map to the tensor product,
and construct its inverse by lifting the doubled paths through the preprojective relation.

## References

See Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
problem*, Section 1, for the additive preprojective presentation.
-/

public section

noncomputable section

namespace TauCeti

open _root_.Quiver PathAlgebra
open scoped TensorProduct

universe u v w z

variable {k : Type w} {l : Type z} [CommRing k] [CommRing l] [Algebra k l]
  (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

-- Restrict the target's scalar action only for the tensor-product universal property.
private abbrev coefficientAlgebra : Algebra k (preprojectiveAlgebra l Q) :=
  Algebra.compHom _ (algebraMap k l)

attribute [local instance] coefficientAlgebra

private abbrev coefficientScalarTower : IsScalarTower k l (preprojectiveAlgebra l Q) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] coefficientScalarTower

private def coefficientAlgHom :
    preprojectiveAlgebra k Q →ₐ[k] preprojectiveAlgebra l Q where
  __ := RingHom.preprojectiveBaseChange (algebraMap k l)
  commutes' a := by
    exact (RingHom.preprojectiveBaseChange_algebraMap (Q := Q) (algebraMap k l) a).trans
      (IsScalarTower.algebraMap_apply k l _ a).symm

private def scalarExtension :
    l ⊗[k] preprojectiveAlgebra k Q →ₐ[l] preprojectiveAlgebra l Q :=
  AlgHom.liftEquiv k l _ _ (coefficientAlgHom (k := k) (l := l) Q)

private theorem scalarExtension_tmul (a : l) (x : preprojectiveAlgebra k Q) :
    scalarExtension (k := k) (l := l) Q (a ⊗ₜ[k] x) =
      a • RingHom.preprojectiveBaseChange (algebraMap k l) x :=
  AlgHom.liftEquiv_tmul (coefficientAlgHom (k := k) (l := l) Q) a x

private def tensorPathAlgHom :
    pathAlgebra l (Symmetrify Q) →ₐ[l] l ⊗[k] preprojectiveAlgebra k Q := by
  let g : pathAlgebra k (Symmetrify Q) →ₐ[k] l ⊗[k] preprojectiveAlgebra k Q :=
    Algebra.TensorProduct.includeRight.comp (preprojectiveMk k Q)
  refine liftAlgHom l (fun p => g (ofPath p)) ?_ ?_ ?_
  · intro a b d p q
    rw [← map_mul, ofPath_mul_ofPath_of_comp]
  · intro p q hpq
    rw [← map_mul, ofPath_mul_ofPath_of_not_composable hpq, map_zero]
  · let _ := Fintype.ofFinite (Symmetrify Q)
    rw [← map_sum]
    simp only [← vertexIdempotent_eq_ofPath, ← one_def, map_one]

private theorem tensorPathAlgHom_ofPath (p : Quiver.TotalPath (Symmetrify Q)) :
    tensorPathAlgHom (k := k) (l := l) Q (ofPath p) =
      1 ⊗ₜ[k] preprojectiveMk k Q (ofPath p) := by
  dsimp only [tensorPathAlgHom]
  refine liftAlgHom_ofPath l _ ?_ ?_ _ p
  · intro a b d p q
    rw [← map_mul, ofPath_mul_ofPath_of_comp]
  · intro p q hpq
    rw [← map_mul, ofPath_mul_ofPath_of_not_composable hpq, map_zero]

private theorem tensorPathAlgHom_relator :
    tensorPathAlgHom (k := k) (l := l) Q (preprojectiveRelator l Q) = 0 := by
  rw [preprojectiveRelator_def]
  simp only [map_sum, map_sub, headBacktrackElem_def, tailBacktrackElem_def,
    tensorPathAlgHom_ofPath]
  simpa only [preprojectiveRelator_def, headBacktrackElem_def, tailBacktrackElem_def,
    map_sum, map_sub, TensorProduct.tmul_sum, TensorProduct.tmul_sub,
    TensorProduct.tmul_zero] using
      congrArg (fun x => (1 : l) ⊗ₜ[k] x) (preprojectiveMk_preprojectiveRelator k Q)

private def scalarExtensionInverse :
    preprojectiveAlgebra l Q →ₐ[l] l ⊗[k] preprojectiveAlgebra k Q :=
  preprojectiveLift (tensorPathAlgHom (k := k) (l := l) Q)
    (tensorPathAlgHom_relator (k := k) (l := l) Q)

private theorem scalarExtensionInverse_ofPath (p : Quiver.TotalPath (Symmetrify Q)) :
    scalarExtensionInverse (k := k) (l := l) Q (preprojectiveMk l Q (ofPath p)) =
      1 ⊗ₜ[k] preprojectiveMk k Q (ofPath p) := by
  rw [scalarExtensionInverse, preprojectiveLift_preprojectiveMk, tensorPathAlgHom_ofPath]

private theorem scalarExtension_leftInverse :
    (scalarExtensionInverse (k := k) (l := l) Q).comp (scalarExtension (k := k) (l := l) Q) =
      AlgHom.id l (l ⊗[k] preprojectiveAlgebra k Q) := by
  apply Algebra.TensorProduct.ext_ring
  apply (AlgHom.cancel_right (preprojectiveMk_surjective k Q)).mp
  apply PathAlgebra.algHom_ext k
  intro p
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
  simp only [scalarExtension_tmul, one_smul,
    RingHom.preprojectiveBaseChange_preprojectiveMk_ofPath, scalarExtensionInverse_ofPath]

private theorem scalarExtension_rightInverse :
    (scalarExtension (k := k) (l := l) Q).comp (scalarExtensionInverse (k := k) (l := l) Q) =
      AlgHom.id l (preprojectiveAlgebra l Q) := by
  apply (AlgHom.cancel_right (preprojectiveMk_surjective l Q)).mp
  apply PathAlgebra.algHom_ext l
  intro p
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  simp only [scalarExtensionInverse_ofPath, scalarExtension_tmul, one_smul,
    RingHom.preprojectiveBaseChange_preprojectiveMk_ofPath]

/-- Scalar extension of the additive preprojective algebra is the preprojective algebra over
the extended coefficient ring, for any finite quiver, including loops and multiple arrows. -/
def preprojectiveScalarExtensionEquiv :
    l ⊗[k] preprojectiveAlgebra k Q ≃ₐ[l] preprojectiveAlgebra l Q :=
  AlgEquiv.ofAlgHom (scalarExtension (k := k) (l := l) Q)
    (scalarExtensionInverse (k := k) (l := l) Q)
    (scalarExtension_rightInverse (k := k) (l := l) Q)
    (scalarExtension_leftInverse (k := k) (l := l) Q)

-- Keep these characteristic equations as named rewrites: evaluating either direction eagerly
-- can prevent the generic `AlgEquiv` inverse rules from matching the bundled applications.

/-- The scalar-extension equivalence sends a pure tensor to its scalar times the coefficient
image of its preprojective class. -/
theorem preprojectiveScalarExtensionEquiv_tmul (a : l) (x : preprojectiveAlgebra k Q) :
    preprojectiveScalarExtensionEquiv (k := k) (l := l) Q (a ⊗ₜ[k] x) =
      a • RingHom.preprojectiveBaseChange (algebraMap k l) x := by
  rw [preprojectiveScalarExtensionEquiv, AlgEquiv.ofAlgHom_apply, scalarExtension_tmul]

/-- The inverse scalar-extension equivalence sends a coefficient image to its unit pure tensor. -/
theorem preprojectiveScalarExtensionEquiv_symm_baseChange (x : preprojectiveAlgebra k Q) :
    (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).symm
      (RingHom.preprojectiveBaseChange (algebraMap k l) x) = 1 ⊗ₜ[k] x := by
  apply (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).injective
  rw [AlgEquiv.apply_symm_apply, preprojectiveScalarExtensionEquiv_tmul, one_smul]

/-- The inverse scalar-extension equivalence sends each doubled path class to the unit pure
tensor of that path class over the original coefficient ring. -/
theorem preprojectiveScalarExtensionEquiv_symm_preprojectiveMk_ofPath
    (p : Quiver.TotalPath (Symmetrify Q)) :
    (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).symm
      (preprojectiveMk l Q (ofPath p)) = 1 ⊗ₜ[k] preprojectiveMk k Q (ofPath p) := by
  apply (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).injective
  rw [AlgEquiv.apply_symm_apply, preprojectiveScalarExtensionEquiv_tmul,
    RingHom.preprojectiveBaseChange_preprojectiveMk_ofPath, one_smul]

end TauCeti
