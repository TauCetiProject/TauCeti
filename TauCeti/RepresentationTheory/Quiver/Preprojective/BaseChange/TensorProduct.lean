/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.BaseChange.TensorProduct

/-!
# Tensor-product scalar extension of preprojective algebras

For a finite quiver and an algebra of commutative rings `k → l`, the additive preprojective
algebra commutes with scalar extension:
`l ⊗[k] Π_k(Q) ≃ₐ[l] Π_l(Q)`. The equivalence sends `a ⊗ x` to `a` times the coefficient
image of `x`, and its inverse sends each path class to the corresponding unit pure tensor.
No flatness or injectivity hypothesis is needed, and loops and multiple arrows are retained.

The scalar-extension construction is adapted from `Zigzag.BaseChange.TensorProduct`.
Its inverse uses the shared path-algebra tensor lift to send doubled paths to unit pure
tensors, then descends through the preprojective relation.

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

private theorem tensorLiftAlgHom_relator :
    tensorLiftAlgHom (l := l) (preprojectiveMk k Q) (preprojectiveRelator l Q) = 0 := by
  rw [preprojectiveRelator_def]
  simp only [map_sum, map_sub, headBacktrackElem_def, tailBacktrackElem_def,
    tensorLiftAlgHom_ofPath]
  simpa only [preprojectiveRelator_def, headBacktrackElem_def, tailBacktrackElem_def,
    map_sum, map_sub, TensorProduct.tmul_sum, TensorProduct.tmul_sub,
    TensorProduct.tmul_zero] using
      congrArg (fun x => (1 : l) ⊗ₜ[k] x) (preprojectiveMk_preprojectiveRelator k Q)

private def scalarExtensionInverse :
    preprojectiveAlgebra l Q →ₐ[l] l ⊗[k] preprojectiveAlgebra k Q :=
  preprojectiveLift (tensorLiftAlgHom (l := l) (preprojectiveMk k Q))
    (tensorLiftAlgHom_relator (k := k) (l := l) Q)

private theorem scalarExtensionInverse_ofPath (p : Quiver.TotalPath (Symmetrify Q)) :
    scalarExtensionInverse (k := k) (l := l) Q (preprojectiveMk l Q (ofPath p)) =
      1 ⊗ₜ[k] preprojectiveMk k Q (ofPath p) := by
  rw [scalarExtensionInverse, preprojectiveLift_preprojectiveMk, tensorLiftAlgHom_ofPath]

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

/-- The scalar-extension equivalence sends a pure tensor to its scalar times the coefficient
image of its preprojective class. -/
@[simp]
theorem preprojectiveScalarExtensionEquiv_tmul (a : l) (x : preprojectiveAlgebra k Q) :
    preprojectiveScalarExtensionEquiv (k := k) (l := l) Q (a ⊗ₜ[k] x) =
      a • RingHom.preprojectiveBaseChange (algebraMap k l) x := by
  rw [preprojectiveScalarExtensionEquiv, AlgEquiv.ofAlgHom_apply, scalarExtension_tmul]

/-- The inverse scalar-extension equivalence sends a coefficient image to its unit pure tensor. -/
@[simp]
theorem preprojectiveScalarExtensionEquiv_symm_baseChange (x : preprojectiveAlgebra k Q) :
    (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).symm
      (RingHom.preprojectiveBaseChange (algebraMap k l) x) = 1 ⊗ₜ[k] x := by
  apply (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).injective
  rw [AlgEquiv.apply_symm_apply, preprojectiveScalarExtensionEquiv_tmul, one_smul]

/-- The inverse scalar-extension equivalence sends a scaled coefficient image to its pure
tensor. -/
-- Run before generic scalar-map simplification, which leaves a scalar outside a unit tensor
-- and prevents ordinary simplification of inverse cancellation on pure tensors.
@[simp 1100]
theorem preprojectiveScalarExtensionEquiv_symm_smul_baseChange
    (a : l) (x : preprojectiveAlgebra k Q) :
    (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).symm
      (a • RingHom.preprojectiveBaseChange (algebraMap k l) x) = a ⊗ₜ[k] x := by
  rw [map_smul, preprojectiveScalarExtensionEquiv_symm_baseChange,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The inverse scalar-extension equivalence sends each doubled path class to the unit pure
tensor of that path class over the original coefficient ring. -/
@[simp]
theorem preprojectiveScalarExtensionEquiv_symm_preprojectiveMk_ofPath
    (p : Quiver.TotalPath (Symmetrify Q)) :
    (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).symm
      (preprojectiveMk l Q (ofPath p)) = 1 ⊗ₜ[k] preprojectiveMk k Q (ofPath p) := by
  apply (preprojectiveScalarExtensionEquiv (k := k) (l := l) Q).injective
  rw [AlgEquiv.apply_symm_apply, preprojectiveScalarExtensionEquiv_tmul,
    RingHom.preprojectiveBaseChange_preprojectiveMk_ofPath, one_smul]

end TauCeti
