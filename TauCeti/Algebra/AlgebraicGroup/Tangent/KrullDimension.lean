/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
public import TauCeti.AlgebraicGeometry.TangentSpace.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Krull dimension and Lie dimension of an affine group

For an affine group of finite type over an algebraically closed field, translation identifies
the heights of all maximal ideals with the height of the augmentation ideal. Thus the dimension
of the group is its local dimension at the identity. Krull's height theorem bounds this by the
dimension of its Lie algebra, with equality exactly when the local ring at the identity is
regular. No reducedness, smoothness, or connectedness is assumed.

These are the dimension comparisons underlying the tangent-space criterion for smoothness.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 11.
-/

public section

open AlgebraicGeometry

namespace TauCeti.HopfAlgebra

section CommRing

variable {k H : Type*} [CommRing k] [CommRing H] [_root_.HopfAlgebra k H]

/-- Translation identifies the height of the ideal of any rational point with the height of
the augmentation ideal. -/
theorem height_kernel_eq_height_augmentation (g : WithConv (H →ₐ[k] k)) :
    (RingHom.ker (g.ofConv : H →+* k)).height = (Bialgebra.AugmentationIdeal k H).height := by
  have h : (Bialgebra.AugmentationIdeal k H).comap
      (rightTranslationAlgEquiv g).toRingEquiv = RingHom.ker (g.ofConv : H →+* k) := by
    exact (RingHom.comap_ker (_root_.Bialgebra.counitAlgHom k H).toRingHom
      (rightTranslationAlgEquiv g).toAlgHom.toRingHom).trans
      (congrArg (fun f : H →ₐ[k] k ↦ RingHom.ker f.toRingHom)
      ((congrArg ((_root_.Bialgebra.counitAlgHom k H).comp)
        (rightTranslationAlgEquiv_toAlgHom g)).trans
          (counitAlgHom_comp_rightTranslationAlgHom g)))
  rw [← h]
  exact (rightTranslationAlgEquiv g).toRingEquiv.height_comap _

end CommRing

variable {k H : Type*} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [IsAlgClosed k] [Algebra.FiniteType k H]

/-- The dimension of an affine group over an algebraically closed field equals the height of
its augmentation ideal. -/
theorem ringKrullDim_eq_height_augmentation :
    ringKrullDim H = (Bialgebra.AugmentationIdeal k H).height := by
  apply le_antisymm
  · apply (ringKrullDim_le_iff_isMaximal_height_le _).mpr
    intro m hm
    let _ := hm
    let _ : Field (H ⧸ m) := Ideal.Quotient.field m
    let _ : Module.Finite k (H ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (H ⧸ m)
    let ι : H ⧸ m →ₐ[k] k := IsAlgClosed.lift
    let g : H →ₐ[k] k := ι.comp (Ideal.Quotient.mkₐ k m)
    have hker : RingHom.ker (g : H →+* k) = m := by
      exact (RingHom.ker_comp_of_injective (Ideal.Quotient.mk m)
        (f := ι.toRingHom) ι.injective).trans (Ideal.mk_ker)
    rw [← hker, height_kernel_eq_height_augmentation]
  · exact Ideal.height_le_ringKrullDim_of_isPrime

/-- The local ring at the identity of a finite-type affine group over an algebraically closed
field has the same dimension as the group. -/
@[simp]
theorem ringKrullDim_augmentationStalk :
    ringKrullDim ((Spec (CommRingCat.of H)).presheaf.stalk (Bialgebra.augmentationPoint k H)) =
      ringKrullDim H := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (Bialgebra.AugmentationIdeal k H),
    ringKrullDim_eq_height_augmentation (k := k)]

/-- The dimension of a finite-type affine group over an algebraically closed field is at most
the dimension of its Lie algebra. This includes non-reduced group schemes. -/
theorem ringKrullDim_le_finrank_lie :
    ringKrullDim H ≤
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  rw [Derivation.finrank_eq_finrank_cotangentSpace, ← ringKrullDim_augmentationStalk (k := k)]
  exact AlgHom.ringKrullDim_kernelStalk_le_finrank_kernelCotangent
    (_root_.Bialgebra.counitAlgHom k H)

/-- Lie dimension equals group dimension exactly when the local ring at the identity is
regular, for a finite-type affine group over an algebraically closed field. -/
theorem isRegularLocalRing_augmentationStalk_iff :
    IsRegularLocalRing
        ((Spec (CommRingCat.of H)).presheaf.stalk (Bialgebra.augmentationPoint k H)) ↔
      (Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) : WithBot ℕ∞) =
        ringKrullDim H := by
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  rw [AlgHom.isRegularLocalRing_kernelStalk_iff,
    Derivation.finrank_eq_finrank_cotangentSpace, ringKrullDim_augmentationStalk]

end TauCeti.HopfAlgebra
