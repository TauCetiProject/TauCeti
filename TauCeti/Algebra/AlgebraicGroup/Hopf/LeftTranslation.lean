/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-!
# Left translations of an affine group

Left translation by a base-valued point is an automorphism of the coordinate algebra.
Its pullback is convolution of the constant point with the universal point, in that order.
This is the source translation that intertwines a representation's orbit map with the
linear action on its target. The formula holds on points over every commutative algebra.
Equivalently, left translation applies the point to the first tensor factor of the
comultiplication, and it fixes a point valued in an algebra with injective structure map only
when the translating point is the identity.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2 and 7.c.
* Formal precursors: `HopfAlgebra.rightTranslationAlgEquiv` and
  `HopfAlgebra.pointConjugationBialgEquiv`.
-/

public section

open WithConv

namespace TauCeti.HopfAlgebra

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.HopfAlgebra R H]

/-- Pullback by left translation by a base-valued point. -/
noncomputable def leftTranslationAlgEquiv (g : WithConv (H →ₐ[R] R)) : H ≃ₐ[R] H :=
  (pointConjugationBialgEquiv g).toAlgEquiv.trans (rightTranslationAlgEquiv g)

/-- The coordinate map of left translation is convolution of the constant translating
point with the universal point. -/
theorem toConv_leftTranslationAlgEquiv (g : WithConv (H →ₐ[R] R)) :
    toConv (leftTranslationAlgEquiv g).toAlgHom =
      AlgHom.mapValue (Algebra.ofId R H) g * toConv (AlgHom.id R H) := by
  have hcomp : (leftTranslationAlgEquiv g).toAlgHom =
      (rightTranslationAlgEquiv g).toAlgHom.comp (pointConjugationAlgHom g) := by
    rw [← pointConjugationBialgEquiv_toAlgHom]
    rfl
  rw [hcomp, comp_pointConjugationAlgHom, toConv_rightTranslationAlgEquiv]
  simp [mul_assoc]

/-- Left translation evaluates by applying the point to the first tensor factor of the
comultiplication. -/
theorem leftTranslationAlgEquiv_apply (g : WithConv (H →ₐ[R] R)) (x : H) :
    leftTranslationAlgEquiv g x =
      TensorProduct.lid R H (g.ofConv.toLinearMap.rTensor H (Coalgebra.comul x)) := by
  have h := DFunLike.congr_fun (congrArg ofConv (toConv_leftTranslationAlgEquiv g)) x
  rw [ofConv_toConv, AlgHom.convMul_apply] at h
  refine h.trans ?_
  induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.smul_def]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Precomposition by left translation multiplies an arbitrary algebra-valued point
on the left by the constant translating point. -/
theorem toConv_comp_leftTranslationAlgEquiv {A : Type*} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    toConv (x.ofConv.comp (leftTranslationAlgEquiv g).toAlgHom) =
      AlgHom.mapValue (Algebra.ofId R A) g * x := by
  have h := congrArg (AlgHom.mapValue x.ofConv) (toConv_leftTranslationAlgEquiv g)
  rw [map_mul, WithConv.mapValue_algebraOfId] at h
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id] using h

/-- Left translation by the identity point is the identity algebra automorphism. -/
@[simp]
theorem leftTranslationAlgEquiv_one :
    leftTranslationAlgEquiv (1 : WithConv (H →ₐ[R] R)) = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply toConv_injective
  rw [toConv_leftTranslationAlgEquiv, map_one, one_mul]
  rfl

/-- Pullback by left translation reverses the order of convolution products. -/
@[simp]
theorem leftTranslationAlgEquiv_mul (g h : WithConv (H →ₐ[R] R)) :
    leftTranslationAlgEquiv (g * h) =
      leftTranslationAlgEquiv h * leftTranslationAlgEquiv g := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply toConv_injective
  -- The monoid hom identifies multiplication of equivalences with composition of algebra maps.
  rw [show (leftTranslationAlgEquiv h * leftTranslationAlgEquiv g).toAlgHom =
    (leftTranslationAlgEquiv h).toAlgHom.comp (leftTranslationAlgEquiv g).toAlgHom from
      map_mul (AlgEquiv.toAlgHomHom R H) _ _]
  rw [toConv_comp_leftTranslationAlgEquiv,
    toConv_leftTranslationAlgEquiv, toConv_leftTranslationAlgEquiv, map_mul, mul_assoc]

/-- Left translation by the inverse point is the inverse algebra automorphism. -/
@[simp]
theorem leftTranslationAlgEquiv_inv (g : WithConv (H →ₐ[R] R)) :
    leftTranslationAlgEquiv g⁻¹ = (leftTranslationAlgEquiv g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← leftTranslationAlgEquiv_mul, mul_inv_cancel, leftTranslationAlgEquiv_one]

/-- Left translation by a base-valued point fixes a point valued in an algebra with injective
structure map only when the translating point is the identity. Thus the left translation action
of the rational points is free on algebra-valued points. -/
theorem comp_leftTranslationAlgEquiv_eq_self_iff {A : Type*} [CommRing A] [Algebra R A]
    (hA : Function.Injective (algebraMap R A)) (g : WithConv (H →ₐ[R] R)) (x : H →ₐ[R] A) :
    x.comp (leftTranslationAlgEquiv g).toAlgHom = x ↔ g = 1 := by
  have hmul := toConv_comp_leftTranslationAlgEquiv g (toConv x)
  rw [ofConv_toConv] at hmul
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h] at hmul
    exact AlgHom.mapValue_injective (φ := Algebra.ofId R A) hA
      ((mul_eq_right.mp hmul.symm).trans (map_one _).symm)
  · rw [h, leftTranslationAlgEquiv_one]
    ext a
    simp

end TauCeti.HopfAlgebra
