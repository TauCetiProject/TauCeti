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

The construction uses right translation and `HopfAlgebra.pointConjugationBialgEquiv`:
conjugating `x * g` by `g` gives `g * x`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2 and 7.c.
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

/-- Precomposition by left translation multiplies an arbitrary algebra-valued point
on the left by the constant translating point. -/
theorem comp_leftTranslationAlgEquiv {A : Type*} [CommRing A] [Algebra R A]
    (g : WithConv (H →ₐ[R] R)) (x : WithConv (H →ₐ[R] A)) :
    toConv (x.ofConv.comp (leftTranslationAlgEquiv g).toAlgHom) =
      AlgHom.mapValue (Algebra.ofId R A) g * x := by
  have h := congrArg (AlgHom.mapValue x.ofConv) (toConv_leftTranslationAlgEquiv g)
  rw [map_mul, AlgHom.mapValue_algebraOfId] at h
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id] using h

end TauCeti.HopfAlgebra
