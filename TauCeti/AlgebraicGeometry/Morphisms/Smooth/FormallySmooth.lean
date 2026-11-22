/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth

/-!
# Smooth and formally smooth morphisms of schemes

We compare Mathlib's smooth morphisms of schemes with Tau Ceti's formally smooth morphisms,
defined by the infinitesimal lifting property along affine first-order thickenings.

## Main results

* `TauCeti.AlgebraicGeometry.smooth_of_formallySmooth`: a formally smooth morphism locally of
  finite presentation is smooth.
* `TauCeti.AlgebraicGeometry.FormallySmooth.of_smooth_of_isAffineHom`: a smooth affine morphism is
  formally smooth, so `smooth_iff_formallySmooth_of_isAffineHom`.

That an arbitrary smooth morphism `f : X ⟶ S` is formally smooth is not proved here. For a
first-order thickening `T ⟶ T'`, lifts `T' ⟶ X` exist locally on `T'`, and the sheaf of local
lifts on `T'` is a torsor rather than having a unique section. The missing argument must show
that this torsor has a global section when `T'` is affine.

## References

* [Stacks Project, Lemma 37.11.7](https://stacks.math.columbia.edu/tag/02H6), smooth morphisms
  and formally smooth morphisms locally of finite presentation.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A smooth affine morphism is formally smooth. -/
instance (priority := 100) FormallySmooth.of_smooth_of_isAffineHom (f : X ⟶ S) [Smooth f]
    [IsAffineHom f] : FormallySmooth f where
  exists_lift {T T'} _ i _ a h w := by
    -- Lift through the base change `X ×_S T' ⟶ T'`, a smooth morphism of affine schemes.
    have : FormallySmooth (pullback.snd f h) := by
      rw [formallySmooth_iff_of_isAffine]
      exact ((HasRingHomProperty.iff_of_isAffine (P := @Smooth)).1 inferInstance).formallySmooth
    obtain ⟨l, hl, hl'⟩ := exists_lift (f := pullback.snd f h) i (pullback.lift a i w) (𝟙 T')
      (by simp)
    refine ⟨l ≫ pullback.fst f h, by rw [reassoc_of% hl, pullback.lift_fst], ?_⟩
    rw [Category.assoc, pullback.condition, reassoc_of% hl']

/-- A formally smooth morphism locally of finite presentation is smooth. -/
@[stacks 02H6]
theorem smooth_of_formallySmooth (f : X ⟶ S) [FormallySmooth f]
    [LocallyOfFinitePresentation f] : Smooth f := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  exact fun U V e ↦ RingHom.smooth_def.2
    ⟨f.formallySmooth_appLE U.property V.property e,
      f.finitePresentation_appLE U.property V.property e⟩

/-- An affine morphism locally of finite presentation is smooth if and only if it is formally
smooth. -/
theorem smooth_iff_formallySmooth_of_isAffineHom (f : X ⟶ S) [IsAffineHom f]
    [LocallyOfFinitePresentation f] : Smooth f ↔ FormallySmooth f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ smooth_of_formallySmooth f⟩

end TauCeti.AlgebraicGeometry
