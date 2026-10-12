/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.SingularLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified
import TauCeti.RingTheory.Node.Syntomic

/-!
# Nodal relative curves over an affine base

A relative curve over `Spec R` is at worst nodal when it is syntomic of relative dimension one
and its relative singular subscheme is unramified over `Spec R`. The singular subscheme is a
closed subscheme and its structure morphism is locally of finite type, so this condition amounts
to formal unramifiedness in the criterion.

The standard chart `xy = a` satisfies the criterion for every commutative ring and every
smoothing parameter. In particular this includes the smooth charts where `a` is a unit.

Smooth relative curves satisfy the same criterion: their singular subscheme is empty.

## Main result

* `AtWorstNodalOfRelativeDimensionOne.of_smooth`: smooth morphisms of relative dimension one
  over an affine base are at worst nodal.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The scheme-theoretic nodal-curve criterion over an affine base: the morphism is syntomic
of relative dimension one, and its singular subscheme is unramified over the base. -/
def AtWorstNodalOfRelativeDimensionOne (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ h : SyntomicOfRelativeDimension 1 f,
    letI : SyntomicOfRelativeDimension 1 f := h
    Unramified
      ((@Scheme.singularLocus R _ X ⟨f⟩
        (SyntomicOfRelativeDimension.flat 1 f)
        (SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 f)
        (PureRelativeDimension.of_syntomicOfRelativeDimension f)).subschemeι ≫ f)

/-- A relative curve is at worst nodal exactly when it is syntomic of relative dimension one
and its singular subscheme is unramified over the base. -/
theorem AtWorstNodalOfRelativeDimensionOne_iff {f : X ⟶ Spec (.of R)} :
    AtWorstNodalOfRelativeDimensionOne f ↔
      ∃ h : SyntomicOfRelativeDimension 1 f,
        letI : SyntomicOfRelativeDimension 1 f := h
        Unramified
          ((@Scheme.singularLocus R _ X ⟨f⟩
            (SyntomicOfRelativeDimension.flat 1 f)
            (SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 f)
            (PureRelativeDimension.of_syntomicOfRelativeDimension f)).subschemeι ≫ f) :=
  Iff.rfl

/-- Construct a nodal relative curve from syntomicity and unramifiedness of its
singular subscheme. -/
theorem AtWorstNodalOfRelativeDimensionOne.mk {f : X ⟶ Spec (.of R)}
    (hf : SyntomicOfRelativeDimension 1 f)
    (hs : letI : SyntomicOfRelativeDimension 1 f := hf
      Unramified
        ((@Scheme.singularLocus R _ X ⟨f⟩
          (SyntomicOfRelativeDimension.flat 1 f)
          (SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 f)
          (PureRelativeDimension.of_syntomicOfRelativeDimension f)).subschemeι ≫ f)) :
    AtWorstNodalOfRelativeDimensionOne f :=
  ⟨hf, hs⟩

/-- A nodal relative curve is syntomic of relative dimension one. -/
theorem AtWorstNodalOfRelativeDimensionOne.syntomic
    {f : X ⟶ Spec (.of R)} (h : AtWorstNodalOfRelativeDimensionOne f) :
    SyntomicOfRelativeDimension 1 f := h.choose

/-- The singular subscheme of a nodal relative curve is unramified over the base. -/
theorem AtWorstNodalOfRelativeDimensionOne.unramified_singularLocus
    {f : X ⟶ Spec (.of R)} (h : AtWorstNodalOfRelativeDimensionOne f) :
    letI : SyntomicOfRelativeDimension 1 f := h.syntomic
    Unramified
      ((@Scheme.singularLocus R _ X ⟨f⟩
        (SyntomicOfRelativeDimension.flat 1 f)
        (SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 f)
        (PureRelativeDimension.of_syntomicOfRelativeDimension f)).subschemeι ≫ f) :=
  h.choose_spec

/-- Nodal relative curves remain nodal after extension of the base ring. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_isPullback
    {R' : Type u} [CommRing R'] [Algebra R R']
    [X.Over (Spec (.of R))] {X' : Scheme.{u}} [X'.Over (Spec (.of R'))]
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (h : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) :
    AtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of R')) := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := h.syntomic
  have hf' : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of R')) :=
    MorphismProperty.of_isPullback (P := @SyntomicOfRelativeDimension 1) H inferInstance
  refine ⟨hf', ?_⟩
  have : Flat (X ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.flat 1 (X ↘ Spec (.of R))
  have : LocallyOfFinitePresentation (X ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 (X ↘ Spec (.of R))
  have : Flat (X' ↘ Spec (.of R')) :=
    SyntomicOfRelativeDimension.flat 1 (X' ↘ Spec (.of R'))
  have : LocallyOfFinitePresentation (X' ↘ Spec (.of R')) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 (X' ↘ Spec (.of R'))
  have hs := Scheme.isPullback_singularLocus_subschemeι (R := R) (R' := R')
    (X := X) (X' := X') H
  have hs' := hs.flip.paste_vert H
  exact MorphismProperty.of_isPullback (P := @Unramified) hs'
    h.unramified_singularLocus

/-- A smooth morphism of relative dimension one over an affine base is at worst nodal. Its
relative singular subscheme is empty, so the singular-locus condition in the nodal criterion
holds automatically. -/
private theorem smooth_unramified_singularLocus
    [X.Over (Spec (.of R))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))]
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    Unramified
      ((@Scheme.singularLocus R _ X inferInstance inferInstance inferInstance).subschemeι ≫
        (X ↘ Spec (.of R))) := by
  have hsing : X.singularLocus R = ⊤ := Scheme.singularLocus_eq_top R X
  rw [hsing]
  infer_instance

/-- A smooth morphism of relative dimension one over an affine base is at worst nodal. Its
relative singular subscheme is empty, so the singular-locus condition in the nodal criterion
holds automatically. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_smooth
    [X.Over (Spec (.of R))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)) := by
  refine ⟨inferInstance, ?_⟩
  exact smooth_unramified_singularLocus (R := R) (X := X)

/-- The local model `xy = a` is a nodal relative curve over `Spec R`. -/
theorem _root_.TauCeti.NodeAlgebra.atWorstNodalOfRelativeDimensionOne (a : R) :
    AtWorstNodalOfRelativeDimensionOne
      (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) := by
  let f : Spec (.of (NodeAlgebra R a)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))
  refine ⟨inferInstance, ?_⟩
  have : IsClosedImmersion _ := NodeAlgebra.isClosedImmersion_singularLocus a
  infer_instance

end TauCeti.AlgebraicGeometry
