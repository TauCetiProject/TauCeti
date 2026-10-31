/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The smooth locus of a morphism

For a morphism `f : X ⟶ S` locally of finite presentation, Mathlib's `Scheme.Hom.smoothLocus`
is the open subscheme of points of `X` at which `f` is smooth. This file records that `f` is
smooth on its smooth locus, and that the smooth locus is preserved by base change: for every
`g : T ⟶ S`, a point of `X ×_S T` lying over the smooth locus of `f` lies in the smooth locus of
the projection `X ×_S T ⟶ T`.

Over a perfect field, a reduced scheme locally of finite type is smooth if its
automorphisms over the field act transitively on closed points. This spreads the dense
smooth locus to the whole scheme, following Andrew Yang's proof underlying Mathlib's
`AlgebraicGeometry.smooth_of_grpObj`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smooth_smoothLocus_ι_comp`: the restriction of `f` to its smooth
  locus is smooth.
* `AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_le_smoothLocus_pullback_snd`: the preimage
  of the smooth locus of `f` in `X ×_S T` lies in the smooth locus of `X ×_S T ⟶ T`.
* `AlgebraicGeometry.Scheme.Hom.smooth_of_transitive_on_closedPoints`: a reduced scheme
  locally of finite type over a perfect field is smooth if its automorphisms over the field
  act transitively on closed points.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X S T : Scheme.{u}}

/-- A morphism locally of finite presentation is smooth on its smooth locus. -/
instance smooth_smoothLocus_ι_comp (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq, Scheme.Opens.ι_preimage_self]

/-- **The smooth locus is stable under base change.** For `f : X ⟶ S` locally of finite
presentation and `g : T ⟶ S`, the preimage of the smooth locus of `f` under the projection
`X ×_S T ⟶ X` lies in the smooth locus of the projection `X ×_S T ⟶ T`. -/
theorem preimage_smoothLocus_le_smoothLocus_pullback_snd (f : X ⟶ S) (g : T ⟶ S)
    [LocallyOfFinitePresentation f] :
    pullback.fst f g ⁻¹ᵁ f.smoothLocus ≤ (pullback.snd f g).smoothLocus := by
  set V := pullback.fst f g ⁻¹ᵁ f.smoothLocus
  -- `V ⟶ T` is the base change of the restriction of `f` to its smooth locus, so it is smooth.
  have h : IsPullback (pullback.fst f g ∣_ f.smoothLocus) (V.ι ≫ pullback.snd f g)
      (f.smoothLocus.ι ≫ f) g :=
    (isPullback_morphismRestrict _ _).paste_vert (IsPullback.of_hasPullback f g)
  have : Smooth (V.ι ≫ pullback.snd f g) := MorphismProperty.of_isPullback h inferInstance
  intro x hx
  have : (⟨x, hx⟩ : V) ∈ (V.ι ≫ pullback.snd f g).smoothLocus :=
    (smoothLocus_eq_top (V.ι ≫ pullback.snd f g)).ge trivial
  rwa [← preimage_smoothLocus_eq] at this

/-- A reduced scheme locally of finite type over a perfect field is smooth if its
automorphisms over the field act transitively on closed points. Empty schemes are allowed. -/
theorem smooth_of_transitive_on_closedPoints {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [IsReduced X] [LocallyOfFiniteType f]
    (htrans : ∀ y ∈ closedPoints X, ∀ z ∈ closedPoints X,
      ∃ e : X ≅ X, e.hom ≫ f = f ∧ e.hom y = z) : Smooth f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [← smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro h
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints h
    f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
  have : Nonempty X := ⟨y⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.isOpen.isLocallyClosed
  obtain ⟨e, he, hyz⟩ := htrans y hyc z hzc
  have hz' : y ∈ e.hom ⁻¹ᵁ f.smoothLocus := by
    rw [mem_preimage, hyz]
    exact hz
  exact hy (by simpa only [preimage_smoothLocus_eq, he, SetLike.mem_coe] using hz')

end AlgebraicGeometry.Scheme.Hom
