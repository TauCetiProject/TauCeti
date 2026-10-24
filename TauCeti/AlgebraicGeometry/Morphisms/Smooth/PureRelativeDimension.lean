/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth

/-!
# Smooth morphisms of pure relative dimension

A morphism of schemes is smooth of relative dimension `n` exactly when it is smooth and has pure
relative dimension `n`. This lets one establish a fixed smooth relative dimension from smoothness
together with every fibre being pure of dimension `n`, without exhibiting standard smooth charts
of that dimension.

Consequently, on the smooth locus of a morphism of pure relative dimension `n` the morphism is
smooth of relative dimension `n`. For `n = 1`, such as the smooth locus of a nodal relative curve,
this is the hypothesis under which a section through the smooth locus is a relative effective
Cartier divisor.

## Main results

* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension`:
  smooth of relative dimension `n` means smooth and of pure relative dimension `n`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_smoothLocus_ι_comp`: a morphism of
  pure relative dimension `n` is smooth of relative dimension `n` on its smooth locus.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A morphism is smooth of relative dimension `n` if and only if it is smooth and has pure
relative dimension `n`. -/
theorem smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension {n : ℕ}
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SmoothOfRelativeDimension n f ↔ Smooth f ∧ PureRelativeDimension n f := by
  refine ⟨fun _ ↦ ⟨SmoothOfRelativeDimension.smooth n f, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨?_⟩⟩
  intro x
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  -- The standard smooth chart around `x` has some relative dimension `m`.
  obtain ⟨m, hm⟩ : ∃ m, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  -- The chart, viewed as a morphism `Spec Γ(X, V) ⟶ Y`, has pure relative dimensions `m` and `n`.
  have : SmoothOfRelativeDimension m (Spec.map (f.appLE U V e)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension m)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hm
  have : PureRelativeDimension m (Spec.map (f.appLE U V e) ≫ hU.fromSpec) :=
    (pureRelativeDimension_comp_iff_of_injective _ _ hU.fromSpec.isEmbedding.injective).mpr
      inferInstance
  have : PureRelativeDimension n (Spec.map (f.appLE U V e) ≫ hU.fromSpec) := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV]
    infer_instance
  have : Nonempty (Spec Γ(X, V)) := ⟨hV.isoSpec.hom ⟨x, hx⟩⟩
  obtain rfl := PureRelativeDimension.unique (d := m) (e := n)
    (Spec.map (f.appLE U V e) ≫ hU.fromSpec)
  exact hm

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A morphism locally of finite presentation and of pure relative dimension `n` is smooth of
relative dimension `n` on its smooth locus. -/
instance smoothOfRelativeDimension_smoothLocus_ι_comp {n : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [TauCeti.AlgebraicGeometry.PureRelativeDimension n f] :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) :=
  (TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension
    _).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom
