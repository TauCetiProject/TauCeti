/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver

/-!
# Standard smooth charts over an affine target

If `f : X ⟶ Y` is smooth of relative dimension `n` and `Y` is affine, then every point of `X`
has an affine open neighbourhood `W` on which the map `Γ(Y, ⊤) → Γ(X, W)` induced by `f` is
standard smooth of relative dimension `n`. The defining charts of `SmoothOfRelativeDimension n`
only provide this over some affine open of `Y`; shrinking them to basic opens and using that
standard smoothness is stable under localization away from an element brings the source of the
ring map up to all of `Y`.

A smooth morphism has, around every point, standard smooth charts of some relative dimension,
so it is smooth of some relative dimension on an open neighbourhood of every point. Smoothness of
fixed relative dimension is local on the source and on the target.
It also records that smoothness on an open subscheme `U ⊆ X` yields standard smooth charts of
`f` itself around the points of `U`, as for the smooth locus of a family of curves.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.exists_isStandardSmoothOfRelativeDimension_of_smooth`: a smooth
  morphism has standard smooth charts of some relative dimension around every point.
* `AlgebraicGeometry.Scheme.Hom.exists_smoothOfRelativeDimension_ι_comp_of_smooth`: a smooth
  morphism is, near every point of its source, smooth of some relative dimension.
* `AlgebraicGeometry.Scheme.Hom.locally_isStandardSmoothOfRelativeDimension_sections`: for
  `f : X ⟶ Spec R` smooth of relative dimension `n`, the sections over every affine open of `X`
  form a locally standard smooth `R`-algebra of relative dimension `n`.
* `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top`, in Mathlib's
  `AlgebraicGeometry` namespace: standard smooth charts whose ring map starts at the global
  sections of the affine target.
* `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_of_comp_ι`: standard
  smooth charts of `f` inside an open `U ⊆ X` on which `f` is smooth.

## References

The proof is adapted from Mathlib's proof of
`AlgebraicGeometry.SmoothOfRelativeDimension.smoothOfRelativeDimension_comp` in
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` (Apache-2.0): the same shrinking of the charts to
basic opens via `exists_basicOpen_le_appLE_of_appLE_of_isAffine`, followed by composing with the
localization away from `r`, here taken from the global sections of the affine target rather
than from a chart of a second smooth morphism.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace RingHom

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Around every point, a smooth morphism has an affine chart on which it is standard smooth of
some relative dimension `m`. -/
theorem exists_isStandardSmoothOfRelativeDimension_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (x : X) :
    ∃ (m : ℕ) (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h
  exact ⟨P.dimension, U, hU, V, hV, hx, e, _, _, _, ‹_›, P, rfl⟩

/-- **Smooth morphisms have a local relative dimension.** Every point of the source of a smooth
morphism `f` has an open neighbourhood `V` on which `f` is smooth of some relative dimension `k`:
the relative dimension of a standard smooth chart of `f` around the point. -/
theorem exists_smoothOfRelativeDimension_ι_comp_of_smooth {Y S : Scheme.{u}} (f : Y ⟶ S)
    [Smooth f] (y : Y) :
    ∃ (V : Y.Opens) (k : ℕ), y ∈ V ∧ SmoothOfRelativeDimension k (V.ι ≫ f) := by
  -- the standard smooth chart `Γ(S, U) → Γ(Y, V)` has some relative dimension `k`
  obtain ⟨k, U, hU, V, hV, hy, e, hk⟩ := f.exists_isStandardSmoothOfRelativeDimension_of_smooth y
  have : SmoothOfRelativeDimension k (Spec.map (f.appLE U V e)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension k)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hk
  have : SmoothOfRelativeDimension k (hV.fromSpec ≫ f) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e]
    exact inferInstanceAs (SmoothOfRelativeDimension (k + 0) _)
  refine ⟨V, k, hy, ?_⟩
  have h := (inferInstance :
    SmoothOfRelativeDimension (0 + k) (hV.isoSpec.hom ≫ hV.fromSpec ≫ f))
  rwa [Nat.zero_add, ← Category.assoc, hV.isoSpec_hom_fromSpec] at h

/-- If `f : X ⟶ Spec R` is smooth of relative dimension `n`, then over every affine open `V` of `X`
the `R`-algebra of sections `Γ(X, V)` induced by `f` is locally standard smooth of relative
dimension `n`. -/
theorem locally_isStandardSmoothOfRelativeDimension_sections {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {V : X.Opens} (hV : IsAffineOpen V) :
    letI := f.sectionsAlgebra V
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R Γ(X, V)) :=
  f.algebraMap_sections V ▸
  (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).right _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
    (HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SmoothOfRelativeDimension

universe u

/-- Smoothness of fixed relative dimension is local on the source. -/
instance {n : ℕ} : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (@IsStandardSmoothOfRelativeDimension n))

/-- Smoothness of fixed relative dimension is local on the target. -/
instance {n : ℕ} : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (@IsStandardSmoothOfRelativeDimension n))

/-- If `f : X ⟶ Y` is smooth of relative dimension `n` and `Y` is affine, then around every point
of `X` there is an affine open `W` such that `Γ(Y, ⊤) → Γ(X, W)` is standard smooth of relative
dimension `n`. -/
theorem exists_isStandardSmoothOfRelativeDimension_appLE_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) :
    ∃ W : X.affineOpens, x ∈ W.val ∧
        (f.appLE ⊤ W.val le_top).hom.IsStandardSmoothOfRelativeDimension n
      := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  -- Shrink the charts to basic opens `D(r) ⊆ Y` and `D(s) ⊆ V`.
  obtain ⟨r, s, hxs, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
    x ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨V, hV⟩ ⟨V, hV⟩ hx hx e hf (Opens.mem_top _)
  refine ⟨⟨X.basicOpen s, hV.basicOpen s⟩, hxs, ?_⟩
  -- Since `Γ(Y, D(r))` is the localization of `Γ(Y, ⊤)` away from `r`, the map out of `Γ(Y, ⊤)`
  -- is still standard smooth of relative dimension `n`.
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    (isAffineOpen_top _).isLocalization_basicOpen r
  have heq : f.appLE ⊤ (X.basicOpen s) le_top =
      CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r)) ≫ f.appLE _ _ e₁ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Scheme.Hom.map_appLE]
  rw [heq, CommRingCat.hom_comp]
  exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
    _ r _ hf₁

/-- If `f : X ⟶ Y` restricted to an open subscheme `U ⊆ X` is smooth of relative dimension `n`,
then every point of `U` has an affine open neighbourhood `V ⊆ U` lying over an affine open `W`
of `Y` such that `Γ(Y, W) → Γ(X, V)` is standard smooth of relative dimension `n`. -/
theorem exists_isStandardSmoothOfRelativeDimension_of_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (n : ℕ) [SmoothOfRelativeDimension n (U.ι ≫ f)] {x : X} (hx : x ∈ U) :
    ∃ (W : Y.affineOpens) (V : X.affineOpens) (_ : V.val ≤ U) (_ : x ∈ V.val)
      (e : V.val ≤ f ⁻¹ᵁ W.val), (f.appLE W V e).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨W, hW, V, hV, hxV, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n)
      (f := U.ι ≫ f) ⟨x, hx⟩
  have e' : U.ι ''ᵁ V ≤ f ⁻¹ᵁ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact e hz
  refine ⟨⟨W, hW⟩, ⟨U.ι ''ᵁ V, hV.image_of_isOpenImmersion _⟩, (U.ι.image_le_opensRange V).trans
    U.opensRange_ι.le, ⟨⟨x, hx⟩, hxV, rfl⟩, e', ?_⟩
  -- The chart of `U.ι ≫ f` is the chart of `f` followed by the isomorphism `Γ(X, ι(V)) ≅ Γ(U, V)`.
  have heq : (U.ι ≫ f).appLE W V e =
      f.appLE W (U.ι ''ᵁ V) e' ≫ (U.ι.appIso V).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  rw [heq] at h
  exact (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_right_isIso _ _ |>.mp h

end AlgebraicGeometry.SmoothOfRelativeDimension

namespace TauCeti.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- Around every point of a scheme smooth of relative dimension `n` over `Spec R`, there is an
affine open whose ring of functions is standard smooth of relative dimension `n` over `R`. -/
lemma exists_isStandardSmoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] (x : X) :
    ∃ W : X.affineOpens, x ∈ W.val ∧
      ((X.baseRingToStructurePresheaf R).app (op W.val)).hom.IsStandardSmoothOfRelativeDimension n
        := by
  obtain ⟨W, hxW, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top
      (X ↘ Spec (.of R)) n x
  refine ⟨W, hxW, ?_⟩
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
  exact (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).right _
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv h

end TauCeti.AlgebraicGeometry
