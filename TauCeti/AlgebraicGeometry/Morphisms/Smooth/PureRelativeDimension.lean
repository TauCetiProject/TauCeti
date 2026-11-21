/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.SourceDescent

/-!
# Smooth morphisms of pure relative dimension

A morphism of schemes is smooth of relative dimension `n` exactly when it is smooth and has pure
relative dimension `n`, since near every point a smooth morphism is smooth of some relative
dimension, and a nonempty open has only one pure relative dimension. This lets one establish a
fixed smooth relative dimension from smoothness together with every fibre being pure of dimension
`n`, without exhibiting standard smooth charts of that dimension.

The same comparison shows that relative dimension descends along smooth surjections: if `g` is
surjective and smooth of relative dimension `m` and `g ≫ f` is smooth of relative dimension `m + n`,
then `f` is smooth of relative dimension `n`. This computes the relative dimension of a smooth
scheme from a smooth cover of known relative dimension, as for the fine modular curve `Y₁(N)`.

Consequently, on the smooth locus of a morphism of pure relative dimension `n` the morphism is
smooth of relative dimension `n`. For `n = 1`, such as the smooth locus of a nodal relative curve,
this is the hypothesis under which a section through the smooth locus is a relative effective
Cartier divisor.

## Main results

* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension`:
  smooth of relative dimension `n` means smooth and of pure relative dimension `n`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_smoothLocus_ι_comp`: a morphism of
  pure relative dimension `n` is smooth of relative dimension `n` on its smooth locus.
* `AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_ι_comp`: a smooth morphism is, near
  every point of its source, smooth of some relative dimension.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_surjective`: if `g` is surjective and smooth
  of relative dimension `m`, and `g ≫ f` is smooth of relative dimension `m + n`, then `f` is smooth
  of relative dimension `n`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Smooth

universe u

/-- **Smooth morphisms have a local relative dimension.** Every point of the source of a smooth
morphism `f` has an open neighbourhood `V` on which `f` is smooth of some relative dimension `k`:
the relative dimension of a standard smooth chart of `f` around the point. -/
theorem exists_smoothOfRelativeDimension_ι_comp {Y S : Scheme.{u}} (f : Y ⟶ S)
    [Smooth f] (y : Y) :
    ∃ (V : Y.Opens) (k : ℕ), y ∈ V ∧ SmoothOfRelativeDimension k (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hy, e, h⟩ := Smooth.exists_isStandardSmooth f y
  -- the standard smooth chart `Γ(S, U) → Γ(Y, V)` has some relative dimension `k`
  obtain ⟨k, hk⟩ : ∃ k, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension k := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
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

end AlgebraicGeometry.Smooth

namespace TauCeti.AlgebraicGeometry

universe u

/-- A morphism is smooth of relative dimension `n` if and only if it is smooth and has pure
relative dimension `n`. -/
theorem smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension {n : ℕ}
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SmoothOfRelativeDimension n f ↔ Smooth f ∧ PureRelativeDimension n f := by
  refine ⟨fun _ ↦ ⟨SmoothOfRelativeDimension.smooth n f, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  -- Around every point `f` is smooth of some relative dimension `k`, and comparing pure relative
  -- dimensions on that nonempty open gives `k = n`.
  have key (x : X) : ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
    obtain ⟨V, k, hx, hk⟩ := Smooth.exists_smoothOfRelativeDimension_ι_comp f x
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    obtain rfl := PureRelativeDimension.unique (d := k) (e := n) (V.ι ≫ f)
    exact ⟨V, hx, hk⟩
  choose V hV h using key
  exact @IsZariskiLocalAtSource.of_iSup_eq_top _ (HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @SmoothOfRelativeDimension n)) _ _ _ _ V
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hV x⟩) h

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

namespace AlgebraicGeometry.SmoothOfRelativeDimension

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

/-- **Relative dimension descends along smooth surjections.** Let `g : X ⟶ Y` be surjective and
smooth of relative dimension `m`, and let `f : Y ⟶ S` be locally of finite presentation. If
`g ≫ f` is smooth of relative dimension `m + n`, then `f` is smooth of relative dimension `n`.
Smoothness of `f` itself descends along the flat surjection `g` (`Smooth.of_comp_surjective`);
near a point of `Y` its relative dimension `k` is read off a standard smooth chart, and on the
nonempty preimage of the chart `g ≫ f` is smooth of both relative dimensions `m + k` and `m + n`. -/
theorem of_comp_surjective {m n : ℕ} {X Y S : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)
    [SmoothOfRelativeDimension m g] [Surjective g] [LocallyOfFinitePresentation f]
    [SmoothOfRelativeDimension (m + n) (g ≫ f)] : SmoothOfRelativeDimension n f := by
  have : Smooth g := SmoothOfRelativeDimension.smooth m g
  have : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth (m + n) (g ≫ f)
  have : Smooth f := Smooth.of_comp_surjective g f
  have key (y : Y) : ∃ V : Y.Opens, y ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
    obtain ⟨V, k, hy, hk⟩ := Smooth.exists_smoothOfRelativeDimension_ι_comp f y
    obtain ⟨x, rfl⟩ := g.surjective y
    -- on the preimage `W` of `V`, the morphism `g ≫ f` has relative dimensions `m + k`, `m + n`
    let W := g ⁻¹ᵁ V
    have : Nonempty W := ⟨⟨x, hy⟩⟩
    have : SmoothOfRelativeDimension m (g ∣_ V) :=
      @IsZariskiLocalAtTarget.restrict _ (HasRingHomProperty.instIsZariskiLocalAtTarget
        (P := @SmoothOfRelativeDimension m)) _ _ _ ‹_› V
    have : SmoothOfRelativeDimension (m + k) (W.ι ≫ g ≫ f) := by
      rw [← morphismRestrict_ι_assoc g V]
      infer_instance
    have : SmoothOfRelativeDimension (m + n) (W.ι ≫ g ≫ f) :=
      @IsZariskiLocalAtSource.comp _ (HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @SmoothOfRelativeDimension (m + n))) _ _ _ _ ‹_› W.ι _
    have hkn : m + k = m + n := PureRelativeDimension.unique (W.ι ≫ g ≫ f)
    exact ⟨V, hy, Nat.add_left_cancel hkn ▸ hk⟩
  choose V hV h using key
  exact @IsZariskiLocalAtSource.of_iSup_eq_top _ (HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @SmoothOfRelativeDimension n)) _ _ _ _ V
    (eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hV y⟩) h

end AlgebraicGeometry.SmoothOfRelativeDimension
