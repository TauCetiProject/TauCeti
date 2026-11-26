/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.SourceDescent
public import TauCeti.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Descent

/-!
# Smooth morphisms of pure relative dimension

A morphism of schemes is smooth of relative dimension `n` exactly when it is smooth and has pure
relative dimension `n`, since near every point a smooth morphism is smooth of some relative
dimension, and a nonempty open has only one pure relative dimension. This lets one establish a
fixed smooth relative dimension from smoothness together with every fibre being pure of dimension
`n`, without exhibiting standard smooth charts of that dimension.

The same comparison shows that relative dimension descends along smooth surjections: if `g` is
surjective and smooth of relative dimension `m`, `f` is locally of finite presentation, and `g ≫ f`
is smooth of relative dimension `m + n`, then `f` is smooth of relative dimension `n`. This
computes the relative dimension of a smooth scheme from a smooth cover of known relative dimension,
as for the fine modular curve `Y₁(N)`.

Consequently, on the smooth locus of a morphism of pure relative dimension `n` the morphism is
smooth of relative dimension `n`. For `n = 1`, such as the smooth locus of a nodal relative curve,
this is the hypothesis under which a section through the smooth locus is a relative effective
Cartier divisor.

For a smooth morphism whose fibres are irreducible, such as a smooth morphism with geometrically
connected fibres, the fibre dimension is a locally constant function on the target. Near a point
of the source the morphism is smooth of some relative dimension `n`, and an irreducible fibre
meeting that open has a nonempty open part of pure dimension `n`, hence dimension `n`; smooth
morphisms are open, so the fibres over a neighbourhood of every point of the target have the same
dimension. Such a morphism is smooth of relative dimension `n` exactly when every fibre has
dimension `n`.

## Main results

* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension`:
  smooth of relative dimension `n` means smooth and of pure relative dimension `n`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_smoothLocus_ι_comp`: a morphism of
  pure relative dimension `n` is smooth of relative dimension `n` on its smooth locus.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_surjective`: if `g` is surjective and smooth
  of relative dimension `m`, `f` is locally of finite presentation, and `g ≫ f` is smooth of
  relative dimension `m + n`, then `f` is smooth of relative dimension `n`.
* `AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  being smooth of relative dimension `n` descends along flat, surjective, quasi-compact morphisms.
* `TauCeti.AlgebraicGeometry.isLocallyConstant_topologicalKrullDim_fiber`: for a smooth morphism
  with irreducible fibres, the fibre dimension is locally constant on the target, and finite
  (`TauCeti.AlgebraicGeometry.exists_topologicalKrullDim_fiber_eq_natCast`).
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_forall_topologicalKrullDim_fiber_eq`:
  such a morphism is smooth of relative dimension `n` exactly when all fibres have dimension `n`.
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
  refine ⟨fun _ ↦ ⟨SmoothOfRelativeDimension.smooth n f, inferInstance⟩, fun ⟨_, _⟩ ↦ ?_⟩
  -- Around every point `f` is smooth of some relative dimension `k`, and comparing pure relative
  -- dimensions on that nonempty open gives `k = n`.
  have key (x : X) : ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
    obtain ⟨V, k, hx, hk⟩ := f.exists_smoothOfRelativeDimension_ι_comp_of_smooth x
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    obtain rfl := PureRelativeDimension.unique (d := k) (e := n) (V.ι ≫ f)
    exact ⟨V, hx, hk⟩
  exact IsZariskiLocalAtSource.of_forall_exists_ι_comp key

section IrreducibleFibers

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [∀ y, IrreducibleSpace (f.fiber y)]

/-- A smooth morphism with irreducible fibres is smooth of relative dimension `n` if and only if
every fibre has dimension `n`. -/
theorem smoothOfRelativeDimension_iff_forall_topologicalKrullDim_fiber_eq {n : ℕ} :
    SmoothOfRelativeDimension n f ↔ ∀ y, topologicalKrullDim (f.fiber y) = n := by
  simp only [smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension,
    pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber,
    isPureDimensional_iff_topologicalKrullDim_eq, and_iff_right ‹Smooth f›]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨fun y ↦ (h y).le⟩, h⟩⟩

/-- For a smooth morphism with irreducible fibres, every point `x` of the source has an open
neighbourhood `U` of `f x` over which all fibres have the same finite dimension. -/
theorem exists_isOpen_forall_topologicalKrullDim_fiber_eq (x : X) :
    ∃ (U : Set Y) (n : ℕ), IsOpen U ∧ f x ∈ U ∧
      ∀ y ∈ U, topologicalKrullDim (f.fiber y) = n := by
  -- Near `x`, `f` is smooth of some relative dimension `n` on an open `V`, and every fibre
  -- meeting `V` is irreducible with a nonempty open part of pure dimension `n`.
  obtain ⟨V, n, hx, hn⟩ := f.exists_smoothOfRelativeDimension_ι_comp_of_smooth x
  refine ⟨f '' V, n, f.isOpenMap _ V.isOpen, ⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact topologicalKrullDim_fiber_eq_of_pureRelativeDimension_comp V.ι f ⟨v, hv⟩ rfl

/-- Every fibre of a smooth morphism with irreducible fibres has finite Krull dimension. -/
theorem exists_topologicalKrullDim_fiber_eq_natCast (y : Y) :
    ∃ n : ℕ, topologicalKrullDim (f.fiber y) = n := by
  obtain ⟨p⟩ : Nonempty (f.fiber y) := inferInstance
  obtain ⟨U, n, -, hU, h⟩ := exists_isOpen_forall_topologicalKrullDim_fiber_eq f (f.fiberHomeo y p)
  exact ⟨n, (f.fiberHomeo y p).property ▸ h _ hU⟩

/-- **The fibre dimension of a smooth morphism with irreducible fibres is locally constant** on
the target. -/
theorem isLocallyConstant_topologicalKrullDim_fiber :
    IsLocallyConstant fun y ↦ topologicalKrullDim (f.fiber y) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun y ↦ ?_
  obtain ⟨p⟩ : Nonempty (f.fiber y) := inferInstance
  obtain ⟨U, n, hUo, hU, h⟩ := exists_isOpen_forall_topologicalKrullDim_fiber_eq f
    (f.fiberHomeo y p)
  rw [(f.fiberHomeo y p).property] at hU
  exact ⟨U, hUo, hU, fun y' hy' ↦ (h y' hy').trans (h y hU).symm⟩

end IrreducibleFibers

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
`g ≫ f` is smooth of relative dimension `m + n`, then `f` is smooth of relative dimension `n`. -/
theorem of_comp_surjective {m n : ℕ} {X Y S : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ S)
    [SmoothOfRelativeDimension m g] [Surjective g] [LocallyOfFinitePresentation f]
    [SmoothOfRelativeDimension (m + n) (g ≫ f)] : SmoothOfRelativeDimension n f := by
  have : Smooth g := SmoothOfRelativeDimension.smooth m g
  have : Smooth (g ≫ f) := SmoothOfRelativeDimension.smooth (m + n) (g ≫ f)
  -- smoothness of `f` descends along the flat surjection `g`
  have : Smooth f := Smooth.of_comp_surjective g f
  -- near a point of `Y`, `f` has the relative dimension `k` of a standard smooth chart; on the
  -- nonempty preimage of the chart, `g ≫ f` has both relative dimensions `m + k` and `m + n`
  have key (y : Y) : ∃ V : Y.Opens, y ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
    obtain ⟨V, k, hy, hk⟩ := f.exists_smoothOfRelativeDimension_ι_comp_of_smooth y
    obtain ⟨x, rfl⟩ := g.surjective y
    -- on the preimage `W` of `V`, the morphism `g ≫ f` has relative dimensions `m + k`, `m + n`
    let W := g ⁻¹ᵁ V
    have : Nonempty W := ⟨⟨x, hy⟩⟩
    have : SmoothOfRelativeDimension m (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : SmoothOfRelativeDimension (m + k) (W.ι ≫ g ≫ f) := by
      rw [← morphismRestrict_ι_assoc g V]
      infer_instance
    have : SmoothOfRelativeDimension (m + n) (W.ι ≫ g ≫ f) := IsZariskiLocalAtSource.comp ‹_› W.ι
    have hkn : m + k = m + n := PureRelativeDimension.unique (W.ι ≫ g ≫ f)
    exact ⟨V, hy, Nat.add_left_cancel hkn ▸ hk⟩
  exact IsZariskiLocalAtSource.of_forall_exists_ι_comp key

open MorphismProperty in
/-- **Being smooth of relative dimension `n` descends along flat, surjective, quasi-compact
morphisms.** Smoothness descends along such morphisms, and so does being syntomic of relative
dimension `n`, which gives pure relative dimension `n`. In particular a scheme over a field `k` is
smooth of relative dimension `n` if its base change to an extension field is. -/
instance descendsAlong_surjective_inf_flat_inf_quasiCompact (n : ℕ) :
    DescendsAlong (@SmoothOfRelativeDimension n) (@Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact) := by
  refine ⟨fun {A X Y Z fst snd f g} h hf hfst ↦ ?_⟩
  have : SmoothOfRelativeDimension n fst := hfst
  have : Smooth g := of_isPullback_of_descendsAlong h hf (SmoothOfRelativeDimension.smooth n fst)
  have : SyntomicOfRelativeDimension n g := of_isPullback_of_descendsAlong h hf inferInstance
  exact (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension g).mpr
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.SmoothOfRelativeDimension
