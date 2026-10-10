/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RingHom.StandardSyntomic
public import TauCeti.AlgebraicGeometry.Morphisms.StandardSyntomic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Syntomic morphisms of fixed relative dimension

A syntomic morphism of relative dimension `n` is locally on affine charts standard syntomic
of relative dimension `n`. These morphisms are flat and locally finitely presented, are local
on both source and target, and are stable under arbitrary base change. They have relative
dimension at most `n`. The affine criterion connects the scheme property to the existing
algebraic complete-intersection presentations.

The consequences `SyntomicOfRelativeDimension.flat n f` and
`SyntomicOfRelativeDimension.locallyOfFinitePresentation n f` take the dimension explicitly,
since it is absent from their conclusions. For downstream typeclass-based APIs, install them
locally with `have := SyntomicOfRelativeDimension.flat n f` and
`have := SyntomicOfRelativeDimension.locallyOfFinitePresentation n f`.

This construction follows the local-chart API of Mathlib's `SmoothOfRelativeDimension` in
`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`, by Christian Merten. The mathematical
reference is the Stacks Project, *Syntomic morphisms*. Syntomic relative curves provide the
complete-intersection input to the singular-locus criterion for nodal families.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A scheme morphism is syntomic of relative dimension `n` if each source point has affine
source and target neighborhoods on which the induced ring map is standard syntomic of
relative dimension `n`. -/
@[mk_iff]
class SyntomicOfRelativeDimension (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  exists_isStandardSyntomicOfRelativeDimension (x : X) :
    ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
      (e : V.1 ≤ f ⁻¹ᵁ U.1), IsStandardSyntomicOfRelativeDimension n (f.appLE U V e).hom

variable (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The affine ring property of syntomic morphisms is locally standard syntomic. -/
instance : HasRingHomProperty (@SyntomicOfRelativeDimension n)
    (RingHom.Locally (@IsStandardSyntomicOfRelativeDimension n)) :=
  HasRingHomProperty.locally_of_iff
    (isStandardSyntomicOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves.away
    (isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway n)
    fun _ ↦ syntomicOfRelativeDimension_iff n _

/-- Over an affine target, every source point has a standard syntomic affine chart over
the global sections of the target. -/
theorem SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension_appLE_top
    [IsAffine Y] [SyntomicOfRelativeDimension n f] (x : X) :
    ∃ (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ ⊤),
      IsStandardSyntomicOfRelativeDimension n (f.appLE ⊤ V e).hom := by
  obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x)
  have e : V ≤ f ⁻¹ᵁ ⊤ := by simp
  have h := (HasRingHomProperty.iff_appLE (P := @SyntomicOfRelativeDimension n)).mp
    ‹SyntomicOfRelativeDimension n f› ⟨⊤, isAffineOpen_top Y⟩ ⟨V, hV⟩ e
  rw [RingHom.locally_iff_isLocalization (isStandardSyntomicOfRelativeDimension_respectsIso n)] at h
  obtain ⟨s, hs, hfs⟩ := h
  have hx' : x ∈ ⨆ r ∈ s, X.basicOpen r := (iSup_basicOpen_of_span_eq_top V s hs).symm ▸ hx
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using hx'
  refine ⟨⟨X.basicOpen r, hV.basicOpen r⟩, hxr, (X.basicOpen_le r).trans e, ?_⟩
  rw [← f.appLE_map e (homOfLE (X.basicOpen_le r)).op]
  have : IsLocalization.Away r Γ(X, X.basicOpen r) := hV.isLocalization_basicOpen r
  exact hfs r hr _

/-- Syntomic morphisms of fixed relative dimension are stable under arbitrary base change. -/
instance syntomicOfRelativeDimension_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@SyntomicOfRelativeDimension.{u} n) :=
  HasRingHomProperty.isStableUnderBaseChange <| RingHom.locally_isStableUnderBaseChange
    (isStandardSyntomicOfRelativeDimension_respectsIso n)
    (isStandardSyntomicOfRelativeDimension_isStableUnderBaseChange n)

/-- Syntomicity of fixed relative dimension is invariant under isomorphisms. -/
instance : MorphismProperty.RespectsIso (@SyntomicOfRelativeDimension.{u} n) := by
  rw [HasRingHomProperty.eq_affineLocally (P := @SyntomicOfRelativeDimension n)]
  exact affineLocally_respectsIso _
    (locally_isStandardSyntomicOfRelativeDimension_propertyIsLocal n).respectsIso

/-- Syntomicity of fixed relative dimension is local on the source. -/
instance : IsZariskiLocalAtSource (@SyntomicOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @SyntomicOfRelativeDimension n)
    (Q := RingHom.Locally (@IsStandardSyntomicOfRelativeDimension n))

/-- Syntomicity of fixed relative dimension is local on the target. -/
instance : IsZariskiLocalAtTarget (@SyntomicOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SyntomicOfRelativeDimension n)
    (Q := RingHom.Locally (@IsStandardSyntomicOfRelativeDimension n))

/-- Restricting the source to an open subscheme preserves syntomicity and relative dimension. -/
instance : MorphismProperty.Respects (@SyntomicOfRelativeDimension.{u} n) @IsOpenImmersion :=
  HasRingHomProperty.respects_isOpenImmersion <|
    RingHom.locally_stableUnderCompositionWithLocalizationAwaySource
      (isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left

/-- Open immersions, including identities, are syntomic of relative dimension zero. -/
instance (priority := 900) [IsOpenImmersion f] : SyntomicOfRelativeDimension 0 f :=
  HasRingHomProperty.of_isOpenImmersion fun R _ ↦
    RingHom.locally_of (isStandardSyntomicOfRelativeDimension_respectsIso 0) _
      (IsStandardSyntomicOfRelativeDimension.id R)

/-- Syntomic morphisms are flat. -/
theorem SyntomicOfRelativeDimension.flat [SyntomicOfRelativeDimension n f] : Flat f := by
  rw [HasRingHomProperty.iff_appLE (P := @Flat)]
  intro U V e
  have h := (HasRingHomProperty.iff_appLE (P := @SyntomicOfRelativeDimension n)).mp
    ‹SyntomicOfRelativeDimension n f› U V e
  exact (RingHom.locally_iff_of_localizationSpanTarget RingHom.Flat.respectsIso
    RingHom.Flat.ofLocalizationSpanTarget _).mp <|
      RingHom.locally_of_locally (fun hf ↦ hf.flat) h

/-- Syntomic morphisms are locally of finite presentation. -/
theorem SyntomicOfRelativeDimension.locallyOfFinitePresentation
    [SyntomicOfRelativeDimension n f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have h := (HasRingHomProperty.iff_appLE (P := @SyntomicOfRelativeDimension n)).mp
    ‹SyntomicOfRelativeDimension n f› U V e
  exact (RingHom.locally_iff_of_localizationSpanTarget
    RingHom.finitePresentation_respectsIso
    RingHom.finitePresentation_ofLocalizationSpanTarget _).mp <|
      RingHom.locally_of_locally (fun hf ↦ hf.finitePresentation) h

variable {n} in
/-- A standard syntomic algebra gives a syntomic morphism on spectra. -/
instance syntomicOfRelativeDimension_SpecMap (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsStandardSyntomicOfRelativeDimension n R S] :
    SyntomicOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SyntomicOfRelativeDimension n)]
  exact RingHom.locally_of (isStandardSyntomicOfRelativeDimension_respectsIso n) _
    (isStandardSyntomicOfRelativeDimension_algebraMap.mpr inferInstance)

/-- The affine criterion for syntomicity is localization on the source of the induced ring map. -/
@[simp]
theorem syntomicOfRelativeDimension_SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    SyntomicOfRelativeDimension n (Spec.map φ) ↔
      RingHom.Locally (@IsStandardSyntomicOfRelativeDimension n) φ.hom :=
  HasRingHomProperty.Spec_iff

/-- Pulling back a syntomic morphism preserves its relative dimension. -/
instance {S : Scheme.{u}} (g : X ⟶ S) (h : Y ⟶ S) [SyntomicOfRelativeDimension n h] :
    SyntomicOfRelativeDimension n (pullback.fst g h) :=
  letI := MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange
    (@SyntomicOfRelativeDimension n) g
  MorphismProperty.pullback_fst (P := @SyntomicOfRelativeDimension n) g h inferInstance

/-- Pulling back a syntomic morphism preserves its relative dimension. -/
instance {S : Scheme.{u}} (g : X ⟶ S) (h : Y ⟶ S) [SyntomicOfRelativeDimension n g] :
    SyntomicOfRelativeDimension n (pullback.snd g h) :=
  letI := MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange
    (@SyntomicOfRelativeDimension n) h
  MorphismProperty.pullback_snd (P := @SyntomicOfRelativeDimension n) g h inferInstance

/-- A syntomic morphism of relative dimension `n` has all fibres of dimension at most `n`. -/
instance (priority := low) SyntomicOfRelativeDimension.relativeDimensionLE
    [SyntomicOfRelativeDimension n f] :
    RelativeDimensionLE n f := by
  have : MorphismProperty.RespectsRight (@RelativeDimensionLE.{u} n) @IsOpenImmersion :=
    ⟨fun g hg f hf ↦ by
      have := hg
      have := hf
      exact RelativeDimensionLE.comp_isPreimmersion f g⟩
  refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @RelativeDimensionLE n)).mpr fun x ↦ ?_
  obtain ⟨U, V, hx, e, h⟩ :=
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension (n := n) (f := f) x
  refine ⟨U.1, V.1, hx, e, ?_⟩
  -- Pass from affine chart sections to the global sections of the restricted schemes.
  have htop := (isStandardSyntomicOfRelativeDimension_respectsIso n).arrow_mk_iso_iff
    (arrowResLEAppIso f U V e)
  have h' := htop.mpr h
  let φ := (f.resLE U V e).appTop.hom
  let := φ.toAlgebra
  have : Algebra.IsStandardSyntomicOfRelativeDimension n
      Γ(U.1.toScheme, ⊤) Γ(V.1.toScheme, ⊤) :=
    (isStandardSyntomicOfRelativeDimension_iff n φ).mp h'
  have hdim := Algebra.IsStandardSyntomicOfRelativeDimension.relativeDimensionLE_SpecMap
    n Γ(U.1.toScheme, ⊤) Γ(V.1.toScheme, ⊤)
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  -- The restricted affine morphism is canonically isomorphic to the map on spectra.
  rw [MorphismProperty.arrow_mk_iso_iff (@RelativeDimensionLE n)
    (arrowIsoSpecΓOfIsAffine (f.resLE U V e))]
  simpa only [RingHom.algebraMap_toAlgebra, φ, CommRingCat.ofHom_hom] using hdim

end TauCeti.AlgebraicGeometry
