/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Alteration
public import TauCeti.AlgebraicGeometry.Morphisms.MaximallyDominating

import TauCeti.AlgebraicGeometry.Fibers.Finite
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.Topology.Sober

/-!
# Alterations of possibly reducible schemes

A morphism `f : X ⟶ Y` is *finite over the generic points* of `Y` if its base change
`X ×_Y η_Y ⟶ η_Y` to the scheme of generic points `η_Y` of `Y` is finite. It is a *noetherian
alteration* if it is moreover proper, surjective and maximally dominating. This is the notion of
alteration used by Temkin and by Illusie–Laszlo–Orgogozo for noetherian schemes that need not be
irreducible; the definitions make sense for all schemes.

Finiteness over the generic points can be tested on the fibres over the component-generic points.
For a proper morphism it spreads out: the morphism is then finite over an open subscheme
containing every component-generic point of the target. Consequently, from an irreducible source
the noetherian alterations are exactly the alterations of
`TauCeti.AlgebraicGeometry.IsAlteration`, which are proper, dominant and finite over a nonempty
open; for instance, a modification of an irreducible scheme is a noetherian alteration. Noetherian
alterations compose.

The morphism `𝔸¹ ⊔ Spec k ⟶ 𝔸¹` that sends the extra point to the origin is proper, surjective
and finite, but not maximally dominating, so it is not a noetherian alteration; this is why the
comparison with `IsAlteration` requires an irreducible source.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsFiniteOverGenericPoints f`: the base change of `f` to the
  scheme of generic points of its target is finite.
* `AlgebraicGeometry.Scheme.Hom.IsNoetherianAlteration f`: `f` is proper, surjective, maximally
  dominating and finite over the generic points of its target.

## Main results

* `Scheme.Hom.isFiniteOverGenericPoints_iff_forall_isFinite_fiberToSpecResidueField`:
  finiteness over the generic points is finiteness of the fibres over the component-generic
  points.
* `AlgebraicGeometry.Scheme.Hom.isFiniteOverGenericPoints_iff_forall_finite_preimage_singleton`:
  for quasi-compact morphisms locally of finite type, it says that the fibres over the
  component-generic points are finite sets.
* `Scheme.Hom.isFiniteOverGenericPoints_iff_exists_isFinite_morphismRestrict`:
  a proper morphism is finite over the generic points exactly when it is finite over an open
  subscheme containing them.
* `AlgebraicGeometry.Scheme.Hom.IsNoetherianAlteration.comp`: noetherian alterations compose.
* `AlgebraicGeometry.Scheme.Hom.isNoetherianAlteration_iff_isAlteration`: from an irreducible
  source, noetherian alterations are the alterations of `TauCeti.AlgebraicGeometry.IsAlteration`.

## References

* M. Temkin, *Tame distillation and desingularization by p-alterations*, Ann. of Math. 186
  (2017), §4.1.2.
* L. Illusie, Y. Laszlo, F. Orgogozo (eds.), *Travaux de Gabber sur l'uniformisation locale et la
  cohomologie étale des schémas quasi-excellents*, Astérisque 363–364 (2014), Exposé II,
  Définition 1.1.2, and Exposé X, §3.3.1.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` is *finite over the generic points* of `Y` if its base change
`X ×_Y η_Y ⟶ η_Y` to the scheme of generic points of `Y` is finite. -/
def IsFiniteOverGenericPoints (f : X ⟶ Y) : Prop :=
  IsFinite (pullback.snd f Y.fromGenericPointScheme)

/-- Finiteness over the generic points is finiteness of the base change to the scheme of generic
points. -/
theorem isFiniteOverGenericPoints_iff (f : X ⟶ Y) :
    f.IsFiniteOverGenericPoints ↔ IsFinite (pullback.snd f Y.fromGenericPointScheme) :=
  Iff.rfl

/-- A morphism is finite over the generic points of its target exactly when its fibre over each
component-generic point `y` is finite over `Spec κ(y)`. -/
theorem isFiniteOverGenericPoints_iff_forall_isFinite_fiberToSpecResidueField (f : X ⟶ Y) :
    f.IsFiniteOverGenericPoints ↔
      ∀ y ∈ genericPoints Y, IsFinite (f.fiberToSpecResidueField y) := by
  have key (y : genericPoints Y) :
      let ι := Sigma.ι (fun y : genericPoints Y ↦ Spec (Y.residueField y)) y
      IsFinite (pullback.snd (pullback.snd f Y.fromGenericPointScheme) ι) ↔
        IsFinite (f.fiberToSpecResidueField y) := by
    intro ι
    have h : IsPullback (pullback.fst _ ι ≫ pullback.fst _ _)
        (pullback.snd (pullback.snd f Y.fromGenericPointScheme) ι) f
        (Y.fromSpecResidueField y) := by
      rw [← Y.ι_fromGenericPointScheme y]
      exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
    -- `f.fiberToSpecResidueField y` is by definition the second projection of this pullback.
    rw [← h.isoPullback_hom_snd, MorphismProperty.cancel_left_of_respectsIso @IsFinite]
    rfl
  rw [isFiniteOverGenericPoints_iff, IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite)
    (sigmaOpenCover fun y : genericPoints Y ↦ Spec (Y.residueField y))]
  exact ⟨fun h y hy ↦ (key ⟨y, hy⟩).mp (h ⟨y, hy⟩),
    fun h ⟨y, hy⟩ ↦ (key ⟨y, hy⟩).mpr (h y hy)⟩

/-- A quasi-compact morphism locally of finite type is finite over the generic points of its
target exactly when its fibres over the component-generic points are finite sets. -/
theorem isFiniteOverGenericPoints_iff_forall_finite_preimage_singleton (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    f.IsFiniteOverGenericPoints ↔ ∀ y ∈ genericPoints Y, (f ⁻¹' {y}).Finite := by
  simp only [isFiniteOverGenericPoints_iff_forall_isFinite_fiberToSpecResidueField,
    isFinite_fiberToSpecResidueField_iff_finite_preimage_singleton]

/-- A finite morphism is finite over the generic points of its target. -/
theorem isFiniteOverGenericPoints_of_isFinite (f : X ⟶ Y) [IsFinite f] :
    f.IsFiniteOverGenericPoints := by
  rw [isFiniteOverGenericPoints_iff]
  infer_instance

/-- If `f` is finite over the generic points of its target, every point of `X` lying over a
component-generic point of `Y` is a component-generic point of `X`. -/
theorem IsFiniteOverGenericPoints.mem_genericPoints {f : X ⟶ Y}
    (hf : f.IsFiniteOverGenericPoints) {x : X} (hx : f x ∈ genericPoints Y) :
    x ∈ genericPoints X := by
  have := (f.isFiniteOverGenericPoints_iff_forall_isFinite_fiberToSpecResidueField.mp hf) _ hx
  have : DiscreteTopology (f ⁻¹' {f x}) :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton_of_isFinite (f x))
  refine TauCeti.mem_genericPoints_iff.mpr fun x' hx' ↦ ?_
  have hfx' : f x' = f x := TauCeti.mem_genericPoints_iff.mp hx _ (hx'.map f.continuous)
  exact congrArg Subtype.val
    (((subtype_specializes_iff (p := (· ∈ f ⁻¹' {f x})) ⟨x', hfx'⟩ ⟨x, rfl⟩).mpr hx').eq)

/-- A composite of quasi-compact morphisms locally of finite type that are finite over the
generic points of their targets is finite over the generic points of its target. -/
theorem IsFiniteOverGenericPoints.comp {f : X ⟶ Y} {g : Y ⟶ Z} [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    (hg : g.IsFiniteOverGenericPoints) (hf : f.IsFiniteOverGenericPoints) :
    (f ≫ g).IsFiniteOverGenericPoints := by
  have hg' := g.isFiniteOverGenericPoints_iff_forall_finite_preimage_singleton.mp hg
  rw [isFiniteOverGenericPoints_iff_forall_finite_preimage_singleton] at hf ⊢
  intro z hz
  rw [comp_base, TopCat.coe_comp, preimage_comp]
  exact (hg' z hz).preimage' fun y hy ↦ hf y (hg.mem_genericPoints (by rwa [hy]))

/-- **Spreading out finiteness from the generic points.** A proper morphism is finite over the
generic points of its target exactly when it is finite over an open subscheme of the target
containing every component-generic point. The open subscheme can be taken to be the complement of
the image of the locus where `f` is not quasi-finite. -/
theorem isFiniteOverGenericPoints_iff_exists_isFinite_morphismRestrict (f : X ⟶ Y)
    [IsProper f] :
    f.IsFiniteOverGenericPoints ↔ ∃ U : Y.Opens, genericPoints Y ⊆ U ∧ IsFinite (f ∣_ U) := by
  constructor
  · intro hf
    rw [isFiniteOverGenericPoints_iff_forall_isFinite_fiberToSpecResidueField] at hf
    let U : Y.Opens := ⟨(f '' (f.quasiFiniteLocus : Set X)ᶜ)ᶜ,
      (f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl).isOpen_compl⟩
    refine ⟨U, fun y hy ⟨x, hx, hxy⟩ ↦ hx ?_, ?_⟩
    · have := hf y hy
      subst hxy
      exact quasiFiniteAt_of_isFinite_fiberToSpecResidueField
    · have : LocallyQuasiFinite (f ∣_ U) := by
        rw [← quasiFiniteLocus_eq_top_iff, eq_top_iff]
        rintro x -
        rw [mem_quasiFiniteLocus, ← quasiFiniteAt_comp_iff (g := U.ι), morphismRestrict_ι,
          quasiFiniteAt_comp_iff_of_isOpenImmersion]
        by_contra hx
        exact x.property ⟨_, hx, rfl⟩
      exact .of_isProper_of_locallyQuasiFinite _
  · rintro ⟨U, hU, _⟩
    rw [isFiniteOverGenericPoints_iff_forall_finite_preimage_singleton]
    intro y hy
    refine (((f ∣_ U).finite_preimage_singleton ⟨y, hU hy⟩).image (f ⁻¹ᵁ U).ι).subset ?_
    intro x (hx : f x = y)
    exact ⟨⟨x, (hx ▸ hU hy : f x ∈ U)⟩,
      Subtype.ext ((morphismRestrict_base_coe f U _).trans hx), rfl⟩

/-- A morphism `f : X ⟶ Y` is a *noetherian alteration* if it is proper, surjective, maximally
dominating and finite over the generic points of its target, that is, its base change to the
scheme of generic points of `Y` is finite. This is the notion of alteration for noetherian schemes
that need not be irreducible (Temkin, §4.1.2; Illusie–Laszlo–Orgogozo, Exposé X, §3.3.1). -/
structure IsNoetherianAlteration (f : X ⟶ Y) : Prop where
  isProper : IsProper f
  surjective : Surjective f
  isMaximallyDominating : f.IsMaximallyDominating
  isFiniteOverGenericPoints : f.IsFiniteOverGenericPoints

/-- A noetherian alteration is a proper, surjective, maximally dominating morphism that is finite
over the generic points of its target. -/
theorem isNoetherianAlteration_iff (f : X ⟶ Y) :
    f.IsNoetherianAlteration ↔ IsProper f ∧ Surjective f ∧ f.IsMaximallyDominating ∧
      f.IsFiniteOverGenericPoints :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

/-- A composite of noetherian alterations is a noetherian alteration. -/
theorem IsNoetherianAlteration.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hg : g.IsNoetherianAlteration)
    (hf : f.IsNoetherianAlteration) : (f ≫ g).IsNoetherianAlteration := by
  have := hf.isProper
  have := hf.surjective
  have := hg.isProper
  have := hg.surjective
  exact ⟨inferInstance, inferInstance, hg.isMaximallyDominating.comp hf.isMaximallyDominating,
    hg.isFiniteOverGenericPoints.comp hf.isFiniteOverGenericPoints⟩

/-- A finite surjective maximally dominating morphism is a noetherian alteration. -/
theorem isNoetherianAlteration_of_isFinite (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (hf : f.IsMaximallyDominating) : f.IsNoetherianAlteration :=
  ⟨inferInstance, inferInstance, hf, f.isFiniteOverGenericPoints_of_isFinite⟩

/-- The identity of a scheme is a noetherian alteration. -/
theorem _root_.AlgebraicGeometry.Scheme.isNoetherianAlteration_id (X : Scheme.{u}) :
    IsNoetherianAlteration (𝟙 X) :=
  isNoetherianAlteration_of_isFinite _ X.isMaximallyDominating_id

/-- **Comparison with alterations of integral schemes.** A morphism from an irreducible scheme is
a noetherian alteration exactly when it is an alteration in the sense of
`TauCeti.AlgebraicGeometry.IsAlteration`: proper, dominant and finite over a nonempty open. -/
theorem isNoetherianAlteration_iff_isAlteration [IrreducibleSpace X] (f : X ⟶ Y) :
    f.IsNoetherianAlteration ↔ TauCeti.AlgebraicGeometry.IsAlteration f := by
  rw [TauCeti.AlgebraicGeometry.isAlteration_iff]
  constructor
  · rintro ⟨_, _, hmd, hfin⟩
    obtain ⟨U, hU, _⟩ :=
      (isFiniteOverGenericPoints_iff_exists_isFinite_morphismRestrict f).mp hfin
    have hX : genericPoint X ∈ genericPoints X := by
      rw [genericPoints_eq_singleton]
      exact mem_singleton _
    exact ⟨inferInstance, inferInstance, U, ⟨_, hU (f.isMaximallyDominating_iff.mp hmd _ hX)⟩,
      inferInstance⟩
  · rintro ⟨_, _, U, hU, _⟩
    have := f.irreducibleSpace_of_isDominant
    refine ⟨inferInstance, inferInstance, isMaximallyDominating_of_isDominant f,
      (isFiniteOverGenericPoints_iff_exists_isFinite_morphismRestrict f).mpr
        ⟨U, ?_, inferInstance⟩⟩
    rw [genericPoints_eq_singleton, singleton_subset_iff]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by rwa [univ_inter])

/-- A modification of an irreducible scheme is a noetherian alteration. -/
theorem isNoetherianAlteration_of_isModification [IrreducibleSpace X] (f : X ⟶ Y)
    [TauCeti.AlgebraicGeometry.IsModification f] : f.IsNoetherianAlteration := by
  have : Nonempty Y := ⟨f (Nonempty.some inferInstance)⟩
  exact (isNoetherianAlteration_iff_isAlteration f).mpr inferInstance

end AlgebraicGeometry.Scheme.Hom
