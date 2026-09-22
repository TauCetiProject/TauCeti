/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.EpiMono
public import TauCeti.Geometry.Hodge.Orthogonal
public import TauCeti.Geometry.Hodge.Prod
public import TauCeti.Geometry.Hodge.Retract
public import TauCeti.Order.Atoms
public import Mathlib.CategoryTheory.Simple

/-!
# Polarizable pure Hodge structures are semisimple

A polarization splits off every rational Hodge substructure, so the lattice of rational Hodge
substructures of a polarizable pure Hodge structure is complemented. Over a finite-dimensional
rational space that lattice is also modular and satisfies the descending chain condition, and the
two properties together give the classical decomposition: a polarizable pure Hodge structure is
the direct sum of finitely many **simple** rational Hodge substructures — the atoms of the lattice
— pairwise independent and spanning.

The complement itself is the orthogonal complement
`TauCeti.Hodge.RationalHodgeSubstructure.orthogonal` for a polarizing form; the decomposition is
then the lattice-theoretic `TauCeti.exists_finset_isAtom_sup_eq`, which splits off one atom at a
time in any complemented modular lattice with the descending chain condition.
Only *some* polarizing form is used, never a chosen one, so the statements are about
`TauCeti.Hodge.IsPolarizable` structures: this is the semisimplicity of the polarizable Hodge
structures, for which the choice of a form is not part of the object. Categorically, every
monomorphism of polarizable rational Hodge structures corestricts to an isomorphism onto its
rational image. The orthogonal retraction of that image therefore splits the original
monomorphism, making `TauCeti.Hodge.PolarizableHodgeStructureCat` a `SplitMonoCategory`.
The finite independent family of atoms also assembles through categorical biproducts, so every
object is isomorphic to a finite biproduct of simple objects.

Following Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink,
*Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure.complementedLattice_of_isPolarizable`: the lattice of
  rational Hodge substructures of a polarizable pure Hodge structure is complemented.
* `TauCeti.Hodge.RationalHodgeSubstructure.exists_finset_isAtom_sup_eq`: every rational Hodge
  substructure is the supremum of a finite independent family of simple substructures.
* `TauCeti.Hodge.exists_finset_isAtom_sup_eq_top`: **semisimplicity**, a polarizable pure Hodge
  structure is the direct sum of finitely many simple rational Hodge substructures.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.instSplitMonoCategory`: every monomorphism of
  polarizable rational Hodge structures splits.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.exists_iso_biproduct_simple`: every object is
  isomorphic to a finite biproduct of simple objects.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n} [Module.Finite ℚ Vℚ]

namespace RationalHodgeSubstructure

/-- A polarization makes the lattice of rational Hodge substructures complemented: the orthogonal
complement for its form is a lattice complement. -/
theorem complementedLattice (P : Polarization hℂ hs) :
    ComplementedLattice (RationalHodgeSubstructure hℚ hs) :=
  ⟨fun W ↦ ⟨orthogonal P W, isCompl_orthogonal P W⟩⟩

/-- **Every rational Hodge substructure of a polarizable pure Hodge structure is a direct
summand**: the lattice of rational Hodge substructures is complemented. -/
theorem complementedLattice_of_isPolarizable (h : IsPolarizable hℂ hs) :
    ComplementedLattice (RationalHodgeSubstructure hℚ hs) :=
  let ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  complementedLattice P

/-- **Every rational Hodge substructure of a polarized pure Hodge structure is a finite direct sum
of simple substructures**: it is the supremum of a finite family of atoms of the lattice of
rational Hodge substructures, pairwise independent. -/
theorem exists_finset_isAtom_sup_eq (P : Polarization hℂ hs) (W : RationalHodgeSubstructure hℚ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = W :=
  have : ComplementedLattice (RationalHodgeSubstructure hℚ hs) := complementedLattice P
  _root_.TauCeti.exists_finset_isAtom_sup_eq W

end RationalHodgeSubstructure

/-- **Semisimplicity of polarizable pure Hodge structures.** A polarizable pure Hodge structure on
a finite-dimensional rational space is the direct sum of finitely many simple rational Hodge
substructures: there is a finite independent family of atoms of the lattice of rational Hodge
substructures whose supremum is everything. -/
theorem exists_finset_isAtom_sup_eq_top (hℚ : IsBaseChange ℚ ιℚ) (h : IsPolarizable hℂ hs) :
    ∃ s : Finset (RationalHodgeSubstructure hℚ hs),
      (∀ U ∈ s, IsAtom U) ∧ s.SupIndep id ∧ s.sup id = ⊤ := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  exact RationalHodgeSubstructure.exists_finset_isAtom_sup_eq P ⊤

namespace PolarizableHodgeStructureCat

open CategoryTheory Limits

universe u'

variable {n' : ℤ}

/-- **Categorical semisimplicity of polarizable rational Hodge structures.** Every monomorphism
splits. The splitting is obtained by identifying the source with the rational image and then
using the orthogonal retraction of that image in the target. -/
noncomputable instance instSplitMonoCategory :
    SplitMonoCategory (PolarizableHodgeStructureCat.{u'} n') where
  isSplitMono_of_mono {X Y} f := by
    intro hf
    let _ : Mono f := hf
    have hfC := Hom.isMorphism f
    rw [MixedHodgeStructure.Hom.toLinearMap_def] at hfC
    let W := RationalHodgeSubstructure.ofRationalMorphismRange hfC
    have hWQ : W.WQ = LinearMap.range f.hom.toRatLinearMap :=
      RationalHodgeSubstructure.ofRationalMorphismRange_WQ hfC
    let fWQ : X.ratCarrier →ₗ[ℚ] W.WQ :=
      (LinearEquiv.ofEq _ _ hWQ.symm).toLinearMap.comp f.hom.toRatLinearMap.rangeRestrict
    have hfWQ_codRestrict : fWQ =
        f.hom.toRatLinearMap.codRestrict W.WQ fun x ↦ by
          rw [hWQ]
          exact LinearMap.mem_range_self f.hom.toRatLinearMap x := by
      ext
      rfl
    let fW : X ⟶ ofSubstructure Y W :=
      Hom.ofIsMorphism fWQ <| by
        rw [hfWQ_codRestrict]
        exact isMorphism_codRestrict W f.hom.toRatLinearMap hfC fun x ↦ by
          rw [hWQ]
          exact LinearMap.mem_range_self f.hom.toRatLinearMap x
    have hfWQ : fW.hom.toRatLinearMap = fWQ :=
      Hom.ofIsMorphism_toRatLinearMap _ _
    have hfW_bijective : Function.Bijective fW.hom.toRatLinearMap := by
      rw [hfWQ]
      simpa only [fWQ, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap] using
        (LinearEquiv.ofEq _ _ hWQ.symm).bijective.comp
          ⟨(LinearMap.injective_rangeRestrict_iff _).2 <| (mono_iff_injective f).1 inferInstance,
            LinearMap.surjective_rangeRestrict _⟩
    let _ : IsIso fW := (isIso_iff_bijective fW).2 hfW_bijective
    have hfactor : fW ≫ substructureInclusion Y W = f := by
      apply Hom.ext
      rw [comp_toRatLinearMap, substructureInclusion_toRatLinearMap, hfWQ]
      rw [hfWQ_codRestrict]
      exact LinearMap.subtype_comp_codRestrict _ _ _
    let _ : IsSplitMono (substructureInclusion Y W) :=
      isSplitMono_substructureInclusion Y W
    rw [← hfactor]
    infer_instance

/-! ### Decomposition into simple objects -/

variable {n : ℤ} (X : PolarizableHodgeStructureCat.{u'} n)

/-- The canonical map from the biproduct of a finite family of rational Hodge substructures to
the ambient Hodge structure. -/
noncomputable def substructureBiproductDesc
    (s : Finset (RationalHodgeSubstructure X.isBaseChangeRat X.hs)) :
    (⨁ fun U : s ↦ ofSubstructure X U.1) ⟶ X :=
  biproduct.desc fun U ↦ substructureInclusion X U.1

/-- The canonical map out of the biproduct restricts on each summand to the inclusion of the
corresponding rational Hodge substructure. -/
@[simp]
theorem biproduct_ι_comp_substructureBiproductDesc
    (s : Finset (RationalHodgeSubstructure X.isBaseChangeRat X.hs)) (U : s) :
    biproduct.ι (fun U : s ↦ ofSubstructure X U.1) U ≫
      substructureBiproductDesc X s = substructureInclusion X U.1 := by
  rw [substructureBiproductDesc, biproduct.ι_desc]

/-- A nonzero morphism into the object induced by an atomic rational Hodge substructure is
surjective on rational carriers.

Its rational image is a rational Hodge substructure of the atom `U`, and it is not `⊥` because the
morphism is nonzero, so it is all of `U`. -/
theorem surjective_of_isAtom_of_ne_zero {Y : PolarizableHodgeStructureCat.{u'} n}
    {U : RationalHodgeSubstructure X.isBaseChangeRat X.hs} (hU : IsAtom U)
    {f : Y ⟶ ofSubstructure X U} (hf : f ≠ 0) :
    Function.Surjective f.hom.toRatLinearMap := by
  -- The composite with the inclusion has a rational image `V`, a substructure of the ambient `X`.
  let g : Y ⟶ X := f ≫ substructureInclusion X U
  have hg := Hom.isMorphism g
  rw [MixedHodgeStructure.Hom.toLinearMap_def] at hg
  let V : RationalHodgeSubstructure X.isBaseChangeRat X.hs :=
    RationalHodgeSubstructure.ofRationalMorphismRange hg
  -- It is contained in `U`, since `g` factors through the inclusion of `U`.
  have hVU : V ≤ U := by
    rw [RationalHodgeSubstructure.le_def,
      RationalHodgeSubstructure.ofRationalMorphismRange_WQ]
    rw [← Submodule.range_subtype U.WQ]
    simpa only [g, comp_toRatLinearMap, substructureInclusion_toRatLinearMap] using
      (LinearMap.range_comp_le_range f.hom.toRatLinearMap U.WQ.subtype)
  -- It is nonzero, because the inclusion of `U` is injective and `f ≠ 0`.
  have hVne : V ≠ ⊥ := by
    intro hV
    apply hf
    apply Hom.ext
    rw [zero_toRatLinearMap]
    apply LinearMap.ext
    intro y
    apply Submodule.injective_subtype U.WQ
    have hgzero : g.hom.toRatLinearMap = 0 := by
      apply LinearMap.range_eq_bot.1
      rw [← RationalHodgeSubstructure.ofRationalMorphismRange_WQ hg]
      simpa only [V, RationalHodgeSubstructure.bot_WQ] using
        congrArg RationalHodgeSubstructure.WQ hV
    have := LinearMap.congr_fun hgzero y
    simpa only [g, comp_toRatLinearMap, substructureInclusion_toRatLinearMap,
      LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using this
  -- As `U` is an atom, the image is all of `U`, which is surjectivity of `f`.
  have hVUeq : V = U := (hU.ne_bot_iff_eq hVU).1 hVne
  intro y
  let y' : U.WQ := y
  have hy : U.WQ.subtype y' ∈ LinearMap.range g.hom.toRatLinearMap := by
    rw [← RationalHodgeSubstructure.ofRationalMorphismRange_WQ hg]
    have : U.WQ.subtype y' ∈ V.WQ := by rw [hVUeq]; exact y'.property
    simpa only [V] using this
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply Submodule.injective_subtype U.WQ
  simpa only [g, comp_toRatLinearMap, substructureInclusion_toRatLinearMap,
    LinearMap.comp_apply] using hx

/-- An atom of the lattice of rational Hodge substructures gives a simple object of the category
of polarizable rational Hodge structures. -/
theorem simple_of_isAtom
    {U : RationalHodgeSubstructure X.isBaseChangeRat X.hs} (hU : IsAtom U) :
    Simple (ofSubstructure X U) := by
  constructor
  intro Y f hf
  constructor
  · -- An isomorphism is nonzero: were the zero morphism surjective, `U` would be `⊥`.
    intro hfiso hfzero
    have hsurj := (isIso_iff_bijective f).1 hfiso |>.2
    apply hU.ne_bot
    apply RationalHodgeSubstructure.ext
    ext x
    simp only [RationalHodgeSubstructure.bot_WQ, Submodule.mem_bot]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hsurj (⟨x, hx⟩ : (ofSubstructure X U).ratCarrier)
      have hfmap : f.hom.toRatLinearMap = 0 := by
        rw [hfzero, zero_toRatLinearMap]
      have : (⟨x, hx⟩ : (ofSubstructure X U).ratCarrier) = 0 := by
        rw [← hy, hfmap, LinearMap.zero_apply]
      exact congrArg Subtype.val this
    · rintro rfl
      exact U.WQ.zero_mem
  · -- A nonzero monomorphism is injective by assumption and surjective by the range argument.
    intro hfzero
    exact (isIso_iff_bijective f).2
      ⟨(mono_iff_injective f).1 inferInstance, surjective_of_isAtom_of_ne_zero X hU hfzero⟩

/-- An independent finite family of rational Hodge substructures spanning the ambient structure
gives an isomorphism from their biproduct to the ambient object. -/
noncomputable def substructureBiproductIso
    (s : Finset (RationalHodgeSubstructure X.isBaseChangeRat X.hs))
    (hind : s.SupIndep id) (htop : s.sup id = ⊤) :
    (⨁ fun U : s ↦ ofSubstructure X U.1) ≅ X := by
  classical
  let complement : s → RationalHodgeSubstructure X.isBaseChangeRat X.hs :=
    fun U ↦ (s.erase U.1).sup id
  let hcompl : ∀ U, IsCompl U.1 (complement U) :=
    fun U ↦ hind.isCompl_sup_erase htop U.2
  let r : X ⟶ (⨁ fun U : s ↦ ofSubstructure X U.1) :=
    biproduct.lift fun U ↦ substructureRetractionOfIsCompl X U.1 (complement U) (hcompl U)
  let d := substructureBiproductDesc X s
  have hdr : d ≫ r = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro U
    apply biproduct.hom_ext
    intro T
    simp only [d, r, substructureBiproductDesc, biproduct.ι_desc_assoc]
    rw [Category.assoc, biproduct.lift_π, Category.comp_id, biproduct.ι_π]
    by_cases hUT : U = T
    · subst T
      rw [substructureInclusion_comp_substructureRetractionOfIsCompl]
      simp
    · rw [substructureInclusion_comp_substructureRetractionOfIsCompl_eq_zero X T.1
        (complement T) (U := U.1) (hcompl T)]
      · simp [hUT]
      · exact (Finset.le_sup (f := fun W : RationalHodgeSubstructure
          X.isBaseChangeRat X.hs ↦ W)
          (Finset.mem_erase.2 ⟨fun h ↦ hUT (Subtype.ext h), U.2⟩) :
            U.1 ≤ (s.erase T.1).sup id)
  let _ : IsSplitMono d := IsSplitMono.mk' ⟨r, hdr⟩
  let _ : Mono d := inferInstance
  have hd_surjective : Function.Surjective d.hom.toRatLinearMap := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    have hWQtop : (s.sup id).WQ = ⊤ := by rw [htop, RationalHodgeSubstructure.top_WQ]
    rw [← hWQtop, RationalHodgeSubstructure.finsetSup_WQ]
    apply Finset.sup_le
    rintro U hU x hx
    let i : (ofSubstructure X U).ratCarrier →ₗ[ℚ]
        (⨁ fun T : s ↦ ofSubstructure X T.1).ratCarrier :=
      (biproduct.ι (fun T : s ↦ ofSubstructure X T.1) ⟨U, hU⟩).hom.toRatLinearMap
    refine ⟨i ⟨x, hx⟩, ?_⟩
    have hmap := congrArg (fun f ↦ f.hom.toRatLinearMap)
      (biproduct_ι_comp_substructureBiproductDesc X s ⟨U, hU⟩)
    rw [comp_toRatLinearMap, substructureInclusion_toRatLinearMap] at hmap
    exact LinearMap.congr_fun hmap ⟨x, hx⟩
  let _ : Epi d := (epi_iff_surjective d).2 hd_surjective
  let _ : IsIso d := isIso_of_mono_of_epi d
  exact asIso d

/-- The isomorphism from an independent spanning family restricts on each summand to its
substructure inclusion. -/
@[simp]
theorem biproduct_ι_comp_substructureBiproductIso_hom
    (s : Finset (RationalHodgeSubstructure X.isBaseChangeRat X.hs))
    (hind : s.SupIndep id) (htop : s.sup id = ⊤) (U : s) :
    biproduct.ι (fun U : s ↦ ofSubstructure X U.1) U ≫
      (substructureBiproductIso X s hind htop).hom = substructureInclusion X U.1 := by
  rw [substructureBiproductIso, asIso_hom,
    biproduct_ι_comp_substructureBiproductDesc]

/-- **Categorical semisimplicity of polarizable rational Hodge structures.** Every object is
isomorphic to a finite biproduct of simple objects induced by rational Hodge substructures. -/
theorem exists_iso_biproduct_simple :
    ∃ s : Finset (RationalHodgeSubstructure X.isBaseChangeRat X.hs),
      (∀ U ∈ s, Simple (ofSubstructure X U)) ∧
        Nonempty ((⨁ fun U : s ↦ ofSubstructure X U.1) ≅ X) := by
  obtain ⟨s, hatom, hind, htop⟩ :=
    exists_finset_isAtom_sup_eq_top X.isBaseChangeRat X.isPolarizable
  exact ⟨s, fun U hU ↦ simple_of_isAtom X (hatom U hU),
    ⟨substructureBiproductIso X s hind htop⟩⟩

end PolarizableHodgeStructureCat

end TauCeti.Hodge
