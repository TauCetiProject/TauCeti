/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.Algebra.Module.ProjectiveCover.Simple
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.AlmostSplit
public import TauCeti.CategoryTheory.IrreducibleMorphism
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Category.ModuleCat.Injective.LeftAlmostSplit
import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.ModuleCat.Minimal
import TauCeti.CategoryTheory.AlmostSplit.Equivalence
import TauCeti.CategoryTheory.AlmostSplit.Irreducible.Basic
import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Preadditive.Radical.Basic

/-!
# Source and sink maps in `FGModuleCat`

## The inclusion of the radical of a projective module

Let `P` be a finitely generated projective module with local endomorphism ring and finitely
generated radical, as for an indecomposable projective module over an Artin algebra. A morphism
into `P` that is not a split epimorphism is not surjective, so its image is a proper submodule and
lies in the radical of `P`. So the inclusion `rad P ⟶ P` is right almost split in `FGModuleCat`.
It plays the role of the final map of an almost-split sequence at a projective module, where no
such sequence ends. In the functorial picture it presents the simple functor `S_P`, and
`(-, rad P) ⟶ rad(-, P)` is a projective cover.

## Source and sink maps with irreducible components

Over an Artinian ring, let `X` be a finitely generated indecomposable module that has a left
almost split map in `FGModuleCat A` unless it is injective there. Then `X` has a source map, a
left minimal left almost split map, into a finite biproduct of finitely generated indecomposable
modules whose components are irreducible: at an injective module it is `X ⟶ X ⧸ soc X`, and
otherwise the given map is corestricted to a summand of its target onto which it is left minimal
(`ModuleCat.exists_retract_left_minimal`). Dually for sink maps, where `rad X ⟶ X` serves at a
projective module and the Krull–Schmidt property of `FGModuleCat A` gives minimality otherwise.

## Main results

* `FGModuleCat.isRightAlmostSplit_ofHom_subtype_jacobson`: the inclusion of the radical is right
  almost split.
* `FGModuleCat.isRepresentableProjectiveCover_radicalFunctorLift_ofHom_subtype_jacobson`: the map
  `(-, rad P) ⟶ rad(-, P)` is a projective cover.
* `FGModuleCat.exists_isLeftAlmostSplit_biproduct` and
  `FGModuleCat.exists_isRightAlmostSplit_biproduct`: source and sink maps with irreducible
  components.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections V.1 and VI.1.
-/

public section

namespace FGModuleCat

open CategoryTheory TauCeti

universe w v

section Projective

variable (A : Type v) [Ring A] (P : Type w) [AddCommGroup P] [Module A P] [Module.Finite A P]
  [Module.Finite A (Module.jacobson A P)] [Module.Projective A P] [IsLocalRing (Module.End A P)]

/-- **The sink map of a projective module.** For a finitely generated projective module `P` with
local endomorphism ring and finitely generated radical, the inclusion `rad P ⟶ P` is right almost
split in `FGModuleCat`. -/
theorem isRightAlmostSplit_ofHom_subtype_jacobson :
    IsRightAlmostSplit (ofHom (Module.jacobson A P).subtype) := by
  have : Nontrivial P := nontrivial_of_nontrivial_end (R := A) (M := P)
  have hlt := Module.jacobson_lt_top A P
  refine isRightAlmostSplit_iff.2 ⟨fun hs ↦ hlt.ne (Submodule.eq_top_iff'.2 fun x ↦ ?_),
    fun W g hg ↦ ?_⟩
  · let s := section_ (ofHom (Module.jacobson A P).subtype)
    have hx : ((s.hom.hom x : Module.jacobson A P) : P) = x :=
      congrArg (fun φ : of A P ⟶ of A P ↦ φ.hom.hom x)
        (IsSplitEpi.id (ofHom (Module.jacobson A P).subtype))
    exact hx ▸ (s.hom.hom x).property
  · have hrange : LinearMap.range g.hom.hom ≠ ⊤ := fun htop ↦ hg ?_
    · have hle := le_jacobson_of_ne_top_of_isLocalRing_end hrange
      refine ⟨ObjectProperty.homMk (ModuleCat.ofHom
        (g.hom.hom.codRestrict _ fun x ↦ hle ⟨x, rfl⟩)), ?_⟩
      ext x
      rfl
    · obtain ⟨s, hs⟩ := Module.projective_lifting_property g.hom.hom LinearMap.id
        (LinearMap.range_eq_top.1 htop)
      exact .mk' ⟨ObjectProperty.homMk (ModuleCat.ofHom s), by
        ext x
        exact LinearMap.congr_fun hs x⟩

/-- For a finitely generated projective module `P` with local endomorphism ring and finitely
generated radical, the map `(-, rad P) ⟶ rad(-, P)` induced by the inclusion is a projective
cover. -/
theorem isRepresentableProjectiveCover_radicalFunctorLift_ofHom_subtype_jacobson :
    IsRepresentableProjectiveCover (radicalFunctorLift (ofHom (Module.jacobson A P).subtype)
      (isRightAlmostSplit_ofHom_subtype_jacobson A P).mem_jacobsonRadical) :=
  have : Mono (ofHom (Module.jacobson A P).subtype) :=
    ConcreteCategory.mono_of_injective _ Subtype.val_injective
  (isRightAlmostSplit_ofHom_subtype_jacobson A P).isRepresentableProjectiveCover_radicalFunctorLift

end Projective

/-! ### Source and sink maps with irreducible components -/

section Artinian

open CategoryTheory.Limits

variable {A : Type v} [Ring A] [IsArtinianRing A] [Small.{w} A]

/-- **Source maps.** Let `A` be an Artinian ring, and `X` a finitely generated indecomposable
module that, unless it is injective in `FGModuleCat A`, has a left almost split map in
`FGModuleCat A`. Then `X` has a left minimal left almost split map into a finite biproduct of
finitely generated indecomposable modules, each of whose components is irreducible. -/
theorem exists_isLeftAlmostSplit_biproduct {X : FGModuleCat.{w} A} (hX : Indecomposable X.obj)
    (hsrc : ¬ Injective X → ∃ (E : FGModuleCat.{w} A) (i : X ⟶ E), IsLeftAlmostSplit i) :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A) (i : X ⟶ ⨁ F),
      (∀ j, Indecomposable (F j).obj) ∧ IsLeftAlmostSplit i ∧
        (∀ u : ⨁ F ⟶ ⨁ F, i ≫ u = i → IsIso u) ∧
          ∀ j, IsIrreducibleMorphism (i ≫ biproduct.π F j) := by
  -- A left minimal left almost split map.
  obtain ⟨E, f, hf, hmin⟩ : ∃ (E : FGModuleCat.{w} A) (f : X ⟶ E), IsLeftAlmostSplit f ∧
      ∀ u : E ⟶ E, f ≫ u = f → IsIso u := by
    by_cases hinj : Injective X
    · -- By Baer's criterion `X` is an injective module, with the source map `X ⟶ X ⧸ soc X`.
      have := moduleInjective_of_injective X
      have : Injective X.obj := Module.injective_object_of_injective_module A X
      have : IsLocalRing (End X.obj) := (indecomposable_iff_isLocalRing_end X.obj
        (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)).mp hX
      obtain ⟨S, -, hS⟩ := exists_isAtom_isLeftAlmostSplit_ofHom_mkQ (N := X.obj)
      let q : X ⟶ of A (X ⧸ S) := ObjectProperty.homMk (ModuleCat.ofHom S.mkQ)
      have : Epi q := (ObjectProperty.ι _).epi_of_epi_map
        ((ModuleCat.epi_iff_surjective _).mpr S.mkQ_surjective)
      refine ⟨_, q, (ObjectProperty.ι _).isLeftAlmostSplit_of_map q hS, fun u hu ↦ ?_⟩
      rw [(cancel_epi q).mp (hu.trans (Category.comp_id _).symm)]
      infer_instance
    · -- Corestrict the assumed map to a summand of its target onto which it is left minimal.
      obtain ⟨E, i, hi⟩ := hsrc hinj
      have hE : IsFiniteLength A E.obj :=
        isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
      obtain ⟨P, r, hr, hmin⟩ := ModuleCat.exists_retract_left_minimal
        ((ObjectProperty.ι _).map i) hE
      have : Module.Finite A ((ObjectProperty.ι (ModuleCat.isFG.{w} A)).obj E) :=
        inferInstanceAs (Module.Finite A E.obj)
      have : Module.Finite A P :=
        Module.Finite.of_surjective r.r.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      let r' : Retract (⟨P, (ModuleCat.isFG_iff _).mpr this⟩ : FGModuleCat.{w} A) E :=
        ⟨ObjectProperty.homMk r.i, ObjectProperty.homMk r.r,
          (ObjectProperty.ι _).map_injective r.retract⟩
      refine ⟨_, i ≫ r'.r, hi.comp_retract_r r' ((ObjectProperty.ι _).map_injective hr),
        fun u hu ↦ ?_⟩
      have : IsIso ((ObjectProperty.ι _).map u) := hmin _ (congrArg (ObjectProperty.ι _).map hu)
      exact isIso_of_fully_faithful (ObjectProperty.ι _) u
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
  refine ⟨n, F, f ≫ e.hom, hF, hf.comp_iso e.hom, left_minimal_comp_iso hmin e.hom,
    fun j ↦ ?_⟩
  rw [Category.assoc]
  exact hf.isIrreducibleMorphism_comp_of_not_isZero hmin
    (fun hz ↦ (hF j).1 ((ObjectProperty.ι _).map_isZero hz)) _

/-- **Sink maps.** Let `A` be an Artinian ring, and `X` a finitely generated indecomposable module
that, unless it is projective in `FGModuleCat A`, has a right almost split map in
`FGModuleCat A`. Then `X` has a right minimal right almost split map out of a finite biproduct of
finitely generated indecomposable modules, each of whose components is irreducible. -/
theorem exists_isRightAlmostSplit_biproduct {X : FGModuleCat.{w} A} (hX : Indecomposable X.obj)
    (hsink : ¬ Projective X → ∃ (E : FGModuleCat.{w} A) (p : E ⟶ X), IsRightAlmostSplit p) :
    ∃ (n : ℕ) (F : Fin n → FGModuleCat.{w} A) (p : ⨁ F ⟶ X),
      (∀ j, Indecomposable (F j).obj) ∧ IsRightAlmostSplit p ∧
        (∀ u : ⨁ F ⟶ ⨁ F, u ≫ p = p → IsIso u) ∧
          ∀ j, IsIrreducibleMorphism (biproduct.ι F j ≫ p) := by
  have : IsLocalRing (End X) := isLocalRing_end_of_indecomposable hX
  -- A right minimal right almost split map.
  obtain ⟨E, g, hg, hmin⟩ : ∃ (E : FGModuleCat.{w} A) (g : E ⟶ X), IsRightAlmostSplit g ∧
      ∀ u : E ⟶ E, u ≫ g = g → IsIso u := by
    by_cases hproj : Projective X
    · -- `X` is a projective module, with the sink map `rad X ⟶ X`.
      have := moduleProjective_of_projective X
      have : IsLocalRing (End X.obj) :=
        ((ObjectProperty.fullyFaithfulι _).ringEquivEnd X).isLocalRing
      have : IsLocalRing (Module.End A X) := X.obj.endRingEquiv.isLocalRing
      let r : of A (Module.jacobson A X) ⟶ X := ofHom (Module.jacobson A X).subtype
      have : Mono r := (ObjectProperty.ι _).mono_of_mono_map
        ((ModuleCat.mono_iff_injective _).mpr (Module.jacobson A X).injective_subtype)
      refine ⟨_, r, isRightAlmostSplit_ofHom_subtype_jacobson A X, fun u hu ↦ ?_⟩
      rw [(cancel_mono r).mp (hu.trans (Category.id_comp _).symm)]
      infer_instance
    · -- In the Krull–Schmidt category `FGModuleCat A`, the assumed map can be made minimal.
      obtain ⟨E, p, hp⟩ := hsink hproj
      exact IsKrullSchmidt.exists_isRightAlmostSplit_and_minimal X
        ((isFinitelyPresentedFunctor_simpleFunctor_iff X).2 ⟨E, p, hp⟩)
  obtain ⟨n, F, hF, ⟨e⟩⟩ := exists_indecomposable_iso_biproduct E
  refine ⟨n, F, e.inv ≫ g, hF, hg.iso_comp e.inv, right_minimal_iso_comp hmin e.inv,
    fun j ↦ ?_⟩
  rw [← Category.assoc]
  exact hg.isIrreducibleMorphism_comp_of_not_isZero hmin
    (fun hz ↦ (hF j).1 ((ObjectProperty.ι _).map_isZero hz)) _

end Artinian

end FGModuleCat
