/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Limits.Maps
import TauCeti.Topology.Spectral.Limits.Detection
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Checks for maps and finite-stage detection in spectral limits

The constant Sierpiński tower tests the limit criteria without Hausdorffness: the constant-section
map is spectral, generalizing and a quotient map, and its image contains both distinct points.
The diagonal into the product of two Sierpiński spaces is not generalizing even though both
coordinate maps are identities. Thus the cofiltered hypothesis cannot simply be dropped.

The tower of Sierpiński spaces with constant-false transitions tests finite-stage detection:
the nonempty compact open singleton `{True}` misses the limit and disappears after refinement.
In particular, the limit projection is not surjective.
-/

open Set Topology CategoryTheory CategoryTheory.Limits TopCat

namespace TauCeti

/-- The constant-section map for the Sierpiński tower is spectral, generalizing and quotient,
and its sections at `True` and `False` are distinct. -/
example : ∃ f : Prop → (limitCone ((Functor.const ℕᵒᵖ).obj (TopCat.of Prop))).pt,
    IsSpectralMap f ∧ GeneralizingMap f ∧ IsQuotientMap f ∧ f True ≠ f False := by
  have : SpectralSpace Prop := spectralSpace_prop
  let F : ℕᵒᵖ ⥤ TopCat := (Functor.const ℕᵒᵖ).obj (TopCat.of Prop)
  have : ∀ j, SpectralSpace (F.obj j) := fun _ ↦ spectralSpace_prop
  let c : Cone F := ⟨TopCat.of Prop, 𝟙 F⟩
  let f := (limitConeIsLimit F).lift c
  have hF : ∀ {i j} (a : i ⟶ j), IsSpectralMap (F.map a) := fun _ ↦ isSpectralMap_id
  have hcoord (j : ℕᵒᵖ) : (limitCone F).π.app j ∘ f = id := by
    funext x
    exact ConcreteCategory.congr_hom ((limitConeIsLimit F).fac c j) x
  have hs (j : ℕᵒᵖ) : IsSpectralMap ((limitCone F).π.app j ∘ f) := by
    rw [hcoord]
    exact isSpectralMap_id
  have hg (j : ℕᵒᵖ) : GeneralizingMap ((limitCone F).π.app j ∘ f) := by
    rw [hcoord]
    exact IsOpenEmbedding.id.generalizingMap
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨z.val (Opposite.op 0), ?_⟩
    apply Subtype.ext
    funext j
    have heq := congrFun (hcoord j) (z.val (Opposite.op 0))
    have hz := z.property (homOfLE (Nat.zero_le j.unop)).op
    exact heq.trans hz.symm
  refine ⟨f, (isSpectralMap_of_isLimit_iff F hF _ (limitConeIsLimit F) f).mpr hs,
    generalizingMap_of_isLimit F _ (limitConeIsLimit F) f hs hg,
    isQuotientMap_of_isLimit F hF _ (limitConeIsLimit F) f hsurj hs hg, ?_⟩
  intro h
  have heq := congrArg (fun z ↦ (limitCone F).π.app (Opposite.op 0) z) h
  have hTF : True = False := (congrFun (hcoord (Opposite.op 0)) True).symm.trans
    (heq.trans (congrFun (hcoord (Opposite.op 0)) False))
  exact hTF.mp trivial

/-- The diagonal into the product of two Sierpiński spaces has generalizing coordinate maps but
is not generalizing. Products are limits of diagrams that need not be cofiltered. -/
example : GeneralizingMap (id : Prop → Prop) ∧
    ¬ GeneralizingMap (fun p : Prop ↦ (p, p)) := by
  refine ⟨IsOpenEmbedding.id.generalizingMap, fun h ↦ ?_⟩
  have hTF : (True : Prop) ⤳ False :=
    Topology.IsUpperSet.specializes_iff_le.mpr (fun h ↦ h.elim)
  obtain ⟨p, _, hp⟩ := h (a := False) (b := (True, False))
    (hTF.prod (specializes_refl False))
  have hT : p := (congrArg Prod.fst hp).mpr trivial
  exact (congrArg Prod.snd hp).mp hT


/-- A nonempty compact open can disappear in a non-Hausdorff spectral limit, and the
detection theorem finds a transition where it disappears. -/
example : ∃ (F : ℕᵒᵖ ⥤ TopCat.{0}) (s : Set (F.obj (Opposite.op 0))),
    (∀ j, SpectralSpace (F.obj j)) ∧
    (∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f)) ∧
    IsOpen s ∧ IsCompact s ∧ s.Nonempty ∧
    (limitCone F).π.app (Opposite.op 0) ⁻¹' s = ∅ ∧
    ¬ Function.Surjective ((limitCone F).π.app (Opposite.op 0)) ∧
    ∃ (j : ℕᵒᵖ) (f : j ⟶ Opposite.op 0), F.map f ⁻¹' s = ∅ := by
  let F := Functor.ofOpSequence (X := fun _ : ℕ ↦ TopCat.of Prop) fun _ ↦
    (TopCat.ofHom ⟨fun _ : Prop ↦ False, continuous_const⟩ : TopCat.of Prop ⟶ TopCat.of Prop)
  have : ∀ j, SpectralSpace (F.obj j) := fun _ ↦ spectralSpace_prop
  have : ∀ j, Finite (F.obj j) := fun _ ↦ inferInstanceAs (Finite Prop)
  have hF : ∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f) := fun f ↦
    ⟨(F.map f).hom.continuous, fun _ _ _ ↦ Set.toFinite _ |>.isCompact⟩
  have hcoord (x : (limitCone F).pt) (n : ℕ) : x.1 (Opposite.op n) = False := by
    have hx := x.2 (homOfLE (Nat.le_succ n)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at hx
    exact hx.symm
  have hempty : (limitCone F).π.app (Opposite.op 0) ⁻¹' ({True} : Set Prop) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hval : (limitCone F).π.app (Opposite.op 0) x = False := hcoord x 0
    have hx' : (limitCone F).π.app (Opposite.op 0) x = True := hx
    exact (hval.symm.trans hx').mpr trivial
  refine ⟨F, {True}, inferInstance, hF, isOpen_singleton_true, isCompact_singleton,
    singleton_nonempty _, hempty, ?_, ?_⟩
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj True
    have hTF : True = False := hx.symm.trans (hcoord x 0)
    exact hTF.mp trivial
  · exact exists_preimage_eq_of_isLimit F hF _ (limitConeIsLimit F)
      isOpen_singleton_true isCompact_singleton isOpen_empty isCompact_empty
      (by simpa using hempty)

end TauCeti
