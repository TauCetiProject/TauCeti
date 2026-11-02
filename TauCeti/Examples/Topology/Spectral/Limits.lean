/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Limits.Maps
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Checks for maps into spectral limits

The constant Sierpiński tower tests the limit criteria without Hausdorffness: the constant-section
map is spectral, generalizing and a quotient map, and its image contains both distinct points.
The diagonal into the product of two Sierpiński spaces is not generalizing even though both
coordinate maps are identities. Thus the cofiltered hypothesis cannot simply be dropped.
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

end TauCeti
