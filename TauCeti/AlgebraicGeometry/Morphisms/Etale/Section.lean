/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Sections of étale morphisms with connected fibres

Let `f : X ⟶ Y` be an étale morphism with geometrically connected fibres. Every section
`s : Y ⟶ X` of `f` is an isomorphism (`AlgebraicGeometry.isIso_of_comp_eq_id_of_etale`), and
hence so is `f`. Indeed `s` is étale, since `s ≫ f = 𝟙 Y` and `f` are, and a monomorphism, so it
is an open immersion. The fibres of `f` are discrete, since `f` is locally quasi-finite, and
connected, so each of them is the single point it shares with the image of `s`; thus `s` is
surjective.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **A section of an étale morphism with geometrically connected fibres is an isomorphism.** -/
theorem isIso_of_comp_eq_id_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [GeometricallyConnected f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : IsIso s := by
  have : Etale (s ≫ f) := hs ▸ inferInstance
  have : Etale s := MorphismProperty.of_postcomp (W' := @Etale) _ _ f ‹Etale f› ‹_›
  -- An étale monomorphism is an open immersion.
  have : IsSplitMono s := .mk' ⟨f, hs⟩
  have : IsOpenImmersion s := .of_flat_of_mono _
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨this, ⟨fun x ↦ ?_⟩⟩
  -- The fibre through `x` is discrete and connected, so it is the point `s (f x)`.
  have hsub : (f ⁻¹' {f x}).Subsingleton :=
    (f.isConnected_preimage_singleton _).isPreconnected.isDiscrete_iff_subsingleton.mp
      (f.isDiscrete_preimage_singleton _)
  refine ⟨f x, hsub ?_ (Set.mem_preimage.2 (Set.mem_singleton _))⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, hs]
  simp

end AlgebraicGeometry
