/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Sections of unramified morphisms with connected fibres

Let `f : X ⟶ Y` be an unramified morphism with geometrically connected fibres, for instance an
étale one. Every section `s : Y ⟶ X` of `f` is an isomorphism
(`TauCeti.AlgebraicGeometry.isIso_of_comp_eq_id_of_unramified`), and hence so is `f`. Indeed `s`
is an open immersion, since `s ≫ f = 𝟙 Y` is one and open immersions cancel against unramified
morphisms on the right. The fibres of `f` are discrete, since `f` is locally quasi-finite, and
connected, so each of them is the single point it shares with the image of `s`; thus `s` is
surjective.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- **A section of an unramified morphism with geometrically connected fibres is an
isomorphism.** -/
theorem isIso_of_comp_eq_id_of_unramified {X Y : Scheme.{u}} (f : X ⟶ Y) [Unramified f]
    [GeometricallyConnected f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : IsIso s := by
  -- A section of an unramified morphism is an open immersion.
  have : IsOpenImmersion (s ≫ f) := hs ▸ inferInstance
  have : IsOpenImmersion s := MorphismProperty.of_postcomp (W' := @Unramified) _ _ f ‹_› ‹_›
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨this, ⟨fun x ↦ ?_⟩⟩
  -- The fibre through `x` is discrete and connected, so it is the point `s (f x)`.
  have hsub : (f ⁻¹' {f x}).Subsingleton :=
    (f.isConnected_preimage_singleton _).isPreconnected.isDiscrete_iff_subsingleton.mp
      (f.isDiscrete_preimage_singleton _)
  refine ⟨f x, hsub ?_ (Set.mem_preimage.2 (Set.mem_singleton _))⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, hs]
  simp

end TauCeti.AlgebraicGeometry
