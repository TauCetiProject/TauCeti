/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Recognizing pullbacks from an embedded range

A commutative square of topological spaces whose top horizontal map is an embedding and whose
bottom horizontal map is injective is a pullback when the range of the top map is the preimage of
the range of the bottom one. This range criterion is useful for geometric constructions presented
as embedded open subspaces.
-/

public section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace TauCeti.TopCat

universe u

/-- A commutative square whose top horizontal map is an embedding and whose bottom horizontal map
is injective is a pullback when the range of the top map is the preimage of the range of the bottom
map. -/
theorem isPullback_of_isEmbedding_of_range_eq_preimage
    {P X Y Z : TopCat.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hfst : IsEmbedding fst) (hg : Function.Injective g) (hcomm : fst ≫ f = snd ≫ g)
    (hrange : range fst = f ⁻¹' range g) : IsPullback fst snd f g := by
  have mem_range_fst (s : PullbackCone f g) (x : s.pt) : s.fst x ∈ range fst := by
    rw [hrange]
    exact ⟨s.snd x, (CategoryTheory.congr_fun s.condition x).symm⟩
  let lift (s : PullbackCone f g) : s.pt ⟶ P := TopCat.ofHom
    { toFun := fun x ↦ Classical.choose (mem_range_fst s x)
      continuous_toFun := hfst.isInducing.continuous_iff.mpr (by
        convert s.fst.hom.continuous using 1
        funext x
        exact Classical.choose_spec (mem_range_fst s x)) }
  have lift_fst (s : PullbackCone f g) : lift s ≫ fst = s.fst := by
    ext x
    exact Classical.choose_spec (mem_range_fst s x)
  have lift_snd (s : PullbackCone f g) : lift s ≫ snd = s.snd := by
    ext x
    apply hg
    have h : lift s ≫ snd ≫ g = s.snd ≫ g := by
      rw [← hcomm, ← Category.assoc, lift_fst, s.condition]
    exact CategoryTheory.congr_fun h x
  refine IsPullback.of_isLimit' ⟨hcomm⟩
    (PullbackCone.IsLimit.mk hcomm lift lift_fst lift_snd ?_)
  intro s m hm _
  ext x
  apply hfst.injective
  exact CategoryTheory.congr_fun (hm.trans (lift_fst s).symm) x

end TauCeti.TopCat
