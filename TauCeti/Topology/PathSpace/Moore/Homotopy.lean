/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopy invariance of Moore loop maps

A based map `f : (X, x) → (Y, y)` induces the continuous monoid homomorphism
`TauCeti.MooreLoopSpace.map f : Ω_x X → Ω_y Y` of Moore loop spaces, by postcomposition. This file
shows that the induced map only depends on `f` up to based homotopy: a homotopy `F` from `f` to
`g` relative to the base point gives the homotopy `(t, γ) ↦ F_t ∘ γ` from `Ω f` to `Ω g`, which
does not move the constant loop of length zero (`TauCeti.MooreLoopSpace.homotopicRel_map`).
Since the conclusion is again a based homotopy, the statement iterates to the double loop space
`Ω²`. In particular `Ω` preserves pointed left homotopy inverses: if `r ∘ s ≃ id` relative to the
base point, then `Ω r ∘ Ω s ≃ id` relative to the constant loop
(`TauCeti.MooreLoopSpace.homotopicRel_comp_map_id`).

## Main results

* `TauCeti.MooreLoopSpace.homotopicRel_map`: based maps homotopic relative to the base point
  induce Moore loop maps homotopic relative to the constant loop.
* `TauCeti.MooreLoopSpace.homotopicRel_comp_map_id`: the Moore loop functor preserves pointed
  left homotopy inverses.
-/

public section

open scoped unitInterval

namespace TauCeti.MooreLoopSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- **Homotopy invariance of the Moore loop functor.** If `f` and `g` are homotopic relative to
the base point `x`, then the induced maps of Moore loop spaces are homotopic relative to the
constant loop `1`, through the loops `F_t ∘ γ` for a homotopy `F` from `f` to `g`. -/
theorem homotopicRel_map {f g : C(X, Y)} (h : f.HomotopicRel g {x}) (hf : f x = y)
    (hg : g x = y) :
    (map f hf : C(MooreLoopSpace X x, MooreLoopSpace Y y)).HomotopicRel (map g hg) {1} := by
  obtain ⟨F⟩ := h
  have hF (t : I) : F.curry t x = y := (F.eq_fst t rfl).trans hf
  refine ⟨⟨⟨⟨fun p ↦ map (F.curry p.1) (hF p.1) p.2, ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · -- A family of Moore paths is continuous when its lengths and its uncurried paths are.
    refine isEmbedding_toMoorePath.continuous_iff.2 <| MoorePath.continuous_iff.2 ⟨?_, ?_⟩
    · refine (MoorePath.continuous_length.comp (continuous_toMoorePath.comp continuous_snd)).congr
        fun p ↦ ?_
      simp
    · refine (F.continuous.comp <| (continuous_fst.comp continuous_fst).prodMk <|
        (continuous_toMoorePath.comp (continuous_snd.comp continuous_fst)).moorePath_eval
          continuous_snd).congr fun p ↦ ?_
      simp
  · intro γ
    ext1
    simp
  · intro γ
    ext1
    simp
  · rintro t _ rfl
    ext1
    simp

/-- **The Moore loop functor preserves pointed left homotopy inverses.** If `r ∘ s` is homotopic
to the identity relative to the base point `x`, then `Ω r ∘ Ω s` is homotopic to the identity
relative to the constant loop `1`. -/
theorem homotopicRel_comp_map_id {Z : Type*} [TopologicalSpace Z] {z : Z} {s : C(X, Z)}
    {r : C(Z, X)} (h : (r.comp s).HomotopicRel (ContinuousMap.id X) {x}) (hs : s x = z)
    (hr : r z = x) :
    ((map r hr : C(MooreLoopSpace Z z, MooreLoopSpace X x)).comp (map s hs)).HomotopicRel
      (ContinuousMap.id _) {1} := by
  have hrs : r.comp s x = x := by rw [ContinuousMap.comp_apply, hs, hr]
  -- `Ω r ∘ Ω s = Ω (r ∘ s)` and `Ω id = id`, as continuous maps: after `map_comp` and `map_id`,
  -- `rfl` closes the goals since coercing to continuous maps commutes with `comp` and `id`
  -- by definition.
  have hcomp : (map r hr : C(MooreLoopSpace Z z, MooreLoopSpace X x)).comp (map s hs) =
      (map (r.comp s) hrs : C(MooreLoopSpace X x, MooreLoopSpace X x)) := by
    rw [map_comp r s hr hs]
    rfl
  have hid : (map (ContinuousMap.id X) (ContinuousMap.id_apply x) :
      C(MooreLoopSpace X x, MooreLoopSpace X x)) = ContinuousMap.id _ := by
    rw [map_id]
    rfl
  simpa only [hcomp, hid] using homotopicRel_map h hrs (ContinuousMap.id_apply x)

end TauCeti.MooreLoopSpace
