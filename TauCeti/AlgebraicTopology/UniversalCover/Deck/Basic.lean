/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Deck
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Deck transformations of a map

For a map `p : E → B`, its deck transformations are the homeomorphisms of `E` over `B`. Mathlib
collects them as the subgroup `deck p` of the homeomorphism group `E ≃ₜ E`; for a covering
projection `p` this subgroup is the classical deck transformation group.

This file adds the pointwise API that the rest of the deck-transformation development uses.
`TauCeti.Deck.mem_iff` and `deck.map_proj` restate Mathlib's `deck.mem_iff` and
`deck.proj_smul` point by point on the underlying homeomorphism, and
`deck.fiberHomeomorph` restricts a deck transformation to each fibre of `p`.

The action of `deck p` on the total space is inherited, by subgroup transfer, from the
tautological action of the ambient homeomorphism group `E ≃ₜ E` on `E`
(`Homeomorph.applyMulAction`). Each deck transformation preserves `p`, hence
preserves every fibre of `p`.

The deck group only sees `p` through the equalities `p (φ e) = p e`, so postcomposition by an
injective map leaves it unchanged (`TauCeti.deck_comp_of_injective`).
-/

public section

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

namespace Deck

/-- A homeomorphism lies in `deck p` exactly when it preserves `p` pointwise: `deck.mem_iff`
with the equality of maps read point by point. -/
@[simp]
lemma mem_iff (φ : E ≃ₜ E) : φ ∈ deck p ↔ ∀ e, p (φ e) = p e :=
  deck.mem_iff.trans funext_iff

/-- A deck transformation preserves the projection map pointwise: `deck.proj_smul`, stated on
the underlying homeomorphism. -/
lemma _root_.deck.map_proj (φ : deck p) (e : E) : p (φ.1 e) = p e :=
  deck.proj_smul φ e

/-- A deck transformation preserves each fibre of the projection. -/
lemma _root_.deck.mapsTo_fiber (φ : deck p) (b : B) : Set.MapsTo φ.1 (p ⁻¹' {b}) (p ⁻¹' {b}) := by
  intro e he
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, deck.map_proj] using he

/-- The inverse of a deck transformation also preserves each fibre of the projection. -/
lemma _root_.deck.mapsTo_fiber_symm (φ : deck p) (b : B) :
    Set.MapsTo φ.1.symm (p ⁻¹' {b}) (p ⁻¹' {b}) := by
  intro e he
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at he ⊢
  rw [← deck.map_proj φ (φ.1.symm e), Homeomorph.apply_symm_apply]
  exact he

/-- A deck transformation restricts to a homeomorphism of every fibre of the projection,
the restriction of its underlying homeomorphism along `Homeomorph.subtype`. -/
@[expose] def _root_.deck.fiberHomeomorph (φ : deck p) (b : B) : p ⁻¹' {b} ≃ₜ p ⁻¹' {b} :=
  φ.1.subtype fun e => by simp [Set.mem_preimage, eq_comm, deck.map_proj]

/-- On points, the fibre homeomorphism induced by a deck transformation is just evaluation
of that transformation. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_apply (φ : deck p) (b : B) (e : p ⁻¹' {b}) :
    (deck.fiberHomeomorph φ b e : E) = φ.1 e.1 :=
  rfl

/-- On points, the inverse fibre homeomorphism induced by a deck transformation is
evaluation of the inverse homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_symm_apply (φ : deck p) (b : B) (e : p ⁻¹' {b}) :
    ((deck.fiberHomeomorph φ b).symm e : E) = φ.1.symm e.1 :=
  rfl

/-- On points, the action of a deck transformation is evaluation of its underlying
homeomorphism. The action itself is inherited, by subgroup transfer, from the tautological
action of `E ≃ₜ E` on `E`. -/
@[simp]
lemma _root_.deck.smul_eq_apply (φ : deck p) (e : E) : φ • e = φ.1 e :=
  rfl

/-- Applying the inverse deck transformation is evaluation of the inverse homeomorphism. -/
@[simp]
lemma _root_.deck.inv_smul_eq_symm_apply (φ : deck p) (e : E) : (φ⁻¹ : deck p) • e = φ.1.symm e :=
  rfl

-- `FaithfulSMul (deck p) E` is inherited from Mathlib's generic subgroup action, and
-- `ContinuousConstSMul (deck p) E` comes with Mathlib's `deck`.

end Deck

section Injective

variable {E B B' : Type*} [TopologicalSpace E]

/-- Postcomposing a map with an injection does not change its deck group. -/
theorem deck_comp_of_injective {f : B → B'} (hf : Function.Injective f) (p : E → B) :
    deck (f ∘ p) = deck p := by
  ext φ
  simp only [Deck.mem_iff, Function.comp_apply, hf.eq_iff]

end Injective

end TauCeti
