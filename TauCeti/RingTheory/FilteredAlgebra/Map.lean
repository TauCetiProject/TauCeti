/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Completion

/-!
# Maps between filtered ring completions

A ring homomorphism induces a map on completions when, for each target cutoff,
some source cutoff maps into it. A monotone cutoff modulus records these choices.
The induced map computes by the corresponding quotient map at each order and is
independent of the modulus. Identity and composition therefore give functorial maps
even when the original homomorphisms preserve different filtration orders.

The construction uses Mathlib's `Ideal.quotientMap` and the compatible-family
universal property `TauCeti.AlgFiltration.lift`. Rings may be noncommutative, and the
filtrations need not be separated or adic.

Adapted from `yuma-mizuno-lean/Mei`, commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`,
`Mei/RingTheory/FilteredAlgebra/Map.lean` (Apache 2.0).
-/

public section

namespace TauCeti.AlgFiltration

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
  (F : TauCeti.AlgFiltration A) (G : TauCeti.AlgFiltration B)
  (f : A →+* B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)

/-- Extend a ring homomorphism to completions along a monotone cutoff modulus. -/
def mapCompletion : F.completion →+* G.completion :=
  G.lift (fun k => (Ideal.quotientMap (G.ideal (k + 1)) f (hf k)).comp
    (F.projection (l k))) (by
      intro k j h
      apply RingHom.ext
      intro x
      simp only [RingHom.comp_apply]
      rw [← F.factor_projection (hl h) x]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection (l j) x)
      rw [← ha]
      simp)

/-- The target order-`k` component uses only the source order-`l k` component. -/
@[simp]
theorem projection_mapCompletion (k : ℕ) (x : F.completion) :
    G.projection k (F.mapCompletion G f l hl hf x) =
      Ideal.quotientMap (G.ideal (k + 1)) f (hf k) (F.projection (l k) x) := by
  rw [mapCompletion, projection_lift, RingHom.comp_apply]

/-- The induced completion map commutes with the canonical maps from the rings. -/
@[simp]
theorem mapCompletion_toCompletion (a : A) :
    F.mapCompletion G f l hl hf (F.toCompletion a) = G.toCompletion (f a) := by
  apply G.completion_ext
  intro k
  simp

/-- A larger source cutoff computes the same target component. -/
theorem projection_mapCompletion_of_le (k a : ℕ) (ha : l k ≤ a) (x : F.completion) :
    G.projection k (F.mapCompletion G f l hl hf x) =
      Ideal.quotientMap (G.ideal (k + 1)) f
        ((F.antitone (Nat.add_le_add_right ha 1)).trans (hf k)) (F.projection a x) := by
  rw [projection_mapCompletion, ← F.factor_projection ha x]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (F.projection a x)
  rw [← hr]
  simp

/-- The completed homomorphism obeys the original cutoff bound on induced filtrations. -/
theorem mapCompletion_mem_completionIdeal (k : ℕ) {x : F.completion}
    (hx : x ∈ F.completionIdeal (l k + 1)) :
    F.mapCompletion G f l hl hf x ∈ G.completionIdeal (k + 1) := by
  simp only [completionIdeal_succ, RingHom.mem_ker] at hx ⊢
  rw [projection_mapCompletion, hx, map_zero]

variable {l}

/-- Any two cutoff moduli for one ring homomorphism induce the same completion map. -/
theorem mapCompletion_eq (m : ℕ → ℕ) (hm : Monotone m)
    (hfm : ∀ k, F.ideal (m k + 1) ≤ (G.ideal (k + 1)).comap f) :
    F.mapCompletion G f l hl hf = F.mapCompletion G f m hm hfm := by
  apply RingHom.ext
  intro x
  apply G.completion_ext
  intro k
  rw [F.projection_mapCompletion_of_le G f l hl hf k (max (l k) (m k)) (le_max_left _ _),
    F.projection_mapCompletion_of_le G f m hm hfm k (max (l k) (m k)) (le_max_right _ _)]

/-- The identity ring map with the identity modulus induces the identity completion map. -/
@[simp]
theorem mapCompletion_id :
    F.mapCompletion F (RingHom.id A) id monotone_id (fun _ => by simp) =
      RingHom.id F.completion := by
  apply RingHom.ext
  intro x
  apply F.completion_ext
  intro k
  rw [projection_mapCompletion]
  simp only [id_eq, RingHom.id_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection k x)
  simp only [← ha, Ideal.quotientMap_mk, RingHom.id_apply]

variable (H : TauCeti.AlgFiltration C) (g : B →+* C) (m : ℕ → ℕ) (hm : Monotone m)
  (hg : ∀ k, G.ideal (m k + 1) ≤ (H.ideal (k + 1)).comap g)

/-- Successive completion maps compose with cutoff modulus `l ∘ m`. -/
theorem mapCompletion_comp :
    F.mapCompletion H (g.comp f) (l ∘ m) (hl.comp hm)
      (fun k => by
        rw [← Ideal.comap_comap]
        exact (hf (m k)).trans (Ideal.comap_mono (hg k))) =
      (G.mapCompletion H g m hm hg).comp (F.mapCompletion G f l hl hf) := by
  apply RingHom.ext
  intro x
  apply H.completion_ext
  intro k
  rw [projection_mapCompletion, RingHom.comp_apply, projection_mapCompletion,
    projection_mapCompletion]
  simp only [Function.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (F.projection (l (m k)) x)
  simp only [← ha, Ideal.quotientMap_mk, RingHom.comp_apply]

end TauCeti.AlgFiltration
