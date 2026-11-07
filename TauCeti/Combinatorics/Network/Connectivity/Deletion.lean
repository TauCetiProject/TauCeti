/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Connectivity.Monotone

/-!
# Arc connectivity after arrow deletion

Deleting any set of arrow identities cannot increase arc connectivity. Together with
`arcConnectivity_le_withoutHom_add_card`, this bounds the change in connectivity under finite
arrow deletion from both sides.

The example applies the finite-deletion threshold bound to a family with three parallel arrows
between every ordered pair, including three loops at each vertex. Deleting any two arrows leaves
it strongly connected, without requiring the vertex type to be finite.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v}

/-- Deleting any set of arrows cannot increase arc connectivity. -/
theorem arcConnectivity_withoutHom_le (F : Set (Σ v w, Q v w)) :
    arcConnectivity (WithoutHom F) ≤ arcConnectivity Q :=
  arcConnectivity_mono fun _ _ ↦ ⟨Subtype.val, Subtype.val_injective⟩

/-- With three arrows between every ordered pair, deleting any two arrows leaves a strongly
connected family. The vertex type may be infinite, and every vertex has three loops. -/
example (F : Finset (Σ _ _ : V, Fin 3)) (hF : #F = 2) :
    IsArcStrong (WithoutHom (F : Set (Σ _ _ : V, Fin 3))) 1 := by
  classical
  have hthree : IsArcStrong (fun _ _ : V ↦ Fin 3) 3 := by
    rw [isArcStrong_def]
    intro s t
    rw [isArcReachable_def]
    intro H hH
    have hinj : Function.Injective (fun e : Fin 3 ↦ (⟨s, t, e⟩ : Σ _ _ : V, Fin 3)) :=
      sigma_mk_injective.comp sigma_mk_injective
    obtain ⟨e, he⟩ : ∃ e : Fin 3, (⟨s, t, e⟩ : Σ _ _ : V, Fin 3) ∉ H := by
      by_contra! hall
      have hsub : (univ.map ⟨_, hinj⟩ : Finset (Σ _ _ : V, Fin 3)) ⊆ H := by
        rintro a ha
        obtain ⟨e, _, rfl⟩ := mem_map.1 ha
        exact hall e
      have := card_le_card hsub
      simp only [card_map, card_univ, Fintype.card_fin] at this
      omega
    exact (ReachableWithout.refl _ s).tail e he
  simpa [hF] using hthree.withoutHom F

end TauCeti
