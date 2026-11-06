/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Connectivity.Basic
public import Mathlib.Data.Finset.Preimage

/-!
# Directed connectivity under arrow maps and deletion

Injective maps of arrow families on a fixed vertex type preserve arc reachability and arc
strength. Arbitrary maps of arrow families preserve vertex strength: identifying parallel arrows
does not affect vertex deletion, whereas it can destroy arc-disjointness.

Deleting a finite set `F` of arrow identities lowers every arc-reachability threshold by at most
`F.card`. The same estimate holds for global arc strength and for the extended-natural arc
connectivity. Conversely, deletion never increases arc connectivity. These statements need no
finiteness assumption on the vertices or the arrow types and allow loops and parallel arrows.

The bounds concern arrow deletion on a fixed vertex type, not vertex deletion.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {R : V → V → Type w}
variable {k : ℕ} {s t : V}

/-! ### Maps of arrow families -/

/-- Injective maps on each arrow type preserve arc reachability. -/
theorem IsArcReachable.map (h : IsArcReachable Q k s t)
    (φ : ∀ v w, Q v w → R v w) (hφ : ∀ v w, Function.Injective (φ v w)) :
    IsArcReachable R k s t := by
  classical
  let f : (Σ v w, Q v w) → Σ v w, R v w := Sigma.map id fun v ↦ Sigma.map id (φ v)
  have hf : Function.Injective f := Function.injective_id.sigma_map fun v ↦
    Function.injective_id.sigma_map (hφ v)
  rw [isArcReachable_def] at h ⊢
  intro F hF
  have hcard : #(F.preimage f hf.injOn) ≤ #F := by
    rw [card_preimage]
    exact card_filter_le _ _
  exact (h (F.preimage f hf.injOn) (hcard.trans_lt hF)).mem_of_mem
    (C := {v | ReachableWithout (F : Set (Σ v w, R v w)) s v}) (.refl _ _)
    fun v w e hv he ↦ hv.tail (φ v w e) (by simpa [f, Sigma.map_mk] using he)

/-- Injective maps on each arrow type preserve arc strength. -/
theorem IsArcStrong.map (h : IsArcStrong Q k)
    (φ : ∀ v w, Q v w → R v w) (hφ : ∀ v w, Function.Injective (φ v w)) :
    IsArcStrong R k := by
  rw [isArcStrong_def]
  exact fun s t ↦ (h.isArcReachable s t).map φ hφ

/-- Maps on each arrow type preserve vertex strength; no injectivity is needed. -/
theorem IsVertexStrong.map (h : IsVertexStrong Q k) (φ : ∀ v w, Q v w → R v w) :
    IsVertexStrong R k := by
  rw [isVertexStrong_def]
  refine ⟨h.lt_card, fun X hX s hs t ht ↦ ?_⟩
  exact (h.reachableAvoiding hX hs ht).mem_of_mem
    (C := {v | ReachableAvoiding R (X : Set V) s v}) (.refl hs)
    fun v w e hv _ hw ↦ hv.tail (φ v w e) hw

/-- Embedding each arrow type can only increase arc connectivity. -/
theorem arcConnectivity_le_of_injective (φ : ∀ v w, Q v w → R v w)
    (hφ : ∀ v w, Function.Injective (φ v w)) : arcConnectivity Q ≤ arcConnectivity R := by
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
  exact (isArcStrong_iff_le_arcConnectivity k).1
    (((isArcStrong_iff_le_arcConnectivity k).2 hk).map φ hφ)

/-- Mapping each arrow type can only increase vertex strong connectivity. -/
theorem vertexStrongConnectivity_le (φ : ∀ v w, Q v w → R v w) :
    vertexStrongConnectivity Q ≤ vertexStrongConnectivity R := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
  exact (isVertexStrong_iff_le_vertexStrongConnectivity k).1
    (((isVertexStrong_iff_le_vertexStrongConnectivity k).2 hk).map φ)

/-! ### Deleting arrows -/

/-- Deleting `F.card` arrows lowers local arc reachability by at most `F.card`. The result also
covers thresholds at or below `F.card`, where natural subtraction gives zero. -/
theorem IsArcReachable.withoutHom (h : IsArcReachable Q k s t)
    (F : Finset (Σ v w, Q v w)) :
    IsArcReachable (WithoutHom (F : Set (Σ v w, Q v w))) (k - #F) s t := by
  classical
  let incl : (Σ v w, WithoutHom (F : Set (Σ v w, Q v w)) v w) → Σ v w, Q v w :=
    fun a ↦ ⟨a.1, a.2.1, a.2.2.1⟩
  rw [isArcReachable_def] at h ⊢
  intro H hH
  have hcard : #(F ∪ H.image incl) < k := by
    have hu := card_union_le F (H.image incl)
    have hi : #(H.image incl) ≤ #H := card_image_le
    omega
  apply (h (F ∪ H.image incl) hcard).mem_of_mem
    (C := {v | ReachableWithout (Q := WithoutHom (F : Set (Σ v w, Q v w)))
      (H : Set _) s v}) (.refl _ _)
  intro v w e hv he
  have heF : (⟨v, w, e⟩ : Σ v w, Q v w) ∉ F := fun hmem ↦
    he (mem_union_left _ hmem)
  apply hv.tail ⟨e, heF⟩
  intro heH
  exact he (mem_union_right _ (mem_image_of_mem incl heH))

/-- Deleting a finite set of arrows lowers arc strength by at most its cardinality. -/
theorem IsArcStrong.withoutHom (h : IsArcStrong Q k) (F : Finset (Σ v w, Q v w)) :
    IsArcStrong (WithoutHom (F : Set (Σ v w, Q v w))) (k - #F) := by
  rw [isArcStrong_def]
  exact fun s t ↦ (h.isArcReachable s t).withoutHom F

/-- Deleting any set of arrows cannot increase arc connectivity. -/
theorem arcConnectivity_withoutHom_le (F : Set (Σ v w, Q v w)) :
    arcConnectivity (WithoutHom F) ≤ arcConnectivity Q :=
  arcConnectivity_le_of_injective (fun _ _ e ↦ e.1) fun _ _ ↦ Subtype.val_injective

/-- Deleting finitely many arrows reduces arc connectivity by at most the number deleted.
The additive form also applies when either connectivity is infinite. -/
theorem arcConnectivity_le_withoutHom_add_card (F : Finset (Σ v w, Q v w)) :
    arcConnectivity Q ≤ arcConnectivity (WithoutHom (F : Set (Σ v w, Q v w))) + #F := by
  refine ENat.forall_natCast_le_iff_le.1 fun k hk ↦ ?_
  have hk := (isArcStrong_iff_le_arcConnectivity k).2 hk
  by_cases hkF : k ≤ #F
  · exact (Nat.cast_le.2 hkF).trans (le_add_of_nonneg_left zero_le)
  · have h := (isArcStrong_iff_le_arcConnectivity (k - #F)).1 (hk.withoutHom F)
    have heq : k - #F + #F = k := Nat.sub_add_cancel (by omega)
    calc
      (k : ℕ∞) = (k - #F : ℕ) + (#F : ℕ∞) := by rw [← Nat.cast_add, heq]
      _ ≤ arcConnectivity (WithoutHom (F : Set (Σ v w, Q v w))) + #F :=
        add_le_add h le_rfl

/-! ### A family with parallel arrows and loops -/

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
