/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Changing a host graph at one vertex

If two host graphs on the same finite vertex set `W` agree on every pair of vertices avoiding a
fixed vertex `w`, then their homomorphism densities of a pattern `F` differ by at most
`|V(F)| / |W|`.

A vertex map `V(F) → W` whose range avoids `w` preserves adjacency into one host exactly when it
preserves adjacency into the other, so only the maps whose range meets `w` can change status.
A union bound over the vertex of `F` sent to `w` counts at most `|V(F)| · |W| ^ (|V(F)| - 1)` such
maps among the `|W| ^ |V(F)|` in total.

This is the bounded-differences estimate for the ordinary homomorphism density: in a sampled
graph where resampling one vertex only changes the pairs at that vertex, it bounds the effect of
the resampling on the estimator.

## Main results

* `SimpleGraph.abs_homDensityFin_sub_le_of_adj_iff` — the oscillation bound above.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
-/

public section

open Finset

namespace SimpleGraph

open TauCeti.DenseGraphLimits

variable {V W : Type*} [Fintype V] [Fintype W]

/-- **Oscillation of the homomorphism density at one vertex.** If two host graphs agree on every
pair of vertices avoiding `w`, the homomorphism densities of `F` in them differ by at most
`|V(F)| / |W|`: only the vertex maps meeting `w` can distinguish the two hosts. -/
theorem abs_homDensityFin_sub_le_of_adj_iff (F : SimpleGraph V) {G G' : SimpleGraph W} (w : W)
    (h : ∀ a b, a ≠ w → b ≠ w → (G.Adj a b ↔ G'.Adj a b)) :
    |homDensityFin F G - homDensityFin F G'| ≤ (Fintype.card V : ℝ) / Fintype.card W := by
  classical
  have hm : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨w⟩
  set S : Finset (V → W) := univ.filter fun ψ => ∃ v, ψ v = w with hS
  -- The adjacency-preserving vertex maps into a host `H`.
  let P : SimpleGraph W → Finset (V → W) := fun H =>
    univ.filter fun ψ => ∀ a b, F.Adj a b → H.Adj (ψ a) (ψ b)
  have hcard : ∀ H : SimpleGraph W, Nat.card (F →g H) = #(P H) := by
    intro H
    rw [card_hom_eq_card_adjPreservingMaps, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- The maps avoiding `w` preserve adjacency into `G` exactly when they do into `G'`.
  have hsdiff : P G \ S = P G' \ S := by
    ext ψ
    simp only [P, hS, mem_sdiff, mem_filter, mem_univ, true_and, not_exists]
    exact ⟨fun ⟨hψ, hw⟩ => ⟨fun a b hab => (h _ _ (hw a) (hw b)).mp (hψ a b hab), hw⟩,
      fun ⟨hψ, hw⟩ => ⟨fun a b hab => (h _ _ (hw a) (hw b)).mpr (hψ a b hab), hw⟩⟩
  have hG := card_sdiff_add_card_inter (P G) S
  have hG' := card_sdiff_add_card_inter (P G') S
  have hGS : #(P G ∩ S) ≤ #S := card_le_card inter_subset_right
  have hG'S : #(P G' ∩ S) ≤ #S := card_le_card inter_subset_right
  -- A union bound over the vertex sent to `w`: each fibre `{ψ | ψ v = w}` has
  -- `|W| ^ (|V| - 1)` elements.
  have hSle : #S ≤ Fintype.card V * Fintype.card W ^ (Fintype.card V - 1) := by
    have hunion : S = univ.biUnion fun v : V => univ.filter fun ψ : V → W => ψ v = w := by
      ext ψ
      simp [hS]
    rw [hunion]
    refine card_biUnion_le.trans ?_
    simp only [Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset W) _ (mem_univ w),
      ← Fintype.piFinset_univ, sum_const, card_univ, smul_eq_mul, le_refl]
  have hSbound : (#S : ℝ) * Fintype.card W ≤
      Fintype.card V * Fintype.card W ^ Fintype.card V := by
    have hSnat : #S * Fintype.card W ≤ Fintype.card V * Fintype.card W ^ Fintype.card V := by
      refine (Nat.mul_le_mul_right _ hSle).trans_eq ?_
      rcases Nat.eq_zero_or_eq_succ_pred (Fintype.card V) with h | h
      · simp [h]
      · rw [h, Nat.succ_sub_one, pow_succ, mul_assoc]
    exact_mod_cast hSnat
  have hpow : (0 : ℝ) < (Fintype.card W : ℝ) ^ Fintype.card V := by positivity
  have hmR : (0 : ℝ) < Fintype.card W := by exact_mod_cast hm
  rw [homDensityFin_def, homDensityFin_def, hcard, hcard, ← hG, ← hG', hsdiff, ← sub_div,
    abs_div, abs_of_pos hpow, div_le_div_iff₀ hpow hmR]
  push_cast
  have habs : |(#(P G' \ S) + #(P G ∩ S) : ℝ) - (#(P G' \ S) + #(P G' ∩ S))| ≤ #S := by
    rw [add_sub_add_left_eq_sub, abs_le]
    constructor <;> linarith [(Nat.cast_le (α := ℝ)).mpr hGS, (Nat.cast_le (α := ℝ)).mpr hG'S,
      (Nat.cast_nonneg (α := ℝ) #(P G ∩ S)), (Nat.cast_nonneg (α := ℝ) #(P G' ∩ S))]
  calc |(#(P G' \ S) + #(P G ∩ S) : ℝ) - (#(P G' \ S) + #(P G' ∩ S))| * Fintype.card W
      ≤ #S * Fintype.card W := mul_le_mul_of_nonneg_right habs hmR.le
    _ ≤ Fintype.card V * Fintype.card W ^ Fintype.card V := hSbound

end SimpleGraph
