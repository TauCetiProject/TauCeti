/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stability of top regularity under small changes of the support

Recoloring the pairs of a lower skeleton moves triples between polyads. A polyad `P'` of the new
skeleton then has a counterpart `P` of the old one, for instance the polyad with the same cells
and colors, whose support differs from that of `P'` only in the moved triples. If the moved
triples are at most an `η`-fraction of both supports, top regularity of a coloring over `P`
passes to `P'` at a parameter `ε` with `δ + 2η + η / ε ≤ ε`, at the same rank.

The two polyads may live over different skeletons, and neither pair graph need lie in the other,
so neither the slicing lemma nor density inheritance applies. Instead, every subpolyad of `P'`
is restricted to `P` (`Subpolyad3.restrict`), and the densities over the two supports are both
compared with the density over their intersection. All supports count role-ordered injective
triples.

Globally, fix an injective map `f` from polyads over `S` to polyads over `T`, and call a triple
*moved* if its polyad over `T` is not the image under `f` of its polyad over `S`. A polyad `f P`
whose support and that of `P` differ in at most an `η`-fraction of each inherits top regularity
from `P`. Every other polyad over `T` is charged to its moved triples, with a loss of `1 / η`.
The support of the irregular polyads over `T` is therefore at most that over `S` plus
`(1 + 2 / η)` times the number of moved triples.

## Main results

* `TauCeti.Colored3Graph.IsTopRegularOverPolyad.of_card_sdiff_support_le`: top regularity
  over `P` passes to every polyad `P'` whose support differs from that of `P` in a small
  fraction of each.
* `TauCeti.Colored3Graph.sum_card_support_not_isTopRegularOverPolyad_le_of_injective`: under an
  injective map of polyads, the support of the irregular polyads grows by at most a multiple of
  the moved triples.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset

namespace TauCeti.Colored3Graph

open Subpolyad3

variable {κ κ₂ κ₂' V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {S : PairSkeleton3 κ₂ V} {S' : PairSkeleton3 κ₂' V} {P : Polyad3 S} {P' : Polyad3 S'}
  {H : Colored3Graph κ V} {δ ε η : ℝ} {r : ℕ}

/-- The size bookkeeping in the change-of-support transfer: removing at most `η * p'` triples
from a set of size at least `ε * p'` leaves at least `δ * p` triples, when `p'` is at least
`(1 - η) * p` and `δ + 2 * η + η / ε ≤ ε`. -/
private theorem mul_le_of_card_sdiff_le {δ ε η p p' s u t : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hε₁ : ε < 1) (hη : 0 ≤ η) (hbudget : δ + 2 * η + η / ε ≤ ε) (hp : 0 ≤ p)
    (hPP' : (1 - η) * p ≤ p') (hs : s ≤ η * p') (hsum : s + u = t) (ht : ε * p' ≤ t) :
    δ * p ≤ u := by
  have hηε : 0 ≤ η / ε := div_nonneg hη hε.le
  have hεη : 0 ≤ ε - η := by linarith
  calc δ * p ≤ (ε - η) * (1 - η) * p := by
        gcongr
        nlinarith
    _ ≤ (ε - η) * p' := by rw [mul_assoc]; gcongr
    _ ≤ _ := by linarith

/-- The four-term triangle inequality used to compare densities over `Q`, its restriction, and
the two supports. -/
private theorem abs_sub_le_four (a b c d e : ℝ) :
    |a - d| ≤ |a - b| + |b - c| + |c - e| + |d - e| := by
  have h₁ := abs_sub_le a b d
  have h₂ := abs_sub_le b c d
  have h₃ := abs_sub_le c e d
  rw [abs_sub_comm e d] at h₃
  linarith

/-- **Top regularity under a change of support.** If `H` is `(δ, r)`-top-regular over `P`, and
the supports of `P` and `P'` each have at most an `η`-fraction of their triples outside the
other, then `H` is `(ε, r)`-top-regular over `P'` whenever `δ + 2η + η / ε ≤ ε`. The polyads may
live over different skeletons. -/
theorem IsTopRegularOverPolyad.of_card_sdiff_support_le (h : H.IsTopRegularOverPolyad P δ r)
    (hε : 0 < ε) (hη : 0 ≤ η) (hbudget : δ + 2 * η + η / ε ≤ ε)
    (h₁ : (#(P'.support \ P.support) : ℝ) ≤ η * #P'.support)
    (h₂ : (#(P.support \ P'.support) : ℝ) ≤ η * #P.support) :
    H.IsTopRegularOverPolyad P' ε r := by
  obtain hε₁ | hε₁ := le_or_gt 1 ε
  · exact isTopRegularOverPolyad_of_one_le (H := H) (P := P') (r := r) hε₁
  rw [isTopRegularOverPolyad_iff]
  intro c Q hQ
  have hδ : 0 ≤ δ := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  have hηε : 0 ≤ η / ε := div_nonneg hη hε.le
  -- The test is restricted to `P`; the restriction loses only triples outside `P`.
  have hU := unionSupport_restrict Q P
  have hUsub : unionSupport (fun i ↦ (Q i).restrict P) ⊆ unionSupport Q :=
    hU ▸ inter_subset_left
  have hUsdiff : unionSupport Q \ unionSupport (fun i ↦ (Q i).restrict P) ⊆
      P'.support \ P.support := by
    intro x hx
    rw [hU, mem_sdiff, mem_inter, not_and] at hx
    exact mem_sdiff.2 ⟨unionSupport_subset Q hx.1, hx.2 hx.1⟩
  have hcardU : (#(unionSupport Q \ unionSupport fun i ↦ (Q i).restrict P) : ℝ) ≤
      η * #P'.support := (Nat.cast_le.2 (card_le_card hUsdiff)).trans h₁
  -- The restricted test passes the size threshold over `P`.
  have hPP' : (1 - η) * #P.support ≤ #P'.support := by
    have h := card_le_card_sdiff_add_card (s := P.support) (t := P'.support)
    have : (#P.support : ℝ) ≤ #(P.support \ P'.support) + #P'.support := by exact_mod_cast h
    linarith
  have hsize : δ * #P.support ≤ #(unionSupport fun i ↦ (Q i).restrict P) := by
    have h := card_sdiff_add_card_eq_card hUsub
    refine mul_le_of_card_sdiff_le (s := (#(unionSupport Q \ unionSupport fun i ↦
      (Q i).restrict P) : ℝ)) (t := #(unionSupport Q)) hδ hε hε₁ hη hbudget
      (Nat.cast_nonneg _) hPP' hcardU ?_ hQ
    exact_mod_cast h
  -- Compare the four densities.
  have d₁ := H.abs_relDensityOn_sub_le_div_of_card_sdiff_le c hUsub hε hη hQ hcardU
  have d₂ := isTopRegularOverPolyad_iff.1 h c (fun i ↦ (Q i).restrict P) hsize
  have d₃ := H.abs_relDensityOn_sub_le_div_of_card_sdiff_le c (N := #P.support)
    (inter_subset_left (s₁ := P.support) (s₂ := P'.support)) one_pos hη (by rw [one_mul])
    (by rwa [sdiff_inter_self_left])
  have d₄ := H.abs_relDensityOn_sub_le_div_of_card_sdiff_le c (N := #P'.support)
    (inter_subset_right (s₁ := P.support) (s₂ := P'.support)) one_pos hη (by rw [one_mul])
    (by rwa [sdiff_inter_self_right])
  rw [div_one] at d₃ d₄
  rw [relativeDensity_def] at d₂ ⊢
  refine (abs_sub_le_four (H.relDensityOn c (unionSupport Q) : ℝ)
    (H.relDensityOn c (unionSupport fun i ↦ (Q i).restrict P))
    (H.relDensityOn c P.support) (H.relDensityOn c P'.support)
    (H.relDensityOn c (P.support ∩ P'.support))).trans ?_
  linarith

section Injective

variable {T : PairSkeleton3 κ₂' V} {f : Polyad3 S → Polyad3 T}

open Classical in
/-- One polyad and its image: if the image is irregular, it is charged to the irregular support
of the original polyad and to the moved triples, collected in `M`, in either support. -/
private theorem card_support_not_isTopRegularOverPolyad_le (hf : Function.Injective f)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε)
    {M : Finset {x : Fin 3 → V // Function.Injective x}}
    (hM : ∀ x, Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x) → x ∈ M) (P : Polyad3 S) :
    (if ¬H.IsTopRegularOverPolyad (f P) ε r then (#(f P).support : ℝ) else 0) ≤
      (if ¬H.IsTopRegularOverPolyad P δ r then (#P.support : ℝ) else 0) +
        #(M ∩ (f P).support) + (#(M ∩ (f P).support) + #(M ∩ P.support)) / η := by
  -- Triples in exactly one of the two supports are moved.
  have hQ : (#((f P).support \ P.support) : ℝ) ≤ #(M ∩ (f P).support) := by
    refine Nat.cast_le.2 (card_le_card fun x hx ↦ ?_)
    obtain ⟨hxQ, hxP⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨hM x fun h ↦ hxP ?_, hxQ⟩
    exact Polyad3.mem_support_iff_eq_ofTriple.2
      (hf ((Polyad3.mem_support_iff_eq_ofTriple.1 hxQ).trans h))
  have hP : (#(P.support \ (f P).support) : ℝ) ≤ #(M ∩ P.support) := by
    refine Nat.cast_le.2 (card_le_card fun x hx ↦ ?_)
    obtain ⟨hxP, hxQ⟩ := mem_sdiff.1 hx
    refine mem_inter.2 ⟨hM x fun h ↦ hxQ ?_, hxP⟩
    rw [Polyad3.mem_support_iff_eq_ofTriple, Polyad3.mem_support_iff_eq_ofTriple.1 hxP]
    exact h.symm
  have hcard : (#(f P).support : ℝ) ≤ #((f P).support \ P.support) + #P.support := by
    exact_mod_cast card_le_card_sdiff_add_card
  have hMQ : (0 : ℝ) ≤ #(M ∩ (f P).support) / η := by positivity
  have hMP : (0 : ℝ) ≤ #(M ∩ P.support) / η := by positivity
  have hsum : (#(M ∩ (f P).support) + #(M ∩ P.support) : ℝ) / η =
      #(M ∩ (f P).support) / η + #(M ∩ P.support) / η := add_div _ _ _
  rw [hsum]
  by_cases hnew : H.IsTopRegularOverPolyad (f P) ε r
  · simp only [hnew, not_true_eq_false, ↓reduceIte]
    positivity
  simp only [hnew, not_false_eq_true, ↓reduceIte]
  by_cases hold : H.IsTopRegularOverPolyad P δ r
  · simp only [hold, not_true_eq_false, ↓reduceIte, zero_add]
    -- A regular original polyad passes regularity on unless a support difference is large.
    obtain h₁ | h₁ := le_or_gt (#((f P).support \ P.support) : ℝ) (η * #(f P).support)
    · obtain h₂ | h₂ := le_or_gt (#(P.support \ (f P).support) : ℝ) (η * #P.support)
      · exact absurd (hold.of_card_sdiff_support_le hε hη.le hbudget h₁ h₂) hnew
      · have : (#P.support : ℝ) ≤ #(M ∩ P.support) / η := by
          rw [le_div_iff₀ hη]
          linarith
        linarith
    · have : (#(f P).support : ℝ) ≤ #(M ∩ (f P).support) / η := by
        rw [le_div_iff₀ hη]
        linarith
      have : (0 : ℝ) ≤ #(M ∩ (f P).support) := Nat.cast_nonneg _
      linarith
  · simp only [hold, not_false_eq_true, ↓reduceIte]
    linarith

open Classical in
/-- **Exceptional support after recoloring the pairs.** Let `f` be an injective map from polyads
over `S` to polyads over `T`, and call a triple moved when its polyad over `T` is not the image
of its polyad over `S`. If the parameters satisfy `δ + 2η + η / ε ≤ ε`, the support of the
polyads over `T` that are not `(ε, r)`-top-regular is at most that of the polyads over `S` that
are not `(δ, r)`-top-regular, plus `(1 + 2 / η)` times the number of moved triples. -/
theorem sum_card_support_not_isTopRegularOverPolyad_le_of_injective [Fintype κ₂] [Fintype κ₂']
    [DecidableEq κ₂'] (hf : Function.Injective f)
    (hε : 0 < ε) (hη : 0 < η) (hbudget : δ + 2 * η + η / ε ≤ ε) :
    (∑ Q : Polyad3 T with ¬H.IsTopRegularOverPolyad Q ε r, (#Q.support : ℝ)) ≤
      (∑ P : Polyad3 S with ¬H.IsTopRegularOverPolyad P δ r, (#P.support : ℝ)) +
        (1 + 2 / η) * #{x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)} := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple T x ≠ f (Polyad3.ofTriple S x)}
  set I : Finset (Polyad3 T) := univ.image f
  -- The polyads over `T` outside the image of `f` consist of moved triples.
  have hout : ∀ Q ∈ univ \ I, (if ¬H.IsTopRegularOverPolyad Q ε r then (#Q.support : ℝ) else 0) ≤
      #(M ∩ Q.support) := by
    intro Q hQ
    have hsub : Q.support ⊆ M := fun x hx ↦ mem_filter.2 ⟨mem_univ _, fun h ↦
      (mem_sdiff.1 hQ).2 (mem_image.2 ⟨_, mem_univ _,
        (h.symm.trans (Polyad3.mem_support_iff_eq_ofTriple.1 hx).symm)⟩)⟩
    rw [inter_eq_right.2 hsub]
    split_ifs <;> simp
  have hsplit (F : Polyad3 T → ℝ) : ∑ Q, F Q = ∑ Q ∈ univ \ I, F Q + ∑ P, F (f P) := by
    rw [← sum_sdiff (subset_univ I), sum_image hf.injOn]
  have hT := Polyad3.sum_card_inter_support (S := T) M
  have hS := Polyad3.sum_card_inter_support (S := S) M
  have hM : (0 : ℝ) ≤ #M := Nat.cast_nonneg _
  rw [sum_filter, sum_filter, hsplit]
  have hT' : ∑ Q ∈ univ \ I, (#(M ∩ Q.support) : ℝ) + ∑ P, (#(M ∩ (f P).support) : ℝ) = #M := by
    rw [← hsplit fun Q ↦ (#(M ∩ Q.support) : ℝ)]
    exact_mod_cast hT
  have hS' : ∑ P : Polyad3 S, (#(M ∩ P.support) : ℝ) = #M := by exact_mod_cast hS
  have hloc := sum_le_sum fun (P : Polyad3 S) (_ : P ∈ univ) ↦
    card_support_not_isTopRegularOverPolyad_le (H := H) (r := r) hf hε hη hbudget
      (fun x hx ↦ mem_filter.2 ⟨mem_univ x, hx⟩) P
  rw [sum_add_distrib, sum_add_distrib, ← sum_div, sum_add_distrib, hS'] at hloc
  have hout' := sum_le_sum hout
  have hle : ∑ P, (#(M ∩ (f P).support) : ℝ) ≤ #M := by
    have : (0 : ℝ) ≤ ∑ Q ∈ univ \ I, (#(M ∩ Q.support) : ℝ) := sum_nonneg fun _ _ ↦ by positivity
    linarith
  have hdiv : (∑ P, (#(M ∩ (f P).support) : ℝ) + #M) / η ≤ 2 / η * #M := by
    rw [div_mul_eq_mul_div, two_mul]
    gcongr
  linarith

end Injective

end TauCeti.Colored3Graph
