/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Triadic.TopRegularization

/-!
# Recoloring irregular polyads

A coloring top-regular over most selected polyads can be edited to be top-regular over every
selected polyad. The edit assigns a fixed color to every unordered triple occurring in an
irregular selected polyad. This must erase all orderings of such a triple, since the top
coloring is defined on unordered triples, whereas polyads have ordered roles.

The union of erased unordered supports is saturated on each polyad support, including
polyads with repeated vertex cells and oriented pair palettes. Thus each selected polyad
is either unchanged and already regular, or becomes constant. The discrepancy of the edit
is at most six times the original exceptional proportion, for every positive regularity
parameter and every rank. No decomposition hypothesis on the selected polyads is needed.

The bounded refinement corollary combines this edit with
`Colored3Graph.exists_topRegularOverMostPolyads` for a fixed lower skeleton. It preserves
that skeleton's vertex partition and the projection of pair colors;
it does not assert regularity of the lower skeleton.
-/

public section

open Finset

namespace TauCeti.Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

/-- The unordered supports of any family of polyads are saturated on every polyad support.
The same reindexing of two supported triples has the same polyad, so erasing one ordering
of one triple erases all triples of its original polyad. -/
private theorem mem_unordered_support_of_ofTriple_eq
    {κ₂ : Type*} {S : PairSkeleton3 κ₂ V} (A : Finset (Polyad3 S))
    {x y : {x : Fin 3 → V // Function.Injective x}}
    (h : Polyad3.ofTriple S x = Polyad3.ofTriple S y)
    (hx : Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ ∈
      A.biUnion fun P ↦ P.support.image fun z ↦ Set.powersetCard.ofFinEmb 3 V ⟨z.1, z.2⟩) :
    Set.powersetCard.ofFinEmb 3 V ⟨y.1, y.2⟩ ∈
      A.biUnion fun P ↦ P.support.image fun z ↦ Set.powersetCard.ofFinEmb 3 V ⟨z.1, z.2⟩ := by
  classical
  obtain ⟨P, hP, hzP⟩ := mem_biUnion.1 hx
  obtain ⟨z, hz, hzx⟩ := mem_image.1 hzP
  have hindices (i : Fin 3) : ∃ j, x.1 j = z.1 i := by
    have hzi : z.1 i ∈ Set.powersetCard.ofFinEmb 3 V ⟨z.1, z.2⟩ := by simp
    rw [hzx, Set.powersetCard.mem_ofFinEmb_iff_mem_range] at hzi
    exact hzi
  choose f hf using hindices
  let e : Fin 3 ↪ Fin 3 := ⟨f, fun i j hij ↦ z.2 (by rw [← hf i, ← hf j, hij])⟩
  have hzcomp : (⟨x.1 ∘ e, x.2.comp e.injective⟩ :
      {x : Fin 3 → V // Function.Injective x}) = z := Subtype.ext (funext hf)
  let w : {x : Fin 3 → V // Function.Injective x} := ⟨y.1 ∘ e, y.2.comp e.injective⟩
  have hw : w ∈ P.support := by
    rw [Polyad3.mem_support_iff_eq_ofTriple,
      Polyad3.mem_support_iff_eq_ofTriple.1 hz, ← hzcomp]
    exact Polyad3.ofTriple_comp_eq_ofTriple_comp h e
  have hwy : Set.powersetCard.ofFinEmb 3 V ⟨w.1, w.2⟩ =
      Set.powersetCard.ofFinEmb 3 V ⟨y.1, y.2⟩ := by
    apply SetLike.coe_injective
    simp only [Set.powersetCard.coe_ofFinEmb]
    exact (Finite.surjective_of_injective e.injective).range_comp y.1
  exact mem_biUnion.2 ⟨P, hP, mem_image.2 ⟨w, hw, hwy⟩⟩

/-- A coloring regular over most selected polyads admits an edit of discrepancy at most
`6 * ε` that is top-regular over every selected polyad at the original parameter and rank.
The palette need not be finite; `c₀` is the color assigned to the erased triples. -/
theorem exists_approximates3_forall_isTopRegularOverPolyad
    (H : Colored3Graph κ V) (C : TriadicComplex3 V) {η ε : ℝ} {r : ℕ}
    (hη : 0 < η) (h : H.TopRegularOverMostPolyads C η ε r) (c₀ : κ) :
    ∃ H' : Colored3Graph κ V, H.Approximates3 H' (6 * ε) ∧
      ∀ P ∈ C.polyads, H'.IsTopRegularOverPolyad P η r := by
  classical
  let A := C.polyads.filter fun P ↦ ¬H.IsTopRegularOverPolyad P η r
  let B := A.biUnion fun P ↦ P.support.image fun x ↦
    Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩
  let H' : Colored3Graph κ V := ⟨fun s ↦ if s ∈ B then c₀ else H.color s⟩
  have hcolor (s : Set.powersetCard V 3) :
      H'.color s = if s ∈ B then c₀ else H.color s := rfl
  refine ⟨H', ?_, ?_⟩
  -- Charge each erased unordered triple to one supported ordering of a bad polyad.
  · have hB : #B ≤ ∑ P ∈ A, #P.support :=
      card_biUnion_le.trans (sum_le_sum fun P _ ↦ card_image_le)
    have hmass : (#B : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 3 := by
      calc
        (#B : ℝ) ≤ ∑ P ∈ A, (#P.support : ℝ) := by exact_mod_cast hB
        _ ≤ ε * (Fintype.card V).descFactorial 3 := h.sum_card_support_le
        _ ≤ ε * (Fintype.card V : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left
            (by exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3) h.nonneg
    have hsub : {s | H.color s ≠ H'.color s} ⊆ (B : Set (Set.powersetCard V 3)) := by
      intro s hs
      by_contra hsB
      have hsB' : s ∉ B := hsB
      exact hs (by simp only [hcolor, ite_eq_right hsB'])
    have hedit : ({s | H.color s ≠ H'.color s}.ncard : ℝ) ≤ #B := by
      exact_mod_cast (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_coe_finset B)
    rw [approximates3_iff, editDiscrepancy3_def]
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat, Nat.card_eq_fintype_card]
    by_cases hn : Fintype.card V = 0
    · simpa [hn] using h.nonneg
    · apply (div_le_iff₀ (pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) 3)).2
      nlinarith
  -- Saturation makes a touched polyad constant; every untouched selected polyad was regular.
  · intro P hP
    by_cases hB : ∃ x ∈ P.support, Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ ∈ B
    · obtain ⟨x, hx, hxB⟩ := hB
      apply (isTopRegularOverPolyad_const P r c₀ hη).congr
      intro y hy
      rw [color_const, hcolor, ite_eq_left]
      exact mem_unordered_support_of_ofTriple_eq A
        ((Polyad3.mem_support_iff_eq_ofTriple.1 hx).symm.trans
          (Polyad3.mem_support_iff_eq_ofTriple.1 hy)) hxB
    · have hreg : H.IsTopRegularOverPolyad P η r := by
        by_contra hirr
        obtain hzero | ⟨x, hx⟩ := P.support.eq_empty_or_nonempty
        · exact hirr ((isTopRegularOverPolyad_const P r c₀ hη).congr
            fun x hx ↦ (notMem_empty x (hzero ▸ hx)).elim)
        · exact hB ⟨x, hx, mem_biUnion.2 ⟨P, mem_filter.2 ⟨hP, hirr⟩,
            mem_image.2 ⟨x, hx, rfl⟩⟩⟩
      apply hreg.congr
      intro x hx
      rw [hcolor, ite_eq_right (fun hxB ↦ hB ⟨x, hx, hxB⟩)]

/-- A fixed lower skeleton has a bounded pair-color refinement and a nearby top coloring
regular over every polyad, with the original vertex cells and coherent projection of pair
colors. This is a top-layer approximation only: no lower pair-regularity is asserted. -/
theorem exists_approximates3_topRegular_refinement [Finite κ] {κ₂ : Type*} [Fintype κ₂]
    (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (r : ℕ) (c₀ : κ) :
    ∃ (H' : Colored3Graph κ V) (C : TriadicComplex3 V)
      (π : Fin C.pairColorCount → κ₂),
      H.Approximates3 H' (6 * ε) ∧
      C.pairColorCount ≤
        topRegularRefinementBound #S.vertexPart.parts r η ε (Fintype.card κ₂) ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧ ∀ P : Polyad3 C.skeleton, H'.IsTopRegularOverPolyad P η r := by
  obtain ⟨C, π, hbound, hV, hπ, hrev, hall, hmost⟩ :=
    H.exists_topRegularOverMostPolyads S hη hε r
  obtain ⟨H', hedit, hreg⟩ :=
    H.exists_approximates3_forall_isTopRegularOverPolyad C hη hmost c₀
  exact ⟨H', C, π, hedit, hbound, hV, hπ, hrev, hall, fun P ↦ hreg P (hall ▸ mem_univ P)⟩

end TauCeti.Colored3Graph
