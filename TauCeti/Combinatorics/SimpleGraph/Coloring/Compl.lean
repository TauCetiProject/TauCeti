/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Coloring.IndepNum

import TauCeti.Combinatorics.SimpleGraph.Degree

/-!
# The chromatic numbers of a graph and its complement

The Nordhaus–Gaddum inequalities bound the chromatic numbers of a finite graph `G` on `n`
vertices and of its complement `Gᶜ` against each other:

* `chromaticNumber_add_chromaticNumber_compl_le`: `χ(G) + χ(Gᶜ) ≤ n + 1`;
* `card_le_chromaticNumber_mul_chromaticNumber_compl`: `n ≤ χ(G) · χ(Gᶜ)`.

Both are attained by the complete graph. The sum is bounded by adding the vertices one at a time,
each needing a new colour in `G` or in `Gᶜ` only when it has at least as many neighbours there as
colours are in use. The product follows from the bound `n ≤ χ(G) · α(G)` of
`SimpleGraph.card_le_chromaticNumber_mul_indepNum`, since an independent set of `G` is a clique of
`Gᶜ`.

See Nordhaus and Gaddum, *On complementary graphs* (1956), and Bondy–Murty, *Graph Theory with
Applications*, Exercise 8.1.4.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `f` colours the vertices of `s` properly for `H`, by natural numbers below `a`. -/
private def IsBddColoringOn (H : SimpleGraph V) (s : Finset V) (a : ℕ) (f : V → ℕ) : Prop :=
  (∀ v ∈ s, f v < a) ∧ ∀ v ∈ s, ∀ w ∈ s, H.Adj v w → f v ≠ f w

/-- Giving a new vertex `v` a colour `c` that none of its neighbours in `s` has extends a proper
colouring of `s` to `insert v s`. -/
private lemma IsBddColoringOn.update [DecidableEq V] {H : SimpleGraph V} {s : Finset V}
    {a b c : ℕ} {f : V → ℕ} {v : V} (hf : IsBddColoringOn H s a f) (hv : v ∉ s) (hab : a ≤ b)
    (hc : c < b) (hcf : ∀ w ∈ s, H.Adj v w → f w ≠ c) :
    IsBddColoringOn H (insert v s) b (Function.update f v c) := by
  have hne : ∀ w ∈ s, w ≠ v := fun w hw hwv ↦ hv (hwv ▸ hw)
  refine ⟨fun w hw ↦ ?_, fun x hx y hy hxy ↦ ?_⟩
  · obtain rfl | hw := mem_insert.mp hw
    · simpa using hc
    · simpa [hne w hw] using (hf.1 w hw).trans_le hab
  rcases mem_insert.mp hx with hxv | hxs <;> rcases mem_insert.mp hy with hyv | hys
  · exact absurd (hxv.trans hyv.symm) hxy.ne
  · simpa [hxv, hne y hys] using (hcf y hys (hxv ▸ hxy)).symm
  · simpa [hyv, hne x hxs] using hcf x hxs (hyv ▸ hxy.symm)
  · simpa [hne x hxs, hne y hys] using hf.2 x hxs y hys hxy

/-- A proper colouring of `s` extends to `insert v s` with the same colours, or with one more
colour when the neighbours of `v` in `s` are at least as many as the colours. -/
private lemma IsBddColoringOn.exists_insert [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {s : Finset V} {a : ℕ} {f : V → ℕ} {v : V}
    (hf : IsBddColoringOn H s a f) (hv : v ∉ s) :
    ∃ f', IsBddColoringOn H (insert v s) a f' ∨
      a ≤ #{w ∈ s | H.Adj v w} ∧ IsBddColoringOn H (insert v s) (a + 1) f' := by
  by_cases h : ∃ c < a, ∀ w ∈ s, H.Adj v w → f w ≠ c
  · obtain ⟨c, hc, hcf⟩ := h
    exact ⟨_, .inl (hf.update hv le_rfl hc hcf)⟩
  · push Not at h
    refine ⟨_, .inr ⟨?_, hf.update hv a.le_succ a.lt_succ_self fun w _ _ hw ↦
      (hf.1 w ‹_›).ne hw⟩⟩
    calc
      a = #(range a) := (card_range a).symm
      _ ≤ #({w ∈ s | H.Adj v w}.image f) := card_le_card fun c hc ↦ by
        obtain ⟨w, hw, hvw, rfl⟩ := h c (mem_range.mp hc)
        exact mem_image_of_mem f (mem_filter.mpr ⟨hw, hvw⟩)
      _ ≤ #{w ∈ s | H.Adj v w} := card_image_le

/-- The vertices of each finite set `s` can be coloured properly for `G` and for `Gᶜ` with at
most `#s + 1` colours in total. -/
private lemma exists_isBddColoringOn_compl (s : Finset V) :
    ∃ a b f g, IsBddColoringOn G s a f ∧ IsBddColoringOn Gᶜ s b g ∧ a + b ≤ #s + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, 0, ⟨by simp, by simp⟩, ⟨by simp, by simp⟩, by simp⟩
  | insert v s hv ih =>
    obtain ⟨a, b, f, g, hf, hg, hab⟩ := ih
    have hdeg := card_filter_adj_add_card_filter_compl_adj (G := G) hv
    rw [card_insert_of_notMem hv]
    obtain ⟨f', hf' | ⟨ha, hf'⟩⟩ := hf.exists_insert hv <;>
      obtain ⟨g', hg' | ⟨hb, hg'⟩⟩ := hg.exists_insert hv
    · exact ⟨a, b, f', g', hf', hg', by omega⟩
    · exact ⟨a, b + 1, f', g', hf', hg', by omega⟩
    · exact ⟨a + 1, b, f', g', hf', hg', by omega⟩
    · exact ⟨a + 1, b + 1, f', g', hf', hg', by omega⟩

/-- A proper colouring by natural numbers below `a` of all the vertices makes `H` colourable with
`a` colours. -/
private lemma IsBddColoringOn.colorable [Fintype V] {H : SimpleGraph V} {a : ℕ} {f : V → ℕ}
    (hf : IsBddColoringOn H univ a f) : H.Colorable a :=
  (colorable_iff_exists_bdd_nat_coloring a).mpr
    ⟨Coloring.mk f fun {v w} h ↦ hf.2 v (mem_univ v) w (mem_univ w) h,
      fun v ↦ hf.1 v (mem_univ v)⟩

/-- **Nordhaus–Gaddum inequality** for the sum: a finite graph on `n` vertices and its complement
have chromatic numbers summing to at most `n + 1`. -/
theorem chromaticNumber_add_chromaticNumber_compl_le [Fintype V] :
    G.chromaticNumber + Gᶜ.chromaticNumber ≤ Fintype.card V + 1 := by
  classical
  obtain ⟨a, b, f, g, hf, hg, hab⟩ := exists_isBddColoringOn_compl (G := G) univ
  rw [card_univ] at hab
  calc
    G.chromaticNumber + Gᶜ.chromaticNumber ≤ a + b :=
      add_le_add hf.colorable.chromaticNumber_le hg.colorable.chromaticNumber_le
    _ ≤ Fintype.card V + 1 := by exact_mod_cast hab

/-- **Nordhaus–Gaddum inequality** for the product: the number of vertices of a finite graph is at
most the product of its chromatic number and the chromatic number of its complement. -/
theorem card_le_chromaticNumber_mul_chromaticNumber_compl [Fintype V] :
    (Fintype.card V : ℕ∞) ≤ G.chromaticNumber * Gᶜ.chromaticNumber := by
  calc
    (Fintype.card V : ℕ∞) ≤ G.chromaticNumber * G.indepNum :=
      card_le_chromaticNumber_mul_indepNum
    _ ≤ G.chromaticNumber * Gᶜ.chromaticNumber := by
      gcongr
      rw [← cliqueNum_compl]
      exact Gᶜ.cliqueNum_le_chromaticNumber

end SimpleGraph
