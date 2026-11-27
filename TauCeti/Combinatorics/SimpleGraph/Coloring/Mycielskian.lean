/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Mycielski's construction

The Mycielskian of a graph `G` on `V` is the graph `G.mycielskian` on `V ⊕ V ⊕ Unit` whose
vertices are the vertices `inl v` of `G`, a *shadow* `inr (inl v)` of each of them and an *apex*
`inr (inr ())`. The vertices of `G` keep their edges, the shadow of `v` is joined to the
neighbours of `v` in `G`, and the apex is joined to every shadow; there are no other edges.

The Mycielskian raises the chromatic number by exactly one, `χ(G.mycielskian) = χ(G) + 1` in
`ℕ∞`, while for `n ≥ 3` it has a clique on `n` vertices only when `G` has one. Iterating the
construction from the graph on no vertices therefore produces, for every `k : ℕ`, a finite graph
with no triangle and chromatic number `k`.

## Main definitions

* `SimpleGraph.mycielskian`: the Mycielskian of a graph.

## Main results

* `SimpleGraph.colorable_mycielskian_add_one_iff`: `G.mycielskian` is colourable with `n + 1`
  colours exactly when `G` is colourable with `n` colours.
* `SimpleGraph.chromaticNumber_mycielskian`: `χ(G.mycielskian) = χ(G) + 1`.
* `SimpleGraph.cliqueFree_mycielskian_iff`: for `n ≥ 3`, `G.mycielskian` has no clique on `n`
  vertices exactly when `G` has none.
* `SimpleGraph.exists_cliqueFree_three_chromaticNumber_eq`: Mycielski's theorem, that for every
  `k` some triangle-free graph on finitely many vertices has chromatic number `k`.

## References

* J. Mycielski, *Sur le coloriage des graphs*, Colloq. Math. 3 (1955), 161–162.
* J. A. Bondy and U. S. R. Murty, *Graph Theory with Applications*, Theorem 8.7 and its proof.
-/

public section

namespace SimpleGraph

variable {V α : Type*} {G : SimpleGraph V} {n : ℕ}

/-- The Mycielskian of `G`, on `V ⊕ V ⊕ Unit`: the vertices `inl v` carry a copy of `G`, the
shadow `inr (inl v)` of `v` is joined to every `inl w` with `w` adjacent to `v` in `G`, and the
apex `inr (inr ())` is joined to every shadow. -/
def mycielskian (G : SimpleGraph V) : SimpleGraph (V ⊕ V ⊕ Unit) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inl v, .inr (.inl w) => G.Adj v w
    | .inr (.inl v), .inl w => G.Adj v w
    | .inr (.inl _), .inr (.inr _) => True
    | .inr (.inr _), .inr (.inl _) => True
    | _, _ => False
  symm := ⟨by rintro (v | v | u) (w | w | u') h <;> first | exact h.symm | trivial⟩
  loopless := ⟨by rintro (v | v | u) h <;> first | exact G.loopless.irrefl v h | exact h⟩

@[simp, grind =]
theorem mycielskian_adj_inl_inl {v w : V} :
    G.mycielskian.Adj (.inl v) (.inl w) ↔ G.Adj v w :=
  Iff.rfl

@[simp, grind =]
theorem mycielskian_adj_inl_inr_inl {v w : V} :
    G.mycielskian.Adj (.inl v) (.inr (.inl w)) ↔ G.Adj v w :=
  Iff.rfl

@[simp, grind =]
theorem mycielskian_adj_inr_inl_inl {v w : V} :
    G.mycielskian.Adj (.inr (.inl v)) (.inl w) ↔ G.Adj v w :=
  Iff.rfl

@[simp, grind .]
theorem mycielskian_adj_inr_inl_inr_inr {v : V} {u : Unit} :
    G.mycielskian.Adj (.inr (.inl v)) (.inr (.inr u)) :=
  trivial

@[simp, grind .]
theorem mycielskian_adj_inr_inr_inr_inl {u : Unit} {v : V} :
    G.mycielskian.Adj (.inr (.inr u)) (.inr (.inl v)) :=
  trivial

@[simp, grind .]
theorem not_mycielskian_adj_inl_inr_inr {v : V} {u : Unit} :
    ¬G.mycielskian.Adj (.inl v) (.inr (.inr u)) :=
  id

@[simp, grind .]
theorem not_mycielskian_adj_inr_inr_inl {u : Unit} {v : V} :
    ¬G.mycielskian.Adj (.inr (.inr u)) (.inl v) :=
  id

/-- Two shadows are never adjacent. -/
@[simp, grind .]
theorem not_mycielskian_adj_inr_inl_inr_inl {v w : V} :
    ¬G.mycielskian.Adj (.inr (.inl v)) (.inr (.inl w)) :=
  id

/-- The embedding of `G` into its Mycielskian, onto the vertices `inl v`. -/
def Embedding.mycielskianInl : G ↪g G.mycielskian where
  toFun := .inl
  inj' _ _ := Sum.inl.inj
  map_rel_iff' := mycielskian_adj_inl_inl

@[simp]
theorem Embedding.mycielskianInl_apply (v : V) :
    (Embedding.mycielskianInl : G ↪g G.mycielskian) v = .inl v :=
  (rfl)

/-! ### Colourings -/

/-- A colouring of `G` by `α` extends to a colouring of `G.mycielskian` by `Option α`: each
shadow gets the colour of its vertex and the apex the new colour `none`. -/
private def Coloring.mycielskian (C : G.Coloring α) : G.mycielskian.Coloring (Option α) :=
  Coloring.mk (Sum.elim (some ∘ C) (Sum.elim (some ∘ C) fun _ ↦ none)) <| by
    rintro (v | v | u) (w | w | u') h <;> simp_all [C.valid]

open scoped Classical in
/-- A colouring of `G.mycielskian` restricts to a colouring of `G` that avoids the colour of the
apex: every vertex `v` of the apex's colour is recoloured with the colour of its shadow. -/
private noncomputable def Coloring.ofMycielskian (C : G.mycielskian.Coloring α) :
    G.Coloring {a // a ≠ C (.inr (.inr ()))} :=
  Coloring.mk
    (fun v ↦ if h : C (.inl v) = C (.inr (.inr ())) then
      ⟨C (.inr (.inl v)), C.valid mycielskian_adj_inr_inl_inr_inr⟩ else ⟨C (.inl v), h⟩) <| by
    intro v w h
    have hvw : C (.inl v) ≠ C (.inl w) := C.valid (mycielskian_adj_inl_inl.2 h)
    split_ifs with hv hw hw <;> simp only [ne_eq, Subtype.mk.injEq]
    · exact absurd (hv.trans hw.symm) hvw
    · exact C.valid (mycielskian_adj_inr_inl_inl.2 h)
    · exact C.valid (mycielskian_adj_inl_inr_inl.2 h)
    · exact hvw

/-- If `G` is colourable with `n` colours, its Mycielskian is colourable with `n + 1`. -/
theorem Colorable.mycielskian (h : G.Colorable n) : G.mycielskian.Colorable (n + 1) := by
  simpa using h.some.mycielskian.colorable

/-- If the Mycielskian of `G` is colourable with `n + 1` colours, then `G` is colourable with
`n`. -/
theorem Colorable.of_mycielskian (h : G.mycielskian.Colorable (n + 1)) : G.Colorable n := by
  simpa [Fintype.card_subtype_compl] using h.some.ofMycielskian.colorable

/-- The Mycielskian of `G` is colourable with `n + 1` colours exactly when `G` is colourable with
`n` colours. -/
theorem colorable_mycielskian_add_one_iff :
    G.mycielskian.Colorable (n + 1) ↔ G.Colorable n :=
  ⟨.of_mycielskian, .mycielskian⟩

/-- The Mycielskian raises the chromatic number by exactly one. No finiteness is assumed: if `G`
is not colourable with finitely many colours, both sides are `⊤`. -/
theorem chromaticNumber_mycielskian :
    G.mycielskian.chromaticNumber = G.chromaticNumber + 1 := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [chromaticNumber_le_iff_colorable]
    cases n with
    | zero => simp
    | succ n =>
      rw [colorable_mycielskian_add_one_iff, ← chromaticNumber_le_iff_colorable, Nat.cast_add,
        Nat.cast_one, ENat.add_le_add_iff_right ENat.one_ne_top]

/-! ### Cliques -/

/-- The apex lies on no triangle: its neighbours are shadows, and no two shadows are adjacent. -/
private theorem ne_apex_of_adj_of_adj_of_adj {x y z : V ⊕ V ⊕ Unit}
    (hxy : G.mycielskian.Adj x y) (hxz : G.mycielskian.Adj x z) (hyz : G.mycielskian.Adj y z) :
    x ≠ .inr (.inr ()) := by
  rintro rfl
  rcases y with y | y | y <;> rcases z with z | z | z <;> simp_all

/-- Folding each shadow onto its vertex, with the apex sent to `v₀`. Away from the apex it maps
edges of `G.mycielskian` to edges of `G`. -/
private def foldMycielskian (v₀ : V) : V ⊕ V ⊕ Unit → V :=
  Sum.elim id (Sum.elim id fun _ ↦ v₀)

private theorem adj_foldMycielskian {v₀ : V} {x y : V ⊕ V ⊕ Unit}
    (h : G.mycielskian.Adj x y) (hx : x ≠ .inr (.inr ())) (hy : y ≠ .inr (.inr ())) :
    G.Adj (foldMycielskian v₀ x) (foldMycielskian v₀ y) := by
  rcases x with x | x | x <;> rcases y with y | y | y <;> simp_all [foldMycielskian]

/-- For `n ≥ 3`, the Mycielskian of `G` has no clique on `n` vertices exactly when `G` has none.
A clique on at least three vertices avoids the apex and contains at most one of a vertex and its
shadow, so folding each shadow onto its vertex maps it onto a clique of `G`. -/
theorem cliqueFree_mycielskian_iff (hn : 3 ≤ n) :
    G.mycielskian.CliqueFree n ↔ G.CliqueFree n := by
  refine ⟨fun h ↦ h.comap Embedding.mycielskianInl.isContained, fun hG ↦ ?_⟩
  contrapose hG
  rw [not_cliqueFree_iff_top_isContained] at hG ⊢
  obtain ⟨f⟩ := hG
  have hne (i : Fin n) : f i ≠ .inr (.inr ()) := by
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 <| show 1 < (Finset.univ.erase i).card by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    simp only [Finset.mem_erase] at hj hk
    exact ne_apex_of_adj_of_adj_of_adj (f.toHom.map_adj (Ne.symm hj.1))
      (f.toHom.map_adj (Ne.symm hk.1)) (f.toHom.map_adj hjk)
  obtain ⟨v₀⟩ : Nonempty V := by
    rcases hx : f ⟨0, by omega⟩ with v | v | ⟨⟨⟩⟩
    exacts [⟨v⟩, ⟨v⟩, absurd hx (hne _)]
  let g : completeGraph (Fin n) →g G :=
    ⟨foldMycielskian v₀ ∘ f, fun h ↦ adj_foldMycielskian (f.toHom.map_adj h) (hne _) (hne _)⟩
  exact (g.toCopy g.injective_of_top_hom).isContained

/-! ### Triangle-free graphs of every chromatic number -/

/-- Mycielski's theorem: for every `k : ℕ` there is a graph on `Fin n`, for some `n`, with no
triangle and chromatic number `k`. -/
theorem exists_cliqueFree_three_chromaticNumber_eq (k : ℕ) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), H.CliqueFree 3 ∧ H.chromaticNumber = k := by
  induction k with
  | zero => exact ⟨0, ⊥, cliqueFree_bot (by omega), chromaticNumber_eq_zero_of_isEmpty⟩
  | succ k ih =>
    obtain ⟨n, H, hH, hχ⟩ := ih
    have hc : Fintype.card (Fin n ⊕ Fin n ⊕ Unit) = n + (n + 1) := by simp
    let e := H.mycielskian.overFinIso hc
    refine ⟨_, H.mycielskian.overFin hc, ?_, ?_⟩
    · exact ((cliqueFree_mycielskian_iff le_rfl).2 hH).comap e.symm.isContained
    · rw [← chromaticNumber_congr e, chromaticNumber_mycielskian, hχ, Nat.cast_add, Nat.cast_one]

end SimpleGraph
