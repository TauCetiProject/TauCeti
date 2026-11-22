/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.Combinatorics.SimpleGraph.Clique.Basic

/-!
# Clique tags

Given a simple graph `H` on `V` and a colouring `κ : V → ℕ`, the clique-tagged graph
`H.cliqueTag κ` lives on `V ⊕ Σ x : V, Fin (κ x + 3)`. It has the edges of `H` between the
original vertices, a clique on the `κ x + 3` tag vertices `⟨x, i⟩` of each `x`, and one edge from
`x` to its tag vertex `⟨x, 0⟩`. The size of the clique attached to `x` records the colour of `x`,
so that the colouring becomes part of the uncoloured graph.

When `H` is triangle-free, the tags can be recognised inside the tagged graph: a vertex lies in a
triangle exactly when it is a tag vertex, the unique such neighbour of an original vertex `x` is
`⟨x, 0⟩`, and `⟨x, 0⟩` has exactly `κ x + 2` neighbours lying in triangles. Consequently two
triangle-free coloured graphs have isomorphic tagged graphs exactly when they are isomorphic
through a colour-preserving isomorphism. This turns coloured graphs into plain graphs, the last
step in coding a countable structure into a countable graph so that isomorphism is preserved and
reflected (H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable
structures*, J. Symbolic Logic 54 (1989), Theorem 1). Attaching gadgets to vertices that are told
apart from the coded edges by the short cycles they create follows A. Montalbán, *Computable
Structure Theory: Within the Arithmetic*, Theorem VI.27, whose gadgets differ from the cliques
used here.

The two directions are `SimpleGraph.nonempty_iso_cliqueTag_of_iso`, which needs no hypothesis on
the graphs, and `SimpleGraph.exists_iso_of_iso_cliqueTag`, which needs both to be triangle-free:
in the tagged graph of a triangle the original vertices lie in triangles as well.

## Main definitions and results

* `SimpleGraph.cliqueTag`: the clique-tagged graph of a coloured graph.
* `SimpleGraph.comap_inl_cliqueTag`: the tagged graph restricted to the original vertices is `H`.
* `SimpleGraph.exists_isNClique_three_mem_cliqueTag_iff`: for triangle-free `H`, a vertex of the
  tagged graph lies in a triangle exactly when it is a tag vertex.
* `SimpleGraph.cliqueTag_adj_inl_and_isRight_iff`: the only tag neighbour of an original vertex
  `x` is `⟨x, 0⟩`.
* `SimpleGraph.ncard_setOf_cliqueTag_adj_inr_zero_and_isRight`: `⟨x, 0⟩` has `κ x + 2` tag
  neighbours.
* `SimpleGraph.nonempty_iso_cliqueTag_iff`: for triangle-free graphs, the tagged graphs are
  isomorphic exactly when there is a colour-preserving isomorphism of the coloured graphs.
-/

public section

namespace SimpleGraph

variable {V V' : Type*}

/-- The clique-tagged graph of `H` with colouring `κ`, on `V ⊕ Σ x : V, Fin (κ x + 3)`: the
original vertices `Sum.inl v` carry the edges of `H`, the `κ x + 3` tag vertices
`Sum.inr ⟨x, i⟩` of each `x` form a clique, and each `Sum.inl x` is joined to its tag vertex
`Sum.inr ⟨x, 0⟩` and to no other tag vertex. -/
def cliqueTag (H : SimpleGraph V) (κ : V → ℕ) : SimpleGraph (V ⊕ Σ x : V, Fin (κ x + 3)) where
  Adj
    | .inl u, .inl v => H.Adj u v
    | .inl u, .inr p => p.1 = u ∧ p.2 = 0
    | .inr p, .inl u => p.1 = u ∧ p.2 = 0
    | .inr p, .inr q => p.1 = q.1 ∧ p ≠ q
  symm.symm := by
    rintro (u | p) (v | q) h
    · exact h.symm
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl := by
    rintro (u | p) h
    · exact H.irrefl h
    · exact h.2 rfl

variable {H : SimpleGraph V} {κ : V → ℕ} {u v : V} {p q : Σ x : V, Fin (κ x + 3)}

@[simp]
theorem cliqueTag_adj_inl_inl : (H.cliqueTag κ).Adj (.inl u) (.inl v) ↔ H.Adj u v := Iff.rfl

@[simp]
theorem cliqueTag_adj_inl_inr : (H.cliqueTag κ).Adj (.inl u) (.inr p) ↔ p.1 = u ∧ p.2 = 0 :=
  Iff.rfl

@[simp]
theorem cliqueTag_adj_inr_inl : (H.cliqueTag κ).Adj (.inr p) (.inl u) ↔ p.1 = u ∧ p.2 = 0 :=
  Iff.rfl

@[simp]
theorem cliqueTag_adj_inr_inr : (H.cliqueTag κ).Adj (.inr p) (.inr q) ↔ p.1 = q.1 ∧ p ≠ q :=
  Iff.rfl

/-- The tagged graph restricted to the original vertices is the original graph. -/
@[simp]
theorem comap_inl_cliqueTag : (H.cliqueTag κ).comap Sum.inl = H := by
  ext u v
  simp

/-- Every tag vertex lies in a triangle of the tagged graph, inside the clique of its owner. -/
theorem exists_isNClique_three_mem_cliqueTag_inr (p : Σ x : V, Fin (κ x + 3)) :
    ∃ s, (H.cliqueTag κ).IsNClique 3 s ∧ .inr p ∈ s := by
  obtain ⟨x, i⟩ := p
  have hcard : 1 < (Finset.univ.erase i).card := by simp
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase] at ha hb
  refine exists_isNClique_three_mem_iff.2 ⟨.inr ⟨x, a⟩, .inr ⟨x, b⟩, ?_, ?_, ?_⟩ <;>
    simp [ha.1.symm, hb.1.symm, hab]

/-- In the tagged graph of a triangle-free graph, no original vertex lies in a triangle. -/
theorem not_exists_isNClique_three_mem_cliqueTag_inl (hH : H.CliqueFree 3) (v : V) :
    ¬ ∃ s, (H.cliqueTag κ).IsNClique 3 s ∧ .inl v ∈ s := by
  classical
  rw [exists_isNClique_three_mem_iff]
  rintro ⟨a | ⟨x, i⟩, b | ⟨y, j⟩, ha, hb, hab⟩
  · exact hH {v, a, b} (is3Clique_triple_iff.2 ⟨ha, hb, hab⟩)
  · simp only [cliqueTag_adj_inl_inr, cliqueTag_adj_inl_inl] at ha hb hab
    exact ha.ne (hb.1.symm.trans hab.1)
  · simp only [cliqueTag_adj_inl_inr, cliqueTag_adj_inl_inl, cliqueTag_adj_inr_inl] at ha hb hab
    exact hb.ne (ha.1.symm.trans hab.1)
  · simp only [cliqueTag_adj_inl_inr, cliqueTag_adj_inr_inr] at ha hb hab
    obtain ⟨rfl, hi⟩ := ha
    obtain ⟨rfl, hj⟩ := hb
    exact hab.2 (by rw [hi, hj])

/-- In the tagged graph of a triangle-free graph, a vertex lies in a triangle exactly when it is
a tag vertex. -/
theorem exists_isNClique_three_mem_cliqueTag_iff (hH : H.CliqueFree 3)
    {w : V ⊕ Σ x : V, Fin (κ x + 3)} :
    (∃ s, (H.cliqueTag κ).IsNClique 3 s ∧ w ∈ s) ↔ w.isRight := by
  rcases w with v | p
  · simpa using not_exists_isNClique_three_mem_cliqueTag_inl hH v
  · simpa using exists_isNClique_three_mem_cliqueTag_inr p

/-- The only tag vertex adjacent to the original vertex `v` is `⟨v, 0⟩`. -/
theorem cliqueTag_adj_inl_and_isRight_iff {w : V ⊕ Σ x : V, Fin (κ x + 3)} :
    (H.cliqueTag κ).Adj (.inl v) w ∧ w.isRight ↔ w = .inr ⟨v, 0⟩ := by
  rcases w with u | ⟨x, i⟩
  · simp
  · simp only [cliqueTag_adj_inl_inr, Sum.isRight_inr, and_true, Sum.inr.injEq,
      Sigma.mk.injEq]
    constructor
    · rintro ⟨rfl, hi⟩
      exact ⟨rfl, heq_of_eq hi⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, eq_of_heq h⟩

/-- The tag vertex `⟨v, 0⟩` has exactly `κ v + 2` neighbours among the tag vertices: the rest of
the clique attached to `v`. -/
theorem ncard_setOf_cliqueTag_adj_inr_zero_and_isRight (v : V) :
    {w | (H.cliqueTag κ).Adj (.inr ⟨v, 0⟩) w ∧ w.isRight}.ncard = κ v + 2 := by
  classical
  have : {w | (H.cliqueTag κ).Adj (.inr ⟨v, 0⟩) w ∧ w.isRight} =
      ((Finset.univ.erase 0).image fun i : Fin (κ v + 3) ↦
        (Sum.inr ⟨v, i⟩ : V ⊕ Σ x : V, Fin (κ x + 3)) : Set _) := by
    ext (u | ⟨x, i⟩)
    · simp
    · simp only [Set.mem_ofPred_eq, cliqueTag_adj_inr_inr, Sum.isRight_inr, and_true,
        Finset.coe_image, Finset.coe_erase, Finset.coe_univ, Set.mem_image, Set.mem_sdiff,
        Set.mem_univ, Set.mem_singleton_iff, true_and, Sum.inr.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨i, fun hi ↦ h (hi ▸ rfl), rfl⟩
      · rintro ⟨j, hj, h⟩
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
        obtain rfl := eq_of_heq h
        exact ⟨rfl, fun h ↦ hj (eq_of_heq (Sigma.mk.inj_iff.1 h).2).symm⟩
  rw [this, Set.ncard_coe_finset, Finset.card_image_of_injective _ (fun i j h ↦ ?_)]
  · simp
  · simpa using h

/-- A colour-preserving isomorphism of coloured graphs induces an isomorphism of their tagged
graphs. -/
theorem nonempty_iso_cliqueTag_of_iso {H' : SimpleGraph V'} {κ' : V' → ℕ} (e : H ≃g H')
    (hκ : ∀ v, κ' (e v) = κ v) : Nonempty (H.cliqueTag κ ≃g H'.cliqueTag κ') := by
  obtain rfl : κ = κ' ∘ e := funext fun v ↦ (hκ v).symm
  refine ⟨⟨e.toEquiv.sumCongr (e.toEquiv.sigmaCongrLeft (β := fun x ↦ Fin (κ' x + 3))), ?_⟩⟩
  rintro (u | ⟨x, i⟩) (v | ⟨y, j⟩) <;> simp [Equiv.sigmaCongrLeft_apply, e.map_adj_iff]

/-- An isomorphism of the tagged graphs of triangle-free graphs restricts to a colour-preserving
isomorphism of the coloured graphs. -/
theorem exists_iso_of_iso_cliqueTag {H' : SimpleGraph V'} {κ' : V' → ℕ} (hH : H.CliqueFree 3)
    (hH' : H'.CliqueFree 3) (ψ : H.cliqueTag κ ≃g H'.cliqueTag κ') :
    ∃ e : H ≃g H', ∀ v, κ' (e v) = κ v := by
  have hR : ∀ w, (ψ w).isRight ↔ w.isRight := fun w ↦ by
    rw [← exists_isNClique_three_mem_cliqueTag_iff hH, ← ψ.exists_isNClique_mem_iff,
      exists_isNClique_three_mem_cliqueTag_iff hH']
  have hL : ∀ w, (ψ w).isLeft ↔ w.isLeft := fun w ↦ by
    simpa only [Sum.not_isRight] using (hR w).not
  have hL' : ∀ w, (ψ.symm w).isLeft ↔ w.isLeft := fun w ↦ by
    simpa using (hL (ψ.symm w)).symm
  let f : V ≃ V' :=
    { toFun v := (ψ (.inl v)).getLeft ((hL _).2 rfl)
      invFun v := (ψ.symm (.inl v)).getLeft ((hL' _).2 rfl)
      left_inv v := Sum.inl_injective (β := Σ x : V, Fin (κ x + 3)) (by simp)
      right_inv v := Sum.inl_injective (β := Σ x : V', Fin (κ' x + 3)) (by simp) }
  have hf : ∀ v, Sum.inl (f v) = ψ (.inl v) := fun v ↦ Sum.inl_getLeft _ _
  refine ⟨⟨f, fun {u v} ↦ ?_⟩, fun v ↦ ?_⟩
  · rw [← cliqueTag_adj_inl_inl (κ := κ'), hf, hf, ψ.map_adj_iff, cliqueTag_adj_inl_inl]
  · have h0 : ψ (.inr ⟨v, 0⟩) = .inr ⟨f v, 0⟩ := by
      rw [← cliqueTag_adj_inl_and_isRight_iff (H := H'), hf, ψ.map_adj_iff, hR]
      exact cliqueTag_adj_inl_and_isRight_iff.2 rfl
    have hc := ncard_setOf_cliqueTag_adj_inr_zero_and_isRight (H := H') (κ := κ') (f v)
    have hN : {w | (H.cliqueTag κ).Adj (.inr ⟨v, 0⟩) w ∧ w.isRight} ≃
        {w | (H'.cliqueTag κ').Adj (ψ (.inr ⟨v, 0⟩)) w ∧ w.isRight} :=
      ψ.toEquiv.subtypeEquiv fun w ↦ by simp [hR, ψ.map_adj_iff]
    rw [← h0, ← Nat.card_coe_set_eq, ← Nat.card_congr hN, Nat.card_coe_set_eq,
      ncard_setOf_cliqueTag_adj_inr_zero_and_isRight] at hc
    exact (Nat.add_right_cancel hc).symm

/-- **Clique tags.** Two triangle-free coloured graphs have isomorphic tagged graphs exactly when
there is a colour-preserving isomorphism between them. -/
theorem nonempty_iso_cliqueTag_iff {H' : SimpleGraph V'} {κ' : V' → ℕ} (hH : H.CliqueFree 3)
    (hH' : H'.CliqueFree 3) :
    Nonempty (H.cliqueTag κ ≃g H'.cliqueTag κ') ↔ ∃ e : H ≃g H', ∀ v, κ' (e v) = κ v :=
  ⟨fun ⟨ψ⟩ ↦ exists_iso_of_iso_cliqueTag hH hH' ψ,
    fun ⟨e, hκ⟩ ↦ nonempty_iso_cliqueTag_of_iso e hκ⟩

end SimpleGraph
