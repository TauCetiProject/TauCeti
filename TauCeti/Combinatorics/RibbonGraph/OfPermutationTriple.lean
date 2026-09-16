/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.RibbonGraph.Basic
public import TauCeti.GroupTheory.Perm.Basic

/-!
# The bipartite ribbon graph of a permutation triple

A degree-`n` permutation triple and a finite bipartite ribbon graph carry the same information,
and this file builds the graph out of the triple. The edges are the `n` sheets, the black
vertices are the cycles of `σ0` and the white ones the cycles of `σ1` — fixed points included,
so every sheet has exactly one end of each colour — and the cyclic order of the edges around a
vertex is the cycle of the corresponding component through them. For a connected triple the
result is a dessin d'enfants; disconnected triples give disconnected graphs, and
`TauCeti.PermutationTriple.isConnected_ribbonGraph` is the equivalence.

* `TauCeti.PermutationTriple.ribbonGraph`: the construction.
* `TauCeti.PermutationTriple.facePerm_ribbonGraph`: the face permutation of the graph is the
  third component `σinf` of the triple, so the faces of the graph are the cycles of `σinf`.
* `TauCeti.PermutationTriple.isConnected_ribbonGraph`: the graph is connected exactly when the
  triple is, the rotation group of the graph being the monodromy group of the triple.
* `TauCeti.PermutationTriple.eulerChar_ribbonGraph`: the Euler characteristic of the graph,
  counted as `|B| + |W| - |E| + |F|`, is the Euler characteristic of the triple, counted as the
  total number of cycles of the three components less the degree. The two counts agree because
  the black vertices, the white vertices and the faces are precisely the cycles of `σ0`, of `σ1`
  and of `σinf`.

## Implementation notes

The construction is `@[expose]`d. Its edge, black-vertex and white-vertex types are structure
fields of `TauCeti.BipartiteRibbonGraph`, so a consumer cannot so much as state that an edge of
`t.ribbonGraph` is a sheet of `t` without reducing those fields; the lemmas below then read off
the remaining fields.

The black and white vertex types are quotients of `Fin n`, whose `Fintype` and `DecidableEq`
instances are taken classically. The executable cycle decomposition that would make them
computable is a separate matter, and no result here needs it.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

open Equiv Equiv.Perm

-- The carrier vocabulary below follows the formal prototype `Suggested.lean` of the Tau Ceti
-- `BelyiMaps` roadmap.

public section

namespace TauCeti

namespace PermutationTriple

variable {n : ℕ} (t : PermutationTriple n)

/-- The finite bipartite ribbon graph of a permutation triple: its edges are the sheets, its
black and white vertices are the cycles of `σ0` and of `σ1`, and the cyclic orders around them
are `σ0` and `σ1` themselves. For a connected triple this is the dessin d'enfants of the
associated three-point cover. -/
@[expose] noncomputable def ribbonGraph : BipartiteRibbonGraph where
  E := Fin n
  B := Quotient (SameCycle.setoid t.σ0)
  W := Quotient (SameCycle.setoid t.σ1)
  fintypeE := inferInstance
  fintypeB := Fintype.ofFinite _
  fintypeW := Fintype.ofFinite _
  decidableEqE := inferInstance
  decidableEqB := Classical.decEq _
  decidableEqW := Classical.decEq _
  blackEnd := Quotient.mk (SameCycle.setoid t.σ0)
  whiteEnd := Quotient.mk (SameCycle.setoid t.σ1)
  rotB := t.σ0
  rotW := t.σ1
  blackEnd_surjective := Quotient.mk_surjective
  whiteEnd_surjective := Quotient.mk_surjective
  isCycleOn_rotB := Equiv.Perm.isCycleOn_preimage_quotientMk t.σ0
  isCycleOn_rotW := Equiv.Perm.isCycleOn_preimage_quotientMk t.σ1

/-- The cyclic order of the sheets around a black vertex is `σ0`. -/
@[simp] theorem rotB_ribbonGraph : t.ribbonGraph.rotB = t.σ0 := (rfl)

/-- The cyclic order of the sheets around a white vertex is `σ1`. -/
@[simp] theorem rotW_ribbonGraph : t.ribbonGraph.rotW = t.σ1 := (rfl)

/-- The black end of a sheet is its cycle under `σ0`. -/
@[simp] theorem blackEnd_ribbonGraph (i : Fin n) :
    t.ribbonGraph.blackEnd i = Quotient.mk (SameCycle.setoid t.σ0) i := (rfl)

/-- The white end of a sheet is its cycle under `σ1`. -/
@[simp] theorem whiteEnd_ribbonGraph (i : Fin n) :
    t.ribbonGraph.whiteEnd i = Quotient.mk (SameCycle.setoid t.σ1) i := (rfl)

-- After the rewrites, the remaining goal mentions `t.ribbonGraph.E` where the cited lemma
-- mentions `Fin n`, so `exact` closes it on the reduction `@[expose]` supplies; the same holds
-- for the `rfl` ending the next proof.
/-- The faces of the graph are the cycles of the third component: the face permutation is `σinf`
on the nose, the product-one convention of a triple being that of a ribbon graph. -/
@[simp] theorem facePerm_ribbonGraph : t.ribbonGraph.facePerm = t.σinf := by
  rw [BipartiteRibbonGraph.facePerm_def, rotB_ribbonGraph, rotW_ribbonGraph]
  exact t.σinf_eq_inv.symm

/-- The rotation group of the graph is the monodromy group of the triple. -/
@[simp] theorem rotationGroup_ribbonGraph :
    t.ribbonGraph.rotationGroup = t.monodromyGroup := by
  rw [← BipartiteRibbonGraph.closure_pair_eq_rotationGroup, ← closure_pair_eq_monodromyGroup,
    rotB_ribbonGraph, rotW_ribbonGraph]
  rfl

-- Not `@[simp]`: `BipartiteRibbonGraph.isConnected_iff_card_connectedComponent_eq_one` already
-- rewrites the left-hand side, so this statement is not in simp normal form.
/-- The graph of a triple is connected exactly when the triple is. -/
theorem isConnected_ribbonGraph : t.ribbonGraph.IsConnected ↔ t.IsConnected := by
  rw [BipartiteRibbonGraph.isConnected_def, isConnected_iff, rotationGroup_ribbonGraph]
  exact and_congr (Fin.pos_iff_nonempty.symm.trans Nat.pos_iff_ne_zero) Iff.rfl

/-! ### Relabeling -/

/-- Relabeling the sheets by `τ` is an isomorphism from the ribbon graph of a triple onto the
ribbon graph of the relabeled triple. Isomorphic triples therefore have isomorphic graphs, so
the construction descends to isomorphism classes. -/
def ribbonGraphIsoSmul (τ : Perm (Fin n)) : t.ribbonGraph.Iso (τ • t).ribbonGraph where
  edge := τ
  black := Quotient.congr τ fun i j => by
    have h : t.σ0.SameCycle i j ↔ (τ * t.σ0 * τ⁻¹).SameCycle (τ i) (τ j) := by
      simp [sameCycle_conj]
    exact h
  white := Quotient.congr τ fun i j => by
    have h : t.σ1.SameCycle i j ↔ (τ * t.σ1 * τ⁻¹).SameCycle (τ i) (τ j) := by
      simp [sameCycle_conj]
    exact h
  map_blackEnd _ := (rfl)
  map_whiteEnd _ := (rfl)
  map_rotB := Equiv.semiconj_conj τ t.σ0
  map_rotW := Equiv.semiconj_conj τ t.σ1

@[simp] theorem ribbonGraphIsoSmul_edge_apply (τ : Perm (Fin n)) (i : Fin n) :
    (t.ribbonGraphIsoSmul τ).edge i = τ i := (rfl)

/-! ### Counting cells -/

/-- The edges of the graph are the sheets of the triple. -/
@[simp] theorem card_E_ribbonGraph : Fintype.card t.ribbonGraph.E = n :=
  Fintype.card_fin n

-- The counting proofs here also end with `exact`: the vertex and face types of `t.ribbonGraph`
-- reduce to the orbit quotients that `TauCeti.orbitCount_def` counts.
/-- The black vertices of the graph are the cycles of `σ0`, fixed points included. -/
@[simp] theorem card_B_ribbonGraph : Fintype.card t.ribbonGraph.B = orbitCount t.σ0 := by
  rw [← Nat.card_eq_fintype_card]
  exact (orbitCount_def t.σ0).symm

/-- The white vertices of the graph are the cycles of `σ1`, fixed points included. -/
@[simp] theorem card_W_ribbonGraph : Fintype.card t.ribbonGraph.W = orbitCount t.σ1 := by
  rw [← Nat.card_eq_fintype_card]
  exact (orbitCount_def t.σ1).symm

/-- The faces of the graph are the cycles of `σinf`, fixed points included. -/
@[simp] theorem faceCount_ribbonGraph : t.ribbonGraph.faceCount = orbitCount t.σinf := by
  rw [BipartiteRibbonGraph.faceCount_def, ← Nat.card_eq_fintype_card, ← facePerm_ribbonGraph]
  exact (orbitCount_def _).symm

/-- The Euler characteristic of the graph is the Euler characteristic of the triple: the two
counts agree cell by cell. -/
@[simp] theorem eulerChar_ribbonGraph : t.ribbonGraph.eulerChar = t.eulerChar := by
  rw [BipartiteRibbonGraph.eulerChar_def, eulerChar_def, card_B_ribbonGraph, card_W_ribbonGraph,
    faceCount_ribbonGraph, card_E_ribbonGraph]

end PermutationTriple

end TauCeti
