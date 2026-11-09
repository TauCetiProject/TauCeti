/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.CutTree
public import TauCeti.Combinatorics.Network.MinimumCut.Noncrossing
import Mathlib.Combinatorics.SimpleGraph.Star
import TauCeti.Data.Sym.Sym2

/-!
# Existence of Gomory–Hu cut trees

Every symmetric submodular set function `f` on a nonempty finite vertex type has a cut tree: a
weighted tree on the vertices in which the minimum cut value between any two distinct vertices is
the minimum weight on the tree path between them, and deleting any tree edge leaves a minimum cut
between its ends. Cut capacities of weighted graphs are the motivating instances, but only
symmetry, submodularity and finiteness are used.

The construction is the contraction-free form of the Gomory–Hu construction. It grows a set `R`
of representatives, keeping a tree on all vertices in which every vertex outside `R` is a leaf
attached to a representative, and every edge between representatives leaves a minimum cut between
its ends. To absorb a leaf `x` attached to `r`, the multi-cut non-crossing lemma supplies a
minimum `r`–`x` cut crossing none of the cuts of tree edges between representatives. Every branch
of the tree at `r` then lies on one side of this cut. The edge `s(r, x)` stays, and the branches on
the side of `x` are moved from `r` to `x`; by the ultrametric inequality, the moved edges still
leave minimum cuts. The sides of the new tree's edges are identified from which of its edges
cross a given set, so no walks need to be transported between the two trees. Once every vertex is
a representative, `TauCeti.TerminalCut.IsCutTree.of_isMinimum_edgeSide` gives the cut tree.

## Main results

* `TauCeti.TerminalCut.exists_isCutTree`: the Gomory–Hu theorem for symmetric submodular set
  functions.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551–570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143–155.
* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.
-/

public section

namespace TauCeti.TerminalCut

open Finset SimpleGraph

variable {V K : Type*}

section Construction

/-!
## One step of the construction

For a tree `T`, a leaf `x` attached to `r`, and the side `X` of a cut containing `x` but not `r`,
the graph `rewire T X r x` keeps the edges of `T` away from `r` and the edge `s(r, x)`, and
attaches every other neighbour `y` of `r` to `hub X r x y`, which is `x` when `y ∈ X` and `r`
otherwise.
-/

variable {T : SimpleGraph V} {X : Finset V} {r x y : V}

variable [DecidableEq V]

/-- The vertex to which the neighbour `y` of `r` is attached after the step: `x` when `y` lies on
the side `X` of `x`, and `r` otherwise. -/
private def hub (X : Finset V) (r x y : V) : V := if y ∈ X then x else r

private theorem hub_of_mem (h : y ∈ X) : hub X r x y = x := by simp [hub, h]

private theorem hub_of_notMem (h : y ∉ X) : hub X r x y = r := by simp [hub, h]

private theorem hub_eq_or (X : Finset V) (r x y : V) : hub X r x y = r ∨ hub X r x y = x := by
  by_cases h : y ∈ X
  exacts [.inr (hub_of_mem h), .inl (hub_of_notMem h)]

/-- The tree obtained from `T` by moving to `x` the edges `s(r, y)` with `y ∈ X`, `y ≠ x`. -/
private def rewire (T : SimpleGraph V) (X : Finset V) (r x : V) : SimpleGraph V :=
  .fromRel fun a b ↦ (T.Adj a b ∧ a ≠ r ∧ b ≠ r) ∨ (a = r ∧ b = x) ∨
    (T.Adj r b ∧ b ≠ x ∧ a = hub X r x b)

private theorem rewire_adj_cases {a b : V} (h : (rewire T X r x).Adj a b) :
    (T.Adj a b ∧ a ≠ r ∧ b ≠ r) ∨ s(a, b) = s(r, x) ∨
      ∃ y, T.Adj r y ∧ y ≠ x ∧ s(a, b) = s(y, hub X r x y) := by
  rw [rewire, fromRel_adj] at h
  obtain ⟨-, h | h⟩ := h
  · rcases h with h | ⟨rfl, rfl⟩ | ⟨hy, hyx, rfl⟩
    · exact .inl h
    · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨b, hy, hyx, Sym2.eq_swap⟩)
  · rcases h with ⟨h, hb, ha⟩ | ⟨rfl, rfl⟩ | ⟨hy, hyx, rfl⟩
    · exact .inl ⟨h.symm, ha, hb⟩
    · exact .inr (.inl Sym2.eq_swap)
    · exact .inr (.inr ⟨a, hy, hyx, rfl⟩)

private theorem rewire_adj_of_ne {a b : V} (h : T.Adj a b) (ha : a ≠ r) (hb : b ≠ r) :
    (rewire T X r x).Adj a b := by
  rw [rewire, fromRel_adj]
  exact ⟨h.ne, .inl (.inl ⟨h, ha, hb⟩)⟩

private theorem rewire_adj_self_left (hrx : r ≠ x) : (rewire T X r x).Adj r x := by
  rw [rewire, fromRel_adj]
  exact ⟨hrx, .inl (.inr (.inl ⟨rfl, rfl⟩))⟩

private theorem rewire_adj_hub (hy : T.Adj r y) (hyx : y ≠ x) :
    (rewire T X r x).Adj y (hub X r x y) := by
  rw [rewire, fromRel_adj]
  refine ⟨?_, .inr (.inr (.inr ⟨hy, hyx, rfl⟩))⟩
  rcases hub_eq_or X r x y with h | h <;> rw [h]
  exacts [hy.ne.symm, hyx]

private theorem connected_rewire (hT : T.Connected) (hrx : r ≠ x) : (rewire T X r x).Connected := by
  have hreach {y : V} (hy : T.Adj r y) : (rewire T X r x).Reachable r y := by
    obtain rfl | hyx := eq_or_ne y x
    · exact (rewire_adj_self_left hrx).reachable
    have h := (rewire_adj_hub (X := X) hy hyx).reachable.symm
    rcases hub_eq_or X r x y with h' | h' <;> rw [h'] at h
    exacts [h, (rewire_adj_self_left hrx).reachable.trans h]
  have hadj {a b : V} (hab : T.Adj a b) : (rewire T X r x).Reachable a b := by
    by_cases ha : a = r
    · rw [ha] at hab ⊢
      exact hreach hab
    by_cases hb : b = r
    · rw [hb] at hab ⊢
      exact (hreach hab.symm).symm
    exact (rewire_adj_of_ne hab ha hb).reachable
  have := hT.nonempty
  refine ⟨fun u v ↦ ?_⟩
  induction (reachable_iff_reflTransGen u v).mp (hT.preconnected u v) with
  | refl => rfl
  | tail _ hab ih => exact ih.trans (hadj hab)

/-- A leaf of `T` other than `r` and `x` stays a leaf: it keeps its neighbour `c` unless `c = r`,
in which case it is attached to its hub. -/
private theorem exists_rewire_adj_iff_of_leaf {v c : V} (hvr : v ≠ r) (hvx : v ≠ x)
    (hc : ∀ y, T.Adj v y ↔ y = c) :
    ∃ c', (c' = c ∨ c' = r ∨ c' = x) ∧ ∀ y, (rewire T X r x).Adj v y ↔ y = c' := by
  have hnot {y y' : V} (h : s(v, y) = s(r, x) ∨ v = hub X r x y') : False := by
    rcases h with h | h
    · rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      exacts [hvr h, hvx h]
    · rcases hub_eq_or X r x y' with h' | h' <;> rw [h'] at h
      exacts [hvr h, hvx h]
  by_cases hcr : c = r
  · subst hcr
    refine ⟨hub X c x v, (hub_eq_or X c x v).elim .inl fun h ↦ .inr (.inr h), fun y ↦
      ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩⟩
    · rcases rewire_adj_cases hy with ⟨hy, -, hyc⟩ | h | ⟨y', -, -, h⟩
      · exact absurd ((hc y).mp hy) hyc
      · exact (hnot (y' := v) (.inl h)).elim
      · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨h, -⟩
        · rfl
        · exact (hnot (y := y) (.inr h)).elim
    · rw [hy]
      exact rewire_adj_hub ((hc c).mpr rfl).symm hvx
  · refine ⟨c, .inl rfl, fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩⟩
    · rcases rewire_adj_cases hy with ⟨hy, -, -⟩ | h | ⟨y', hy', -, h⟩
      · exact (hc y).mp hy
      · exact (hnot (y' := v) (.inl h)).elim
      · rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨h, -⟩
        · exact absurd ((hc r).mp hy'.symm).symm hcr
        · exact (hnot (y := y) (.inr h)).elim
    · rw [hy]
      exact rewire_adj_of_ne ((hc c).mpr rfl) hvr hcr

variable [Fintype V] (hT : T.IsTree) (hx : ∀ y, T.Adj x y ↔ y = r)
include hT hx

/-- Both `r` and `x`, and hence every hub, lie off the side of another neighbour `y` of `r`. -/
private theorem hub_notMem_edgeSide (hy : T.Adj r y) (hyx : y ≠ x) (z : V) :
    hub X r x z ∉ T.edgeSide y r := by
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hy.symm
  rcases hub_eq_or X r x z with h | h <;> rw [h]
  exacts [hbr.notMem_edgeSide, hbr.notMem_edgeSide_of_adj ((hx r).mpr rfl).symm hyx.symm]

/-- An edge of `T` away from `r` keeps its sides. -/
private theorem edgeSide_rewire_of_ne {a b : V} (hab : T.Adj a b) (ha : a ≠ r) (hb : b ≠ r) :
    (rewire T X r x).edgeSide a b = T.edgeSide a b := by
  have hxr : T.Adj x r := (hx r).mpr rfl
  have hne {y : V} : s(y, r) ≠ s(a, b) :=
    Sym2.ne_of_mem_notMem (Sym2.mem_mk_right y r) <| by
      simpa only [Sym2.mem_iff, not_or] using ⟨ha.symm, hb.symm⟩
  have hrx : r ∈ T.edgeSide a b ↔ x ∈ T.edgeSide a b := (hxr.mem_edgeSide_iff hne).symm
  refine edgeSide_eq_of_forall_adj (connected_rewire hT.connected hxr.ne.symm).preconnected
    (self_mem_edgeSide T a b)
    ((isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hab).notMem_edgeSide)
    fun c d hcd hcd' ↦ ?_
  rcases rewire_adj_cases hcd with ⟨hcd, -, -⟩ | h | ⟨y, hy, -, h⟩
  · exact hcd.mem_edgeSide_iff hcd'
  · exact (Sym2.iff_iff_of_mk_eq h).mpr hrx
  · refine (Sym2.iff_iff_of_mk_eq h).mpr ?_
    have hyr : y ∈ T.edgeSide a b ↔ r ∈ T.edgeSide a b := hy.symm.mem_edgeSide_iff hne
    rcases hub_eq_or X r x y with h' | h' <;> rw [h']
    exacts [hyr, hyr.trans hrx]

/-- After the step, the side of `y` for its edge to `hub X r x y` is its side in `T` for the edge
`s(y, r)`. -/
private theorem edgeSide_rewire_hub (hy : T.Adj r y) (hyx : y ≠ x) :
    (rewire T X r x).edgeSide y (hub X r x y) = T.edgeSide y r := by
  have hxr : T.Adj x r := (hx r).mpr rfl
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hy.symm
  have hhub := hub_notMem_edgeSide (X := X) hT hx hy hyx
  have hrS : r ∉ T.edgeSide y r := hbr.notMem_edgeSide
  have hxS : x ∉ T.edgeSide y r := hbr.notMem_edgeSide_of_adj hxr.symm hyx.symm
  refine edgeSide_eq_of_forall_adj (connected_rewire hT.connected hxr.ne.symm).preconnected
    (self_mem_edgeSide T y r) (hhub y) fun c d hcd hcd' ↦ ?_
  rcases rewire_adj_cases hcd with ⟨hcd, hc, hd⟩ | h | ⟨y', hy', -, h⟩
  · exact hcd.mem_edgeSide_iff_of_ne hc hd
  · exact (Sym2.iff_iff_of_mk_eq h).mpr ⟨fun h ↦ absurd h hrS, fun h ↦ absurd h hxS⟩
  · refine (Sym2.iff_iff_of_mk_eq h).mpr
      ⟨fun h' ↦ absurd h' ?_, fun h' ↦ absurd h' (hhub y')⟩
    exact hbr.notMem_edgeSide_of_adj hy' fun h' ↦ hcd' (h' ▸ h)

/-- If every branch of `T` at `r` lies on one side of `X`, then after the step the side of `x`
for the edge `s(x, r)` is `X`. -/
private theorem edgeSide_rewire_self (hxX : x ∈ X) (hrX : r ∉ X)
    (hbranch : ∀ ⦃y⦄, T.Adj r y → ∀ z ∈ T.edgeSide y r, (z ∈ X ↔ y ∈ X)) :
    (rewire T X r x).edgeSide x r = X := by
  have hxr : T.Adj x r := (hx r).mpr rfl
  refine edgeSide_eq_of_forall_adj (connected_rewire hT.connected hxr.ne.symm).preconnected hxX hrX
    fun c d hcd hcd' ↦ ?_
  rcases rewire_adj_cases hcd with ⟨hcd, hc, hd⟩ | h | ⟨y, -, -, h⟩
  · -- An edge away from `r` lies inside a single branch at `r`.
    obtain ⟨y, hy, hcy⟩ := (hT.connected.preconnected r c).exists_adj_mem_edgeSide hc
    have hdy : d ∈ T.edgeSide y r := (hcd.mem_edgeSide_iff_of_ne hc hd).mp hcy
    exact (hbranch hy c hcy).trans (hbranch hy d hdy).symm
  · exact absurd (h.trans Sym2.eq_swap) hcd'
  · refine (Sym2.iff_iff_of_mk_eq h).mpr ?_
    by_cases hyX : y ∈ X
    · rw [hub_of_mem hyX]
      exact iff_of_true hyX hxX
    · rw [hub_of_notMem hyX]
      exact iff_of_false hyX hrX

/-- If every branch of `T` at `r` lies on one side of `X`, the step produces a tree. -/
private theorem isTree_rewire (hxX : x ∈ X) (hrX : r ∉ X)
    (hbranch : ∀ ⦃y⦄, T.Adj r y → ∀ z ∈ T.edgeSide y r, (z ∈ X ↔ y ∈ X)) :
    (rewire T X r x).IsTree := by
  have hrx : r ≠ x := ((hx r).mpr rfl).ne.symm
  refine ⟨connected_rewire hT.connected hrx, isAcyclic_iff_forall_adj_isBridge.mpr ?_⟩
  intro a b hab
  rw [← notMem_edgeSide_iff]
  rcases rewire_adj_cases hab with ⟨hab, ha, hb⟩ | h | ⟨y, hy, hyx, h⟩
  · rw [edgeSide_rewire_of_ne hT hx hab ha hb]
    exact (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hab).notMem_edgeSide
  · rw [notMem_edgeSide_iff, h, Sym2.eq_swap, ← notMem_edgeSide_iff,
      edgeSide_rewire_self hT hx hxX hrX hbranch]
    exact hrX
  · rw [notMem_edgeSide_iff, h, ← notMem_edgeSide_iff, edgeSide_rewire_hub hT hx hy hyx]
    exact hub_notMem_edgeSide hT hx hy hyx y

end Construction

/-!
## The invariant and the induction
-/

variable [Fintype V]

/-- The invariant of the construction for a set `R` of representatives: `T` is a tree on all
vertices, every vertex outside `R` is a leaf attached to a representative, and every edge between
representatives leaves a minimum cut between its ends. -/
private structure IsPartialCutTree [Preorder K] (f : Finset V → K) (R : Finset V)
    (T : SimpleGraph V) : Prop where
  isTree : T.IsTree
  exists_adj_iff : ∀ v ∉ R, ∃ c ∈ R, ∀ y, T.Adj v y ↔ y = c
  isMinimum : ∀ ⦃u v : V⦄, u ∈ R → v ∈ R → T.Adj u v → IsMinimum f {u} {v} (T.edgeSide u v)

/-- If a cut side `Y` containing the leaf `x` attached to `r`, but not `r` itself, crosses no cut
of an edge between representatives, then every branch of the tree at `r` lies on one side of
`Y`. -/
private theorem IsPartialCutTree.mem_iff_of_mem_edgeSide [Preorder K] {f : Finset V → K}
    {R Y : Finset V} {T : SimpleGraph V} (hP : IsPartialCutTree f R T) {r x y z : V}
    (hrR : r ∈ R) (hxR : x ∉ R) (hx : ∀ y, T.Adj x y ↔ y = r) (hxY : x ∈ Y) (hrY : r ∉ Y)
    (hY : ∀ ⦃u v⦄, u ∈ R → v ∈ R → T.Adj u v → ¬Y.Crosses (T.edgeSide u v)) (hy : T.Adj r y)
    (hz : z ∈ T.edgeSide y r) : z ∈ Y ↔ y ∈ Y := by
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hP.isTree.isAcyclic hy.symm
  have hyS := self_mem_edgeSide T y r
  by_cases hyR : y ∈ R
  · rcases nestedOrDisjoint_def.mp ((not_crosses_iff_nestedOrDisjoint hrY hbr.notMem_edgeSide).mp
        (hY hyR hrR hy.symm)) with h | h | h
    · exact absurd (h hxY) (hbr.notMem_edgeSide_of_adj ((hx r).mpr rfl).symm
        fun h ↦ hxR (h ▸ hyR))
    · exact ⟨fun _ ↦ h hyS, fun _ ↦ h hz⟩
    · exact ⟨fun h' ↦ absurd hz (disjoint_left.mp h h'),
        fun h' ↦ absurd hyS (disjoint_left.mp h h')⟩
  · -- A branch at a leaf is the leaf alone.
    obtain ⟨c, -, hc⟩ := hP.exists_adj_iff y hyR
    have hcr : r = c := (hc r).mp hy.symm
    rw [edgeSide_eq_singleton fun y' hy' ↦ ((hc y').mp hy').trans hcr.symm] at hz
    rw [mem_singleton.mp hz]

variable [DecidableEq V] [AddCommMonoid K] [LinearOrder K] [IsOrderedCancelAddMonoid K]
  {f : Finset V → K}

/-- A partial cut tree has a minimum cut between a representative `r` and a new leaf `x` attached
to `r` that crosses no cut of an edge between representatives. -/
private theorem IsPartialCutTree.exists_isMinimum_not_crosses (hf : IsSymmSubmodular f)
    {R : Finset V} {T : SimpleGraph V} (hP : IsPartialCutTree f R T) {r x : V} (hxR : x ∉ R)
    (hxr : T.Adj x r) :
    ∃ X, IsMinimum f {r} {x} X ∧
      ∀ ⦃u v : V⦄, u ∈ R → v ∈ R → T.Adj u v → ¬X.Crosses (T.edgeSide u v) := by
  obtain ⟨X, hX, hXcross⟩ := exists_isMinimum_forall_not_crosses hf
    (𝒞 := {S | ∃ u v, u ∈ R ∧ v ∈ R ∧ T.Adj u v ∧ T.edgeSide u v = S})
    (by
      rintro _ ⟨a, b, -, -, hab, rfl⟩ _ ⟨c, d, -, -, hcd, rfl⟩ -
      exact hP.isTree.not_crosses_edgeSide hab hcd)
    (fun _ ⟨a, b, ha, hb, hab, h⟩ ↦ ⟨a, b, h ▸ hP.isMinimum ha hb hab⟩) hxr.ne.symm
    (by
      rintro _ ⟨u, v, hu, hv, -, rfl⟩
      refine hxr.symm.mem_edgeSide_iff <|
        Sym2.ne_of_mem_notMem (Sym2.mem_mk_right r x) ?_
      simpa only [Sym2.mem_iff, not_or] using
        ⟨fun h ↦ hxR (h ▸ hu), fun h ↦ hxR (h ▸ hv)⟩)
  exact ⟨X, hX, fun u v hu hv huv ↦ hXcross _ ⟨u, v, hu, hv, huv, rfl⟩⟩

omit [IsOrderedCancelAddMonoid K] in
/-- A branch at `r` that leaves a minimum cut keeps leaving one after the cut `X` between `r` and
the new leaf `x` moves it to the hub `hub Xᶜ r x y`. -/
private theorem IsPartialCutTree.isMinimum_edgeSide_hub (hf : IsSymmSubmodular f)
    {R : Finset V} {T : SimpleGraph V} (hP : IsPartialCutTree f R T) {r x y : V} {X : Finset V}
    (hrR : r ∈ R) (hxR : x ∉ R) (hxr : T.Adj x r) (hX : IsMinimum f {r} {x} X)
    (hy : T.Adj r y) (hyR : y ∈ R) :
    IsMinimum f {y} {hub Xᶜ r x y} (T.edgeSide y r) := by
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hP.isTree.isAcyclic
  have hSy := hP.isMinimum hyR hrR hy.symm
  by_cases hyX : y ∈ Xᶜ
  · rw [hub_of_mem hyX]
    exact hSy.reattach hf.symm hX (by simpa using hyX)
      ((hbr hy.symm).notMem_edgeSide_of_adj hxr.symm fun h ↦ hxR (h ▸ hyR))
  · rw [hub_of_notMem hyX]
    exact hSy

omit [AddCommMonoid K] [LinearOrder K] [IsOrderedCancelAddMonoid K] in
/-- After rewiring, a leaf `v` outside `insert x R` is still attached to a single representative. -/
private theorem IsPartialCutTree.exists_mem_insert_rewire_adj_iff [Preorder K] {f : Finset V → K}
    {R : Finset V} {T : SimpleGraph V} (hP : IsPartialCutTree f R T) {r x v : V} {X : Finset V}
    (hrR : r ∈ R) (hv : v ∉ insert x R) :
    ∃ c ∈ insert x R, ∀ y, (rewire T X r x).Adj v y ↔ y = c := by
  obtain ⟨hvx, hvR⟩ := not_or.mp (mt mem_insert.mpr hv)
  obtain ⟨c, hcR, hc⟩ := hP.exists_adj_iff v hvR
  obtain ⟨c', hc', hc'adj⟩ :=
    exists_rewire_adj_iff_of_leaf (X := X) (fun h : v = r ↦ hvR (h ▸ hrR)) hvx hc
  refine ⟨c', ?_, hc'adj⟩
  rcases hc' with rfl | rfl | rfl
  exacts [mem_insert_of_mem hcR, mem_insert_of_mem hrR, mem_insert_self _ R]

/-- One step of the construction: a partial cut tree absorbs any vertex outside its
representatives. -/
private theorem IsPartialCutTree.exists_insert (hf : IsSymmSubmodular f)
    {R : Finset V} {T : SimpleGraph V} (hP : IsPartialCutTree f R T) {x : V} (hxR : x ∉ R) :
    ∃ T', IsPartialCutTree f (insert x R) T' := by
  obtain ⟨r, hrR, hx⟩ := hP.exists_adj_iff x hxR
  have hT := hP.isTree
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic
  have hxr : T.Adj x r := (hx r).mpr rfl
  have hrx : r ≠ x := hxr.ne.symm
  -- Choose a minimum `r`–`x` cut `X` crossing none of the cuts of edges between representatives.
  obtain ⟨X, hX, hXcross⟩ := hP.exists_isMinimum_not_crosses hf hxR hxr
  obtain ⟨hrX, hxX⟩ := isAdmissible_singleton.mp hX.admissible
  have hrX' : r ∉ Xᶜ := by simpa using hrX
  have hxX' : x ∈ Xᶜ := mem_compl.mpr hxX
  -- Every branch of `T` at `r` lies on one side of the cut.
  have hbranch ⦃y : V⦄ (hy : T.Adj r y) (z : V) (hz : z ∈ T.edgeSide y r) :
      z ∈ Xᶜ ↔ y ∈ Xᶜ :=
    hP.mem_iff_of_mem_edgeSide hrR hxR hx hxX' hrX'
      (fun u v hu hv huv ↦ crosses_compl_left.not.mpr (hXcross hu hv huv)) hy hz
  let T' := rewire T Xᶜ r x
  have hside₁ {a b : V} (hab : T.Adj a b) (ha : a ≠ r) (hb : b ≠ r) :
      T'.edgeSide a b = T.edgeSide a b :=
    edgeSide_rewire_of_ne hT hx hab ha hb
  have hside₂ : T'.edgeSide x r = Xᶜ := edgeSide_rewire_self hT hx hxX' hrX' hbranch
  have hside₃ {y : V} (hy : T.Adj r y) (hyx : y ≠ x) :
      T'.edgeSide y (hub Xᶜ r x y) = T.edgeSide y r :=
    edgeSide_rewire_hub hT hx hy hyx
  have hT' : T'.IsTree := isTree_rewire hT hx hxX' hrX' hbranch
  have hcompl {a b : V} (h : T'.Adj a b) : T'.edgeSide b a = (T'.edgeSide a b)ᶜ :=
    ((isAcyclic_iff_forall_adj_isBridge.mp hT'.isAcyclic h).compl_edgeSide
      hT'.connected.preconnected).symm
  refine ⟨T', hT', fun v hv ↦ ?_, fun u v hu hv huv ↦ ?_⟩
  · exact hP.exists_mem_insert_rewire_adj_iff hrR hv
  · -- Every edge between representatives leaves a minimum cut.
    have hcompl_min {a b : V} (h : T'.Adj a b) (hm : IsMinimum f {a} {b} (T'.edgeSide a b)) :
        IsMinimum f {b} {a} (T'.edgeSide b a) := by
      rw [hcompl h]
      exact hm.compl hf.symm
    rcases rewire_adj_cases huv with ⟨huv', hur, hvr⟩ | h | ⟨y, hy, hyx, h⟩
    · have hux : u ≠ x := fun h ↦ hvr ((hx v).mp (h ▸ huv'))
      have hvx : v ≠ x := fun h ↦ hur ((hx u).mp (h ▸ huv'.symm))
      rw [hside₁ huv' hur hvr]
      exact hP.isMinimum ((mem_insert.mp hu).resolve_left hux)
        ((mem_insert.mp hv).resolve_left hvx) huv'
    · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hcompl (rewire_adj_self_left hrx).symm, hside₂, compl_compl]
        exact hX
      · rw [hside₂]
        exact hX.compl hf.symm
    · have hm (hyR : y ∈ insert x R) :
          IsMinimum f {y} {hub Xᶜ r x y} (T'.edgeSide y (hub Xᶜ r x y)) := by
        rw [hside₃ hy hyx]
        exact hP.isMinimum_edgeSide_hub hf hrR hxR hxr hX hy ((mem_insert.mp hyR).resolve_left hyx)
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hm hu
      · exact hcompl_min (rewire_adj_hub hy hyx) (hm hv)

/-- **Gomory–Hu theorem.** Every symmetric submodular set function on a nonempty finite vertex
type has a cut tree: a weighted tree on the vertices in which the minimum cut value between any
two distinct vertices is the minimum weight on the tree path between them, and deleting any tree
edge leaves a minimum cut between its ends. -/
theorem exists_isCutTree [Nonempty V] (hf : IsSymmSubmodular f) :
    ∃ (T : SimpleGraph V) (w : Sym2 V → K), IsCutTree f T w := by
  classical
  obtain ⟨r⟩ := ‹Nonempty V›
  -- Start from the star at `r`, with `r` the only representative.
  have hinit : IsPartialCutTree f {r} (starGraph r) := by
    refine ⟨isTree_starGraph r, fun v hv ↦ ⟨r, mem_singleton_self r, fun y ↦ ?_⟩, ?_⟩
    · have hvr : v ≠ r := by simpa using hv
      simp only [starGraph_adj]
      exact ⟨fun ⟨_, h⟩ ↦ h.resolve_left hvr, fun h ↦ ⟨h ▸ hvr, .inr h⟩⟩
    · intro u v hu hv huv
      simp only [mem_singleton] at hu hv
      subst hu hv
      exact absurd huv (SimpleGraph.irrefl _)
  -- A largest set of representatives admitting a partial cut tree contains every vertex.
  obtain ⟨R, hR, hmax⟩ := exists_max_image ({R | ∃ T, IsPartialCutTree f R T} : Finset (Finset V))
    card ⟨{r}, by simpa using ⟨_, hinit⟩⟩
  obtain ⟨T, hT⟩ : ∃ T, IsPartialCutTree f R T := by simpa using hR
  have hRuniv : R = univ := eq_univ_iff_forall.mpr fun x ↦ by_contra fun hx ↦ by
    obtain ⟨T', hT'⟩ := hT.exists_insert hf hx
    have := hmax (insert x R) (by simpa using ⟨T', hT'⟩)
    rw [card_insert_of_notMem hx] at this
    omega
  subst hRuniv
  exact ⟨T, Sym2.lift ⟨pairMinimumValue f, pairMinimumValue_comm hf.symm⟩,
    .of_isMinimum_edgeSide hT.isTree (fun u v h ↦ hT.isMinimum (mem_univ u) (mem_univ v) h)
      fun u v _ ↦ by simp⟩

end TauCeti.TerminalCut
