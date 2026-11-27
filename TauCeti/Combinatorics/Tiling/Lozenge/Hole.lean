/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Cochain
public import TauCeti.Combinatorics.Tiling.Lozenge.HexGraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.BigOperators.Fin

/-!
# Holes obstruct simple connectivity

If `Q` is a nonempty finite set of faces outside a region `R` such that every face sharing an
edge with a face of `Q` lies in `Q ∪ R`, then `R` is not simply connected. The witness is the
cochain dual to a path of faces from a face `q₀ ∈ Q` to infinity, the ray of faces to the right of
`q₀`: it sums to zero round every face other than `q₀` and to `±1` round `q₀`. If it had a
primitive on `R`, subtracting the coboundary of that primitive would give a cochain vanishing on the
edges of `R` with the same sums round faces; the signed sum of these over the faces of `Q`
telescopes to a sum over the boundary edges of `Q`, all of which are edges of `R`, so it vanishes,
while it is `±1`.

Consequently the complement of a simply connected region is connected through shared edges when
the region is finite: every component of the faces outside `R` is infinite, since a finite one
would be a hole, and for finite `R` the faces far from `R` all lie in one component, the only
infinite one.

## Main definitions

* `TauCeti.rayCochain q`: the cochain dual to the ray of faces to the right of the face `q`.

## Main statements

* `TauCeti.sum_faceSign_mul_faceSum_eq_zero`: the signed sum of the face sums of a cochain over a
  finite set `Q` of faces vanishes when the cochain vanishes on the edges with exactly one face in
  `Q`.
* `TauCeti.faceSum_rayCochain_of_ne`, `TauCeti.faceSign_mul_faceSum_rayCochain_self`: the ray
  cochain of `q` sums to zero round every face other than `q`, and its circulation round `q` is
  `1`.
* `TauCeti.not_isSimplyConnectedRegion_of_hole`: a region with a hole is not simply connected.
* `TauCeti.IsSimplyConnectedRegion.infinite_supp`: every component of the graph of faces outside a
  simply connected region is infinite.
* `TauCeti.existsUnique_infinite_supp_of_finite`: for finite `R`, the graph of faces outside `R` has
  exactly one infinite component.
* `TauCeti.IsSimplyConnectedRegion.connected_induce_compl`: for finite simply connected `R`, the
  faces outside `R` are connected through shared edges.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
-/

public section

namespace TauCeti

variable {R : Set TriFace} {f : TriFace}

/-! ### Discrete Stokes -/

/-- **Discrete Stokes formula.** If a cochain `d` vanishes on every edge of a face of a finite set
`Q` whose face across it is not in `Q`, then the signed sum of the face sums of `d` over `Q`
vanishes: each edge with both faces in `Q` is counted once in each direction. -/
theorem sum_faceSign_mul_faceSum_eq_zero (Q : Finset TriFace) (d : TriEdge → ℤ)
    (hd : ∀ q ∈ Q, ∀ k, q.across k ∉ Q → d (q.edge k) = 0) :
    ∑ q ∈ Q, faceSign q * faceSum d q = 0 := by
  classical
  let s : Fin 3 → ℤ := ![1, 1, -1]
  have hsum : ∀ q, faceSign q * faceSum d q = ∑ k : Fin 3, faceSign q * s k * d (q.edge k) := by
    intro q
    simp only [faceSum_def, Fin.sum_univ_three, s, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hsum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution
    (fun a _ => if a.1.across a.2 ∈ Q then (a.1.across a.2, a.2) else a) ?_ ?_ ?_ ?_
  · rintro ⟨q, k⟩ ha
    have hq : q ∈ Q := (Finset.mem_product.1 ha).1
    dsimp only
    split_ifs with h
    · rw [faceSign_across, TriFace.edge_across]
      ring
    · rw [hd q hq k h]
      ring
  · rintro ⟨q, k⟩ ha hne
    have hq : q ∈ Q := (Finset.mem_product.1 ha).1
    dsimp only
    split_ifs with h
    · exact fun h' => TriFace.across_ne q k (congrArg Prod.fst h')
    · exact absurd (by rw [hd q hq k h]; ring) hne
  · rintro ⟨q, k⟩ ha
    dsimp only
    split_ifs with h
    · exact Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩
    · exact ha
  · rintro ⟨q, k⟩ ha
    have hq : q ∈ Q := (Finset.mem_product.1 ha).1
    dsimp only
    split_ifs with h h'
    · simp
    · exact absurd (by rw [TriFace.across_across]; exact hq) h'
    · simp

/-! ### The ray cochain -/

/-- The cochain dual to the ray of faces to the right of the face `q = W(v)` or `B(v)`: `1` on the
edges `((i, v₂), 2)` and `((i, v₂), 3)` with `i > v₁`, which the faces `B(v + e₁), W(v + e₁),
B(v + 2e₁), …` cross, and, for a black face `q = B(v)`, also `1` on its edge `(v, 3)`, across which
the ray leaves `B(v)`. -/
def rayCochain (q : TriFace) (e : TriEdge) : ℤ :=
  (if e.k ≠ 0 ∧ e.v.2 = q.v.2 ∧ q.v.1 < e.v.1 then 1 else 0) +
    if q.isWhite = false ∧ e = ⟨q.v, 2⟩ then 1 else 0

theorem rayCochain_def (q : TriFace) (e : TriEdge) :
    rayCochain q e = (if e.k ≠ 0 ∧ e.v.2 = q.v.2 ∧ q.v.1 < e.v.1 then 1 else 0) +
      if q.isWhite = false ∧ e = ⟨q.v, 2⟩ then 1 else 0 := (rfl)

/-- The ray cochain of `q` sums to zero round every face other than `q`. -/
theorem faceSum_rayCochain_of_ne {q : TriFace} (hf : f ≠ q) : faceSum (rayCochain q) f = 0 := by
  obtain ⟨⟨a, b⟩, cq⟩ := q
  obtain ⟨⟨x, y⟩, cf⟩ := f
  cases cf <;> cases cq <;> simp [faceSum_def, rayCochain_def, TriFace.ext_iff] at hf ⊢ <;> grind

/-- The circulation of the ray cochain of `q` round `q` is `1`. -/
theorem faceSign_mul_faceSum_rayCochain_self (q : TriFace) :
    faceSign q * faceSum (rayCochain q) q = 1 := by
  obtain ⟨⟨a, b⟩, cq⟩ := q
  cases cq <;> simp [faceSum_def, rayCochain_def]

/-! ### Holes -/

/-- **Holes obstruct simple connectivity.** If `Q` is a nonempty finite set of faces outside `R`
such that every face sharing an edge with a face of `Q` lies in `Q ∪ R`, then `R` is not simply
connected. -/
theorem not_isSimplyConnectedRegion_of_hole {Q : Finset TriFace} (hQ : Q.Nonempty)
    (hQR : ∀ q ∈ Q, q ∉ R)
    (hnbr : ∀ q ∈ Q, ∀ g : TriFace, ∀ e ∈ q.edges, e ∈ g.edges → g ∈ Q ∨ g ∈ R) :
    ¬ IsSimplyConnectedRegion R := by
  intro hR
  obtain ⟨q₀, hq₀⟩ := hQ
  have hclosed : IsClosedCochainOn R (rayCochain q₀) :=
    isClosedCochainOn_iff_faceSum.2 fun f hf =>
      faceSum_rayCochain_of_ne fun h => hQR q₀ hq₀ (h ▸ hf)
  obtain ⟨g, hg⟩ := isExactCochainOn_def.1 (hR.isExactCochainOn_of_isClosedCochainOn _ hclosed)
  rw [isCochainPrimitiveOn_def] at hg
  set d : TriEdge → ℤ := rayCochain q₀ - fun e => g e.target - g e.v with hd_def
  have hface : ∀ f, faceSum d f = faceSum (rayCochain q₀) f := fun f => by
    rw [hd_def, faceSum_sub, faceSum_coboundary, sub_zero]
  have hzero := sum_faceSign_mul_faceSum_eq_zero Q d fun q hq k hk => by
    have hR' : q.across k ∈ R :=
      (hnbr q hq _ _ (q.edge_mem_edges k) (q.edge_mem_edges_across k)).resolve_left hk
    rw [hd_def, Pi.sub_apply, hg _ (mem_regionEdges.2 ⟨_, hR', q.edge_mem_edges_across k⟩),
      sub_self]
  simp_rw [hface] at hzero
  rw [Finset.sum_eq_single_of_mem q₀ hq₀ fun f _ hf => by
    rw [faceSum_rayCochain_of_ne hf, mul_zero], faceSign_mul_faceSum_rayCochain_self] at hzero
  exact one_ne_zero hzero

/-! ### The complement of a simply connected region -/

/-- **Components outside a simply connected region are infinite.** Every connected component of
the graph of faces outside a simply connected region `R`, adjacent when they share an edge, is
infinite: a finite one would be a hole. -/
theorem IsSimplyConnectedRegion.infinite_supp (hR : IsSimplyConnectedRegion R)
    (c : (hexGraph.induce Rᶜ).ConnectedComponent) : c.supp.Infinite := by
  classical
  intro hfin
  set Q : Finset TriFace := hfin.toFinset.map (Function.Embedding.subtype _) with hQ_def
  have hmemQ : ∀ g : TriFace, g ∈ Q ↔ ∃ hg : g ∉ R, (⟨g, hg⟩ : ↥Rᶜ) ∈ c.supp := by
    intro g
    simp [hQ_def]
  refine not_isSimplyConnectedRegion_of_hole (Q := Q) ?_ ?_ ?_ hR
  · obtain ⟨v, rfl⟩ := c.exists_rep
    exact ⟨v.val, (hmemQ v.val).2
      ⟨v.property, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩
  · intro q hq
    exact ((hmemQ q).1 hq).1
  · intro q hq g e hq' hg'
    obtain ⟨hqR, hqc⟩ := (hmemQ q).1 hq
    by_cases hgR : g ∈ R
    · exact Or.inr hgR
    by_cases hgq : q = g
    · exact Or.inl (hgq ▸ hq)
    refine Or.inl ((hmemQ g).2 ⟨hgR, ?_⟩)
    have hadj : (hexGraph.induce Rᶜ).Adj ⟨q, hqR⟩ ⟨g, hgR⟩ :=
      SimpleGraph.induce_adj.2 (hexGraph_adj.2 ⟨hgq, e, hq', hg'⟩)
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hqc ⊢
    rw [← hqc]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm

/-- A finite region lies in a box: there is `N ≥ 0` with `|v.1| ≤ N` and `|v.2| ≤ N` for the
lower-left vertex `v` of every face of `R`. -/
private theorem exists_abs_le_of_finite (hR : R.Finite) :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ f ∈ R, |f.v.1| ≤ N ∧ |f.v.2| ≤ N := by
  classical
  have h0 : ∀ f : TriFace, 0 ≤ |f.v.1| + |f.v.2| := fun f =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨∑ f ∈ hR.toFinset, (|f.v.1| + |f.v.2|), Finset.sum_nonneg fun f _ => h0 f,
    fun f hf => ?_⟩
  have h := Finset.single_le_sum (f := fun f : TriFace => |f.v.1| + |f.v.2|)
    (fun f _ => h0 f) (hR.mem_toFinset.2 hf)
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans h,
    (le_add_of_nonneg_left (abs_nonneg _)).trans h⟩

section Far

variable {S : Set TriFace} {P : ℤ × ℤ → Prop}

/-- Reachability in the graph of faces of `S`, for faces given as elements of `TriFace`. -/
private def ReachIn (S : Set TriFace) (f g : TriFace) : Prop :=
  ∃ (hf : f ∈ S) (hg : g ∈ S), (hexGraph.induce S).Reachable ⟨f, hf⟩ ⟨g, hg⟩

private theorem ReachIn.refl {f : TriFace} (hf : f ∈ S) : ReachIn S f f := ⟨hf, hf, .rfl⟩

private theorem ReachIn.trans {f g k : TriFace} (h₁ : ReachIn S f g) (h₂ : ReachIn S g k) :
    ReachIn S f k := by
  obtain ⟨hf, hg, r₁⟩ := h₁
  obtain ⟨hg', hk, r₂⟩ := h₂
  exact ⟨hf, hk, r₁.trans r₂⟩

private theorem ReachIn.symm {f g : TriFace} (h : ReachIn S f g) : ReachIn S g f := by
  obtain ⟨hf, hg, h⟩ := h
  exact ⟨hg, hf, h.symm⟩

private theorem reachIn_of_adj {f g : TriFace} (hf : f ∈ S) (hg : g ∈ S) (h : hexGraph.Adj f g) :
    ReachIn S f g :=
  ⟨hf, hg, (SimpleGraph.induce_adj.2 h).reachable⟩

/-- `W(v)` and `W(v + e₁)` are joined through `B(v + e₁)`. -/
private theorem reachIn_white_add_one_fst (hP : ∀ u, P u → ∀ b, (⟨u, b⟩ : TriFace) ∈ S)
    {v : ℤ × ℤ} (hv : P v) (hv' : P (v + (1, 0))) :
    ReachIn S ⟨v, true⟩ ⟨v + (1, 0), true⟩ := by
  refine (reachIn_of_adj (hP v hv true) (hP _ hv' false) ?_).trans
    (reachIn_of_adj (hP _ hv' false) (hP _ hv' true) ?_)
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_true]
    simp
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_false]
    simp

/-- `W(v)` and `W(v + e₂)` are joined through `B(v)`. -/
private theorem reachIn_white_add_one_snd (hP : ∀ u, P u → ∀ b, (⟨u, b⟩ : TriFace) ∈ S)
    {v : ℤ × ℤ} (hv : P v) (hv' : P (v + (0, 1))) :
    ReachIn S ⟨v, true⟩ ⟨v + (0, 1), true⟩ := by
  refine (reachIn_of_adj (hP v hv true) (hP v hv false) ?_).trans
    (reachIn_of_adj (hP v hv false) (hP _ hv' true) ?_)
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_true]
    simp
  · rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_false]
    simp

/-- White faces along a horizontal segment of positions satisfying `P` are joined. -/
private theorem reachIn_white_fst (hP : ∀ u, P u → ∀ b, (⟨u, b⟩ : TriFace) ∈ S) (y : ℤ)
    {a b : ℤ} (hab : a ≤ b) (h : ∀ x, a ≤ x → x ≤ b → P (x, y)) :
    ReachIn S ⟨(a, y), true⟩ ⟨(b, y), true⟩ := by
  obtain ⟨n, rfl⟩ := Int.le.dest hab
  clear hab
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    exact ReachIn.refl (hP _ (h a le_rfl (by simp)) true)
  | succ n ih =>
    refine (ih fun x h₁ h₂ => h x h₁ (by push_cast; omega)).trans ?_
    have := reachIn_white_add_one_fst hP (v := (a + n, y)) (h _ (by omega) (by push_cast; omega))
      (by simpa using h (a + n + 1) (by omega) (by push_cast; omega))
    simpa [add_assoc] using this

/-- White faces along a vertical segment of positions satisfying `P` are joined. -/
private theorem reachIn_white_snd (hP : ∀ u, P u → ∀ b, (⟨u, b⟩ : TriFace) ∈ S) (x : ℤ)
    {a b : ℤ} (hab : a ≤ b) (h : ∀ y, a ≤ y → y ≤ b → P (x, y)) :
    ReachIn S ⟨(x, a), true⟩ ⟨(x, b), true⟩ := by
  obtain ⟨n, rfl⟩ := Int.le.dest hab
  clear hab
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    exact ReachIn.refl (hP _ (h a le_rfl (by simp)) true)
  | succ n ih =>
    refine (ih fun y h₁ h₂ => h y h₁ (by push_cast; omega)).trans ?_
    have := reachIn_white_add_one_snd hP (v := (x, a + n)) (h _ (by omega) (by push_cast; omega))
      (by simpa using h (a + n + 1) (by omega) (by push_cast; omega))
    simpa [add_assoc] using this

private theorem reachIn_white_fst' (hP : ∀ u, P u → ∀ b, (⟨u, b⟩ : TriFace) ∈ S) (y a b : ℤ)
    (h : ∀ x, min a b ≤ x → x ≤ max a b → P (x, y)) :
    ReachIn S ⟨(a, y), true⟩ ⟨(b, y), true⟩ := by
  rcases le_total a b with hab | hab
  · exact reachIn_white_fst hP y hab fun x hx hx' => h x (by omega) (by omega)
  · exact (reachIn_white_fst hP y hab fun x hx hx' => h x (by omega) (by omega)).symm

private theorem reachIn_white_snd' (hP : ∀ u, P u → ∀ b, (⟨u, b⟩ : TriFace) ∈ S) (x a b : ℤ)
    (h : ∀ y, min a b ≤ y → y ≤ max a b → P (x, y)) :
    ReachIn S ⟨(x, a), true⟩ ⟨(x, b), true⟩ := by
  rcases le_total a b with hab | hab
  · exact reachIn_white_snd hP x hab fun y hy hy' => h y (by omega) (by omega)
  · exact (reachIn_white_snd hP x hab fun y hy hy' => h y (by omega) (by omega)).symm

/-- Every face at a position outside the box `[-N, N]²` is joined to `W(N + 1, N + 1)` by faces at
positions outside the box. -/
private theorem reachIn_far {N : ℤ} (hN : 0 ≤ N)
    (hP : ∀ u : ℤ × ℤ, (N < |u.1| ∨ N < |u.2|) → ∀ b, (⟨u, b⟩ : TriFace) ∈ S)
    (f : TriFace) (hf : N < |f.v.1| ∨ N < |f.v.2|) :
    ReachIn S f ⟨(N + 1, N + 1), true⟩ := by
  obtain ⟨⟨x, y⟩, c⟩ := f
  have hwhite : ReachIn S ⟨(x, y), c⟩ ⟨(x, y), true⟩ := by
    cases c
    · refine reachIn_of_adj (hP _ hf false) (hP _ hf true) ?_
      rw [← SimpleGraph.mem_neighborSet, hexGraph_neighborSet_mk_false]
      simp
    · exact ReachIn.refl (hP _ hf true)
  refine hwhite.trans ?_
  have hNN : N < |N + 1| := by rw [abs_of_pos (by omega)]; omega
  simp only at hf
  rcases hf with hx | hy
  · exact (reachIn_white_snd' hP x y (N + 1) fun _ _ _ => Or.inl hx).trans
      (reachIn_white_fst' hP (N + 1) x (N + 1) fun _ _ _ => Or.inr hNN)
  · exact (reachIn_white_fst' hP y x (N + 1) fun _ _ _ => Or.inr hy).trans
      (reachIn_white_snd' hP (N + 1) y (N + 1) fun _ _ _ => Or.inl hNN)

end Far

/-- The faces at positions in the box `[-N, N]²` form a finite set. -/
private theorem finite_setOf_abs_le (N : ℤ) :
    {f : TriFace | |f.v.1| ≤ N ∧ |f.v.2| ≤ N}.Finite := by
  refine (((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).prod
    (Set.finite_univ (α := Bool))).image (fun p => (⟨p.1, p.2⟩ : TriFace)) |>.subset ?_
  rintro ⟨v, b⟩ ⟨h₁, h₂⟩
  exact ⟨(v, b), ⟨⟨abs_le.1 h₁, abs_le.1 h₂⟩, trivial⟩, rfl⟩

/-- **Exactly one infinite component.** For finite `R`, the graph of faces outside `R`, adjacent
when they share an edge, has exactly one infinite component: it contains every face far from `R`. -/
theorem existsUnique_infinite_supp_of_finite (hR : R.Finite) :
    ∃! c : (hexGraph.induce Rᶜ).ConnectedComponent, c.supp.Infinite := by
  obtain ⟨N, hN, hRN⟩ := exists_abs_le_of_finite hR
  have hP : ∀ u : ℤ × ℤ, (N < |u.1| ∨ N < |u.2|) → ∀ b, (⟨u, b⟩ : TriFace) ∈ Rᶜ := by
    intro u hu b hb
    have := hRN _ hb
    rcases hu with hu | hu
    · exact absurd this.1 (not_le.2 hu)
    · exact absurd this.2 (not_le.2 hu)
  have hNN : N < |N + 1| := by rw [abs_of_pos (by omega)]; omega
  have hhub : (⟨(N + 1, N + 1), true⟩ : TriFace) ∈ Rᶜ := hP _ (Or.inl hNN) true
  set c₀ := (hexGraph.induce Rᶜ).connectedComponentMk ⟨_, hhub⟩ with hc₀
  have hfar : ∀ (f : TriFace) (hfR : f ∈ Rᶜ), (N < |f.v.1| ∨ N < |f.v.2|) →
      (⟨f, hfR⟩ : ↥Rᶜ) ∈ c₀.supp := by
    intro f hfR hf
    obtain ⟨_, _, hr⟩ := reachIn_far hN hP f hf
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hc₀]
    exact SimpleGraph.ConnectedComponent.sound hr
  refine ⟨c₀, ?_, fun c hc => ?_⟩
  · intro hfin
    have hinf : Infinite TriFace := Infinite.of_injective (fun v : ℤ × ℤ => (⟨v, true⟩ : TriFace))
      fun a b h => by simpa using congrArg TriFace.v h
    refine (finite_setOf_abs_le N).infinite_compl ((hfin.image Subtype.val).subset ?_)
    intro f hf
    have hf' : N < |f.v.1| ∨ N < |f.v.2| := by
      by_contra! H
      exact hf H
    exact ⟨⟨f, hP f.v hf' f.isWhite⟩, hfar _ _ hf', rfl⟩
  · obtain ⟨⟨f, hfR⟩, hfc, hf⟩ : ∃ x ∈ c.supp, N < |x.val.v.1| ∨ N < |x.val.v.2| := by
      by_contra! H
      refine hc (((finite_setOf_abs_le N).preimage Subtype.val_injective.injOn).subset ?_)
      exact fun x hx => H x hx
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hfc
    rw [← hfc]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 (hfar f hfR hf)

/-- **The complement of a finite simply connected region is connected.** For finite simply
connected `R`, the faces outside `R` are connected through shared edges. -/
theorem IsSimplyConnectedRegion.connected_induce_compl (hR : IsSimplyConnectedRegion R)
    (hfin : R.Finite) : (hexGraph.induce Rᶜ).Connected := by
  obtain ⟨c, hc, huniq⟩ := existsUnique_infinite_supp_of_finite hfin
  have hall : ∀ c', c' = c := fun c' => huniq c' (hR.infinite_supp c')
  obtain ⟨v, -⟩ := hc.nonempty
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨v, fun w => SimpleGraph.ConnectedComponent.exact ((hall _).trans (hall _).symm)⟩

end TauCeti
