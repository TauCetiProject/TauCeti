/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Orientation.Indegree
public import TauCeti.Combinatorics.Network.IntervalExcess

/-!
# Prescribed and bounded indegree orientations

For a finite multigraph `G`, loops and parallel edges allowed, and natural vertex bounds
`a ≤ b`, an orientation with `a v ≤ indegree v ≤ b v` at every vertex exists exactly when every
vertex set `S` satisfies

* `|E(S)| ≤ b(S)`, where `E(S)` is the set of edges internal to `S`, and
* `a(S) ≤ |I(S)|`, where `I(S)` is the set of edges incident with `S`.

With `a = b = d` this is **Hakimi's theorem**: an orientation with indegree `d` exists exactly
when `d` sums to the number of edges and `|E(S)| ≤ d(S)` for every `S`. The one-sided bounds and
the outdegree forms are corollaries.

The proof is a reduction to interval-excess feasibility over `ℤ`. The edge-to-endpoint network
`Graph.EndpointHom` has a node for each actual edge and each actual vertex, and a capacity-one
arrow from an edge node to each distinct end of the edge, so that a loop has a single arrow.
Prescribing excess `-1` at edge nodes and excess in `[a v, b v]` at vertex nodes, the integral
feasible assignments are exactly the orientations within the bounds: the unit leaving an edge
node goes to the chosen head (`Graph.orientationEndpointEquiv`). The cut criterion of
`TauCeti.ExcessIntervalFlow.nonempty_iff` for this network reduces to the two displayed families
of inequalities (`Graph.forall_cutBound_endpointBound_iff`).

## Main declarations

* `Graph.EndpointHom`: the arrows of the edge-to-endpoint network.
* `Graph.orientationEndpointEquiv`: orientations within vertex bounds are the integral feasible
  assignments of the edge-to-endpoint network.
* `Graph.exists_orientation_indegree_mem_Icc_iff`: the bounded-indegree theorem.
* `Graph.exists_orientation_indegree_eq_iff`: Hakimi's prescribed-indegree theorem.

## References

* S. L. Hakimi, *On the degrees of the vertices of a directed graph*, J. Franklin Inst. 279
  (1965), 290–308.
* A. Frank, *Connections in Combinatorial Optimization*, Oxford University Press, 2011.
-/

public section

open Finset TauCeti

namespace Graph

universe u v

variable {V : Type u} {E : Type v} {G : Graph V E}

/-- The arrows of the edge-to-endpoint network of `G`. Its nodes are the actual edges and the
actual vertices of `G`. There is one arrow from each edge node to each distinct end of that
edge, so a loop has a single arrow, and there are no other arrows. The family is exposed so that
its `Fintype` instance compiles consistently in importing modules. -/
@[expose] def EndpointHom (G : Graph V E) : G.edgeSet ⊕ G.vertexSet → G.edgeSet ⊕ G.vertexSet → Type
  | .inl e, .inr x => PLift (G.Inc e.1 x.1)
  | .inl _, .inl _ => PEmpty
  | .inr _, _ => PEmpty

namespace EndpointHom

/-- The arrow from an edge node to an end of the edge. -/
def arrow {e : G.edgeSet} {x : G.vertexSet} (h : G.Inc e.1 x.1) :
    G.EndpointHom (.inl e) (.inr x) :=
  ⟨h⟩

/-- The target of an arrow leaving an edge node is an end of the edge. -/
theorem inc {e : G.edgeSet} {x : G.vertexSet} (p : G.EndpointHom (.inl e) (.inr x)) :
    G.Inc e.1 x.1 :=
  PLift.down p

instance instSubsingleton (e : G.edgeSet) (x : G.vertexSet) :
    Subsingleton (G.EndpointHom (.inl e) (.inr x)) :=
  inferInstanceAs (Subsingleton (PLift _))

instance instIsEmptyInl (e f : G.edgeSet) : IsEmpty (G.EndpointHom (.inl e) (.inl f)) :=
  inferInstanceAs (IsEmpty PEmpty)

instance instIsEmptyInr (x : G.vertexSet) (y : G.edgeSet ⊕ G.vertexSet) :
    IsEmpty (G.EndpointHom (.inr x) y) :=
  inferInstanceAs (IsEmpty PEmpty)

noncomputable instance instFintype : ∀ y z, Fintype (G.EndpointHom y z)
  | .inl e, .inr x => by
    classical
    exact inferInstanceAs (Fintype (PLift (G.Inc e.1 x.1)))
  | .inl _, .inl _ => inferInstanceAs (Fintype PEmpty)
  | .inr _, _ => inferInstanceAs (Fintype PEmpty)

/-- Arrow sums in the edge-to-endpoint network only see arrows from edge nodes in `T` to vertex
nodes in `T'`. -/
theorem arrowSum_eq {K : Type*} [AddCommMonoid K] (f : Assignment G.EndpointHom K)
    (T T' : Finset (G.edgeSet ⊕ G.vertexSet)) :
    arrowSum f T T' =
      ∑ e ∈ T.toLeft, ∑ x ∈ T'.toRight, ∑ p : G.EndpointHom (.inl e) (.inr x), f p := by
  simp [arrowSum_def, sum_sum_eq_sum_toLeft_add_sum_toRight]

section Excess

variable [Fintype G.edgeSet] [Fintype G.vertexSet] {K : Type*} [AddCommGroup K]

/-- The excess at an edge node is minus the total value leaving it. -/
theorem excessAt_inl (f : Assignment G.EndpointHom K) (e : G.edgeSet) :
    excessAt f (.inl e) = -∑ x, ∑ p : G.EndpointHom (.inl e) (.inr x), f p := by
  simp [excessAt_def, Fintype.sum_sum_type]

/-- The excess at a vertex node is the total value entering it. -/
theorem excessAt_inr (f : Assignment G.EndpointHom K) (x : G.vertexSet) :
    excessAt f (.inr x) = ∑ e, ∑ p : G.EndpointHom (.inl e) (.inr x), f p := by
  simp [excessAt_def, Fintype.sum_sum_type]

end Excess

end EndpointHom

/-- Vertex bounds for the edge-to-endpoint network: excess `-1` at every edge node, so that each
edge sends out one unit, and the bound `c` at every vertex node. -/
def endpointBound (c : G.vertexSet → ℕ) : G.edgeSet ⊕ G.vertexSet → ℤ :=
  Sum.elim (fun _ ↦ -1) fun x ↦ c x

@[simp]
theorem endpointBound_inl (c : G.vertexSet → ℕ) (e : G.edgeSet) :
    endpointBound c (.inl e) = -1 :=
  (rfl)

@[simp]
theorem endpointBound_inr (c : G.vertexSet → ℕ) (x : G.vertexSet) :
    endpointBound c (.inr x) = c x :=
  (rfl)

/-- Vertex bounds of the edge-to-endpoint network compare exactly as the bounds at vertex
nodes. -/
theorem endpointBound_mem_Icc_iff {a b c : G.vertexSet → ℕ} :
    endpointBound c ∈ Set.Icc (endpointBound a) (endpointBound b) ↔
      ∀ x, c x ∈ Set.Icc (a x) (b x) := by
  simp [Set.mem_Icc, Pi.le_def, Sum.forall, forall_and]

/-- Ordered vertex bounds give ordered bounds on the edge-to-endpoint network. -/
theorem endpointBound_mono {a b : G.vertexSet → ℕ} (h : a ≤ b) :
    endpointBound a ≤ endpointBound b := by
  rintro (_ | x)
  · simp
  · simpa using h x

namespace Orientation

open Classical in
/-- The assignment of the edge-to-endpoint network sending the unit of each edge node to the
chosen head of the edge. -/
noncomputable def headAssignment (o : Orientation G) : Assignment G.EndpointHom ℤ
  | .inl e, .inr x, _ => if o.head e = x then 1 else 0
  | .inl _, .inl _, _ => 0
  | .inr _, _, _ => 0

@[simp]
theorem headAssignment_apply [DecidableEq G.vertexSet] (o : Orientation G) {e : G.edgeSet}
    {x : G.vertexSet} (p : G.EndpointHom (.inl e) (.inr x)) :
    o.headAssignment p = if o.head e = x then 1 else 0 := by
  rw [headAssignment]
  congr

/-- The head assignment takes values between `0` and `1`. -/
theorem headAssignment_mem_Icc (o : Orientation G) :
    o.headAssignment ∈ Set.Icc (0 : Assignment G.EndpointHom ℤ) 1 := by
  classical
  constructor <;> rintro (e | e) (x | x) p
  all_goals first
    | exact (IsEmpty.false p).elim
    | rw [headAssignment_apply]; split_ifs <;> simp

end Orientation

section Excess

variable [DecidableEq G.vertexSet]

/-- An assignment taking value `1` on the arrow to the chosen head of each edge and `0`
elsewhere has total value `1` or `0` on the arrows from an edge node to a vertex node, according
as the vertex is the head. -/
private theorem sum_eq_ite {o : Orientation G} {g : Assignment G.EndpointHom ℤ} (e : G.edgeSet)
    (x : G.vertexSet)
    (hg : ∀ p : G.EndpointHom (.inl e) (.inr x), g p = if o.head e = x then 1 else 0) :
    ∑ p : G.EndpointHom (.inl e) (.inr x), g p = if o.head e = x then 1 else 0 := by
  split_ifs with h
  · subst h
    simp [Fintype.sum_subsingleton _ (EndpointHom.arrow (o.head_inc e)), hg]
  · exact sum_eq_zero fun p _ ↦ by simp [hg, h]

/-- The excess of an assignment sending each edge's unit to its chosen head is `-1` at edge nodes
and the indegree at vertex nodes. -/
private theorem excessAt_eq_endpointBound [Fintype G.edgeSet] [Fintype G.vertexSet]
    {o : Orientation G} {g : Assignment G.EndpointHom ℤ}
    (hg : ∀ e x (p : G.EndpointHom (.inl e) (.inr x)), g p = if o.head e = x then 1 else 0) :
    excessAt g = endpointBound o.indegree := by
  funext y
  rcases y with e | x
  · simp [EndpointHom.excessAt_inl, sum_eq_ite e _ (hg e _)]
  · simp [EndpointHom.excessAt_inr, sum_eq_ite _ x (hg _ x), o.indegree_def]

end Excess

/-- The excess of the head assignment of an orientation is `-1` at edge nodes and the indegree at
vertex nodes. -/
@[simp]
theorem Orientation.excessAt_headAssignment [Fintype G.edgeSet] [Fintype G.vertexSet]
    (o : Orientation G) : excessAt o.headAssignment = endpointBound o.indegree := by
  classical
  exact excessAt_eq_endpointBound fun _ _ p ↦ o.headAssignment_apply p

namespace EndpointHom

variable [Fintype G.edgeSet] [Fintype G.vertexSet] {a b : G.vertexSet → ℕ}
variable (f : ExcessIntervalFlow (0 : Assignment G.EndpointHom ℤ) 1 (endpointBound a)
  (endpointBound b))

private theorem apply_eq_zero_or_eq_one {y z} (p : G.EndpointHom y z) :
    f.1 p = 0 ∨ f.1 p = 1 := by
  have h₀ : 0 ≤ f.1 p := f.mem_Icc.1 _ _ p
  have h₁ : f.1 p ≤ 1 := f.mem_Icc.2 _ _ p
  omega

private theorem sum_sum_eq_one (e : G.edgeSet) :
    ∑ x, ∑ p : G.EndpointHom (.inl e) (.inr x), f.1 p = 1 := by
  have h₁ := f.excessAt_mem_Icc.1 (.inl e)
  have h₂ := f.excessAt_mem_Icc.2 (.inl e)
  simp only [endpointBound_inl, excessAt_inl] at h₁ h₂
  omega

private theorem exists_eq_one (e : G.edgeSet) :
    ∃ x, ∃ p : G.EndpointHom (.inl e) (.inr x), f.1 p = 1 := by
  by_contra! h
  have := sum_sum_eq_one f e
  rw [sum_eq_zero fun x _ ↦ sum_eq_zero fun p _ ↦
    (apply_eq_zero_or_eq_one f p).resolve_right (h x p)] at this
  exact zero_ne_one this

private theorem eq_of_eq_one {e : G.edgeSet} {x y : G.vertexSet}
    {p : G.EndpointHom (.inl e) (.inr x)} {q : G.EndpointHom (.inl e) (.inr y)}
    (hp : f.1 p = 1) (hq : f.1 q = 1) : x = y := by
  by_contra hxy
  have h := add_le_sum (f := fun z ↦ ∑ r : G.EndpointHom (.inl e) (.inr z), f.1 r)
    (fun z _ ↦ sum_nonneg fun r _ ↦ f.mem_Icc.1 _ _ r) (mem_univ x) (mem_univ y) hxy
  rw [Fintype.sum_subsingleton _ p, Fintype.sum_subsingleton _ q, hp, hq,
    sum_sum_eq_one] at h
  omega

/-- The head chosen by a feasible assignment: the end of the edge receiving its unit. -/
private noncomputable def headOf (e : G.edgeSet) : G.vertexSet :=
  (exists_eq_one f e).choose

private theorem inc_headOf (e : G.edgeSet) : G.Inc e.1 (headOf f e).1 :=
  (exists_eq_one f e).choose_spec.choose.inc

private theorem apply_eq_ite [DecidableEq G.vertexSet] {e : G.edgeSet} {x : G.vertexSet}
    (p : G.EndpointHom (.inl e) (.inr x)) : f.1 p = if headOf f e = x then 1 else 0 := by
  obtain ⟨q, hq⟩ := (exists_eq_one f e).choose_spec
  split_ifs with h
  · subst h
    rwa [Subsingleton.elim p q]
  · exact (apply_eq_zero_or_eq_one f p).resolve_right fun hp ↦ h (eq_of_eq_one f hq hp)

private theorem headOf_eq {o : Orientation G}
    (hf : ∀ y z (p : G.EndpointHom y z), f.1 p = o.headAssignment p) (e : G.edgeSet) :
    headOf f e = o.head e := by
  classical
  obtain ⟨p, hp⟩ := (exists_eq_one f e).choose_spec
  rw [hf, Orientation.headAssignment_apply] at hp
  split_ifs at hp with h
  · exact h.symm
  · exact absurd hp zero_ne_one

end EndpointHom

section Reduction

variable [Fintype G.edgeSet] [Fintype G.vertexSet]

/-- **Edge-to-endpoint reduction.** Orientations of `G` with indegrees between `a` and `b` are
equivalent to the integral assignments of the edge-to-endpoint network with arrow bounds `0` and
`1`, excess `-1` at edge nodes, and excess between `a` and `b` at vertex nodes. An orientation
sends the unit of each edge node to the chosen head of the edge. -/
noncomputable def orientationEndpointEquiv (a b : G.vertexSet → ℕ) :
    {o : Orientation G // ∀ x, o.indegree x ∈ Set.Icc (a x) (b x)} ≃
      ExcessIntervalFlow (0 : Assignment G.EndpointHom ℤ) 1 (endpointBound a)
        (endpointBound b) where
  toFun o := ⟨o.1.headAssignment, o.1.headAssignment_mem_Icc, by
    rw [Orientation.excessAt_headAssignment]
    exact endpointBound_mem_Icc_iff.2 o.2⟩
  invFun f := ⟨Orientation.ofHead (EndpointHom.headOf f) (EndpointHom.inc_headOf f), by
    classical
    refine endpointBound_mem_Icc_iff.1 ?_
    rw [← excessAt_eq_endpointBound (g := f.1) fun e x p ↦ by
      rw [EndpointHom.apply_eq_ite f p, Orientation.ofHead_head]]
    exact f.excessAt_mem_Icc⟩
  left_inv o := Subtype.ext <| Orientation.ext_of_head fun e ↦ by
    rw [Orientation.ofHead_head]
    exact EndpointHom.headOf_eq _ (fun _ _ _ ↦ rfl) e
  right_inv f := by
    classical
    refine Subtype.ext ?_
    funext y z p
    rcases y with e | x
    · rcases z with f' | x
      · exact (IsEmpty.false p).elim
      · dsimp only
        rw [Orientation.headAssignment_apply, Orientation.ofHead_head,
          EndpointHom.apply_eq_ite f p]
    · exact (IsEmpty.false p).elim

@[simp]
theorem orientationEndpointEquiv_apply_coe (a b : G.vertexSet → ℕ)
    (o : {o : Orientation G // ∀ x, o.indegree x ∈ Set.Icc (a x) (b x)}) :
    (orientationEndpointEquiv a b o).1 = o.1.headAssignment :=
  (rfl)

/-- The orientation of a feasible assignment of the edge-to-endpoint network chooses as head of
an edge the end whose arrow carries the edge's unit. -/
theorem orientationEndpointEquiv_symm_head_eq_iff {a b : G.vertexSet → ℕ}
    (f : ExcessIntervalFlow (0 : Assignment G.EndpointHom ℤ) 1 (endpointBound a)
      (endpointBound b))
    {e : G.edgeSet} {x : G.vertexSet} (h : G.Inc e.1 x.1) :
    ((orientationEndpointEquiv a b).symm f).1.head e = x ↔ f.1 (EndpointHom.arrow h) = 1 := by
  classical
  rw [← (orientationEndpointEquiv a b).apply_symm_apply f, orientationEndpointEquiv_apply_coe,
    Equiv.symm_apply_apply, Orientation.headAssignment_apply]
  split_ifs <;> simp_all

/-- The indegree of the orientation recovered from a feasible endpoint assignment is the excess
at the corresponding vertex node. -/
@[simp]
theorem orientationEndpointEquiv_symm_indegree {a b : G.vertexSet → ℕ}
    (f : ExcessIntervalFlow (0 : Assignment G.EndpointHom ℤ) 1 (endpointBound a)
      (endpointBound b)) (x : G.vertexSet) :
    (((orientationEndpointEquiv a b).symm f).1.indegree x : ℤ) =
      excessAt f.1 (.inr x) := by
  rw [← endpointBound_inr]
  rw [← Orientation.excessAt_headAssignment]
  have h := congrArg Subtype.val ((orientationEndpointEquiv a b).apply_symm_apply f)
  exact congrArg (fun g : Assignment G.EndpointHom ℤ ↦ excessAt g (.inr x)) <|
    by simpa only [orientationEndpointEquiv_apply_coe] using h

section Cuts

omit [Fintype G.edgeSet] [Fintype G.vertexSet] in
private theorem sum_endpointBound (c : G.vertexSet → ℕ) (T : Finset (G.edgeSet ⊕ G.vertexSet)) :
    ∑ y ∈ T, endpointBound c y = -(#T.toLeft : ℤ) + ∑ x ∈ T.toRight, (c x : ℤ) := by
  simp [sum_sum_eq_sum_toLeft_add_sum_toRight]

private theorem cutBound_eq [DecidableEq (G.edgeSet ⊕ G.vertexSet)]
    (T : Finset (G.edgeSet ⊕ G.vertexSet)) :
    cutBound (0 : Assignment G.EndpointHom ℤ) 1 T =
      ∑ e ∈ T.toLeft, ∑ x ∈ Tᶜ.toRight,
        (Fintype.card (G.EndpointHom (.inl e) (.inr x)) : ℤ) := by
  simp [cutBound_zero_left, EndpointHom.arrowSum_eq]

omit [Fintype G.edgeSet] [Fintype G.vertexSet] in
/-- An edge with an end in `S` has an arrow into `S`. -/
private theorem one_le_sum_card {e : G.edgeSet} {x : G.vertexSet} {S : Finset G.vertexSet}
    (hx : x ∈ S) (h : G.Inc e.1 x.1) :
    (1 : ℤ) ≤ ∑ y ∈ S, (Fintype.card (G.EndpointHom (.inl e) (.inr y)) : ℤ) := by
  have : 0 < Fintype.card (G.EndpointHom (.inl e) (.inr x)) :=
    Fintype.card_pos_iff.2 ⟨EndpointHom.arrow h⟩
  exact (by exact_mod_cast this : (1 : ℤ) ≤ _).trans <|
    single_le_sum (f := fun y ↦ (Fintype.card (G.EndpointHom (.inl e) (.inr y)) : ℤ))
      (fun _ _ ↦ Nat.cast_nonneg' _) hx

variable {a b : G.vertexSet → ℕ}

/-- The lower cut inequalities of the edge-to-endpoint network follow from
`a(S) ≤ |I(S)|`: an edge incident with `S` either has its node on the same side as `S`, or has an
arrow into `S` crossing the cut. -/
private theorem sum_endpointBound_le_cutBound_compl [DecidableEq (G.edgeSet ⊕ G.vertexSet)]
    (ha : ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S))
    (T : Finset (G.edgeSet ⊕ G.vertexSet)) :
    ∑ y ∈ T, endpointBound a y ≤ cutBound (0 : Assignment G.EndpointHom ℤ) 1 Tᶜ := by
  classical
  have hc : Tᶜ.toLeft = (T.toLeft)ᶜ := by ext; simp
  rw [sum_endpointBound, cutBound_eq, compl_compl, hc]
  set S := T.toRight
  set F := T.toLeft
  set w : G.edgeSet → ℤ := fun e ↦
    ∑ x ∈ S, (Fintype.card (G.EndpointHom (.inl e) (.inr x)) : ℤ)
  have key (e : G.edgeSet) : (if e ∈ G.incidentEdges S then (1 : ℤ) else 0) ≤
      (if e ∈ F then 1 else 0) + if e ∈ Fᶜ then w e else 0 := by
    have hw : 0 ≤ w e := sum_nonneg fun _ _ ↦ Nat.cast_nonneg' _
    by_cases hF : e ∈ F <;> by_cases hI : e ∈ G.incidentEdges S <;>
      simp only [hF, hI, mem_compl, not_true_eq_false, not_false_eq_true, ↓reduceIte] <;>
      try omega
    obtain ⟨x, hx, hex⟩ := G.mem_incidentEdges.1 hI
    exact (one_le_sum_card hx hex).trans_eq (zero_add _).symm
  have hI : (#(G.incidentEdges S) : ℤ) ≤ #F + ∑ e ∈ Fᶜ, w e := by
    have := sum_le_sum fun e (_ : e ∈ univ) ↦ key e
    simpa only [sum_add_distrib, sum_ite_mem_eq, sum_const, nsmul_one] using this
  have hS : ∑ x ∈ S, (a x : ℤ) ≤ #(G.incidentEdges S) := by exact_mod_cast ha S
  have hw : ∑ e ∈ Fᶜ, w e = Fᶜ.sum w := rfl
  omega

/-- The upper cut inequalities of the edge-to-endpoint network follow from `|E(S)| ≤ b(S)`: an
edge whose node lies on the same side as `S` is either internal to `S`, or has an arrow leaving
the side of `S` across the cut. -/
private theorem neg_cutBound_le_sum_endpointBound [DecidableEq (G.edgeSet ⊕ G.vertexSet)]
    (hb : ∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x)
    (T : Finset (G.edgeSet ⊕ G.vertexSet)) :
    -cutBound (0 : Assignment G.EndpointHom ℤ) 1 T ≤ ∑ y ∈ T, endpointBound b y := by
  classical
  rw [sum_endpointBound, cutBound_eq]
  set S := T.toRight
  set F := T.toLeft
  set w : G.edgeSet → ℤ := fun e ↦
    ∑ x ∈ Tᶜ.toRight, (Fintype.card (G.EndpointHom (.inl e) (.inr x)) : ℤ)
  have key (e : G.edgeSet) : (1 : ℤ) ≤ (if e ∈ G.internalEdges S then 1 else 0) + w e := by
    have hw : 0 ≤ w e := sum_nonneg fun _ _ ↦ Nat.cast_nonneg' _
    split_ifs with hE
    · omega
    rw [zero_add]
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
    have : ⟨x, hxy.left_mem⟩ ∉ S ∨ ⟨y, hxy.right_mem⟩ ∉ S := by
      by_contra! h
      exact hE (G.mem_internalEdges.2 ⟨_, h.1, _, h.2, hxy⟩)
    rcases this with h | h
    · exact one_le_sum_card (S := Tᶜ.toRight) (by simpa [S] using h) hxy.inc_left
    · exact one_le_sum_card (S := Tᶜ.toRight) (by simpa [S] using h) hxy.inc_right
  have hF : (#F : ℤ) ≤ #(G.internalEdges S) + ∑ e ∈ F, w e := by
    have h₁ := sum_le_sum fun e (_ : e ∈ F) ↦ key e
    have h₂ : ∑ e ∈ F, (if e ∈ G.internalEdges S then (1 : ℤ) else 0) ≤
        ∑ e, if e ∈ G.internalEdges S then (1 : ℤ) else 0 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ F) fun _ _ _ ↦ by split_ifs <;> simp
    rw [sum_ite_mem_eq, sum_const, nsmul_one] at h₂
    rw [sum_add_distrib, sum_const, nsmul_one] at h₁
    omega
  have hS : (#(G.internalEdges S) : ℤ) ≤ ∑ x ∈ S, (b x : ℤ) := by exact_mod_cast hb S
  have hw : ∑ e ∈ F, w e = F.sum w := rfl
  omega

/-- **Reduction of the cut inequalities.** For the edge-to-endpoint network, the cut inequalities
over all sets of nodes are equivalent to `|E(S)| ≤ b(S)` and `a(S) ≤ |I(S)|` over all sets
`S` of vertices. -/
theorem forall_cutBound_endpointBound_iff [DecidableEq (G.edgeSet ⊕ G.vertexSet)] :
    ((∀ T, ∑ y ∈ T, endpointBound a y ≤ cutBound (0 : Assignment G.EndpointHom ℤ) 1 Tᶜ) ∧
        ∀ T, -cutBound (0 : Assignment G.EndpointHom ℤ) 1 T ≤ ∑ y ∈ T, endpointBound b y) ↔
      (∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x) ∧
        ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S) := by
  refine ⟨fun h ↦ ?_, fun ⟨hb, ha⟩ ↦
    ⟨sum_endpointBound_le_cutBound_compl ha, neg_cutBound_le_sum_endpointBound hb⟩⟩
  constructor
  · intro S
    let T := (G.internalEdges S).disjSum S
    have hcut : cutBound (0 : Assignment G.EndpointHom ℤ) 1 T = 0 := by
      rw [cutBound_eq]
      apply sum_eq_zero
      intro e he
      apply sum_eq_zero
      intro x hx
      exact_mod_cast Fintype.card_eq_zero_iff.2 ⟨fun p ↦ by
        have hxS : x ∉ S := by simpa [T] using hx
        obtain ⟨u, hu, v, hv, huv⟩ := G.mem_internalEdges.1 (by simpa [T] using he)
        rcases p.inc.eq_or_eq_of_isLink huv with hxu | hxv
        · exact hxS (Subtype.ext hxu ▸ hu)
        · exact hxS (Subtype.ext hxv ▸ hv)⟩
    have hS := h.2 T
    rw [hcut, sum_endpointBound] at hS
    have hT : (#T.toLeft : ℤ) ≤ ∑ x ∈ T.toRight, (b x : ℤ) := by omega
    have hS' : (#(G.internalEdges S) : ℤ) ≤ ∑ x ∈ S, (b x : ℤ) := by
      simpa only [T, toLeft_disjSum, toRight_disjSum, neg_zero] using hT
    exact_mod_cast hS'
  · intro S
    let T := (G.incidentEdges S).disjSum S
    have hcut : cutBound (0 : Assignment G.EndpointHom ℤ) 1 Tᶜ = 0 := by
      rw [cutBound_eq]
      apply sum_eq_zero
      intro e he
      apply sum_eq_zero
      intro x hx
      exact_mod_cast Fintype.card_eq_zero_iff.2 ⟨fun p ↦ by
        have heS : e ∉ G.incidentEdges S := by simpa [T] using he
        have hxS : x ∈ S := by simpa [T] using hx
        exact heS (G.mem_incidentEdges.2 ⟨x, hxS, p.inc⟩)⟩
    have hS := h.1 T
    rw [hcut, sum_endpointBound] at hS
    have hT : ∑ x ∈ T.toRight, (a x : ℤ) ≤ (#T.toLeft : ℤ) := by omega
    have hS' : ∑ x ∈ S, (a x : ℤ) ≤ #(G.incidentEdges S) := by
      simpa only [T, toLeft_disjSum, toRight_disjSum] using hT
    exact_mod_cast hS'

end Cuts

end Reduction

variable [Fintype G.edgeSet]

/-- **Bounded-indegree orientations.** For vertex bounds `a ≤ b`, a finite multigraph has an
orientation with every indegree between `a` and `b` exactly when every vertex set `S` has at most
`b(S)` internal edges and at least `a(S)` incident edges. -/
theorem exists_orientation_indegree_mem_Icc_iff [Finite G.vertexSet] {a b : G.vertexSet → ℕ}
    (hab : a ≤ b) :
    (∃ o : Orientation G, ∀ x, o.indegree x ∈ Set.Icc (a x) (b x)) ↔
      (∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x) ∧
        ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S) := by
  classical
  have := Fintype.ofFinite G.vertexSet
  rw [← forall_cutBound_endpointBound_iff, ← ExcessIntervalFlow.nonempty_iff zero_le_one
    (endpointBound_mono hab), ← (orientationEndpointEquiv a b).nonempty_congr, nonempty_subtype]

/-- A finite multigraph has an orientation with indegrees between `a ≤ b`, or some vertex set
has more than `b(S)` internal edges or fewer than `a(S)` incident edges. -/
theorem exists_orientation_indegree_mem_Icc_or_certificate [Finite G.vertexSet]
    {a b : G.vertexSet → ℕ} (hab : a ≤ b) :
    (∃ o : Orientation G, ∀ x, o.indegree x ∈ Set.Icc (a x) (b x)) ∨
      ∃ S : Finset G.vertexSet,
        ∑ x ∈ S, b x < #(G.internalEdges S) ∨ #(G.incidentEdges S) < ∑ x ∈ S, a x := by
  by_cases h : (∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x) ∧
      ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S)
  · exact .inl ((exists_orientation_indegree_mem_Icc_iff hab).2 h)
  · rcases not_and_or.1 h with h | h <;> push Not at h <;> obtain ⟨S, hS⟩ := h
    exacts [.inr ⟨S, .inl hS⟩, .inr ⟨S, .inr hS⟩]

/-- **Upper-bounded indegrees.** A finite multigraph has an orientation with every indegree at
most `b` exactly when every vertex set `S` has at most `b(S)` internal edges. -/
theorem exists_orientation_indegree_le_iff [Finite G.vertexSet] (b : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, o.indegree x ≤ b x) ↔
      ∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x := by
  simpa using exists_orientation_indegree_mem_Icc_iff (a := 0) (b := b) fun _ ↦ Nat.zero_le _

/-- **Lower-bounded indegrees.** A finite multigraph has an orientation with every indegree at
least `a` exactly when every vertex set `S` has at least `a(S)` incident edges. -/
theorem exists_orientation_le_indegree_iff [Finite G.vertexSet] (a : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, a x ≤ o.indegree x) ↔
      ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S) := by
  refine ⟨fun ⟨o, ho⟩ S ↦ (sum_le_sum fun x _ ↦ ho x).trans
    (o.sum_indegree_le_card_incidentEdges S), fun ha ↦ ?_⟩
  -- An upper bound of at least the number of edges at every vertex imposes no constraint.
  set b : G.vertexSet → ℕ := fun x ↦ a x + Fintype.card G.edgeSet
  have hb (S : Finset G.vertexSet) : #(G.internalEdges S) ≤ ∑ x ∈ S, b x := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · exact (card_le_univ _).trans <| (Nat.le_add_left _ (a x)).trans <|
        single_le_sum (f := b) (fun _ _ ↦ Nat.zero_le _) hx
  obtain ⟨o, ho⟩ := (exists_orientation_indegree_mem_Icc_iff (b := b)
    fun _ ↦ Nat.le_add_right _ _).2 ⟨hb, ha⟩
  exact ⟨o, fun x ↦ (ho x).1⟩

/-- **Hakimi's theorem.** A finite multigraph has an orientation with indegree `d` exactly when
`d` sums to the number of actual edges and every vertex set `S` has at most `d(S)` internal
edges. -/
theorem exists_orientation_indegree_eq_iff [Fintype G.vertexSet] (d : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, o.indegree x = d x) ↔
      ∑ x, d x = Fintype.card G.edgeSet ∧
        ∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, d x := by
  classical
  constructor
  · rintro ⟨o, ho⟩
    simp_rw [← ho]
    exact ⟨o.sum_indegree, o.card_internalEdges_le_sum_indegree⟩
  rintro ⟨hd, hE⟩
  simp_rw [← Set.mem_singleton_iff, ← Set.Icc_self]
  refine (exists_orientation_indegree_mem_Icc_iff le_rfl).2 ⟨hE, fun S ↦ ?_⟩
  -- The edges not incident with `S` are internal to its complement.
  have h₁ := G.card_incidentEdges_add_card_internalEdges_compl S
  have h₂ := hE Sᶜ
  have h₃ := sum_add_sum_compl S d
  omega

/-- A finite multigraph has an orientation with indegree `d`, or `d` does not sum to the number
of actual edges, or some vertex set `S` has more than `d(S)` internal edges. -/
theorem exists_orientation_indegree_eq_or_certificate [Fintype G.vertexSet]
    (d : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, o.indegree x = d x) ∨ ∑ x, d x ≠ Fintype.card G.edgeSet ∨
      ∃ S : Finset G.vertexSet, ∑ x ∈ S, d x < #(G.internalEdges S) := by
  by_cases h : ∑ x, d x = Fintype.card G.edgeSet ∧
      ∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, d x
  · exact .inl ((exists_orientation_indegree_eq_iff d).2 h)
  · rcases not_and_or.1 h with h | h
    · exact .inr (.inl h)
    · push Not at h
      exact .inr (.inr h)

/-! ### Outdegree forms -/

/-- The outdegree form of `Graph.exists_orientation_indegree_mem_Icc_iff`. -/
theorem exists_orientation_outdegree_mem_Icc_iff [Finite G.vertexSet] {a b : G.vertexSet → ℕ}
    (hab : a ≤ b) :
    (∃ o : Orientation G, ∀ x, o.outdegree x ∈ Set.Icc (a x) (b x)) ↔
      (∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x) ∧
        ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S) :=
  (Orientation.exists_outdegree_iff_exists_indegree fun d ↦ ∀ x, d x ∈ Set.Icc (a x) (b x)).trans
    (exists_orientation_indegree_mem_Icc_iff hab)

/-- The outdegree form of `Graph.exists_orientation_indegree_le_iff`. -/
theorem exists_orientation_outdegree_le_iff [Finite G.vertexSet] (b : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, o.outdegree x ≤ b x) ↔
      ∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, b x :=
  (Orientation.exists_outdegree_iff_exists_indegree fun d ↦ ∀ x, d x ≤ b x).trans
    (exists_orientation_indegree_le_iff b)

/-- The outdegree form of `Graph.exists_orientation_le_indegree_iff`. -/
theorem exists_orientation_le_outdegree_iff [Finite G.vertexSet] (a : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, a x ≤ o.outdegree x) ↔
      ∀ S : Finset G.vertexSet, ∑ x ∈ S, a x ≤ #(G.incidentEdges S) :=
  (Orientation.exists_outdegree_iff_exists_indegree fun d ↦ ∀ x, a x ≤ d x).trans
    (exists_orientation_le_indegree_iff a)

/-- The outdegree form of Hakimi's theorem `Graph.exists_orientation_indegree_eq_iff`. -/
theorem exists_orientation_outdegree_eq_iff [Fintype G.vertexSet] (d : G.vertexSet → ℕ) :
    (∃ o : Orientation G, ∀ x, o.outdegree x = d x) ↔
      ∑ x, d x = Fintype.card G.edgeSet ∧
        ∀ S : Finset G.vertexSet, #(G.internalEdges S) ≤ ∑ x ∈ S, d x :=
  (Orientation.exists_outdegree_iff_exists_indegree fun d' ↦ ∀ x, d' x = d x).trans
    (exists_orientation_indegree_eq_iff d)

end Graph
