/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.AuxiliaryTerminals.Paths
public import TauCeti.Combinatorics.Network.VertexSplitting

/-!
# Auxiliary terminals after vertex splitting

Vertex splitting turns vertex constraints into arrow constraints, while auxiliary terminals turn
walks between two vertex sets into walks between a single source and sink. This file composes the
two constructions. For terminal sets `A` and `B`, the fresh source is joined to the entrance
`(a, false)` of every `a ∈ A`, and the exit `(b, true)` of every `b ∈ B` is joined to the fresh
sink.

The equivalence `TauCeti.SplitAuxTerminalHom.walkEquiv` identifies source-to-sink walks in the
combined family with original walks whose first endpoint lies in `A` and last endpoint lies in
`B`. It preserves and reflects paths. More importantly for vertex-disjoint path problems, two
combined lifts are internally disjoint exactly when the vertex lists of their original walks are
disjoint, including their endpoints. The same characterization is provided for indexed families.
Zero-length original paths at a vertex of `A ∩ B` are included; their combined lift crosses that
vertex's split arrow.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

namespace TauCeti

open Finset Sum

universe u v w

variable {V : Type u} {Q : V → V → Type v} {A B : Finset V}

namespace SplitAuxTerminalHom

/-- The entrances of the vertices in `A`. -/
def entrances (A : Finset V) : Finset (V × Bool) :=
  A.map (Function.Embedding.sectL V false)

/-- The exits of the vertices in `B`. -/
def exits (B : Finset V) : Finset (V × Bool) :=
  B.map (Function.Embedding.sectL V true)

@[simp]
theorem mem_entrances {x : V × Bool} : x ∈ entrances A ↔ x.1 ∈ A ∧ x.2 = false := by
  simp [entrances, Prod.ext_iff, and_comm]

@[simp]
theorem mem_exits {x : V × Bool} : x ∈ exits B ↔ x.1 ∈ B ∧ x.2 = true := by
  simp [exits, Prod.ext_iff, and_comm]

/-- The vertices in `A` are equivalent to their entrances in the split network. -/
def entranceEquiv (A : Finset V) : A ≃ entrances A where
  toFun a := ⟨((a : V), false), by simp⟩
  invFun x := ⟨x.val.1, (mem_entrances.mp x.property).1⟩
  left_inv _ := Subtype.ext rfl
  right_inv x := Subtype.ext (Prod.ext rfl (mem_entrances.mp x.property).2.symm)

/-- The vertices in `B` are equivalent to their exits in the split network. -/
def exitEquiv (B : Finset V) : B ≃ exits B where
  toFun b := ⟨((b : V), true), by simp⟩
  invFun x := ⟨x.val.1, (mem_exits.mp x.property).1⟩
  left_inv _ := Subtype.ext rfl
  right_inv x := Subtype.ext (Prod.ext rfl (mem_exits.mp x.property).2.symm)

@[simp]
theorem coe_entranceEquiv_apply (a : A) :
    (entranceEquiv A a : V × Bool) = ((a : V), false) :=
  (rfl)

@[simp]
theorem coe_exitEquiv_apply (b : B) :
    (exitEquiv B b : V × Bool) = ((b : V), true) :=
  (rfl)

end SplitAuxTerminalHom

/-- The arrow family obtained by splitting every vertex and then adding a fresh source joined to
the entrances of `A` and a fresh sink joined from the exits of `B`. -/
abbrev SplitAuxTerminalHom (Q : V → V → Type v) (A B : Finset V) :
    (V × Bool) ⊕ Bool → (V × Bool) ⊕ Bool → Type v :=
  AuxTerminalHom (SplitHom Q) (SplitAuxTerminalHom.entrances A)
    (SplitAuxTerminalHom.exits B)

namespace SplitAuxTerminalHom

/-! ### Capacities and cuts -/

/-- Capacities on the combined arrow family: `cap` on original arrows, `c` on split arrows,
`cσ` on arrows from the fresh source and `cτ` on arrows to the fresh sink. -/
def capacity {K : Type w} (cap : Assignment Q K) (c cσ cτ : V → K) :
    Assignment (SplitAuxTerminalHom Q A B) K :=
  auxTerminalCapacity (SplitHom.assignment cap c) (fun x ↦ cσ x.1) fun x ↦ cτ x.1

@[simp]
theorem capacity_original {K : Type w} (cap : Assignment Q K) (c cσ cτ : V → K)
    {x y : V} (e : Q x y) :
    capacity (A := A) (B := B) cap c cσ cτ
        (AuxTerminalHom.original (SplitHom.original e)) = cap e :=
  by rw [capacity, auxTerminalCapacity_original, SplitHom.assignment_original]

@[simp]
theorem capacity_split {K : Type w} (cap : Assignment Q K) (c cσ cτ : V → K) (x : V) :
    capacity (A := A) (B := B) cap c cσ cτ
        (AuxTerminalHom.original (SplitHom.split x)) = c x :=
  by rw [capacity, auxTerminalCapacity_original, SplitHom.assignment_split]

@[simp]
theorem capacity_source {K : Type w} (cap : Assignment Q K) (c cσ cτ : V → K)
    {x : V × Bool} (hx : x ∈ entrances A) :
    capacity (B := B) cap c cσ cτ (AuxTerminalHom.source hx) = cσ x.1 :=
  by rw [capacity, auxTerminalCapacity_source]

@[simp]
theorem capacity_sink {K : Type w} (cap : Assignment Q K) (c cσ cτ : V → K)
    {x : V × Bool} (hx : x ∈ exits B) :
    capacity (A := A) cap c cσ cτ (AuxTerminalHom.sink hx) = cτ x.1 :=
  by rw [capacity, auxTerminalCapacity_sink]

/-- Combined capacities are nonnegative when all capacities that occur on their arrows are
nonnegative. -/
theorem capacity_nonneg [Zero K] [Preorder K] {cap : Assignment Q K} {c cσ cτ : V → K}
    (hcap : 0 ≤ cap) (hc : 0 ≤ c) (hσ : ∀ a ∈ A, 0 ≤ cσ a)
    (hτ : ∀ b ∈ B, 0 ≤ cτ b) :
    0 ≤ capacity (Q := Q) (A := A) (B := B) cap c cσ cτ := by
  apply auxTerminalCapacity_nonneg
  · rw [← SplitHom.assignment_zero, SplitHom.assignment_le_assignment_iff]
    exact ⟨hcap, hc⟩
  · intro x hx
    exact hσ x.1 (mem_entrances.mp hx).1
  · intro x hx
    exact hτ x.1 (mem_exits.mp hx).1

/-- **Cuts after splitting and adjoining auxiliary terminals.** A source-to-sink cut pays for the
source arrows to omitted entrances, the sink arrows from included exits, the split arrows crossing
the cut, and the original arrows crossing the cut. -/
theorem arrowSum_capacity [AddCommMonoid K] [Fintype V] [DecidableEq V]
    [∀ x y, Fintype (Q x y)] (cap : Assignment Q K) (c cσ cτ : V → K)
    {S : Finset ((V × Bool) ⊕ Bool)} (hσ : inr false ∈ S) (hτ : inr true ∉ S) :
    arrowSum (capacity (A := A) (B := B) cap c cσ cτ) S Sᶜ =
      ∑ x ∈ entrances A \ S.toLeft, cσ x.1 +
        ∑ x ∈ exits B ∩ S.toLeft, cτ x.1 +
          (∑ x ∈ SplitHom.cutVertices S.toLeft, c x +
            ∑ e ∈ SplitHom.cutArrows Q S.toLeft, cap e.2.2) := by
  rw [capacity, arrowSum_auxTerminalCapacity _ _ _ hσ hτ,
    SplitHom.arrowSum_assignment_compl]

/-! ### Paths -/

/-- Endpoint-indexed walks in `Q` correspond to walks between the selected entrances and exits in
the split arrow family. -/
noncomputable def splitWalkEquiv (Q : V → V → Type v) (A B : Finset V) :
    (Σ a : A, Σ b : B, ArrowWalk Q a b) ≃
      (Σ a : entrances A, Σ b : exits B, ArrowWalk (SplitHom Q) a b) where
  toFun p :=
    ⟨⟨((p.1 : V), false), by simp⟩, ⟨((p.2.1 : V), true), by simp⟩,
      p.2.2.splitLift true⟩
  invFun p :=
    ⟨⟨p.1.val.1, (mem_entrances.mp p.1.property).1⟩,
      ⟨p.2.1.val.1, (mem_exits.mp p.2.1.property).1⟩, p.2.2.splitProj⟩
  left_inv p := by
    rcases p with ⟨⟨a, ha⟩, ⟨⟨b, hb⟩, p⟩⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨⟨a, c⟩, ha⟩, ⟨⟨⟨b, d⟩, hb⟩, p⟩⟩
    have hc : c = false := (mem_entrances.mp ha).2
    have hd : d = true := (mem_exits.mp hb).2
    subst c
    subst d
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact ArrowWalk.splitLift_splitProj p

/-- Walks from `A` to `B` in the original arrow family correspond to walks from the fresh source
to the fresh sink after vertex splitting and adjoining auxiliary terminals. -/
noncomputable def walkEquiv (Q : V → V → Type v) (A B : Finset V) :
    (Σ a : A, Σ b : B, ArrowWalk Q a b) ≃
      ArrowWalk (SplitAuxTerminalHom Q A B) (inr false) (inr true) :=
  (splitWalkEquiv Q A B).trans
    (AuxTerminalHom.walkEquiv (SplitHom Q) (entrances A) (exits B))

/-- Lift an original walk from `a ∈ A` to `b ∈ B` through vertex splitting and the auxiliary
terminals. -/
noncomputable def lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    ArrowWalk (SplitAuxTerminalHom Q A B) (inr false) (inr true) :=
  walkEquiv Q A B ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩

@[simp]
theorem walkEquiv_apply (p : Σ a : A, Σ b : B, ArrowWalk Q a b) :
    walkEquiv Q A B p =
      AuxTerminalHom.lift
        (show ((p.1 : V), false) ∈ entrances A by simp)
        (show ((p.2.1 : V), true) ∈ exits B by simp)
        (p.2.2.splitLift true) := by
  rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩
  rw [walkEquiv, Equiv.trans_apply, AuxTerminalHom.walkEquiv_apply]
  rfl

/-- The inverse correspondence first removes the auxiliary arrows and then forgets the split
arrows. -/
theorem walkEquiv_symm_apply
    (p : ArrowWalk (SplitAuxTerminalHom Q A B) (inr false) (inr true)) :
    (walkEquiv Q A B).symm p =
      let P := AuxTerminalHom.project p
      ⟨⟨P.source.1, (mem_entrances.mp P.source_mem).1⟩,
        ⟨P.target.1, (mem_exits.mp P.target_mem).1⟩, P.walk.splitProj⟩ := by
  rw [walkEquiv, Equiv.symm_trans_apply, AuxTerminalHom.walkEquiv_symm_apply]
  rfl

/-- The combined lift is the auxiliary-terminal lift of the vertex-split walk. -/
theorem lift_eq {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    lift ha hb p =
      AuxTerminalHom.lift
        (show (a, false) ∈ entrances A by simpa using ha)
        (show (b, true) ∈ exits B by simpa using hb) (p.splitLift true) := by
  rw [lift, walkEquiv_apply]

/-- Combined lifting is injective for fixed original endpoints. -/
theorem lift_injective {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    Function.Injective (lift (Q := Q) ha hb) := by
  intro p q h
  have h' := (walkEquiv Q A B).injective h
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h'

@[simp]
theorem lift_inj {a b : V} (ha : a ∈ A) (hb : b ∈ B) {p q : ArrowWalk Q a b} :
    lift ha hb p = lift ha hb q ↔ p = q :=
  (lift_injective ha hb).eq_iff

/-- The vertex list of a combined lift consists of the fresh source, both copies of every original
vertex in order, and the fresh sink. -/
theorem vertices_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (lift ha hb p).vertices =
      inr false :: (p.vertices.flatMap fun x ↦ [(x, false), (x, true)]).map inl ++ [inr true] := by
  rw [lift_eq, AuxTerminalHom.vertices_lift, ArrowWalk.vertices_splitLift_true]

/-- A split copy of `x` lies on the combined lift exactly when `x` lies on the original walk. -/
@[simp]
theorem inl_mk_mem_vertices_lift {a b x : V} (c : Bool) (ha : a ∈ A) (hb : b ∈ B)
    (p : ArrowWalk Q a b) :
    inl (x, c) ∈ (lift ha hb p).vertices ↔ x ∈ p.vertices := by
  rw [lift_eq, AuxTerminalHom.vertices_lift]
  simp

/-- The combined lift adds both split copies of every vertex and the two auxiliary terminals. -/
@[simp]
theorem length_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (lift ha hb p).length = 2 * p.length + 3 := by
  rw [lift_eq, AuxTerminalHom.length_lift, ArrowWalk.length_splitLift]
  simp

/-- Combined lifting preserves and reflects paths. -/
@[simp]
theorem isPath_lift {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (lift ha hb p).IsPath ↔ p.IsPath := by
  rw [lift_eq, AuxTerminalHom.isPath_lift, ArrowWalk.isPath_splitLift]

/-- Two combined lifts are internally disjoint exactly when their original vertex lists are
disjoint. In particular, original endpoints may not be shared. -/
theorem internallyDisjoint_lift_iff {a b c d : V} (ha : a ∈ A) (hb : b ∈ B)
    (hc : c ∈ A) (hd : d ∈ B) (p : ArrowWalk Q a b) (q : ArrowWalk Q c d) :
    (lift ha hb p).InternallyDisjoint (lift hc hd q) ↔ p.vertices.Disjoint q.vertices := by
  constructor
  · intro h
    rw [List.disjoint_left]
    intro x hxp hxq
    have hx := ArrowWalk.internallyDisjoint_def.1 h (inl (x, false))
      ((inl_mk_mem_vertices_lift false ha hb p).2 hxp)
      ((inl_mk_mem_vertices_lift false hc hd q).2 hxq)
    exact hx.elim Sum.inl_ne_inr Sum.inl_ne_inr
  · intro h
    rw [ArrowWalk.internallyDisjoint_def]
    rintro (x | (_ | _)) hx hy
    · exact ((List.disjoint_left.mp h)
        ((inl_mk_mem_vertices_lift x.2 ha hb p).1 hx)
        ((inl_mk_mem_vertices_lift x.2 hc hd q).1 hy)).elim
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- A family of combined lifts is pairwise internally disjoint exactly when the corresponding
original walks have pairwise disjoint vertex lists. -/
theorem pairwise_internallyDisjoint_lift_iff {I : Type*} {a b : I → V}
    (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B) (P : ∀ i, ArrowWalk Q (a i) (b i)) :
    (Pairwise fun i j ↦ (lift (ha i) (hb i) (P i)).InternallyDisjoint
      (lift (ha j) (hb j) (P j))) ↔
      Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices := by
  simp only [internallyDisjoint_lift_iff]

end SplitAuxTerminalHom

end TauCeti
