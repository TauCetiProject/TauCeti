/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.FreeGGroup
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Makanin–Razborov diagrams

A Makanin–Razborov diagram (a `Hom`-diagram) describes the set of homomorphisms from a group to a
free group by a finite rooted tree. Every vertex carries a group and a group of automorphisms of
it, its *modular group*; every edge carries a homomorphism from the group of its source to the
group of its target; the leaves carry free groups. A branch from the root to a leaf, a choice of
a modular automorphism `σᵢ` at each of its vertices and a homomorphism `ψ` from its leaf to the
target determine the composite `ψ ∘ πₖ ∘ σₖ ∘ ⋯ ∘ π₁ ∘ σ₁ ∘ π₀ ∘ σ₀`, where the `πᵢ` are the
edge homomorphisms. The diagram is *complete* when every homomorphism from the root group to the
target is such a composite.

Everything is done over a group `A` of coefficients: the vertex groups receive `A`, and the edge
homomorphisms, the modular automorphisms and the homomorphisms out of the leaves are
`A`-homomorphisms; the leaves are free `A`-groups `A ∗ F(Y)`. For `A = F` this is the diagram of
the `F`-homomorphisms to `F`, that is, of the solutions in `F` of a system of equations with
coefficients in `F`; over trivial coefficients it is the diagram of all homomorphisms, with free
leaves.

The modular groups are data of the diagram: nothing here refers to JSJ decompositions, which are
what supplies them in the canonical diagrams of a finitely generated group. A vertex with no
outgoing edge which is not a leaf carries no branch; a root of this kind is the diagram of a
system without solutions.

## Main definitions

* `TauCeti.LimitGroup.MRDiagram ι`: the diagrams whose root group receives the coefficients
  through `ι`.
* `TauCeti.LimitGroup.MRDiagram.modular`: the modular group of the root.
* `TauCeti.LimitGroup.MRDiagram.branchHoms`: the set of composites along the branches.
* `TauCeti.LimitGroup.MRDiagram.IsComplete`: every `A`-homomorphism to the target is a branch
  composite.
* `TauCeti.LimitGroup.MRDiagram.IsSound`: every branch composite sends a given tuple of the root
  group to a solution of a given system.
* `TauCeti.LimitGroup.MRDiagram.HasProperQuotients`: the edges below the root are proper
  epimorphisms.
* `TauCeti.LimitGroup.MRDiagram.edge`, `TauCeti.LimitGroup.MRDiagram.empty`,
  `TauCeti.LimitGroup.MRDiagram.freeRoot`: a root with one outgoing edge, the diagram without
  branches, and the one-edge diagram of a free `A`-group.

## Main results

* `TauCeti.LimitGroup.MRDiagram.exists_mem_branchHoms_node`: every choice of an edge at the root,
  a modular automorphism and a branch composite below is realised by a branch composite.
* `TauCeti.LimitGroup.MRDiagram.isSound_node`, `TauCeti.LimitGroup.MRDiagram.isSound_edge`: a
  vertex is sound exactly when its subdiagrams are sound at the transported tuples.
* `TauCeti.LimitGroup.MRDiagram.isComplete_node_iff_of_forall_isComplete`: a vertex with complete
  subdiagrams is complete exactly when every `A`-homomorphism factors through one step of it.
* `TauCeti.LimitGroup.MRDiagram.isComplete_iff_of_subsingleton`: over trivial coefficients,
  completeness concerns all homomorphisms from the root group to the target.
* `TauCeti.LimitGroup.MRDiagram.isComplete_freeRoot`: the one-edge diagram of a free `A`-group is
  complete.
* `TauCeti.LimitGroup.MRDiagram.isComplete_empty_iff`: the diagram without branches is complete
  exactly when there is no `A`-homomorphism to the target.
* `TauCeti.LimitGroup.MRDiagram.not_hasProperEdges_edge_of_injective`: an edge labelled by an
  isomorphism is not a proper quotient.
* `TauCeti.LimitGroup.MRDiagram.isSound_coordGroup`,
  `TauCeti.LimitGroup.MRDiagram.isComplete_coordGroup_iff`: a diagram of the coordinate group of a
  system is sound for that system, and it is complete exactly when every solution of the system is
  the value of a branch composite on the variables; likewise for the group presented by the system.

## References

* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, in: Groups, Languages,
  Algorithms, Contemp. Math. 378 (2005), §11.1 (hom-diagrams, their branches and fundamental
  sequences, completeness) and Theorems 11.1–11.3.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.6, Theorem 7.
* Z. Sela, *Diophantine geometry over groups I: Makanin–Razborov diagrams*, Publ. Math. IHÉS 93
  (2001), §5.
-/

public section

namespace TauCeti.LimitGroup

open GroupAlgGeom Monoid.Coprod

universe u v w

/-- A Makanin–Razborov diagram (a `Hom`-diagram) over the coefficient group `A`, rooted at a group
`H` receiving the coefficients through `ι`. It is a finite rooted tree: a vertex is either a leaf,
whose group is a free `A`-group, or carries a modular group of automorphisms fixing the
coefficients and finitely many outgoing edges, each labelled by an `A`-homomorphism to the group
at the root of a subdiagram. -/
inductive MRDiagram {A : Type v} [Group A] :
    {H : Type u} → [Group H] → (A →* H) → Type (max (u + 1) v)
  /-- A leaf: its group is a free `A`-group. -/
  | leaf {H : Type u} [Group H] {ι : A →* H} (free : IsFreeGGroup ι) : MRDiagram ι
  /-- A vertex with modular group `M` and with `n` outgoing edges, the `i`-th one labelled by the
  `A`-homomorphism `π i` to the root group of the subdiagram `child i`. -/
  | node {H : Type u} [Group H] {ι : A →* H} (M : Subgroup (MulAut H))
      (hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)) {n : ℕ} {K : Fin n → Type u}
      [∀ i, Group (K i)] {κ : ∀ i, A →* K i} (π : ∀ i, GHom ι (κ i))
      (child : ∀ i, MRDiagram (κ i)) : MRDiagram ι

namespace MRDiagram

variable {A : Type v} [Group A] {H : Type u} [Group H] {ι : A →* H}
  {L : Type w} [Group L] (ιL : A →* L)

/-! ### The modular group of the root -/

/-- The modular group of the root of a diagram. A leaf carries none: its homomorphisms to the
target are unconstrained. -/
def modular : MRDiagram ι → Subgroup (MulAut H)
  | leaf _ => ⊥
  | node M _ _ _ => M

@[simp]
theorem modular_leaf (free : IsFreeGGroup ι) : (leaf free).modular = ⊥ := (rfl)

@[simp]
theorem modular_node (M : Subgroup (MulAut H)) (hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι))
    {n : ℕ} {K : Fin n → Type u} [∀ i, Group (K i)] {κ : ∀ i, A →* K i}
    (π : ∀ i, GHom ι (κ i)) (child : ∀ i, MRDiagram (κ i)) :
    (node M hM π child).modular = M := (rfl)

/-- Modular automorphisms fix the coefficients. -/
theorem modular_le_fixingSubgroup (D : MRDiagram ι) :
    D.modular ≤ fixingSubgroup (MulAut H) (Set.range ι) := by
  cases D with
  | leaf _ => simp
  | node M hM π child => exact hM

/-- Modular automorphisms fix the coefficients. -/
theorem apply_coeff_of_mem_modular (D : MRDiagram ι) {σ : MulAut H} (hσ : σ ∈ D.modular) (a : A) :
    σ (ι a) = ι a :=
  (mem_fixingSubgroup_iff _).1 (D.modular_le_fixingSubgroup hσ) _ ⟨a, rfl⟩

/-! ### Branch composites -/

/-- The homomorphisms to the target determined by a diagram: the composites
`ψ ∘ πₖ ∘ σₖ ∘ ⋯ ∘ π₀ ∘ σ₀` along a branch from the root to a leaf, where `σᵢ` is a modular
automorphism of the `i`-th vertex of the branch, `πᵢ` is the homomorphism of its `i`-th edge and
`ψ` is an `A`-homomorphism from the group of its leaf to the target. -/
def branchHoms : ∀ {H : Type u} [Group H] {ι : A →* H}, MRDiagram ι → Set (GHom ι ιL)
  | _, _, _, leaf _ => Set.univ
  | _, _, _, node M _ π child =>
    {φ | ∃ i, ∃ σ ∈ M, ∃ ψ ∈ branchHoms (child i), ∀ x, φ x = ψ (π i (σ x))}

/-- Every `A`-homomorphism from the group of a leaf is a branch composite. -/
@[simp]
theorem branchHoms_leaf (free : IsFreeGGroup ι) : (leaf free).branchHoms ιL = Set.univ := (rfl)

variable {ιL}

/-- The branch composites of a vertex with outgoing edges: a modular automorphism of the vertex,
followed by the homomorphism of an edge and by a branch composite of the subdiagram at its end. -/
@[simp]
theorem mem_branchHoms_node {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} {φ : GHom ι ιL} :
    φ ∈ (node M hM π child).branchHoms ιL ↔
      ∃ i, ∃ σ ∈ M, ∃ ψ ∈ (child i).branchHoms ιL, ∀ x, φ x = ψ (π i (σ x)) :=
  Iff.rfl

/-- Every choice of an edge at the root, of a modular automorphism of the root and of a branch
composite of the subdiagram at the end of the edge is realised by a branch composite. -/
theorem exists_mem_branchHoms_node {M : Subgroup (MulAut H)}
    (hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)) {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} (π : ∀ i, GHom ι (κ i))
    (child : ∀ i, MRDiagram (κ i)) (i : Fin n) {σ : MulAut H} (hσ : σ ∈ M)
    {ψ : GHom (κ i) ιL} (hψ : ψ ∈ (child i).branchHoms ιL) :
    ∃ φ ∈ (node M hM π child).branchHoms ιL, ∀ x, φ x = ψ (π i (σ x)) := by
  refine ⟨⟨((ψ : K i →* L).comp (π i : H →* K i)).comp σ.toMonoidHom, fun a => ?_⟩,
    mem_branchHoms_node.2 ⟨i, σ, hσ, ψ, hψ, fun x => rfl⟩, fun x => rfl⟩
  simp [(node M hM π child).apply_coeff_of_mem_modular hσ a]

/-- A vertex without outgoing edges which is not a leaf carries no branch composite. -/
@[simp]
theorem branchHoms_node_zero (M : Subgroup (MulAut H))
    (hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)) {K : Fin 0 → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} (π : ∀ i, GHom ι (κ i))
    (child : ∀ i, MRDiagram (κ i)) : (node M hM π child).branchHoms ιL = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => (mem_branchHoms_node.1 h).choose.elim0

/-! ### Completeness and soundness -/

variable (ιL) in
/-- A diagram is *complete* for the target `L` when every `A`-homomorphism from its root group
to `L` is a branch composite. -/
def IsComplete (D : MRDiagram ι) : Prop :=
  ∀ φ : GHom ι ιL, φ ∈ D.branchHoms ιL

theorem isComplete_iff {D : MRDiagram ι} :
    D.IsComplete ιL ↔ ∀ φ : GHom ι ιL, φ ∈ D.branchHoms ιL :=
  Iff.rfl

theorem isComplete_iff_branchHoms_eq_univ {D : MRDiagram ι} :
    D.IsComplete ιL ↔ D.branchHoms ιL = Set.univ :=
  Set.eq_univ_iff_forall.symm

/-- A leaf is complete. -/
@[simp]
theorem isComplete_leaf (free : IsFreeGGroup ι) : (leaf free).IsComplete ιL :=
  fun _ => Set.mem_univ _

/-- Over trivial coefficients every homomorphism is an `A`-homomorphism: a diagram is complete
exactly when every homomorphism from its root group to the target is a branch composite. -/
theorem isComplete_iff_of_subsingleton [Subsingleton A] {D : MRDiagram ι} :
    D.IsComplete ιL ↔ ∀ φ : H →* L, ∃ ψ ∈ D.branchHoms ιL, (ψ : H →* L) = φ := by
  refine ⟨fun h φ => ⟨⟨φ, fun a => by simp [Subsingleton.elim a 1]⟩, h _, rfl⟩, fun h φ => ?_⟩
  obtain ⟨ψ, hψ, hψφ⟩ := h φ
  rwa [GHom.toMonoidHom_injective hψφ] at hψ

variable (ιL) in
/-- A diagram is *sound* for the system `S` of equations at the tuple `x` of its root group when
every branch composite sends `x` to a solution of `S` in the target. -/
def IsSound {X : Type*} (D : MRDiagram ι) (S : Set (GX A X)) (x : X → H) : Prop :=
  ∀ φ ∈ D.branchHoms ιL, (fun i => φ (x i)) ∈ V ιL S

theorem isSound_iff {X : Type*} {D : MRDiagram ι} {S : Set (GX A X)} {x : X → H} :
    D.IsSound ιL S x ↔ ∀ φ ∈ D.branchHoms ιL, (fun i => φ (x i)) ∈ V ιL S :=
  Iff.rfl

/-- A diagram sound for a system is sound for every subsystem. -/
theorem IsSound.mono {X : Type*} {D : MRDiagram ι} {S T : Set (GX A X)} {x : X → H}
    (h : D.IsSound ιL S x) (hTS : T ⊆ S) : D.IsSound ιL T x :=
  fun φ hφ => V_antitone ιL hTS (h φ hφ)

/-- A leaf is sound for a system at a tuple exactly when every `A`-homomorphism from its group to
the target sends the tuple to a solution. -/
@[simp]
theorem isSound_leaf {X : Type*} (free : IsFreeGGroup ι) {S : Set (GX A X)} {x : X → H} :
    (leaf free).IsSound ιL S x ↔ ∀ φ : GHom ι ιL, (fun i => φ (x i)) ∈ V ιL S := by
  simp [isSound_iff]

/-- A vertex is sound for a system at a tuple exactly when, for every outgoing edge and every
modular automorphism `σ`, the subdiagram at the end of the edge is sound at the image of the tuple
under `σ` followed by the edge homomorphism. -/
@[simp]
theorem isSound_node {X : Type*} {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} {S : Set (GX A X)} {x : X → H} :
    (node M hM π child).IsSound ιL S x ↔
      ∀ i, ∀ σ ∈ M, (child i).IsSound ιL S fun j => π i (σ (x j)) := by
  refine ⟨fun h i σ hσ ψ hψ => ?_, fun h φ hφ => ?_⟩
  · obtain ⟨φ, hφ, hφψ⟩ := exists_mem_branchHoms_node hM π child i hσ hψ
    simpa [hφψ] using h φ hφ
  · obtain ⟨i, σ, hσ, ψ, hψ, hφψ⟩ := mem_branchHoms_node.1 hφ
    simpa [hφψ] using h i σ hσ ψ hψ

/-! ### Diagrams with one edge at the root, and the diagram without branches -/

section edge

variable {K : Type u} [Group K] {κ : A →* K}

/-- The diagram whose root has modular group `M` and a single outgoing edge, labelled `π`, to the
root of the diagram `D`. -/
def edge (M : Subgroup (MulAut H)) (hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι))
    (π : GHom ι κ) (D : MRDiagram κ) : MRDiagram ι :=
  node M hM (n := 1) (fun _ => π) fun _ => D

variable {M : Subgroup (MulAut H)} {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)}
  {π : GHom ι κ} {D : MRDiagram κ}

theorem edge_def : edge M hM π D = node M hM (n := 1) (fun _ => π) fun _ => D := (rfl)

@[simp]
theorem modular_edge : (edge M hM π D).modular = M := (rfl)

/-- The branch composites of a diagram with one edge at the root: a modular automorphism of the
root, followed by the edge homomorphism and by a branch composite of the subdiagram. -/
@[simp]
theorem mem_branchHoms_edge {φ : GHom ι ιL} :
    φ ∈ (edge M hM π D).branchHoms ιL ↔
      ∃ σ ∈ M, ∃ ψ ∈ D.branchHoms ιL, ∀ x, φ x = ψ (π (σ x)) :=
  mem_branchHoms_node.trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

/-- Every choice of a modular automorphism of the root and of a branch composite of the
subdiagram is realised by a branch composite of a diagram with one edge at the root. -/
theorem exists_mem_branchHoms_edge {σ : MulAut H} (hσ : σ ∈ M) {ψ : GHom κ ιL}
    (hψ : ψ ∈ D.branchHoms ιL) : ∃ φ ∈ (edge M hM π D).branchHoms ιL, ∀ x, φ x = ψ (π (σ x)) :=
  exists_mem_branchHoms_node hM (fun _ => π) (fun _ => D) 0 hσ hψ

/-- A diagram with one edge at the root is sound for a system at a tuple exactly when, for every
modular automorphism `σ` of the root, the subdiagram is sound at the image of the tuple under `σ`
followed by the edge homomorphism. -/
@[simp]
theorem isSound_edge {X : Type*} {S : Set (GX A X)} {x : X → H} :
    (edge M hM π D).IsSound ιL S x ↔ ∀ σ ∈ M, D.IsSound ιL S fun j => π (σ (x j)) :=
  isSound_node.trans ⟨fun h => h 0, fun h _ => h⟩

end edge

/-- A vertex whose subdiagrams are complete is complete exactly when every `A`-homomorphism from
its group to the target factors as a modular automorphism, followed by the homomorphism of an
outgoing edge and by an `A`-homomorphism out of the group at the end of that edge. -/
theorem isComplete_node_iff_of_forall_isComplete {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} (hchild : ∀ i, (child i).IsComplete ιL) :
    (node M hM π child).IsComplete ιL ↔
      ∀ φ : GHom ι ιL, ∃ i, ∃ σ ∈ M, ∃ ψ : GHom (κ i) ιL, ∀ x, φ x = ψ (π i (σ x)) := by
  simp only [isComplete_iff, mem_branchHoms_node]
  exact forall_congr' fun _ => exists_congr fun i => exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun ⟨ψ, _, h⟩ => ⟨ψ, h⟩, fun ⟨ψ, h⟩ => ⟨ψ, hchild i ψ, h⟩⟩

/-- A diagram with one edge at the root, whose subdiagram is complete, is complete exactly when
every `A`-homomorphism from the root group to the target factors as a modular automorphism,
followed by the edge homomorphism and by an `A`-homomorphism out of the group at its end. -/
theorem isComplete_edge_iff_of_isComplete {K : Type u} [Group K] {κ : A →* K}
    {M : Subgroup (MulAut H)} {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {π : GHom ι κ}
    {D : MRDiagram κ} (hD : D.IsComplete ιL) :
    (edge M hM π D).IsComplete ιL ↔
      ∀ φ : GHom ι ιL, ∃ σ ∈ M, ∃ ψ : GHom κ ιL, ∀ x, φ x = ψ (π (σ x)) :=
  (isComplete_node_iff_of_forall_isComplete fun _ => hD).trans
    (forall_congr' fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩)

/-- An identity edge without modular automorphisms does not change the branch composites. -/
@[simp]
theorem branchHoms_edge_bot_id (D : MRDiagram ι) :
    (edge ⊥ bot_le (GHom.id ι) D).branchHoms ιL = D.branchHoms ιL := by
  ext φ
  refine mem_branchHoms_edge.trans ⟨fun ⟨σ, hσ, ψ, hψ, h⟩ => ?_,
    fun h => ⟨1, Subgroup.mem_bot.2 rfl, φ, h, fun _ => by simp⟩⟩
  obtain rfl := Subgroup.mem_bot.1 hσ
  exact (GHom.ext fun x => by simpa using h x) ▸ hψ

/-- An identity edge without modular automorphisms does not change completeness. -/
@[simp]
theorem isComplete_edge_bot_id_iff {D : MRDiagram ι} :
    (edge ⊥ bot_le (GHom.id ι) D).IsComplete ιL ↔ D.IsComplete ιL := by
  simp [isComplete_iff_branchHoms_eq_univ]

variable (ι) in
/-- The diagram without branches: its root has no outgoing edge and is not a leaf. It is the
diagram of a system of equations without solutions. -/
protected def empty : MRDiagram ι :=
  node ⊥ bot_le (n := 0) (K := fun _ => PUnit) (κ := fun _ => 1) (fun i => i.elim0)
    fun i => i.elim0

theorem empty_def :
    MRDiagram.empty ι = node ⊥ bot_le (n := 0) (K := fun _ => PUnit) (κ := fun _ => 1)
      (fun i => i.elim0) fun i => i.elim0 :=
  (rfl)

@[simp]
theorem modular_empty : (MRDiagram.empty ι).modular = ⊥ := (rfl)

/-- The diagram without branches has no branch composite. -/
@[simp]
theorem branchHoms_empty : (MRDiagram.empty ι).branchHoms ιL = ∅ :=
  branchHoms_node_zero ..

/-- The diagram without branches is complete exactly when there is no `A`-homomorphism from its
root group to the target. -/
@[simp]
theorem isComplete_empty_iff : (MRDiagram.empty ι).IsComplete ιL ↔ IsEmpty (GHom ι ιL) := by
  simp [isComplete_iff, isEmpty_iff]

/-- The diagram without branches is sound for every system. -/
@[simp]
theorem isSound_empty {X : Type*} (S : Set (GX A X)) (x : X → H) :
    (MRDiagram.empty ι).IsSound ιL S x :=
  fun _ h => by simp at h

/-- The one-edge diagram of a free `A`-group: the identity edge from the root to a leaf carrying
the same group. -/
def freeRoot (free : IsFreeGGroup ι) : MRDiagram ι :=
  edge ⊥ bot_le (GHom.id ι) (leaf free)

theorem freeRoot_def (free : IsFreeGGroup ι) :
    freeRoot free = edge ⊥ bot_le (GHom.id ι) (leaf free) :=
  (rfl)

@[simp]
theorem modular_freeRoot (free : IsFreeGGroup ι) : (freeRoot free).modular = ⊥ := (rfl)

/-- Every `A`-homomorphism from a free `A`-group is a branch composite of its one-edge diagram. -/
@[simp]
theorem branchHoms_freeRoot (free : IsFreeGGroup ι) :
    (freeRoot free).branchHoms ιL = Set.univ :=
  (branchHoms_edge_bot_id _).trans (branchHoms_leaf ιL free)

/-- The one-edge diagram of a free `A`-group is complete. -/
@[simp]
theorem isComplete_freeRoot (free : IsFreeGGroup ι) : (freeRoot free).IsComplete ιL :=
  isComplete_iff_branchHoms_eq_univ.2 (branchHoms_freeRoot free)

/-- Over trivial coefficients, every homomorphism from a free group `H` to the target is a branch
composite of the one-edge diagram from `H` to the leaf `H`. -/
theorem exists_mem_branchHoms_freeRoot_eq [Subsingleton A] [IsFreeGroup H] (φ : H →* L) :
    ∃ ψ ∈ (freeRoot (IsFreeGGroup.of_subsingleton ι)).branchHoms ιL, (ψ : H →* L) = φ :=
  isComplete_iff_of_subsingleton.1 (isComplete_freeRoot _) φ

/-! ### Proper quotients -/

/-- Every edge of the diagram is labelled by a proper epimorphism: a surjective homomorphism
which is not injective. -/
def HasProperEdges : ∀ {H : Type u} [Group H] {ι : A →* H}, MRDiagram ι → Prop
  | _, _, _, leaf _ => True
  | _, _, _, node _ _ π child =>
    ∀ i, Function.Surjective (π i) ∧ ¬Function.Injective (π i) ∧ HasProperEdges (child i)

@[simp]
theorem hasProperEdges_leaf (free : IsFreeGGroup ι) : (leaf free).HasProperEdges :=
  trivial

@[simp]
theorem hasProperEdges_node {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} :
    (node M hM π child).HasProperEdges ↔ ∀ i, Function.Surjective (π i) ∧
      ¬Function.Injective (π i) ∧ (child i).HasProperEdges :=
  Iff.rfl

/-- The edges below the root are labelled by proper epimorphisms; the edges issuing from the
root are arbitrary homomorphisms. -/
def HasProperQuotients : MRDiagram ι → Prop
  | leaf _ => True
  | node _ _ _ child => ∀ i, (child i).HasProperEdges

@[simp]
theorem hasProperQuotients_leaf (free : IsFreeGGroup ι) : (leaf free).HasProperQuotients :=
  trivial

@[simp]
theorem hasProperQuotients_node {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} :
    (node M hM π child).HasProperQuotients ↔ ∀ i, (child i).HasProperEdges :=
  Iff.rfl

/-- A diagram all of whose edges are proper epimorphisms has proper quotients below the root. -/
theorem HasProperEdges.hasProperQuotients {D : MRDiagram ι} (h : D.HasProperEdges) :
    D.HasProperQuotients := by
  cases D with
  | leaf _ => trivial
  | node M hM π child => exact fun i => (hasProperEdges_node.1 h i).2.2

section edge

variable {K : Type u} [Group K] {κ : A →* K} {M : Subgroup (MulAut H)}
  {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {π : GHom ι κ} {D : MRDiagram κ}

@[simp]
theorem hasProperEdges_edge :
    (edge M hM π D).HasProperEdges ↔
      Function.Surjective π ∧ ¬Function.Injective π ∧ D.HasProperEdges :=
  hasProperEdges_node.trans ⟨fun h => h 0, fun h _ => h⟩

@[simp]
theorem hasProperQuotients_edge : (edge M hM π D).HasProperQuotients ↔ D.HasProperEdges :=
  hasProperQuotients_node.trans ⟨fun h => h 0, fun h _ => h⟩

end edge

/-- An edge labelled by an injective homomorphism, in particular by an isomorphism, is not a
proper epimorphism: a diagram with proper quotients has no such edge below its root. -/
theorem not_hasProperEdges_edge_of_injective {K : Type u} [Group K] {κ : A →* K}
    (M : Subgroup (MulAut H)) (hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)) {π : GHom ι κ}
    (hπ : Function.Injective π) (D : MRDiagram κ) : ¬(edge M hM π D).HasProperEdges :=
  fun h => (hasProperEdges_edge.1 h).2.1 hπ

/-- The diagram without branches has no edge, so all its edges are proper epimorphisms. -/
@[simp]
theorem hasProperEdges_empty : (MRDiagram.empty ι).HasProperEdges :=
  hasProperEdges_node.2 fun i => i.elim0

/-- The diagram without branches has proper quotients. -/
@[simp]
theorem hasProperQuotients_empty : (MRDiagram.empty ι).HasProperQuotients :=
  hasProperEdges_empty.hasProperQuotients

/-- The one-edge diagram of a free `A`-group has proper quotients: it has no edge below the
root. -/
@[simp]
theorem hasProperQuotients_freeRoot (free : IsFreeGGroup ι) :
    (freeRoot free).HasProperQuotients :=
  hasProperQuotients_edge.2 (hasProperEdges_leaf free)

/-! ### Diagrams of the coordinate group of a system -/

section System

variable {X : Type*} (S : Set (GX A X))

/-- If every `A`-homomorphism from the root group to the target sends the tuple `x` to a solution
of the system `S`, then the diagram is sound for `S` at `x`. -/
theorem isSound_of_forall (D : MRDiagram ι) {x : X → H}
    (h : ∀ φ : GHom ι ιL, (fun i => φ (x i)) ∈ V ιL S) : D.IsSound ιL S x :=
  fun φ _ => h φ

/-- If the `A`-homomorphisms from the root group to the target are the solutions of the system
`S`, through their values at the tuple `x`, then the diagram is complete exactly when every
solution of `S` in the target is the value at `x` of a branch composite. -/
theorem isComplete_iff_of_equiv {D : MRDiagram ι} {x : X → H} (e : GHom ι ιL ≃ V ιL S)
    (he : ∀ φ i, (e φ : X → L) i = φ (x i)) :
    D.IsComplete ιL ↔ ∀ v ∈ V ιL S, ∃ φ ∈ D.branchHoms ιL, ∀ i, φ (x i) = v i := by
  refine ⟨fun h v hv => ⟨_, h (e.symm ⟨v, hv⟩), fun i => ?_⟩, fun h φ => ?_⟩
  · rw [← he, e.apply_symm_apply]
  · obtain ⟨ψ, hψ, hψv⟩ := h _ (e φ).2
    rwa [← e.injective (Subtype.ext (funext fun i => (he ψ i).trans (hψv i)))]

/-- A diagram of the coordinate group of a system `S` over the target is sound for `S` at the
variables: every branch composite is a solution of `S`. -/
theorem isSound_coordGroup (D : MRDiagram (CoordGroup.coeff ιL S)) :
    D.IsSound ιL S (CoordGroup.genericPoint ιL S) :=
  D.isSound_of_forall S fun φ => by
    have : (CoordGroup.homEquiv ιL S φ : X → L) = fun x => φ (CoordGroup.genericPoint ιL S x) :=
      funext fun x => by simp [CoordGroup.genericPoint_apply]
    exact this ▸ (CoordGroup.homEquiv ιL S φ).2

/-- A diagram of the coordinate group of a system `S` over the target is complete exactly when
every solution of `S` in the target is the value on the variables of a branch composite. -/
theorem isComplete_coordGroup_iff {D : MRDiagram (CoordGroup.coeff ιL S)} :
    D.IsComplete ιL ↔ ∀ v ∈ V ιL S, ∃ φ ∈ D.branchHoms ιL,
      ∀ x, φ (CoordGroup.genericPoint ιL S x) = v x :=
  isComplete_iff_of_equiv S (CoordGroup.homEquiv ιL S) fun φ x => by
    simp [CoordGroup.genericPoint_apply]

/-- A diagram of the group presented by a system `S` is sound for `S` at the variables: every
branch composite is a solution of `S`. -/
theorem isSound_systemGroup (D : MRDiagram (SystemGroup.coeff S)) :
    D.IsSound ιL S fun x => ((inr (FreeGroup.of x) : GX A X) : SystemGroup A S) :=
  D.isSound_of_forall S fun φ =>
    funext (SystemGroup.homEquiv_apply_coe φ) ▸ (SystemGroup.homEquiv ιL S φ).2

/-- A diagram of the group presented by a system `S` is complete exactly when every solution of
`S` in the target is the value on the variables of a branch composite. -/
theorem isComplete_systemGroup_iff {D : MRDiagram (SystemGroup.coeff S)} :
    D.IsComplete ιL ↔ ∀ v ∈ V ιL S, ∃ φ ∈ D.branchHoms ιL,
      ∀ x, φ ((inr (FreeGroup.of x) : GX A X) : SystemGroup A S) = v x :=
  isComplete_iff_of_equiv S (SystemGroup.homEquiv ιL S) SystemGroup.homEquiv_apply_coe

end System

end MRDiagram

end TauCeti.LimitGroup
