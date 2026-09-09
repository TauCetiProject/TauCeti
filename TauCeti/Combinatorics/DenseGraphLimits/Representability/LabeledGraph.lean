/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum

/-!
# `k`-labeled graphs and their gluing

A `k`-labeled graph is a finite simple graph together with an ordered `k`-tuple of *distinct*
vertices.  Gluing two of them identifies corresponding labeled vertices and takes the union of the
edge sets; the identified vertices keep their labels, so the result is again a `k`-labeled graph and
gluing iterates.  This is Lovász–Szegedy's product `F₁F₂` of `k`-labeled graphs, the algebra
underlying connection matrices and reflection positivity.

## Main definitions

* `TauCeti.DenseGraphLimits.LabeledGraph` is the `k`-labeled graph;
* `TauCeti.DenseGraphLimits.LabeledGraph.glue` glues two of them along their labels;
* `TauCeti.DenseGraphLimits.LabeledGraph.glueInl` and
  `TauCeti.DenseGraphLimits.LabeledGraph.glueInr` are the two vertex maps into the gluing;
* `TauCeti.DenseGraphLimits.LabeledGraph.forgetLabels` is the underlying unlabeled graph.

## Main results

* `TauCeti.DenseGraphLimits.LabeledGraph.glue_graph` identifies the glued graph as the supremum of
  the two mapped sources, so no edge is created that neither source carries;
* `TauCeti.DenseGraphLimits.LabeledGraph.glueInl_eq_glueInr_iff` says the two sides meet exactly at
  corresponding labels, and
  `TauCeti.DenseGraphLimits.LabeledGraph.glue_surjective` that they cover the gluing: together they
  present the vertex set as the pushout;
* `TauCeti.DenseGraphLimits.LabeledGraph.glue_card` is the resulting vertex count
  `n₁ + n₂ - k`;
* `TauCeti.DenseGraphLimits.LabeledGraph.glue_adj_inl`,
  `TauCeti.DenseGraphLimits.LabeledGraph.glue_adj_inr` and
  `TauCeti.DenseGraphLimits.LabeledGraph.glue_adj_inl_inr` are the adjacency eliminators, and
  `TauCeti.DenseGraphLimits.LabeledGraph.not_glue_adj_of_unlabeled` records that unlabeled vertices
  of the two sides are never joined;
* `TauCeti.DenseGraphLimits.LabeledGraph.glueCommIso` is the commutativity of the gluing algebra,
  the isomorphism between the two orders of a gluing that makes connection matrices symmetric.

## Implementation

The vertex set of a gluing is built as the concrete pushout carrier
`Fin k ⊕ (G₁.Unlabeled ⊕ G₂.Unlabeled)` — the shared labels, then the private vertices of each
side — and transported to a `Fin`-representative along `Fintype.equivFin`, since the structure
stores its vertex set as `Fin n`.  Writing the carrier in this *symmetric* shape is what makes
commutativity a swap of the two summands rather than a bespoke bijection.

Both adjacency eliminators are stated in their honest form.  Two labeled vertices of the left side
can be joined by an edge contributed by the *right* side, so the naive `Adj (glueInl a)
(glueInl b) ↔ G₁.graph.Adj a b` is false; the correct statement carries the extra disjunct, which
collapses as soon as one of the two vertices is unlabeled
(`glue_adj_inl_of_unlabeled`).

## References

* L. Lovász, B. Szegedy, *Limits of dense graph sequences*, JCTB 96 (2006), 933–957, Section 2 —
  `k`-labeled graphs, their product, and connection matrices.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Chapter 6.
-/

-- Provenance: the names and signatures of the declarations below follow
-- `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.

public section

namespace TauCeti.DenseGraphLimits

variable {k : ℕ}

/-- A **`k`-labeled graph**: a finite simple graph on `Fin n` together with an ordered `k`-tuple of
distinct labeled vertices.  These are the objects of the gluing algebra behind connection
matrices. -/
structure LabeledGraph (k : ℕ) where
  /-- The number of vertices. -/
  n : ℕ
  /-- The underlying simple graph. -/
  graph : SimpleGraph (Fin n)
  /-- The labeled vertices, in order. -/
  label : Fin k → Fin n
  /-- The labeled vertices are distinct. -/
  label_injective : Function.Injective label

namespace LabeledGraph

/-- A labeled graph has at least as many vertices as labels. -/
theorem le_n (G : LabeledGraph k) : k ≤ G.n := by
  simpa using Fintype.card_le_of_injective G.label G.label_injective

/-- The vertices of a labeled graph that carry no label — the ones a gluing keeps private to its
side. -/
abbrev Unlabeled (G : LabeledGraph k) : Type := {a : Fin G.n // ∀ i, G.label i ≠ a}

/-- The unlabeled vertices of a labeled graph inherit a finite type from `Fin G.n`, of which they
are a subtype. -/
instance (G : LabeledGraph k) : Fintype G.Unlabeled := Subtype.fintype _

/-- The number of unlabeled vertices. -/
theorem card_unlabeled (G : LabeledGraph k) : Fintype.card G.Unlabeled = G.n - k := by
  classical
  have hrange : Fintype.card {a : Fin G.n // a ∈ Set.range G.label} = k :=
    (Fintype.card_congr (Equiv.ofInjective _ G.label_injective).symm).trans (Fintype.card_fin k)
  have hcompl : Fintype.card {a : Fin G.n // a ∉ Set.range G.label} = G.n - k := by
    rw [Fintype.card_subtype_compl, hrange, Fintype.card_fin]
  rw [← hcompl]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by simp [eq_comm])

/-- The vertex carrier of a gluing: the `k` shared labels together with the unlabeled vertices of
each side.  Writing it in this symmetric shape makes `glueCommIso` a swap of summands. -/
private abbrev glueCarrier (G₁ G₂ : LabeledGraph k) : Type :=
  Fin k ⊕ (G₁.Unlabeled ⊕ G₂.Unlabeled)

/-- The chosen `Fin`-representative of the gluing carrier. -/
private noncomputable def glueIndex (G₁ G₂ : LabeledGraph k) :
    G₁.glueCarrier G₂ ≃ Fin (Fintype.card (G₁.glueCarrier G₂)) :=
  Fintype.equivFin _

/-- Where a vertex of the left factor lands in the gluing carrier: at its label if it has one, and
in the private left summand otherwise. -/
private noncomputable def glueLeft (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n) : G₁.glueCarrier G₂ :=
  if h : ∃ i, G₁.label i = a then Sum.inl h.choose
  else Sum.inr (Sum.inl ⟨a, fun i hi => h ⟨i, hi⟩⟩)

/-- Where a vertex of the right factor lands in the gluing carrier. -/
private noncomputable def glueRight (G₁ G₂ : LabeledGraph k) (b : Fin G₂.n) : G₁.glueCarrier G₂ :=
  if h : ∃ i, G₂.label i = b then Sum.inl h.choose
  else Sum.inr (Sum.inr ⟨b, fun i hi => h ⟨i, hi⟩⟩)

/-- A labeled left vertex lands on its shared label. -/
@[simp]
private theorem glueLeft_label (G₁ G₂ : LabeledGraph k) (i : Fin k) :
    G₁.glueLeft G₂ (G₁.label i) = Sum.inl i := by
  have h : ∃ j, G₁.label j = G₁.label i := ⟨i, rfl⟩
  rw [glueLeft, dite_eq_left h]
  exact congrArg Sum.inl (G₁.label_injective h.choose_spec)

/-- A labeled right vertex lands on its shared label. -/
@[simp]
private theorem glueRight_label (G₁ G₂ : LabeledGraph k) (i : Fin k) :
    G₁.glueRight G₂ (G₂.label i) = Sum.inl i := by
  have h : ∃ j, G₂.label j = G₂.label i := ⟨i, rfl⟩
  rw [glueRight, dite_eq_left h]
  exact congrArg Sum.inl (G₂.label_injective h.choose_spec)

/-- An unlabeled left vertex lands in the private left summand. -/
private theorem glueLeft_of_unlabeled (G₁ G₂ : LabeledGraph k) {a : Fin G₁.n}
    (ha : ∀ i, G₁.label i ≠ a) : G₁.glueLeft G₂ a = Sum.inr (Sum.inl ⟨a, ha⟩) := by
  rw [glueLeft, dite_eq_right (fun h => ha h.choose h.choose_spec)]

/-- An unlabeled right vertex lands in the private right summand. -/
private theorem glueRight_of_unlabeled (G₁ G₂ : LabeledGraph k) {b : Fin G₂.n}
    (hb : ∀ i, G₂.label i ≠ b) : G₁.glueRight G₂ b = Sum.inr (Sum.inr ⟨b, hb⟩) := by
  rw [glueRight, dite_eq_right (fun h => hb h.choose h.choose_spec)]

/-- The left factor embeds in the gluing carrier. -/
private theorem glueLeft_injective (G₁ G₂ : LabeledGraph k) :
    Function.Injective (G₁.glueLeft G₂) := by
  intro a b hab
  by_cases ha : ∃ i, G₁.label i = a <;> by_cases hb : ∃ i, G₁.label i = b
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [glueLeft_label, glueLeft_label] at hab
    exact congrArg G₁.label (Sum.inl_injective hab)
  · obtain ⟨i, rfl⟩ := ha
    rw [glueLeft_label, glueLeft_of_unlabeled _ _ (fun i hi => hb ⟨i, hi⟩)] at hab
    exact absurd hab (by simp)
  · obtain ⟨j, rfl⟩ := hb
    rw [glueLeft_label, glueLeft_of_unlabeled _ _ (fun i hi => ha ⟨i, hi⟩)] at hab
    exact absurd hab (by simp)
  · rw [glueLeft_of_unlabeled _ _ (fun i hi => ha ⟨i, hi⟩),
      glueLeft_of_unlabeled _ _ (fun i hi => hb ⟨i, hi⟩)] at hab
    simpa using hab

/-- The right factor embeds in the gluing carrier. -/
private theorem glueRight_injective (G₁ G₂ : LabeledGraph k) :
    Function.Injective (G₁.glueRight G₂) := by
  intro a b hab
  by_cases ha : ∃ i, G₂.label i = a <;> by_cases hb : ∃ i, G₂.label i = b
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [glueRight_label, glueRight_label] at hab
    exact congrArg G₂.label (Sum.inl_injective hab)
  · obtain ⟨i, rfl⟩ := ha
    rw [glueRight_label, glueRight_of_unlabeled _ _ (fun i hi => hb ⟨i, hi⟩)] at hab
    exact absurd hab (by simp)
  · obtain ⟨j, rfl⟩ := hb
    rw [glueRight_label, glueRight_of_unlabeled _ _ (fun i hi => ha ⟨i, hi⟩)] at hab
    exact absurd hab (by simp)
  · rw [glueRight_of_unlabeled _ _ (fun i hi => ha ⟨i, hi⟩),
      glueRight_of_unlabeled _ _ (fun i hi => hb ⟨i, hi⟩)] at hab
    simpa using hab

/-- In the gluing carrier the two sides meet exactly at corresponding labels. -/
private theorem glueLeft_eq_glueRight_iff (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n)
    (b : Fin G₂.n) :
    G₁.glueLeft G₂ a = G₁.glueRight G₂ b ↔ ∃ i, a = G₁.label i ∧ b = G₂.label i := by
  constructor
  · intro hab
    by_cases ha : ∃ i, G₁.label i = a
    · obtain ⟨i, rfl⟩ := ha
      by_cases hb : ∃ j, G₂.label j = b
      · obtain ⟨j, rfl⟩ := hb
        rw [glueLeft_label, glueRight_label] at hab
        exact ⟨j, by rw [Sum.inl_injective hab], rfl⟩
      · rw [glueLeft_label, glueRight_of_unlabeled _ _ (fun j hj => hb ⟨j, hj⟩)] at hab
        exact absurd hab (by simp)
    · rw [glueLeft_of_unlabeled _ _ (fun i hi => ha ⟨i, hi⟩)] at hab
      by_cases hb : ∃ j, G₂.label j = b
      · obtain ⟨j, rfl⟩ := hb
        rw [glueRight_label] at hab
        exact absurd hab (by simp)
      · rw [glueRight_of_unlabeled _ _ (fun j hj => hb ⟨j, hj⟩)] at hab
        exact absurd hab (by simp)
  · rintro ⟨i, rfl, rfl⟩
    rw [glueLeft_label, glueRight_label]

/-- Every vertex of the gluing carrier comes from one of the two sides. -/
private theorem glueLeft_surjective_or (G₁ G₂ : LabeledGraph k) (v : G₁.glueCarrier G₂) :
    (∃ a, v = G₁.glueLeft G₂ a) ∨ ∃ b, v = G₁.glueRight G₂ b := by
  match v with
  | Sum.inl i => exact Or.inl ⟨G₁.label i, (glueLeft_label G₁ G₂ i).symm⟩
  | Sum.inr (Sum.inl ⟨a, ha⟩) => exact Or.inl ⟨a, (glueLeft_of_unlabeled G₁ G₂ ha).symm⟩
  | Sum.inr (Sum.inr ⟨b, hb⟩) => exact Or.inr ⟨b, (glueRight_of_unlabeled G₁ G₂ hb).symm⟩

/-- **Gluing.** Glue two `k`-labeled graphs by identifying corresponding labeled vertices and
taking the union of the two edge sets.  The identified vertices keep their labels — and stay
distinct — so the result is again a `k`-labeled graph and gluing iterates.  This is
Lovász–Szegedy's product `F₁F₂`. -/
noncomputable def glue (G₁ G₂ : LabeledGraph k) : LabeledGraph k where
  n := Fintype.card (G₁.glueCarrier G₂)
  graph := (G₁.graph.map fun a => G₁.glueIndex G₂ (G₁.glueLeft G₂ a)) ⊔
    (G₂.graph.map fun b => G₁.glueIndex G₂ (G₁.glueRight G₂ b))
  label i := G₁.glueIndex G₂ (Sum.inl i)
  label_injective := (G₁.glueIndex G₂).injective.comp Sum.inl_injective

/-- The vertex map of the left factor into the gluing. -/
noncomputable def glueInl (G₁ G₂ : LabeledGraph k) : Fin G₁.n ↪ Fin (G₁.glue G₂).n :=
  ⟨fun a => G₁.glueIndex G₂ (G₁.glueLeft G₂ a),
    (G₁.glueIndex G₂).injective.comp (G₁.glueLeft_injective G₂)⟩

/-- The vertex map of the right factor into the gluing. -/
noncomputable def glueInr (G₁ G₂ : LabeledGraph k) : Fin G₂.n ↪ Fin (G₁.glue G₂).n :=
  ⟨fun b => G₁.glueIndex G₂ (G₁.glueRight G₂ b),
    (G₁.glueIndex G₂).injective.comp (G₁.glueRight_injective G₂)⟩

-- Definitional form used to export the characteristic law without exposing the constructors.
private theorem glue_graph_def (G₁ G₂ : LabeledGraph k) :
    (G₁.glue G₂).graph = G₁.graph.map (G₁.glueInl G₂) ⊔ G₂.graph.map (G₁.glueInr G₂) := rfl

/-- **The glued graph is exactly the supremum of the two mapped sources**: gluing creates no edge
that neither side carries. -/
theorem glue_graph (G₁ G₂ : LabeledGraph k) :
    (G₁.glue G₂).graph = G₁.graph.map (G₁.glueInl G₂) ⊔ G₂.graph.map (G₁.glueInr G₂) :=
  glue_graph_def G₁ G₂

/-- **No other identifications**: the two sides meet exactly at corresponding labels. -/
theorem glueInl_eq_glueInr_iff (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n) (b : Fin G₂.n) :
    G₁.glueInl G₂ a = G₁.glueInr G₂ b ↔ ∃ i, a = G₁.label i ∧ b = G₂.label i := by
  rw [← glueLeft_eq_glueRight_iff]
  exact (G₁.glueIndex G₂).apply_eq_iff_eq

/-- The labels of the gluing are the images of the left labels. -/
theorem glueInl_label (G₁ G₂ : LabeledGraph k) :
    (G₁.glue G₂).label = G₁.glueInl G₂ ∘ G₁.label :=
  funext fun i => congrArg _ (glueLeft_label G₁ G₂ i).symm

/-- The labels of the gluing are the images of the right labels. -/
theorem glueInr_label (G₁ G₂ : LabeledGraph k) :
    (G₁.glue G₂).label = G₁.glueInr G₂ ∘ G₂.label :=
  funext fun i => congrArg _ (glueRight_label G₁ G₂ i).symm

/-- Every vertex of the gluing comes from one of the two sides. -/
theorem glue_surjective (G₁ G₂ : LabeledGraph k) (v : Fin (G₁.glue G₂).n) :
    (∃ a, v = G₁.glueInl G₂ a) ∨ ∃ b, v = G₁.glueInr G₂ b := by
  obtain h | h := glueLeft_surjective_or G₁ G₂ ((G₁.glueIndex G₂).symm v)
  · obtain ⟨a, ha⟩ := h
    exact Or.inl ⟨a, (G₁.glueIndex G₂).symm_apply_eq.mp ha⟩
  · obtain ⟨b, hb⟩ := h
    exact Or.inr ⟨b, (G₁.glueIndex G₂).symm_apply_eq.mp hb⟩

/-- **The vertex count of a gluing.**  The two sides share exactly their `k` labels. -/
theorem glue_card (G₁ G₂ : LabeledGraph k) : (G₁.glue G₂).n = G₁.n + G₂.n - k := by
  have h₁ := G₁.le_n
  have h₂ := G₂.le_n
  have hcard : (G₁.glue G₂).n = Fintype.card (G₁.glueCarrier G₂) := by rw [glue.eq_1]
  rw [hcard, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_unlabeled, card_unlabeled]
  omega

/-- **Adjacency on the left side.**  A left edge survives the gluing, and the only edges the
gluing adds between two left vertices are the ones the right side contributes between labels. -/
theorem glue_adj_inl (G₁ G₂ : LabeledGraph k) (a b : Fin G₁.n) :
    (G₁.glue G₂).graph.Adj (G₁.glueInl G₂ a) (G₁.glueInl G₂ b) ↔
      G₁.graph.Adj a b ∨
        ∃ i j, a = G₁.label i ∧ b = G₁.label j ∧ G₂.graph.Adj (G₂.label i) (G₂.label j) := by
  rw [glue_graph, SimpleGraph.sup_adj, SimpleGraph.map_adj_apply, SimpleGraph.map_adj]
  constructor
  · rintro (h | ⟨a', b', hadj, ha', hb'⟩)
    · exact Or.inl h
    · obtain ⟨i, hi₁, hi₂⟩ := (glueInl_eq_glueInr_iff G₁ G₂ a a').1 ha'.symm
      obtain ⟨j, hj₁, hj₂⟩ := (glueInl_eq_glueInr_iff G₁ G₂ b b').1 hb'.symm
      exact Or.inr ⟨i, j, hi₁, hj₁, by rw [← hi₂, ← hj₂]; exact hadj⟩
  · rintro (h | ⟨i, j, rfl, rfl, hadj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨G₂.label i, G₂.label j, hadj,
        ((glueInl_eq_glueInr_iff G₁ G₂ _ _).2 ⟨i, rfl, rfl⟩).symm,
        ((glueInl_eq_glueInr_iff G₁ G₂ _ _).2 ⟨j, rfl, rfl⟩).symm⟩

/-- **Adjacency on the right side**, the mirror of `glue_adj_inl`. -/
theorem glue_adj_inr (G₁ G₂ : LabeledGraph k) (a b : Fin G₂.n) :
    (G₁.glue G₂).graph.Adj (G₁.glueInr G₂ a) (G₁.glueInr G₂ b) ↔
      G₂.graph.Adj a b ∨
        ∃ i j, a = G₂.label i ∧ b = G₂.label j ∧ G₁.graph.Adj (G₁.label i) (G₁.label j) := by
  rw [glue_graph, SimpleGraph.sup_adj, SimpleGraph.map_adj_apply, SimpleGraph.map_adj]
  constructor
  · rintro (⟨a', b', hadj, ha', hb'⟩ | h)
    · obtain ⟨i, hi₁, hi₂⟩ := (glueInl_eq_glueInr_iff G₁ G₂ a' a).1 ha'
      obtain ⟨j, hj₁, hj₂⟩ := (glueInl_eq_glueInr_iff G₁ G₂ b' b).1 hb'
      exact Or.inr ⟨i, j, hi₂, hj₂, by rw [← hi₁, ← hj₁]; exact hadj⟩
    · exact Or.inl h
  · rintro (h | ⟨i, j, rfl, rfl, hadj⟩)
    · exact Or.inr h
    · exact Or.inl ⟨G₁.label i, G₁.label j, hadj,
        (glueInl_eq_glueInr_iff G₁ G₂ _ _).2 ⟨i, rfl, rfl⟩,
        (glueInl_eq_glueInr_iff G₁ G₂ _ _).2 ⟨j, rfl, rfl⟩⟩

/-- **Adjacency across the two sides.**  A left and a right vertex are joined only through a
label: either the right vertex is a label and the left side carries the edge, or the left vertex
is a label and the right side does. -/
theorem glue_adj_inl_inr (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n) (b : Fin G₂.n) :
    (G₁.glue G₂).graph.Adj (G₁.glueInl G₂ a) (G₁.glueInr G₂ b) ↔
      (∃ j, b = G₂.label j ∧ G₁.graph.Adj a (G₁.label j)) ∨
        ∃ i, a = G₁.label i ∧ G₂.graph.Adj (G₂.label i) b := by
  rw [glue_graph, SimpleGraph.sup_adj, SimpleGraph.map_adj, SimpleGraph.map_adj]
  constructor
  · rintro (⟨a', b', hadj, ha', hb'⟩ | ⟨a', b', hadj, ha', hb'⟩)
    · obtain ⟨j, hj₁, hj₂⟩ := (glueInl_eq_glueInr_iff G₁ G₂ b' b).1 hb'
      exact Or.inl ⟨j, hj₂, by
        rw [← hj₁, ← (G₁.glueInl G₂).injective ha']; exact hadj⟩
    · obtain ⟨i, hi₁, hi₂⟩ := (glueInl_eq_glueInr_iff G₁ G₂ a a').1 ha'.symm
      exact Or.inr ⟨i, hi₁, by
        rw [← hi₂, ← (G₁.glueInr G₂).injective hb']; exact hadj⟩
  · rintro (⟨j, rfl, hadj⟩ | ⟨i, rfl, hadj⟩)
    · exact Or.inl ⟨a, G₁.label j, hadj, rfl,
        (glueInl_eq_glueInr_iff G₁ G₂ _ _).2 ⟨j, rfl, rfl⟩⟩
    · exact Or.inr ⟨G₂.label i, b, hadj,
        ((glueInl_eq_glueInr_iff G₁ G₂ _ _).2 ⟨i, rfl, rfl⟩).symm, rfl⟩

/-- Gluing preserves the edges of the left side. -/
theorem glue_adj_inl_of_adj (G₁ G₂ : LabeledGraph k) {a b : Fin G₁.n} (h : G₁.graph.Adj a b) :
    (G₁.glue G₂).graph.Adj (G₁.glueInl G₂ a) (G₁.glueInl G₂ b) :=
  (glue_adj_inl G₁ G₂ a b).2 (Or.inl h)

/-- Gluing preserves the edges of the right side. -/
theorem glue_adj_inr_of_adj (G₁ G₂ : LabeledGraph k) {a b : Fin G₂.n} (h : G₂.graph.Adj a b) :
    (G₁.glue G₂).graph.Adj (G₁.glueInr G₂ a) (G₁.glueInr G₂ b) :=
  (glue_adj_inr G₁ G₂ a b).2 (Or.inl h)

/-- At an unlabeled left vertex the gluing reflects left adjacency faithfully: the extra disjunct
of `glue_adj_inl` needs both endpoints to be labels. -/
theorem glue_adj_inl_of_unlabeled (G₁ G₂ : LabeledGraph k) {a : Fin G₁.n}
    (ha : ∀ i, G₁.label i ≠ a) (b : Fin G₁.n) :
    (G₁.glue G₂).graph.Adj (G₁.glueInl G₂ a) (G₁.glueInl G₂ b) ↔ G₁.graph.Adj a b := by
  rw [glue_adj_inl]
  exact or_iff_left (by rintro ⟨i, _, rfl, -, -⟩; exact ha i rfl)

/-- At an unlabeled right vertex the gluing reflects right adjacency faithfully. -/
theorem glue_adj_inr_of_unlabeled (G₁ G₂ : LabeledGraph k) {a : Fin G₂.n}
    (ha : ∀ i, G₂.label i ≠ a) (b : Fin G₂.n) :
    (G₁.glue G₂).graph.Adj (G₁.glueInr G₂ a) (G₁.glueInr G₂ b) ↔ G₂.graph.Adj a b := by
  rw [glue_adj_inr]
  exact or_iff_left (by rintro ⟨i, _, rfl, -, -⟩; exact ha i rfl)

/-- **No cross-edges are smuggled in**: gluing never joins an unlabeled vertex of one side to an
unlabeled vertex of the other. -/
theorem not_glue_adj_of_unlabeled (G₁ G₂ : LabeledGraph k) {a : Fin G₁.n} {b : Fin G₂.n}
    (ha : ∀ i, G₁.label i ≠ a) (hb : ∀ i, G₂.label i ≠ b) :
    ¬ (G₁.glue G₂).graph.Adj (G₁.glueInl G₂ a) (G₁.glueInr G₂ b) := by
  rw [glue_adj_inl_inr]
  rintro (⟨j, rfl, -⟩ | ⟨i, rfl, -⟩)
  · exact hb j rfl
  · exact ha i rfl

/-- **Unlabeling.**  The underlying finite simple graph of a `k`-labeled graph, labels forgotten —
the object a graph parameter evaluates in a connection-matrix entry. -/
@[expose]
def forgetLabels (G : LabeledGraph k) : Σ m, SimpleGraph (Fin m) := ⟨G.n, G.graph⟩

/-- Unlabeling keeps the vertex count. -/
@[simp]
theorem forgetLabels_fst (G : LabeledGraph k) : G.forgetLabels.1 = G.n := rfl

/-- Unlabeling keeps the graph. -/
@[simp]
theorem forgetLabels_snd (G : LabeledGraph k) : G.forgetLabels.2 = G.graph := rfl

/-! ### Commutativity of the gluing -/

/-- Swapping the two private summands of a gluing carrier. -/
private def glueSwap (G₁ G₂ : LabeledGraph k) : G₁.glueCarrier G₂ ≃ G₂.glueCarrier G₁ :=
  (Equiv.refl (Fin k)).sumCongr (Equiv.sumComm _ _)

/-- Under the swap, the left factor of one order becomes the right factor of the other. -/
private theorem glueSwap_glueLeft (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n) :
    G₁.glueSwap G₂ (G₁.glueLeft G₂ a) = G₂.glueRight G₁ a := by
  by_cases ha : ∃ i, G₁.label i = a
  · obtain ⟨i, rfl⟩ := ha
    rw [glueLeft_label, glueRight_label]
    rfl
  · rw [glueLeft_of_unlabeled _ _ fun i hi => ha ⟨i, hi⟩,
      glueRight_of_unlabeled _ _ fun i hi => ha ⟨i, hi⟩]
    rfl

/-- Under the swap, the right factor of one order becomes the left factor of the other. -/
private theorem glueSwap_glueRight (G₁ G₂ : LabeledGraph k) (b : Fin G₂.n) :
    G₁.glueSwap G₂ (G₁.glueRight G₂ b) = G₂.glueLeft G₁ b := by
  by_cases hb : ∃ i, G₂.label i = b
  · obtain ⟨i, rfl⟩ := hb
    rw [glueRight_label, glueLeft_label]
    rfl
  · rw [glueRight_of_unlabeled _ _ fun i hi => hb ⟨i, hi⟩,
      glueLeft_of_unlabeled _ _ fun i hi => hb ⟨i, hi⟩]
    rfl

/-- The vertex bijection between the two orders of a gluing. -/
private noncomputable def glueCommEquiv (G₁ G₂ : LabeledGraph k) :
    Fin (G₁.glue G₂).n ≃ Fin (G₂.glue G₁).n :=
  (G₁.glueIndex G₂).symm.trans ((G₁.glueSwap G₂).trans (G₂.glueIndex G₁))

/-- The commutativity bijection unfolds to the carrier swap. -/
private theorem glueCommEquiv_apply (G₁ G₂ : LabeledGraph k) (v : Fin (G₁.glue G₂).n) :
    G₁.glueCommEquiv G₂ v =
      G₂.glueIndex G₁ (G₁.glueSwap G₂ ((G₁.glueIndex G₂).symm v)) := rfl

/-- The left vertex map is induced by the left carrier map. -/
private theorem glueInl_apply (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n) :
    G₁.glueInl G₂ a = G₁.glueIndex G₂ (G₁.glueLeft G₂ a) := rfl

/-- The right vertex map is induced by the right carrier map. -/
private theorem glueInr_apply (G₁ G₂ : LabeledGraph k) (b : Fin G₂.n) :
    G₁.glueInr G₂ b = G₁.glueIndex G₂ (G₁.glueRight G₂ b) := rfl

/-- The commutativity bijection exchanges the two vertex maps. -/
private theorem glueCommEquiv_glueInl (G₁ G₂ : LabeledGraph k) (a : Fin G₁.n) :
    G₁.glueCommEquiv G₂ (G₁.glueInl G₂ a) = G₂.glueInr G₁ a := by
  rw [glueCommEquiv_apply, glueInl_apply, Equiv.symm_apply_apply, glueSwap_glueLeft,
    glueInr_apply]

/-- The commutativity bijection exchanges the two vertex maps, on the right. -/
private theorem glueCommEquiv_glueInr (G₁ G₂ : LabeledGraph k) (b : Fin G₂.n) :
    G₁.glueCommEquiv G₂ (G₁.glueInr G₂ b) = G₂.glueInl G₁ b := by
  rw [glueCommEquiv_apply, glueInr_apply, Equiv.symm_apply_apply, glueSwap_glueRight,
    glueInl_apply]

/-- The commutativity bijection carries one glued graph onto the other. -/
private theorem glue_graph_map_glueCommEquiv (G₁ G₂ : LabeledGraph k) :
    (G₁.glue G₂).graph.map (G₁.glueCommEquiv G₂) = (G₂.glue G₁).graph := by
  have h₁ : (G₁.glueCommEquiv G₂ : Fin (G₁.glue G₂).n → Fin (G₂.glue G₁).n) ∘
      (G₁.glueInl G₂ : Fin G₁.n → Fin (G₁.glue G₂).n) = G₂.glueInr G₁ :=
    funext (glueCommEquiv_glueInl G₁ G₂)
  have h₂ : (G₁.glueCommEquiv G₂ : Fin (G₁.glue G₂).n → Fin (G₂.glue G₁).n) ∘
      (G₁.glueInr G₂ : Fin G₂.n → Fin (G₁.glue G₂).n) = G₂.glueInl G₁ :=
    funext (glueCommEquiv_glueInr G₁ G₂)
  have hmap (G H : SimpleGraph (Fin (G₁.glue G₂).n)) :
      (G ⊔ H).map (G₁.glueCommEquiv G₂) =
        G.map (G₁.glueCommEquiv G₂) ⊔ H.map (G₁.glueCommEquiv G₂) :=
    GaloisConnection.l_sup
      (SimpleGraph.map_le_iff_le_comap (G₁.glueCommEquiv G₂).toEmbedding)
  rw [glue_graph, hmap, SimpleGraph.map_map, SimpleGraph.map_map, h₁, h₂, glue_graph, sup_comm]

/-- **Commutativity of the gluing algebra.**  The two orders of a gluing are isomorphic, so a graph
parameter that is isomorphism invariant takes the same value on both — this is what makes
connection matrices symmetric. -/
noncomputable def glueCommIso (G₁ G₂ : LabeledGraph k) :
    (G₁.glue G₂).graph ≃g (G₂.glue G₁).graph where
  toEquiv := G₁.glueCommEquiv G₂
  map_rel_iff' {u v} := by
    conv_lhs => rw [← glue_graph_map_glueCommEquiv G₁ G₂]
    exact SimpleGraph.map_adj_apply (f := (G₁.glueCommEquiv G₂).toEmbedding)

end LabeledGraph

end TauCeti.DenseGraphLimits
