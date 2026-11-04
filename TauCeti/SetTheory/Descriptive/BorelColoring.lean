/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.MeasureTheory.Constructions.Polish.Analytic

/-!
# Independent sets and countable Borel colorings of relations

A relation `G : SetRel X X` is read as a directed graph in which loops are allowed.

* `SetRel.IsIndependent G A`: the set `A` contains no pair of `G`, loops included. This differs
  from Mathlib's `SetRel.IsSeparated`, which only constrains pairs of distinct points; for the
  edge relation of a `SimpleGraph` it agrees with `SimpleGraph.IsIndepSet`.
* `SetRel.HasCountableBorelColoring G`: there is a measurable `c : X → ℕ` with `c x ≠ c y` for
  every pair `(x, y)` of `G`; equivalently, `X` is covered by countably many measurable
  `G`-independent sets. For the edge relation of a `SimpleGraph` it is the existence of a
  measurable `G.Coloring ℕ`.

Countable Borel colorings are the dividing line of the Kechris–Solecki–Todorcevic G₀ dichotomy.
A coloring does not see the direction of a pair, so the dichotomy concerns the symmetrization
`G ∪ G.inv`: an analytic relation `G` on a Polish space either has a countable Borel coloring, or
the graph G₀ on Cantor space admits a continuous homomorphism into `G ∪ G.inv`.

For an equivalence relation `E`, the inequivalence relation `{p | ¬ E p.1 p.2}` has a countable
Borel coloring exactly when `E` has Borel classes and countably many of them, which turns
counting the classes of `E` into a coloring problem.

The Kechris–Solecki–Todorcevic lemma `SetRel.exists_measurableSet_isIndependent_superset` says
that, in a Hausdorff space with its Borel σ-algebra, every analytic independent set of an
analytic relation lies in a Borel independent set. It is what lets families of analytic sets be
captured by countably many Borel independent sets.

## Main definitions

* `SetRel.IsIndependent`, `SetRel.HasCountableBorelColoring`.

## Main results

* `SetRel.hasCountableBorelColoring_iff_exists_cover`: colorings are countable covers by measurable
  independent sets.
* `SetRel.HasCountableBorelColoring.mono`, `SetRel.HasCountableBorelColoring.preimage`: colorings
  restrict to subrelations and pull back along measurable maps.
* `SetRel.not_hasCountableBorelColoring_of_mem`: a relation with a loop has no coloring.
* `SimpleGraph.isIndependent_adj_iff_isIndepSet`,
  `SimpleGraph.hasCountableBorelColoring_adj_iff`: agreement with Mathlib's independent sets and
  colorings of simple graphs.
* `Setoid.hasCountableBorelColoring_not_iff`: the inequivalence relation of `E` has a countable
  Borel coloring iff `E` has countably many classes, all of them Borel. The forward direction
  `Setoid.countable_quotient_of_hasCountableBorelColoring_not` alone needs no measurability.
* `SetRel.exists_measurableSet_isIndependent_superset`: the Kechris–Solecki–Todorcevic lemma.

## References

* A. S. Kechris, S. Solecki and S. Todorcevic, *Borel chromatic numbers*, Advances in Mathematics
  141 (1999), 1–44, Proposition 3.1 (independent analytic sets lie in independent Borel sets).
* B. D. Miller, *The graph-theoretic approach to descriptive set theory*, Bulletin of Symbolic
  Logic 18 (2012), 554–575.
* `SetRel.IsIndependent` and `SetRel.exists_measurableSet_isIndependent_superset` are adapted from
  `RelIndependent` and `exists_measurableSet_relIndependent_superset` in
  `InfinitaryLogic/Descriptive/G0Dichotomy.lean` of `cameronfreer/infinitary-logic` (Apache-2.0),
  commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`.
* Divergences from that source: independence is in the `SetRel` namespace, next to Mathlib's
  `SetRel.IsSeparated`; the Kechris–Solecki–Todorcevic lemma is proved by two Lusin separations,
  against the image and then the preimage of the relation, rather than by an ω-recursion against
  symmetric neighbourhoods, and so holds in every Hausdorff space with its Borel σ-algebra rather
  than only in Polish spaces.
-/

public section

open MeasureTheory Set

namespace SetRel

variable {X Y : Type*} {G H : SetRel X X} {A B : Set X}

/-- A set is **independent** for a relation `G` if it contains no pair of `G`, loops
included. -/
def IsIndependent (G : SetRel X X) (A : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → (x, y) ∉ G

/-- Unfolding lemma for `SetRel.IsIndependent`. -/
theorem isIndependent_iff : G.IsIndependent A ↔ ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → (x, y) ∉ G :=
  Iff.rfl

/-- A set is independent iff its square misses the relation. -/
theorem isIndependent_iff_disjoint_prod : G.IsIndependent A ↔ Disjoint (A ×ˢ A) G := by
  rw [isIndependent_iff, Set.disjoint_left]
  exact ⟨fun h p hp ↦ h hp.1 hp.2, fun h x hx y hy ↦ h ⟨hx, hy⟩⟩

/-- A set is independent iff it misses its own image under the relation. -/
theorem isIndependent_iff_disjoint_image : G.IsIndependent A ↔ Disjoint A (G.image A) := by
  simp only [isIndependent_iff, Set.disjoint_left, mem_image, not_exists, not_and]
  exact ⟨fun h y hy x hx hxy ↦ h hx hy hxy, fun h x hx y hy hxy ↦ h hy x hx hxy⟩

/-- A set is independent iff it misses its own preimage under the relation. -/
theorem isIndependent_iff_disjoint_preimage : G.IsIndependent A ↔ Disjoint A (G.preimage A) := by
  simp only [isIndependent_iff, Set.disjoint_left, mem_preimage, not_exists, not_and]

/-- Independence is separation together with the absence of loops. -/
theorem isIndependent_iff_isSeparated :
    G.IsIndependent A ↔ G.IsSeparated A ∧ ∀ x ∈ A, (x, x) ∉ G := by
  refine ⟨fun h ↦ ⟨fun x hx y hy _ ↦ h hx hy, fun x hx ↦ h hx hx⟩, fun ⟨hsep, hloop⟩ x hx y hy ↦ ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  exacts [hloop x hx, hsep hx hy hxy]

/-- Independence passes to subrelations. -/
theorem IsIndependent.mono_left (hHG : H ⊆ G) (h : G.IsIndependent A) : H.IsIndependent A :=
  fun _ hx _ hy hxy ↦ h hx hy (hHG hxy)

/-- Independence passes to subsets. -/
theorem IsIndependent.mono_right (hBA : B ⊆ A) (h : G.IsIndependent A) : G.IsIndependent B :=
  fun _ hx _ hy ↦ h (hBA hx) (hBA hy)

/-- The empty set is independent. -/
@[simp]
protected theorem IsIndependent.empty : G.IsIndependent ∅ :=
  fun _ hx ↦ hx.elim

/-- A singleton is independent iff its point carries no loop. -/
@[simp]
theorem isIndependent_singleton {x : X} : G.IsIndependent {x} ↔ (x, x) ∉ G := by
  simp [isIndependent_iff]

section Coloring

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- A relation `G` has a **countable Borel coloring** if some measurable `c : X → ℕ` gives the two
ends of every pair of `G` different colors. -/
def HasCountableBorelColoring (G : SetRel X X) : Prop :=
  ∃ c : X → ℕ, Measurable c ∧ ∀ ⦃x y⦄, (x, y) ∈ G → c x ≠ c y

/-- Unfolding lemma for `SetRel.HasCountableBorelColoring`. -/
theorem hasCountableBorelColoring_iff :
    G.HasCountableBorelColoring ↔ ∃ c : X → ℕ, Measurable c ∧ ∀ ⦃x y⦄, (x, y) ∈ G → c x ≠ c y :=
  Iff.rfl

/-- A relation has a countable Borel coloring iff the space is covered by countably many
measurable independent sets. -/
theorem hasCountableBorelColoring_iff_exists_cover :
    G.HasCountableBorelColoring ↔
      ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n) ∧ G.IsIndependent (B n)) ∧ ⋃ n, B n = univ := by
  classical
  refine ⟨fun ⟨c, hc, hG⟩ ↦ ⟨fun n ↦ c ⁻¹' {n}, fun n ↦ ⟨hc (measurableSet_singleton n),
    fun x hx y hy hxy ↦ hG hxy (hx.trans hy.symm)⟩, iUnion_eq_univ_iff.2 fun x ↦ ⟨c x, rfl⟩⟩,
    fun ⟨B, hB, hcov⟩ ↦ ?_⟩
  have hex : ∀ x, ∃ n, x ∈ B n := iUnion_eq_univ_iff.1 hcov
  refine ⟨fun x ↦ Nat.find (hex x), measurable_find hex fun n ↦ (hB n).1, fun x y hxy heq ↦ ?_⟩
  beta_reduce at heq
  have hy := Nat.find_spec (hex y)
  rw [← heq] at hy
  exact (hB _).2 (Nat.find_spec (hex x)) hy hxy

/-- A coloring of a relation colors every subrelation. -/
theorem HasCountableBorelColoring.mono (hHG : H ⊆ G) (h : G.HasCountableBorelColoring) :
    H.HasCountableBorelColoring :=
  let ⟨c, hc, hG⟩ := h
  ⟨c, hc, fun _ _ hxy ↦ hG (hHG hxy)⟩

/-- A coloring of a relation pulls back along a measurable map. Combined with
`SetRel.HasCountableBorelColoring.mono`, a relation `H` with a measurable map `f` sending `H`-pairs
to `G`-pairs inherits a coloring from one of `G`. -/
theorem HasCountableBorelColoring.preimage (h : G.HasCountableBorelColoring) {f : Y → X}
    (hf : Measurable f) : SetRel.HasCountableBorelColoring (Prod.map f f ⁻¹' G) :=
  let ⟨c, hc, hG⟩ := h
  ⟨c ∘ f, hc.comp hf, fun _ _ hxy ↦ hG (Set.mem_preimage.1 hxy)⟩

/-- A relation with a loop has no coloring at all. -/
theorem not_hasCountableBorelColoring_of_mem {x : X} (hx : (x, x) ∈ G) :
    ¬ G.HasCountableBorelColoring :=
  fun ⟨_, _, hG⟩ ↦ hG hx rfl

end Coloring

/-- **The Kechris–Solecki–Todorcevic lemma.** In a Hausdorff space with its Borel σ-algebra, an
analytic independent set of an analytic relation is contained in a Borel independent set. -/
theorem exists_measurableSet_isIndependent_superset [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (hG : AnalyticSet G) (hA : AnalyticSet A)
    (hind : G.IsIndependent A) : ∃ B, MeasurableSet B ∧ A ⊆ B ∧ G.IsIndependent B := by
  -- Separate `A` from its `G`-image, which is analytic and disjoint from `A`, by a Borel `B₀`.
  obtain ⟨B₀, hAB₀, hB₀, hB₀m⟩ :=
    hA.measurablySeparable (hG.relImage hA) (isIndependent_iff_disjoint_image.1 hind)
  -- The `G`-preimage of `B₀` is analytic as `B₀` is Borel, and it misses `A`: a point of `A`
  -- related to a point of `B₀` would put that point in the `G`-image of `A`.
  have hdisj : Disjoint A (G.preimage B₀) :=
    Set.disjoint_left.2 fun x hx ⟨_, hy, hxy⟩ ↦ Set.disjoint_left.1 hB₀ ⟨x, hx, hxy⟩ hy
  obtain ⟨B₁, hAB₁, hB₁, hB₁m⟩ :=
    hA.measurablySeparable (hG.relPreimage_measurableSet hB₀m) hdisj
  -- A pair `(x, y)` of `G` inside `B₀ ∩ B₁` puts `x` in the `G`-preimage of `B₀`, missed by `B₁`.
  refine ⟨B₀ ∩ B₁, hB₀m.inter hB₁m, subset_inter hAB₀ hAB₁, ?_⟩
  rintro x ⟨-, hx⟩ y ⟨hy, -⟩ hxy
  exact Set.disjoint_left.1 hB₁ ⟨y, hy, hxy⟩ hx

end SetRel

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Independence for the edge relation of a simple graph is Mathlib's `SimpleGraph.IsIndepSet`. -/
@[simp]
theorem isIndependent_adj_iff_isIndepSet {s : Set V} :
    SetRel.IsIndependent {p : V × V | G.Adj p.1 p.2} s ↔ G.IsIndepSet s := by
  rw [SetRel.isIndependent_iff_isSeparated, isIndepSet_iff]
  simp [SetRel.IsSeparated]

/-- The edge relation of a simple graph has a countable Borel coloring iff the graph has a
measurable coloring by `ℕ`. -/
theorem hasCountableBorelColoring_adj_iff [MeasurableSpace V] :
    SetRel.HasCountableBorelColoring {p : V × V | G.Adj p.1 p.2} ↔
      ∃ c : G.Coloring ℕ, Measurable c :=
  ⟨fun ⟨c, hc, hG⟩ ↦ ⟨Coloring.mk c fun h ↦ hG h, hc⟩,
    fun ⟨c, hc⟩ ↦ ⟨c, hc, fun _ _ h ↦ c.valid h⟩⟩

end SimpleGraph

namespace Setoid

variable {X : Type*} [MeasurableSpace X]

/-- If the inequivalence relation of `E` has a countable Borel coloring, then `E` has countably
many classes: two points of the same color are equivalent. -/
theorem countable_quotient_of_hasCountableBorelColoring_not (E : Setoid X)
    (h : SetRel.HasCountableBorelColoring {p : X × X | ¬ E p.1 p.2}) : Countable (Quotient E) := by
  obtain ⟨c, -, hc⟩ := h
  refine Function.Injective.countable (f := fun q : Quotient E ↦ c q.out) fun q r hqr ↦ ?_
  rw [← q.out_eq, ← r.out_eq]
  exact Quotient.sound (not_not.1 fun hne ↦ hc hne hqr)

/-- If the inequivalence relation of `E` has a countable Borel coloring, then every class of `E`
is measurable: it is the union of the color classes of its points. -/
theorem measurableSet_setOf_of_hasCountableBorelColoring_not (E : Setoid X)
    (h : SetRel.HasCountableBorelColoring {p : X × X | ¬ E p.1 p.2}) (x : X) :
    MeasurableSet {y | E x y} := by
  obtain ⟨c, hc, hcol⟩ := h
  -- A point with the color of a point of the class is equivalent to it.
  have : {y | E x y} = c ⁻¹' (c '' {y | E x y}) := by
    refine (subset_preimage_image _ _).antisymm fun y ⟨z, hz, hzy⟩ ↦ ?_
    exact E.trans hz (not_not.1 fun hne ↦ hcol hne hzy)
  rw [this]
  exact hc .of_discrete

/-- For an equivalence relation `E` with measurable classes and countably many of them, the
inequivalence relation of `E` has a countable Borel coloring: color each point by an index of
its class. -/
theorem hasCountableBorelColoring_not_of_countable {E : Setoid X} [Countable (Quotient E)]
    (hE : ∀ x, MeasurableSet {y | E x y}) :
    SetRel.HasCountableBorelColoring {p : X × X | ¬ E p.1 p.2} := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (Quotient E)
  refine ⟨fun x ↦ e (Quotient.mk E x), measurable_to_countable' fun n ↦ ?_,
    fun x y hxy heq ↦ hxy (Quotient.exact (he heq))⟩
  -- The fibre of the coloring over `n` is a countable union of classes.
  have : (fun x ↦ e (Quotient.mk E x)) ⁻¹' {n} = ⋃ q ∈ e ⁻¹' {n}, {y | E q.out y} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
    refine ⟨fun hy ↦ ⟨_, hy, E.symm (Quotient.mk_eq_iff_out.1 rfl)⟩, fun ⟨q, hq, hqy⟩ ↦ ?_⟩
    rwa [Quotient.mk_eq_iff_out.2 (E.symm hqy)]
  rw [this]
  exact MeasurableSet.biUnion (to_countable _) fun q _ ↦ hE q.out

/-- **Countable colorings count classes.** The inequivalence relation of an equivalence relation
`E` has a countable Borel coloring iff `E` has countably many classes, all of them measurable. -/
theorem hasCountableBorelColoring_not_iff {E : Setoid X} :
    SetRel.HasCountableBorelColoring {p : X × X | ¬ E p.1 p.2} ↔
      Countable (Quotient E) ∧ ∀ x, MeasurableSet {y | E x y} :=
  ⟨fun h ↦ ⟨E.countable_quotient_of_hasCountableBorelColoring_not h,
    E.measurableSet_setOf_of_hasCountableBorelColoring_not h⟩,
    fun ⟨_, hE⟩ ↦ hasCountableBorelColoring_not_of_countable hE⟩

end Setoid
