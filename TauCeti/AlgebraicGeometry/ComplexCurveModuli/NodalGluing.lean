/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Quot
public import Mathlib.Logic.Relation
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

/-!
# The gluing quotient of a nodal curve at its flag pairs

A nodal curve is obtained by gluing finitely many smooth curves at finitely many points.  The
gluing data is recorded by *flag pairs*: a flag pair names two normalization components together
with the point of each of them that is identified.  This file builds the underlying topological
space of such a curve, the *gluing quotient*, and records its basic properties.

The roadmap item this file advances is layer D1 of
`TauCetiRoadmap/ComplexCurveModuli/README.md`, whose first sentence reads:

> Construct the compact Hausdorff quotient of normalization components by the finitely many flag
> pairs; prove the equivalence relation closed and the complement maps locally biholomorphic.

The model is the following.

* `NodalCurve` is the gluing data: finitely many normalization components `X i` (indexed by the
  finite type `ι`) together with finitely many flag pairs `f : Flag`.  A flag pair names the two
  components `fst f`, `snd f` and the points `fstPt f`, `sndPt f` of them that are identified.
* `Sigma X` is the disjoint union of the normalization components, with the coproduct topology.
* `flagRel` is the generating relation: the two points of one flag pair are related.
* `gluedRel` is the equivalence relation *generated* by the flag pairs, i.e. the transitive
  closure of `flagRel` (`gluedRel_iff_eqvGen`).  Two points of the disjoint union are glued
  together exactly when they are the points of two flag pairs belonging to the same node.  It is
  symmetric and transitive (`gluedRel_symm`, `gluedRel_trans`), hence an equivalence relation
  (`gluedRel_equivalence`), and it relates two points only when they are equal or when both of
  them are flag points (`gluedRel_flagPoints`).
* `gluedCurve` is the quotient of the disjoint union by that relation: the underlying space of
  the nodal curve.  It is the `Quotient` of the disjoint union by the setoid `gluedRelSetoid`,
  with the quotient topology: `isOpen_iff_preimage` states that a subset of the glued curve is
  open exactly when its inverse image under the quotient map `gluedCurveQuotientMap` is open in
  the disjoint union.  The quotient map is continuous (`continuous_gluedCurveQuotientMap`) and
  identifies two points exactly when the generated relation relates them
  (`gluedRel_iff_quotientMk_eq`).  The glued space is compact whenever the normalization
  components are compact (`instCompactSpaceGluedCurve`).
* `nodeSet` is the image of the flag points in the glued curve: the singular locus of the curve.
  It is the image of the flag pairs (`mem_nodeSet`, `nodeSet_eq_image_nodeOfFlag`), it is finite
  (`nodeSet_finite`) and it is closed (`isClosed_nodeSet`).  The map `nodeOfFlag` sends a flag
  pair to its node; two flag pairs have the same node exactly when they are glued at the same
  node (`nodeOfFlag_eq_iff`), and the map is injective when no two distinct flag pairs are glued
  at the same node (`nodeOfFlag_injective`).
* The complement of the node set is the *smooth locus* `smoothLocus`, which is open
  (`isOpen_smoothLocus`).  The quotient map restricts to a homeomorphism from the disjoint union
  of the normalization components minus their flag points onto the smooth locus
  (`gluedCurveQuotientMapOnSmooth_isHomeomorph`): the restriction is injective away from the
  flag points (`gluedCurveQuotientMap_injective_of_not_flagPoint`), and it is continuous and
  open.

**Scope.** This file is the topological, pre-hypersurface-chart part of the quoted sentence.  What
is proved is:

* the glued space is built: it is the quotient of the disjoint union of the normalization
  components by the generated relation, endowed with the quotient topology; the quotient map is
  continuous; and the glued space is compact when the normalization components are;
* the generated relation is closed (`gluedRel_isClosed`);
* the node set, the image of the flag pairs, is closed, and the quotient map identifies the
  disjoint union minus the flag points homeomorphically with the complement of the node set.

What is **not** proved here:

* the **Hausdorff** part of the quoted sentence: the glued space is not shown to be Hausdorff.
  Its equivalence classes are finite -- the class of a point that is not a flag point is a
  singleton, and the class of a flag point is contained in the finite set of flag points
  (`gluedRel_flagPoints`) -- but the passage from finiteness of the classes, closedness of the
  quotient map and normality of the disjoint union to the Hausdorff property of the quotient is
  not carried out here.
* the **biholomorphic** refinement of "the complement maps locally biholomorphic": the glued
  space carries no complex structure on its smooth locus, so there is nothing for a biholomorphism
  to be a morphism between.
* the **dual graph** of the nodal curve: the file identifies the edges of the dual graph with
  the nodes of the glued curve, i.e. with the classes of flag pairs that are glued at the same
  node (`nodeOfFlag_eq_iff` describes the fibres of the flag-pair map), but it does not build
  the graph itself and does not count its edges.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Chapter 5, for nodal curves as smooth surfaces
  with paired nodal points.
* Robin Hartshorne, *Algebraic Geometry*, Exercise IV.6.3, for the dual graph of a nodal curve,
  whose edges are the nodes of the curve.
-/

public noncomputable section

open Set

namespace TauCeti.ComplexCurveModuli

variable {ι : Type*} {Flag : Type*} {X : ι → Type*}

/-- The gluing data of a nodal curve: the finitely many flag pairs at which the normalization
components are glued.  A flag pair `f` names the two components `fst f` and `snd f` together with
the points `fstPt f` and `sndPt f` of those components that are identified. -/
structure NodalCurve (ι : Type*) (Flag : Type*) (X : ι → Type*) where
  /-- The first component glued at a flag pair. -/
  fst : Flag → ι
  /-- The second component glued at a flag pair. -/
  snd : Flag → ι
  /-- The point of the first component at a flag pair. -/
  fstPt : ∀ f : Flag, X (fst f)
  /-- The point of the second component at a flag pair. -/
  sndPt : ∀ f : Flag, X (snd f)

variable (d : NodalCurve ι Flag X)

/-- The disjoint union of the normalization components of a nodal curve. -/
abbrev ComponentUnion {ι : Type*} (X : ι → Type*) := Sigma X

/-- The first point of a flag pair, as a point of the disjoint union of the components. -/
def fstPoint (d : NodalCurve ι Flag X) (f : Flag) : ComponentUnion X := ⟨d.fst f, d.fstPt f⟩

/-- The second point of a flag pair, as a point of the disjoint union of the components. -/
def sndPoint (d : NodalCurve ι Flag X) (f : Flag) : ComponentUnion X := ⟨d.snd f, d.sndPt f⟩

/-- The generating relation of the gluing: two points of the disjoint union are related when they
are the two points of one flag pair. -/
def flagRel (d : NodalCurve ι Flag X) (x y : ComponentUnion X) : Prop :=
  ∃ f : Flag, (x = fstPoint d f ∧ y = sndPoint d f) ∨ (x = sndPoint d f ∧ y = fstPoint d f)

/-- Two flag pairs are *adjacent* when they share a point of the disjoint union: the point at
which one of them is glued is the point at which the other one is glued. -/
def flagAdjacent (d : NodalCurve ι Flag X) (f g : Flag) : Prop :=
  ∃ z : ComponentUnion X,
    (z = fstPoint d f ∨ z = sndPoint d f) ∧ (z = fstPoint d g ∨ z = sndPoint d g)

/-- Adjacency of flag pairs is symmetric. -/
theorem flagAdjacent_symm {f g : Flag} (h : flagAdjacent d f g) : flagAdjacent d g f := by
  rcases h with ⟨z, hz₁, hz₂⟩
  exact ⟨z, hz₂, hz₁⟩

/-- The flag pairs of `d` are adjacent. -/
instance instStdSymmFlagAdjacent : Std.Symm (flagAdjacent d) where
  symm _ _ h := flagAdjacent_symm d h

/-- Two flag pairs are glued at the *same node* when they are joined by a chain of adjacent flag
pairs.  This is the reflexive transitive closure of `flagAdjacent`. -/
def sameNode (d : NodalCurve ι Flag X) (f g : Flag) : Prop :=
  Relation.ReflTransGen (flagAdjacent d) f g

/-- Two flag pairs glued at the same node are related symmetrically. -/
theorem sameNode_symm {f g : Flag} (h : sameNode d f g) : sameNode d g f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (flagAdjacent_symm d hbc) ih

/-- A flag pair is glued at the same node as itself. -/
theorem sameNode_refl (f : Flag) : sameNode d f f := Relation.ReflTransGen.refl

/-- Flag pairs glued at the same node are transitive. -/
theorem sameNode_trans {f g h : Flag} (hfg : sameNode d f g) (hgh : sameNode d g h) :
    sameNode d f h := Relation.ReflTransGen.trans hfg hgh

/-- The equivalence relation generated by the flag pairs on the disjoint union of the
normalization components: two points are glued together when they are equal, or when they are
the points of two flag pairs that are glued at the same node. -/
def gluedRel (d : NodalCurve ι Flag X) (x y : ComponentUnion X) : Prop :=
  x = y ∨ ∃ f g : Flag,
    (x = fstPoint d f ∨ x = sndPoint d f) ∧
      (y = fstPoint d g ∨ y = sndPoint d g) ∧ sameNode d f g

/-- The glued relation is symmetric. -/
theorem gluedRel_symm {x y : ComponentUnion X} (h : gluedRel d x y) : gluedRel d y x := by
  rcases h with h | ⟨f, g, hx, hy, hfg⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨g, f, hy, hx, sameNode_symm d hfg⟩

/-- The glued relation is transitive. -/
theorem gluedRel_trans {x y z : ComponentUnion X} (h₁ : gluedRel d x y) (h₂ : gluedRel d y z) :
    gluedRel d x z := by
  rcases h₁ with h₁ | ⟨f, g, hx, hy, hfg⟩
  · rcases h₂ with h₂ | ⟨g', h, hy', hz, hgh⟩
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr ⟨g', h, h₁ ▸ hy', hz, hgh⟩
  · rcases h₂ with h₂ | ⟨g', h, hy', hz, hgh⟩
    · exact Or.inr ⟨f, g, hx, h₂ ▸ hy, hfg⟩
    · rcases hy with hy | hy <;> rcases hy' with hy' | hy'
      · exact Or.inr ⟨f, h, hx, hz, sameNode_trans d hfg (sameNode_trans d
          (Relation.ReflTransGen.single ⟨y, Or.inl hy, Or.inl hy'⟩) hgh)⟩
      · exact Or.inr ⟨f, h, hx, hz, sameNode_trans d hfg (sameNode_trans d
          (Relation.ReflTransGen.single ⟨y, Or.inl hy, Or.inr hy'⟩) hgh)⟩
      · exact Or.inr ⟨f, h, hx, hz, sameNode_trans d hfg (sameNode_trans d
          (Relation.ReflTransGen.single ⟨y, Or.inr hy, Or.inl hy'⟩) hgh)⟩
      · exact Or.inr ⟨f, h, hx, hz, sameNode_trans d hfg (sameNode_trans d
          (Relation.ReflTransGen.single ⟨y, Or.inr hy, Or.inr hy'⟩) hgh)⟩

/-- The glued relation is an equivalence relation. -/
instance instIsEquivGluedRel : IsEquiv (ComponentUnion X) (gluedRel d) where
  refl := fun _ => Or.inl rfl
  symm := by
    intro x y hxy
    exact gluedRel_symm d hxy
  trans := by
    intro x y z h₁ h₂
    exact gluedRel_trans d h₁ h₂

/-- The two points of a flag pair are identified by the generated relation. -/
theorem eqvGen_flagRel_of_flagPoints (f : Flag) {x z : ComponentUnion X}
    (hx : x = fstPoint d f ∨ x = sndPoint d f)
    (hz : z = fstPoint d f ∨ z = sndPoint d f) :
    Relation.EqvGen (flagRel d) x z := by
  rcases hx with hx | hx <;> rcases hz with hz | hz
  · subst hx; subst hz; exact Relation.EqvGen.refl _
  · subst hx; subst hz; exact Relation.EqvGen.rel _ _ ⟨f, Or.inl ⟨rfl, rfl⟩⟩
  · subst hx; subst hz; exact Relation.EqvGen.rel _ _ ⟨f, Or.inr ⟨rfl, rfl⟩⟩
  · subst hx; subst hz; exact Relation.EqvGen.refl _

/-- Adjacent flag pairs are glued together: all of their points are identified. -/
theorem eqvGen_flagRel_of_flagAdjacent {f g : Flag} (h : flagAdjacent d f g)
    {p : ComponentUnion X} (hp : p = fstPoint d f ∨ p = sndPoint d f)
    {q : ComponentUnion X} (hq : q = fstPoint d g ∨ q = sndPoint d g) :
    Relation.EqvGen (flagRel d) p q := by
  rcases h with ⟨w, hw₁, hw₂⟩
  exact Relation.EqvGen.trans p w q (eqvGen_flagRel_of_flagPoints d f hp hw₁)
    (eqvGen_flagRel_of_flagPoints d g hw₂ hq)

/-- Flag pairs glued at the same node have all their points identified. -/
theorem eqvGen_flagRel_of_sameNode {f g : Flag} (h : sameNode d f g)
    {p : ComponentUnion X} (hp : p = fstPoint d f ∨ p = sndPoint d f)
    {q : ComponentUnion X} (hq : q = fstPoint d g ∨ q = sndPoint d g) :
    Relation.EqvGen (flagRel d) p q := by
  induction h generalizing p q with
  | refl => exact eqvGen_flagRel_of_flagPoints d _ hp hq
  | tail h₁ hbc ih =>
    rcases hbc with ⟨w, hw₁, hw₂⟩
    have h₁ : Relation.EqvGen (flagRel d) p w := ih hp hw₁
    have h₂ : Relation.EqvGen (flagRel d) w q := eqvGen_flagRel_of_flagPoints d _ hw₂ hq
    exact Relation.EqvGen.trans p w q h₁ h₂

/-- The generating relation is contained in the glued relation. -/
theorem flagRel_le_gluedRel {x y : ComponentUnion X} (h : flagRel d x y) : gluedRel d x y := by
  rcases h with ⟨f, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact Or.inr ⟨f, f, Or.inl rfl, Or.inr rfl, sameNode_refl d f⟩
  · exact Or.inr ⟨f, f, Or.inr rfl, Or.inl rfl, sameNode_refl d f⟩

/-- **The generated relation is the transitive closure of the generating relation.**  The
equivalence relation `gluedRel` generated by the flag pairs is exactly `Relation.EqvGen` of the
generating relation `flagRel`: two points of the disjoint union are glued together precisely
when a chain of flag pairs joins them. -/
theorem gluedRel_iff_eqvGen (x y : ComponentUnion X) :
    gluedRel d x y ↔ Relation.EqvGen (flagRel d) x y := by
  constructor
  · intro h
    rcases h with h | ⟨f, g, hx, hy, hfg⟩
    · subst h; exact Relation.EqvGen.refl _
    · exact eqvGen_flagRel_of_sameNode d hfg hx hy
  · intro h
    exact (Relation.EqvGen.eqvGen_le (r := flagRel d) (r' := gluedRel d)
      fun _ _ h' => flagRel_le_gluedRel d h') x y h

/-- The flag pair `f` is joined to the flag pair `g` by a chain of at most `n` adjacent flag
pairs. -/
def flagReached (d : NodalCurve ι Flag X) (g : Flag) : Nat → Flag → Prop
  | 0, f => f = g
  | n + 1, f => flagReached d g n f ∨ ∃ h, flagReached d g n h ∧ flagAdjacent d f h

/-- The flag pairs joined to `g` by one more adjacent step are still joined to `g`. -/
theorem flagReached_succ {g : Flag} {n : Nat} {f : Flag} (h : flagReached d g n f) :
    flagReached d g (n + 1) f := Or.inl h

/-- The flag pairs joined to `g` by at most `m` steps are joined to `g` by at most `n` steps
whenever `m ≤ n`. -/
theorem flagReached_mono {g : Flag} {f : Flag} {m n : Nat} (h : m ≤ n)
    (hr : flagReached d g m f) : flagReached d g n f := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk]
  clear h hk
  induction k with
  | zero =>
    rw [Nat.add_zero]
    exact hr
  | succ k ih =>
    rw [Nat.add_succ]
    exact flagReached_succ d ih

/-- Two flag pairs glued at the same node are joined by a finite chain of adjacent flag pairs. -/
theorem exists_flagReached {f g : Flag} (h : sameNode d f g) :
    ∃ n, flagReached d g n f := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hxy _ ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, Or.inr ⟨_, hn, hxy⟩⟩

/-- A flag pair joined to `g` is joined to it by a chain of adjacent flag pairs whose entries are
pairwise distinct. -/
theorem exists_flagChain_minimal {g : Flag} :
    ∀ (n : Nat) (f : Flag), flagReached d g n f → (∀ m < n, ¬ flagReached d g m f) →
      ∃ l : List Flag, l.IsChain (flagAdjacent d) ∧ l.Nodup ∧ l.head? = some f ∧
        g ∈ l ∧ ∀ x ∈ l, flagReached d g n x := by
  intro n
  induction n with
  | zero =>
    intro f hf _
    have hfg : f = g := by simpa [flagReached] using hf
    refine ⟨[g], List.isChain_singleton g, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [hfg]
    · simp
    · simp [flagReached]
  | succ n ih =>
    intro f hf hmin
    rw [flagReached] at hf
    rcases hf with hf | ⟨h, hmem, hadj⟩
    · exact absurd hf (hmin n (Nat.lt_succ_self n))
    · have hfnot : ¬ flagReached d g n f := hmin n (Nat.lt_succ_self n)
      have hmin' : ∀ m < n, ¬ flagReached d g m h := by
        intro m hm hh
        have hstep : flagReached d g (m + 1) f := by
          rw [flagReached]; exact Or.inr ⟨h, hh, hadj⟩
        exact hfnot (flagReached_mono d (Nat.succ_le_of_lt hm) hstep)
      rcases ih h hmem hmin' with ⟨l, hl, hnodup, hhead, hgin, hmem'⟩
      refine ⟨f :: l, ?_, ?_, ?_, ?_, ?_⟩
      · refine hl.cons ?_
        intro y hy
        rw [hhead] at hy
        have hy' : h = y := by simpa using hy
        subst hy'
        exact hadj
      · refine hnodup.cons ?_
        intro hx
        exact hfnot (hmem' f hx)
      · simp
      · simp [hgin]
      · intro x hx
        rcases List.mem_cons.mp hx with hxf | hxl
        · subst hxf
          exact Or.inr ⟨h, hmem, hadj⟩
        · exact Or.inl (hmem' x hxl)

/-- **The chain-length bound.**  Two flag pairs that are glued at the same node are joined by a
chain of adjacent flag pairs whose entries are pairwise distinct.  Since the flag pairs form a
finite type, such a chain has length at most the number of flag pairs: the chain of flag pairs
that realises a node never needs to repeat a flag pair. -/
theorem exists_flagChain [Fintype Flag] {f g : Flag} (h : sameNode d f g) :
    ∃ l : List Flag, l.IsChain (flagAdjacent d) ∧ l.Nodup ∧ l.head? = some f ∧
      g ∈ l ∧ l.length ≤ Fintype.card Flag := by
  classical
  have hex : ∃ n, flagReached d g n f := exists_flagReached d h
  have hmin : ∀ m < Nat.find hex, ¬ flagReached d g m f := fun m hm => Nat.find_min hex hm
  have hn : flagReached d g (Nat.find hex) f := Nat.find_spec hex
  rcases exists_flagChain_minimal d (Nat.find hex) f hn hmin with
    ⟨l, hl, hnodup, hhead, hgin, _⟩
  exact ⟨l, hl, hnodup, hhead, hgin, List.Nodup.length_le_card hnodup⟩

/-- The disjoint union of Hausdorff spaces is Hausdorff. -/
instance instT2SpaceComponentUnion [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] :
    T2Space (ComponentUnion X) := by
  constructor
  · intro x y hxy
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    by_cases hij : i = j
    · subst hij
      have hab : a ≠ b := by
        intro hab
        apply hxy
        exact congrArg (Sigma.mk i) hab
      obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation (X := X i) hab
      have hUV' : ∀ ⦃a⦄, a ∈ U → a ∉ V := Set.disjoint_left.mp hUV
      refine ⟨Sigma.mk i '' U, Sigma.mk i '' V, ?_, ?_, ?_, ?_, ?_⟩
      · rw [isOpen_sigma_iff]
        intro k
        rcases eq_or_ne k i with rfl | hki
        · rw [preimage_image_eq _ sigma_mk_injective]
          exact hU
        · rw [preimage_image_sigmaMk_of_ne hki]
          exact isOpen_empty
      · rw [isOpen_sigma_iff]
        intro k
        rcases eq_or_ne k i with rfl | hki
        · rw [preimage_image_eq _ sigma_mk_injective]
          exact hV
        · rw [preimage_image_sigmaMk_of_ne hki]
          exact isOpen_empty
      · exact ⟨a, haU, rfl⟩
      · exact ⟨b, hbV, rfl⟩
      · refine Set.disjoint_left.2 fun a ha => ?_
        rcases ha with ⟨u, hu, hzu⟩
        refine fun hzv => ?_
        rcases hzv with ⟨v, hv, hvu⟩
        have huv : u = v := eq_of_heq (Sigma.mk.inj (hzu.trans hvu.symm)).2
        exact hUV' hu (huv ▸ hv)
    · refine ⟨Sigma.mk i '' (Set.univ : Set (X i)), Sigma.mk j '' (Set.univ : Set (X j)),
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [isOpen_sigma_iff]
        intro k
        rcases eq_or_ne k i with rfl | hki
        · rw [preimage_image_eq _ sigma_mk_injective]
          exact isOpen_univ
        · rw [preimage_image_sigmaMk_of_ne hki]
          exact isOpen_empty
      · rw [isOpen_sigma_iff]
        intro k
        rcases eq_or_ne k j with rfl | hkj
        · rw [preimage_image_eq _ sigma_mk_injective]
          exact isOpen_univ
        · rw [preimage_image_sigmaMk_of_ne hkj]
          exact isOpen_empty
      · exact ⟨a, Set.mem_univ _, rfl⟩
      · exact ⟨b, Set.mem_univ _, rfl⟩
      · refine Set.disjoint_left.2 fun a ha => ?_
        rcases ha with ⟨u, hu, hzu⟩
        refine fun hzv => ?_
        rcases hzv with ⟨v, hv, hvu⟩
        have huv : i = j := (Sigma.mk.inj (hzu.trans hvu.symm)).1
        exact absurd huv hij

/-- The disjoint union of finitely many compact spaces is compact. -/
instance instCompactSpaceComponentUnion [∀ i, TopologicalSpace (X i)] [Fintype ι]
    [∀ i, CompactSpace (X i)] : CompactSpace (ComponentUnion X) := by
  refine ⟨?_⟩
  have hunion : (Set.univ : Set (ComponentUnion X))
      = ⋃ i, Sigma.mk i '' (Set.univ : Set (X i)) := by
    ext ⟨i, x⟩
    simp
  rw [hunion]
  exact isCompact_iUnion fun i => isCompact_univ.image continuous_sigmaMk
/-- The points of the disjoint union that occur in a flag pair. -/
def flagPointSet (d : NodalCurve ι Flag X) : Set (ComponentUnion X) :=
  ⋃ f : Flag, {fstPoint d f, sndPoint d f}

/-- The two points of a flag pair, selected by a boolean. -/
def flagPoint (d : NodalCurve ι Flag X) (p : Flag × Bool) : ComponentUnion X :=
  if p.2 then sndPoint d p.1 else fstPoint d p.1

/-- A point of the disjoint union is a flag point when it occurs in a flag pair. -/
theorem mem_flagPointSet (d : NodalCurve ι Flag X) (x : ComponentUnion X) :
    x ∈ flagPointSet d ↔ ∃ f : Flag, x = fstPoint d f ∨ x = sndPoint d f := by
  simp [flagPointSet]

/-- The flag points of `d` form a finite set. -/
theorem flagPointSet_finite [Fintype Flag] : (flagPointSet d).Finite := by
  have hsub : flagPointSet d ⊆ flagPoint d '' (Set.univ : Set (Flag × Bool)) := by
    intro x hx
    obtain ⟨f, hx⟩ := (mem_flagPointSet d x).mp hx
    rcases hx with hx | hx
    · exact ⟨(f, false), Set.mem_univ _, by simp [flagPoint, hx]⟩
    · exact ⟨(f, true), Set.mem_univ _, by simp [flagPoint, hx]⟩
  exact (Set.finite_univ.image (flagPoint d)).subset hsub

/-- The product of the flag points of `d` with itself is a finite set. -/
theorem flagPointSet_prod_finite [Fintype Flag] :
    (flagPointSet d ×ˢ flagPointSet d).Finite := by
  have hsub : flagPointSet d ×ˢ flagPointSet d
      ⊆ (fun p : (Flag × Bool) × (Flag × Bool) => (flagPoint d p.1, flagPoint d p.2))
          '' (Set.univ : Set ((Flag × Bool) × (Flag × Bool))) := by
    intro z hz
    rcases hz with ⟨hx, hy⟩
    obtain ⟨f, hx⟩ := (mem_flagPointSet d z.1).mp hx
    obtain ⟨g, hy⟩ := (mem_flagPointSet d z.2).mp hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · refine ⟨((f, false), (g, false)), Set.mem_univ _, ?_⟩
      show (fstPoint d f, fstPoint d g) = z
      exact Prod.ext hx.symm hy.symm
    · refine ⟨((f, false), (g, true)), Set.mem_univ _, ?_⟩
      show (fstPoint d f, sndPoint d g) = z
      exact Prod.ext hx.symm hy.symm
    · refine ⟨((f, true), (g, false)), Set.mem_univ _, ?_⟩
      show (sndPoint d f, fstPoint d g) = z
      exact Prod.ext hx.symm hy.symm
    · refine ⟨((f, true), (g, true)), Set.mem_univ _, ?_⟩
      show (sndPoint d f, sndPoint d g) = z
      exact Prod.ext hx.symm hy.symm
  exact (Set.finite_univ.image _).subset hsub

/-- **The generated relation is closed.**  The equivalence relation generated by the flag pairs is a
closed subset of the product of the disjoint union of the normalization components with itself.
Indeed, away from the finitely many flag points the relation is the diagonal, and on the flag
points it is a finite set. -/
theorem gluedRel_isClosed [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [Fintype Flag] :
    IsClosed {p : ComponentUnion X × ComponentUnion X | gluedRel d p.1 p.2} := by
  set R : Set (ComponentUnion X × ComponentUnion X) := {p | gluedRel d p.1 p.2}
  have hsplit : R = (R ∩ (flagPointSet d ×ˢ flagPointSet d))
      ∪ diagonal (ComponentUnion X) := by
    apply Set.ext
    intro z
    constructor
    · intro hz
      by_cases hxy : z.1 = z.2
      · exact Or.inr hxy
      · left
        refine ⟨hz, ?_, ?_⟩
        · rcases (show gluedRel d z.1 z.2 from hz) with h | ⟨f, g, hx, hy, hfg⟩
          · exact absurd h hxy
          · exact (mem_flagPointSet d z.1).mpr ⟨f, hx⟩
        · rcases (show gluedRel d z.1 z.2 from hz) with h | ⟨f, g, hx, hy, hfg⟩
          · exact absurd h hxy
          · exact (mem_flagPointSet d z.2).mpr ⟨g, hy⟩
    · intro hz
      rcases hz with h | h
      · exact h.1
      · exact Or.inl h
  rw [hsplit]
  have hR1 : (R ∩ (flagPointSet d ×ˢ flagPointSet d)).Finite :=
    (flagPointSet_prod_finite d).subset fun _ hz => hz.2
  exact hR1.isClosed.union isClosed_diagonal

/-- The glued relation, as an equivalence relation. -/
theorem gluedRel_equivalence : Equivalence (gluedRel d) where
  refl := fun _ => Or.inl rfl
  symm := fun h => gluedRel_symm d h
  trans := fun h₁ h₂ => gluedRel_trans d h₁ h₂

/-- The generated relation as a setoid: the equivalence relation on the disjoint union of the
normalization components that glues the points of the flag pairs together. -/
def gluedRelSetoid (d : NodalCurve ι Flag X) : Setoid (ComponentUnion X) :=
  Setoid.mk (gluedRel d) (gluedRel_equivalence d)

/-- **The glued space.**  The quotient of the disjoint union of the normalization components by the
generated relation: the underlying topological space of the nodal curve.  The topology is the
quotient topology, i.e. the finest topology making the quotient map continuous. -/
abbrev gluedCurve (d : NodalCurve ι Flag X) :=
  Quotient (gluedRelSetoid d)

/-- The quotient map from the disjoint union of the normalization components to the glued
curve. -/
def gluedCurveQuotientMap (d : NodalCurve ι Flag X) : ComponentUnion X → gluedCurve d :=
  Quotient.mk (gluedRelSetoid d)

/-- The quotient map is continuous. -/
theorem continuous_gluedCurveQuotientMap (d : NodalCurve ι Flag X)
    [∀ i, TopologicalSpace (X i)] : Continuous (gluedCurveQuotientMap d) :=
  continuous_quotient_mk' (s := gluedRelSetoid d)

/-- **The quotient topology.**  A subset of the glued curve is open exactly when its inverse image
under the quotient map is open in the disjoint union of the normalization components. -/
theorem isOpen_iff_preimage {U : Set (gluedCurve d)} [∀ i, TopologicalSpace (X i)] :
    IsOpen U ↔ IsOpen (gluedCurveQuotientMap d ⁻¹' U) := by
  rw [isOpen_coinduced]
  rfl

/-- **The glued space is compact.**  The quotient of a compact space is compact, so the glued curve
is compact as soon as the finitely many normalization components are compact. -/
instance instCompactSpaceGluedCurve (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [Fintype ι] [∀ i, CompactSpace (X i)] : CompactSpace (gluedCurve d) :=
  Quotient.compactSpace (s := gluedRelSetoid d)

/-- The generated relation relates two points of the disjoint union only when they are equal or
when both of them are flag points. -/
theorem gluedRel_flagPoints {a b : ComponentUnion X} (h : gluedRel d a b) :
    a = b ∨ (a ∈ flagPointSet d ∧ b ∈ flagPointSet d) := by
  rcases h with h | ⟨f, g, ha, hb, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, ha⟩, (mem_flagPointSet d b).mpr ⟨g, hb⟩⟩

/-- The quotient map identifies two points of the disjoint union exactly when the generated
relation relates them. -/
theorem gluedRel_iff_quotientMk_eq {a b : ComponentUnion X} :
    gluedCurveQuotientMap d a = gluedCurveQuotientMap d b ↔ gluedRel d a b := by
  constructor
  · intro h
    exact (Quotient.eq (r := gluedRelSetoid d) (x := a) (y := b)).mp h
  · intro h
    exact (Quotient.eq (r := gluedRelSetoid d) (x := a) (y := b)).mpr h

/-- **The node set.**  The image of the flag points in the glued curve: the singular locus of the
nodal curve. -/
def nodeSet (d : NodalCurve ι Flag X) : Set (gluedCurve d) :=
  gluedCurveQuotientMap d '' flagPointSet d

/-- The node set is the image of the flag pairs: a point of the glued curve is a node exactly when
it is the image of one of the two points of a flag pair. -/
theorem mem_nodeSet {q : gluedCurve d} :
    q ∈ nodeSet d ↔ ∃ f : Flag,
      q = gluedCurveQuotientMap d (fstPoint d f) ∨
        q = gluedCurveQuotientMap d (sndPoint d f) := by
  rw [nodeSet, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hqx⟩
    obtain ⟨f, hx'⟩ := (mem_flagPointSet d x).mp hx
    rcases hx' with hx' | hx'
    · exact ⟨f, Or.inl (hx' ▸ hqx.symm)⟩
    · exact ⟨f, Or.inr (hx' ▸ hqx.symm)⟩
  · rintro ⟨f, hq | hq⟩
    · exact ⟨fstPoint d f, (mem_flagPointSet d _).mpr ⟨f, Or.inl rfl⟩, hq.symm⟩
    · exact ⟨sndPoint d f, (mem_flagPointSet d _).mpr ⟨f, Or.inr rfl⟩, hq.symm⟩

/-- The node point of a flag pair: the image of its first point in the glued curve. -/
def nodeOfFlag (d : NodalCurve ι Flag X) (f : Flag) : gluedCurve d :=
  gluedCurveQuotientMap d (fstPoint d f)

/-- The generated relation relates two flag points exactly when the flag pairs are glued at the
same node. -/
theorem gluedRel_of_flagPoints {f g : Flag} {p q : ComponentUnion X}
    (hp : p = fstPoint d f ∨ p = sndPoint d f)
    (hq : q = fstPoint d g ∨ q = sndPoint d g) :
    gluedRel d p q ↔ sameNode d f g := by
  constructor
  · intro h
    rcases h with h | ⟨f', g', hp', hq', hfg⟩
    · exact Relation.ReflTransGen.single ⟨p, hp, h.symm ▸ hq⟩
    · exact Relation.ReflTransGen.head ⟨p, hp, hp'⟩
        (Relation.ReflTransGen.trans hfg (Relation.ReflTransGen.single ⟨q, hq', hq⟩))
  · intro h
    exact Or.inr ⟨f, g, hp, hq, h⟩

/-- **The fibres of the flag-pair map.**  Two flag pairs determine the same node of the glued
curve exactly when they are glued at the same node; in particular the fibre of `nodeOfFlag` over
the node of `f` is the set of the flag pairs glued at the same node as `f`. -/
theorem nodeOfFlag_eq_iff (f g : Flag) :
    nodeOfFlag d f = nodeOfFlag d g ↔ f = g ∨ sameNode d f g := by
  constructor
  · intro h
    have h' : gluedRel d (fstPoint d f) (fstPoint d g) :=
      (gluedRel_iff_quotientMk_eq d).mp h
    exact Or.inr ((gluedRel_of_flagPoints d (f := f) (g := g) (Or.inl rfl) (Or.inl rfl)).mp h')
  · rintro (rfl | hfg)
    · rfl
    · exact (gluedRel_iff_quotientMk_eq d).mpr
        ((gluedRel_of_flagPoints d (f := f) (g := g) (Or.inl rfl) (Or.inl rfl)).mpr hfg)

/-- The flag-pair map to the node set is injective when the flag pairs are pairwise distinct
nodes, that is, when no two distinct flag pairs are glued at the same node. -/
theorem nodeOfFlag_injective (hdiff : ∀ f g : Flag, f ≠ g → ¬ sameNode d f g) :
    Function.Injective (nodeOfFlag d) := by
  intro f g hfg
  by_cases hne : f = g
  · exact hne
  · rcases (nodeOfFlag_eq_iff d f g).mp hfg with h | h
    · exact absurd h hne
    · exact absurd h (hdiff f g hne)

/-- **The node set is the image of the flag pairs.**  The node set of the glued curve is the image
of the flag pairs under the quotient map: the two points of a flag pair are glued together, so the
image of the flag points is the image of the first points of the flag pairs. -/
theorem nodeSet_eq_image_nodeOfFlag (d : NodalCurve ι Flag X) :
    nodeSet d = nodeOfFlag d '' (Set.univ : Set Flag) := by
  ext q
  constructor
  · intro hq
    rw [nodeSet] at hq
    obtain ⟨x, hx, hqx⟩ := (Set.mem_image _ _ _).mp hq
    obtain ⟨f, hxf⟩ := (mem_flagPointSet d x).mp hx
    refine ⟨f, Set.mem_univ _, ?_⟩
    have hglue : gluedRel d (fstPoint d f) (sndPoint d f) :=
      (gluedRel_of_flagPoints d (f := f) (g := f) (Or.inl rfl) (Or.inr rfl)).mpr
        (sameNode_refl d f)
    rcases hxf with hxf | hxf
    · exact (hxf ▸ hqx.symm).symm
    · exact ((hxf ▸ hqx.symm).trans
        ((gluedRel_iff_quotientMk_eq d).mpr (gluedRel_symm d hglue))).symm
  · intro hq
    obtain ⟨f, _, hqf⟩ := hq
    rw [nodeSet]
    exact (Set.mem_image _ _ _).mpr
      ⟨fstPoint d f, (mem_flagPointSet d _).mpr ⟨f, Or.inl rfl⟩, hqf⟩

/-- The node set of the glued curve is finite: it is the image of the finite set of flag points. -/
theorem nodeSet_finite [Fintype Flag] : (nodeSet d).Finite :=
  (flagPointSet_finite d).image _

/-- **The node set is closed.**  The node set of the glued curve is a closed subset of it, so the
smooth locus, its complement, is open. -/
theorem isClosed_nodeSet (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Fintype Flag] : IsClosed (nodeSet d) := by
  refine ⟨?_⟩
  rw [isOpen_iff_preimage, Set.preimage_compl]
  have hpre : gluedCurveQuotientMap d ⁻¹' nodeSet d = flagPointSet d := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hyF, hqy⟩ : ∃ y ∈ flagPointSet d, gluedCurveQuotientMap d y
          = gluedCurveQuotientMap d x := by
        simpa [nodeSet] using hx
      have hrel : gluedRel d y x := (gluedRel_iff_quotientMk_eq d).mp hqy
      rcases (gluedRel_flagPoints d hrel) with heq | ⟨_, hxF⟩
      · exact heq ▸ hyF
      · exact hxF
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre]
  exact (flagPointSet_finite d).isClosed.isOpen_compl

/-- **The smooth locus.**  The complement of the node set in the glued curve: the points at which
the nodal curve is smooth. -/
def smoothLocus (d : NodalCurve ι Flag X) : Set (gluedCurve d) := (nodeSet d)ᶜ

/-- The smooth locus is open, being the complement of the closed node set. -/
theorem isOpen_smoothLocus (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Fintype Flag] : IsOpen (smoothLocus d) :=
  (isClosed_nodeSet d).isOpen_compl

/-- A point of the disjoint union that is not a flag point is not mapped to a node. -/
theorem not_mem_nodeSet_of_not_mem_flagPointSet {x : ComponentUnion X}
    (hx : x ∉ flagPointSet d) : gluedCurveQuotientMap d x ∉ nodeSet d := by
  intro hx'
  obtain ⟨y, hyF, hqy⟩ : ∃ y ∈ flagPointSet d, gluedCurveQuotientMap d y
      = gluedCurveQuotientMap d x := by
    simpa [nodeSet] using hx'
  have hrel : gluedRel d y x := (gluedRel_iff_quotientMk_eq d).mp hqy
  rcases (gluedRel_flagPoints d hrel) with heq | ⟨_, hxF⟩
  · exact hx (heq ▸ hyF)
  · exact hx hxF

/-- The quotient map is injective away from the flag points. -/
theorem gluedCurveQuotientMap_injective_of_not_flagPoint {x y : ComponentUnion X}
    (hx : x ∉ flagPointSet d) (h : gluedCurveQuotientMap d x = gluedCurveQuotientMap d y) :
    x = y := by
  have hrel : gluedRel d x y := (gluedRel_iff_quotientMk_eq d).mp h
  rcases (gluedRel_flagPoints d hrel) with heq | ⟨hxF, _⟩
  · exact heq
  · exact absurd hxF hx

/-- The quotient map, restricted to the smooth locus of the disjoint union of the normalization
components, i.e. to the points that are not flag points. -/
def gluedCurveQuotientMapOnSmooth (d : NodalCurve ι Flag X)
    (x : {x : ComponentUnion X | x ∉ flagPointSet d}) : {q : gluedCurve d | q ∉ nodeSet d} :=
  ⟨gluedCurveQuotientMap d x.1, not_mem_nodeSet_of_not_mem_flagPointSet d x.2⟩

/-- **The quotient map is a homeomorphism of the smooth loci.**  The disjoint union of the
normalization components minus the flag points is homeomorphic to the smooth locus of the glued
curve, the complement of the node set; the homeomorphism is the restriction of the quotient map.
It is a bijection because the quotient map is injective away from the flag points, it is continuous
because the quotient map is, and it is open because the inverse image of the image of an open set
of the smooth locus under the quotient map is that very open set. -/
theorem gluedCurveQuotientMapOnSmooth_isHomeomorph (d : NodalCurve ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [Fintype Flag] :
    IsHomeomorph (gluedCurveQuotientMapOnSmooth d) := by
  have hS : IsOpen {x : ComponentUnion X | x ∉ flagPointSet d} :=
    (flagPointSet_finite d).isClosed.isOpen_compl
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (fun x : {x : ComponentUnion X | x ∉ flagPointSet d} =>
        gluedCurveQuotientMap d x.1) :=
      Continuous.comp (continuous_gluedCurveQuotientMap d) continuous_subtype_val
    exact Continuous.subtype_mk hcont (fun x => not_mem_nodeSet_of_not_mem_flagPointSet d x.2)
  · intro s hs
    have hopen_α : IsOpen (s : Set (ComponentUnion X)) := by
      have h := hS.isOpenEmbedding_subtypeVal.isOpenMap s hs
      exact h
    have hq : IsOpen (gluedCurveQuotientMap d '' (s : Set (ComponentUnion X))) := by
      rw [isOpen_iff_preimage]
      have hpre : gluedCurveQuotientMap d ⁻¹' (gluedCurveQuotientMap d ''
          (s : Set (ComponentUnion X))) = (s : Set (ComponentUnion X)) := by
        ext x
        constructor
        · intro hx
          obtain ⟨z, hz, hqz⟩ := hx
          obtain ⟨w, hw, hzw⟩ := hz
          have hnotF : w.1 ∉ flagPointSet d := w.2
          have hrel : gluedRel d w.1 x := (gluedRel_iff_quotientMk_eq d).mp (hzw ▸ hqz)
          rcases (gluedRel_flagPoints d hrel) with heq | ⟨hwF, _⟩
          · exact ⟨w, hw, heq⟩
          · exact absurd hwF hnotF
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hpre]
      exact hopen_α
    refine (isOpen_induced_iff
      (f := (Subtype.val : {q : gluedCurve d | q ∉ nodeSet d} → gluedCurve d))).2
      ⟨gluedCurveQuotientMap d '' (s : Set (ComponentUnion X)), hq, ?_⟩
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hqz⟩ := hy
      obtain ⟨w, hw, hzw⟩ := hz
      refine ⟨w, hw, ?_⟩
      apply Subtype.ext
      exact (congrArg (fun t => gluedCurveQuotientMap d t) hzw).trans hqz
    · intro hy
      obtain ⟨w, hw, hwf⟩ := hy
      refine ⟨w.1, ⟨w, hw, rfl⟩, ?_⟩
      exact congrArg Subtype.val hwf
  · refine ⟨?_, ?_⟩
    · intro x y hxy
      have hxy' : gluedCurveQuotientMap d x.1 = gluedCurveQuotientMap d y.1 :=
        congrArg Subtype.val hxy
      exact Subtype.ext (gluedCurveQuotientMap_injective_of_not_flagPoint d x.2 hxy')
    · intro y
      obtain ⟨x, hx⟩ := @Quotient.exists_rep _ (gluedRelSetoid d) y.1
      have hnotF : x ∉ flagPointSet d := by
        intro hxF
        apply y.2
        exact ⟨x, hxF, hx⟩
      refine ⟨⟨x, hnotF⟩, ?_⟩
      apply Subtype.ext
      exact hx

end TauCeti.ComplexCurveModuli
