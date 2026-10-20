/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Quot
public import Mathlib.Logic.Relation
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
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
  The data carry one hypothesis: the flag points are pairwise distinct
  (`flagPoints_injective`).  The two points of one flag pair are different, and no point of the
  disjoint union occurs in two different flag pairs.  This is what makes the data the data of a
  *nodal* curve and not of an arbitrary gluing of curves along points: every singularity of the
  glued curve is then a plain node, at which exactly two branches meet.
* `Sigma X` is the disjoint union of the normalization components, with the coproduct topology.
  It is Hausdorff as soon as the components are (Mathlib's `Sigma.t2Space`).
* `flagRel` is the generating relation: the two points of one flag pair are related.
* `flagAdjacent` and `sameNode` relate two flag pairs that are glued at the same node, the second
  through a chain of the first.  Because the flag points are pairwise distinct, two flag pairs
  share a point only when they are the same flag pair, so both relations are simply equality
  (`flagAdjacent_iff`, `sameNode_iff`).
* `gluedRel` is the equivalence relation *generated* by the flag pairs.  Because the flag points
  are pairwise distinct, a chain of flag pairs has at most one step, so the generated relation is
  simply "the two points are equal, or they are the two points of one flag pair"; this is the
  content of the definition of `gluedRel` itself.  It is symmetric and transitive
  (`gluedRel_symm`, `gluedRel_trans`), hence an equivalence relation (`gluedRel_equivalence`), and
  it relates two points only when they are equal or when both of them are flag points
  (`gluedRel_flagPoints`).  It is also exactly the equivalence closure `Relation.EqvGen` of the
  generating relation (`gluedRel_iff_eqvGen`).
* `gluedCurve` is the quotient of the disjoint union by that relation: the underlying space of
  the nodal curve.  It is the `Quotient` of the disjoint union by the setoid `gluedRelSetoid`,
  with the quotient topology: a subset of the glued curve is open exactly when its inverse image
  under the quotient map `Quotient.mk (gluedRelSetoid d)` is open in the disjoint union
  (Mathlib's `isOpen_coinduced` for the coinduced quotient topology).  The quotient map is
  continuous (`continuous_quotient_mk'`) and identifies two points exactly when the generated
  relation relates them (`Quotient.eq`).  The glued space is compact whenever the normalization
  components are compact (`isCompact_gluedCurve`).
* `nodeSet` is the image of the flag points in the glued curve: the singular locus of the curve.
  It is the image of the flag pairs (`mem_nodeSet`, `nodeSet_eq_image_nodeOfFlag`), it is finite
  (`nodeSet_finite`) and it is closed (`isClosed_nodeSet`).  The map `nodeOfFlag` sends a flag
  pair to its node; two flag pairs have the same node exactly when they are the same flag pair
  (`nodeOfFlag_eq_iff`), so `nodeOfFlag` is injective (`nodeOfFlag_injective`).
* The complement of the node set is the *smooth locus* `smoothLocus`, which is open
  (`isOpen_smoothLocus`).  The quotient map restricts to a homeomorphism from the disjoint union
  of the normalization components minus their flag points onto the smooth locus
  (`gluedCurveQuotientMapOnSmooth_isHomeomorph`): the restriction is injective away from the
  flag points (`gluedCurveQuotientMap_injective_of_not_flagPoint`), and it is a quotient map
  because it is the restriction of the quotient map to the preimage of the open smooth locus.

**Scope.** This file is the topological, pre-hypersurface-chart part of the quoted sentence.  What
is proved is:

* the glued space is built: it is the quotient of the disjoint union of the normalization
  components by the generated relation, endowed with the quotient topology; the quotient map is
  continuous; and the glued space is compact when the normalization components are
  (`isCompact_gluedCurve`);
* the generated relation is closed (`gluedRel_isClosed`);
* the node set, the image of the flag pairs, is closed, and the quotient map identifies the
  disjoint union minus the flag points homeomorphically with the complement of the node set;
* the nodes of the glued curve are in bijection with the flag pairs: `nodeOfFlag` is injective
  (`nodeOfFlag_injective`), its image is the node set (`nodeSet_eq_image_nodeOfFlag`), and every
  node is the node of a flag pair (`exists_flag_of_mem_nodeSet`).

What is **not** proved here:

* the **Hausdorff** part of the quoted sentence: the glued space is not shown to be Hausdorff.
  Its equivalence classes are finite -- the class of a point that is not a flag point is a
  singleton, and the class of a flag point is the pair of points of its flag pair
  (the content of the definition of `gluedRel`) -- but the passage from finiteness of the
  classes, closedness of the quotient map and normality of the disjoint union to the Hausdorff
  property of the quotient is not carried out here.
* the **biholomorphic** refinement of "the complement maps locally biholomorphic": the glued
  space carries no complex structure on its smooth locus, so there is nothing for a biholomorphism
  to be a morphism between.
* the **dual graph** of the nodal curve: the flag pairs are the edges of the dual graph of a nodal
  curve, and the nodes of the glued curve are in bijection with the flag pairs, but the graph
  itself, with its vertices and its incidence relations, is not built in this file.

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

/-- The disjoint union of the normalization components of a nodal curve. -/
abbrev ComponentUnion {ι : Type*} (X : ι → Type*) := Sigma X

/-- The gluing data of a nodal curve: the finitely many flag pairs at which the normalization
components are glued.  A flag pair `f` names the two components `fst f` and `snd f` together with
the points `fstPt f` and `sndPt f` of those components that are identified.

The field `flagPoints_injective` says that the flag points are pairwise distinct: the two points
of one flag pair are different, and no point of the disjoint union occurs in two different flag
pairs.  This is the hypothesis that makes the data the data of a nodal curve rather than of an
arbitrary gluing of curves along points. -/
structure NodalCurve (ι : Type*) (Flag : Type*) (X : ι → Type*) where
  /-- The first component glued at a flag pair. -/
  fst : Flag → ι
  /-- The second component glued at a flag pair. -/
  snd : Flag → ι
  /-- The point of the first component at a flag pair. -/
  fstPt : ∀ f : Flag, X (fst f)
  /-- The point of the second component at a flag pair. -/
  sndPt : ∀ f : Flag, X (snd f)
  /-- The flag points are pairwise distinct: the two points of one flag pair are different, and
  no point of the disjoint union occurs in two different flag pairs. -/
  flagPoints_injective : Function.Injective (fun p : Flag × Bool =>
    if p.2 then (⟨snd p.1, sndPt p.1⟩ : ComponentUnion X)
    else (⟨fst p.1, fstPt p.1⟩ : ComponentUnion X))

variable (d : NodalCurve ι Flag X)

/-- The first point of a flag pair, as a point of the disjoint union of the components. -/
def fstPoint (d : NodalCurve ι Flag X) (f : Flag) : ComponentUnion X := ⟨d.fst f, d.fstPt f⟩

/-- The second point of a flag pair, as a point of the disjoint union of the components. -/
def sndPoint (d : NodalCurve ι Flag X) (f : Flag) : ComponentUnion X := ⟨d.snd f, d.sndPt f⟩

/-- The two points of a flag pair, selected by a boolean: `false` selects the first point of the
flag pair, `true` the second. -/
def flagPoint (d : NodalCurve ι Flag X) (p : Flag × Bool) : ComponentUnion X :=
  if p.2 then sndPoint d p.1 else fstPoint d p.1

/-- **The flag points are pairwise distinct.**  The points of the disjoint union that are glued --
the flag points -- are pairwise distinct: the two points of one flag pair are different, and no
point occurs in two different flag pairs. -/
theorem flagPoint_injective (d : NodalCurve ι Flag X) : Function.Injective (flagPoint d) :=
  d.flagPoints_injective

/-- The first point of a flag pair, as a flag point. -/
theorem fstPoint_eq_flagPoint (d : NodalCurve ι Flag X) (f : Flag) :
    fstPoint d f = flagPoint d (f, false) := by
  simp [flagPoint]

/-- The second point of a flag pair, as a flag point. -/
theorem sndPoint_eq_flagPoint (d : NodalCurve ι Flag X) (f : Flag) :
    sndPoint d f = flagPoint d (f, true) := by
  simp [flagPoint]

/-- Two flag pairs with the same first point are the same flag pair. -/
theorem fstPoint_injective (d : NodalCurve ι Flag X) (f g : Flag)
    (h : fstPoint d f = fstPoint d g) : f = g := by
  have h' : flagPoint d (f, false) = flagPoint d (g, false) :=
    (fstPoint_eq_flagPoint d f).symm.trans (h.trans (fstPoint_eq_flagPoint d g))
  exact (Prod.ext_iff.mp (flagPoint_injective d h')).1

/-- Two flag pairs with the same second point are the same flag pair. -/
theorem sndPoint_injective (d : NodalCurve ι Flag X) (f g : Flag)
    (h : sndPoint d f = sndPoint d g) : f = g := by
  have h' : flagPoint d (f, true) = flagPoint d (g, true) :=
    (sndPoint_eq_flagPoint d f).symm.trans (h.trans (sndPoint_eq_flagPoint d g))
  exact (Prod.ext_iff.mp (flagPoint_injective d h')).1

/-- The first point of a flag pair is never the second point of a flag pair: a flag pair never
pairs a point with itself. -/
theorem fstPoint_ne_sndPoint (d : NodalCurve ι Flag X) (f g : Flag) :
    fstPoint d f ≠ sndPoint d g := by
  intro h
  have h' : flagPoint d (f, false) = flagPoint d (g, true) :=
    (fstPoint_eq_flagPoint d f).symm.trans (h.trans (sndPoint_eq_flagPoint d g))
  obtain ⟨_, hbt⟩ := Prod.ext_iff.mp (flagPoint_injective d h')
  simp at hbt

/-- The second point of a flag pair is never the first point of a flag pair. -/
theorem sndPoint_ne_fstPoint (d : NodalCurve ι Flag X) (f g : Flag) :
    sndPoint d f ≠ fstPoint d g :=
  fun h => fstPoint_ne_sndPoint d g f h.symm

/-- A flag point belongs to a unique flag pair. -/
theorem eq_of_flagPoint_mem (d : NodalCurve ι Flag X) {f g : Flag} {p : ComponentUnion X}
    (hp : p = fstPoint d f ∨ p = sndPoint d f)
    (hq : p = fstPoint d g ∨ p = sndPoint d g) : f = g := by
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact fstPoint_injective d f g (hp.symm.trans hq)
  · exact absurd (hp.symm.trans hq) (fstPoint_ne_sndPoint d f g)
  · exact absurd (hp.symm.trans hq) (sndPoint_ne_fstPoint d f g)
  · exact sndPoint_injective d f g (hp.symm.trans hq)

/-- The generating relation of the gluing: two points of the disjoint union are related when they
are the two points of one flag pair. -/
def flagRel (d : NodalCurve ι Flag X) (x y : ComponentUnion X) : Prop :=
  ∃ f : Flag, (x = fstPoint d f ∧ y = sndPoint d f) ∨ (x = sndPoint d f ∧ y = fstPoint d f)

/-- The generating relation is symmetric. -/
theorem flagRel_symm (d : NodalCurve ι Flag X) {x y : ComponentUnion X} (h : flagRel d x y) :
    flagRel d y x := by
  rcases h with ⟨f, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact ⟨f, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨f, Or.inl ⟨rfl, rfl⟩⟩
/-- Two flag pairs are *adjacent* when they share a point of the disjoint union: the point at
which one of them is glued is the point at which the other one is glued. -/
def flagAdjacent (d : NodalCurve ι Flag X) (f g : Flag) : Prop :=
  ∃ z : ComponentUnion X,
    (z = fstPoint d f ∨ z = sndPoint d f) ∧ (z = fstPoint d g ∨ z = sndPoint d g)

/-- **Adjacency is equality.**  The flag points are pairwise distinct, so two flag pairs share a
point of the disjoint union only when they are the same flag pair. -/
theorem flagAdjacent_iff (d : NodalCurve ι Flag X) (f g : Flag) :
    flagAdjacent d f g ↔ f = g := by
  constructor
  · intro h
    obtain ⟨z, hz₁, hz₂⟩ := h
    exact eq_of_flagPoint_mem d hz₁ hz₂
  · intro h
    subst h
    exact ⟨fstPoint d f, Or.inl rfl, Or.inl rfl⟩

/-- Two flag pairs are glued at the *same node* when they are joined by a chain of adjacent flag
pairs.  This is the reflexive transitive closure of `flagAdjacent`. -/
def sameNode (d : NodalCurve ι Flag X) (f g : Flag) : Prop :=
  Relation.ReflTransGen (flagAdjacent d) f g

/-- **Same node is equality.**  The flag points are pairwise distinct, so a chain of adjacent flag
pairs has length at most one: two flag pairs are glued at the same node exactly when they are the
same flag pair. -/
theorem sameNode_iff (d : NodalCurve ι Flag X) (f g : Flag) : sameNode d f g ↔ f = g := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans ((flagAdjacent_iff d _ _).mp hbc)
  · intro h
    subst h
    exact Relation.ReflTransGen.refl

/-- **The flag pairs form a matching.**  Two flag relations that meet in a point glue the same two
points: the flag points being pairwise distinct forces the two flag pairs to be equal, so a chain
of flag pairs has length at most one. -/
theorem flagRel_chain (d : NodalCurve ι Flag X) {x y z : ComponentUnion X}
    (h₁ : flagRel d x y) (h₂ : flagRel d y z) : x = z := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  rcases hf with ⟨hxf, hyf⟩ | ⟨hxf, hyf⟩
  · rcases hg with ⟨hyg, hzg⟩ | ⟨hyg, hzg⟩
    · exact absurd (hyf.symm.trans hyg) (sndPoint_ne_fstPoint d f g)
    · have hfg : f = g := eq_of_flagPoint_mem d (p := y) (Or.inr hyf) (Or.inr hyg)
      exact hxf.trans ((congrArg (fun f => fstPoint d f) hfg).trans hzg.symm)
  · rcases hg with ⟨hyg, hzg⟩ | ⟨hyg, hzg⟩
    · have hfg : f = g := eq_of_flagPoint_mem d (p := y) (Or.inl hyf) (Or.inl hyg)
      exact hxf.trans ((congrArg (fun f => sndPoint d f) hfg).trans hzg.symm)
    · exact absurd (hyf.symm.trans hyg) (fstPoint_ne_sndPoint d f g)

/-- **The equivalence relation generated by the flag pairs.**  Two points of the disjoint union are
glued together exactly when they are equal, or when they are the two points of one flag pair.
Because the flag points are pairwise distinct, no chain of flag pairs has more than one step, so
this is exactly the relation generated by the flag pairs. -/
def gluedRel (d : NodalCurve ι Flag X) (x y : ComponentUnion X) : Prop :=
  x = y ∨ ∃ f : Flag,
    (x = fstPoint d f ∧ y = sndPoint d f) ∨ (x = sndPoint d f ∧ y = fstPoint d f)

/-- The glued relation is symmetric. -/
theorem gluedRel_symm (d : NodalCurve ι Flag X) {x y : ComponentUnion X} (h : gluedRel d x y) :
    gluedRel d y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · rcases h with ⟨f, h | h⟩
    · exact Or.inr ⟨f, Or.inr ⟨h.2, h.1⟩⟩
    · exact Or.inr ⟨f, Or.inl ⟨h.2, h.1⟩⟩

/-- The glued relation is transitive. -/
theorem gluedRel_trans (d : NodalCurve ι Flag X) {x y z : ComponentUnion X}
    (h₁ : gluedRel d x y) (h₂ : gluedRel d y z) : gluedRel d x z := by
  rcases h₁ with h₁ | ⟨f, hf⟩
  · rcases h₂ with h₂ | ⟨g, hg⟩
    · exact Or.inl (h₁.trans h₂)
    · rcases hg with hg | hg
      · exact Or.inr ⟨g, Or.inl ⟨h₁.symm ▸ hg.1, hg.2⟩⟩
      · exact Or.inr ⟨g, Or.inr ⟨h₁.symm ▸ hg.1, hg.2⟩⟩
  · rcases h₂ with h₂ | ⟨g, hg⟩
    · rcases hf with hf | hf
      · exact Or.inr ⟨f, Or.inl ⟨hf.1, h₂ ▸ hf.2⟩⟩
      · exact Or.inr ⟨f, Or.inr ⟨hf.1, h₂ ▸ hf.2⟩⟩
    · exact Or.inl (flagRel_chain d ⟨f, hf⟩ ⟨g, hg⟩)

/-- The generating relation is contained in the glued relation. -/
theorem flagRel_le_gluedRel (d : NodalCurve ι Flag X) {x y : ComponentUnion X}
    (h : flagRel d x y) : gluedRel d x y :=
  Or.inr h

/-- **The relation between two flag points.**  Two flag points of the glued curve are identified
exactly when they belong to the same flag pair. -/
theorem gluedRel_of_flagPoints (d : NodalCurve ι Flag X) {f g : Flag} {p q : ComponentUnion X}
    (hp : p = fstPoint d f ∨ p = sndPoint d f)
    (hq : q = fstPoint d g ∨ q = sndPoint d g) :
    gluedRel d p q ↔ f = g := by
  constructor
  · intro h
    rcases h with h | ⟨c, hc⟩
    · have hpg : p = fstPoint d g ∨ p = sndPoint d g := by
        rcases hq with hq | hq
        · exact Or.inl (h.trans hq)
        · exact Or.inr (h.trans hq)
      exact eq_of_flagPoint_mem d hp hpg
    · rcases hc with ⟨hpc, hqc⟩ | ⟨hpc, hqc⟩
      · have hp' : p = fstPoint d c ∨ p = sndPoint d c := Or.inl hpc
        have hq' : q = fstPoint d c ∨ q = sndPoint d c := Or.inr hqc
        exact (eq_of_flagPoint_mem d hp hp').trans (eq_of_flagPoint_mem d hq' hq)
      · have hp' : p = fstPoint d c ∨ p = sndPoint d c := Or.inr hpc
        have hq' : q = fstPoint d c ∨ q = sndPoint d c := Or.inl hqc
        exact (eq_of_flagPoint_mem d hp hp').trans (eq_of_flagPoint_mem d hq' hq)
  · intro h
    subst h
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl (hp.trans hq.symm)
    · exact Or.inr ⟨f, Or.inl ⟨hp, hq⟩⟩
    · exact Or.inr ⟨f, Or.inr ⟨hp, hq⟩⟩
    · exact Or.inl (hp.trans hq.symm)

/-- **The generated relation is the equivalence closure of the generating relation.**  The
equivalence relation `gluedRel` generated by the flag pairs is exactly `Relation.EqvGen` of the
generating relation `flagRel`: two points of the disjoint union are glued together precisely when
the generating relation relates them, or when they are equal. -/
theorem gluedRel_iff_eqvGen (d : NodalCurve ι Flag X) (x y : ComponentUnion X) :
    gluedRel d x y ↔ Relation.EqvGen (flagRel d) x y := by
  constructor
  · intro h
    rcases h with h | h
    · subst h
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h
  · intro h
    induction h with
    | rel a b hr => exact flagRel_le_gluedRel d hr
    | refl => exact Or.inl rfl
    | symm a b _ ih => exact gluedRel_symm d ih
    | trans a b c _ _ ih₁ ih₂ => exact gluedRel_trans d ih₁ ih₂

/-- The disjoint union of finitely many compact spaces is compact. -/
instance instCompactSpaceComponentUnion [∀ i, TopologicalSpace (X i)] [Finite ι]
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

/-- A point of the disjoint union is a flag point when it occurs in a flag pair. -/
theorem mem_flagPointSet (d : NodalCurve ι Flag X) (x : ComponentUnion X) :
    x ∈ flagPointSet d ↔ ∃ f : Flag, x = fstPoint d f ∨ x = sndPoint d f := by
  simp [flagPointSet]

/-- The flag points of `d` form a finite set. -/
theorem flagPointSet_finite [Finite Flag] : (flagPointSet d).Finite := by
  have hsub : flagPointSet d ⊆ flagPoint d '' (Set.univ : Set (Flag × Bool)) := by
    intro x hx
    obtain ⟨f, hx⟩ := (mem_flagPointSet d x).mp hx
    rcases hx with hx | hx
    · exact ⟨(f, false), Set.mem_univ _, by simp [flagPoint, hx]⟩
    · exact ⟨(f, true), Set.mem_univ _, by simp [flagPoint, hx]⟩
  exact (Set.finite_univ.image (flagPoint d)).subset hsub

/-- The product of the flag points of `d` with itself is a finite set. -/
theorem flagPointSet_prod_finite [Finite Flag] :
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
      change (fstPoint d f, fstPoint d g) = z
      exact Prod.ext hx.symm hy.symm
    · refine ⟨((f, false), (g, true)), Set.mem_univ _, ?_⟩
      change (fstPoint d f, sndPoint d g) = z
      exact Prod.ext hx.symm hy.symm
    · refine ⟨((f, true), (g, false)), Set.mem_univ _, ?_⟩
      change (sndPoint d f, fstPoint d g) = z
      exact Prod.ext hx.symm hy.symm
    · refine ⟨((f, true), (g, true)), Set.mem_univ _, ?_⟩
      change (sndPoint d f, sndPoint d g) = z
      exact Prod.ext hx.symm hy.symm
  exact (Set.finite_univ.image _).subset hsub

/-- **The generated relation is closed.**  The equivalence relation generated by the flag pairs is a
closed subset of the product of the disjoint union of the normalization components with itself.
Indeed, away from the finitely many flag points the relation is the diagonal, and on the flag
points it is a finite set. -/
theorem gluedRel_isClosed (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] :
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
        · have hz' : gluedRel d z.1 z.2 := hz
          rcases hz' with h | ⟨f, hf⟩
          · exact absurd h hxy
          · rcases hf with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact (mem_flagPointSet d z.1).mpr ⟨f, Or.inl h1⟩
            · exact (mem_flagPointSet d z.1).mpr ⟨f, Or.inr h1⟩
        · have hz' : gluedRel d z.1 z.2 := hz
          rcases hz' with h | ⟨f, hf⟩
          · exact absurd h hxy
          · rcases hf with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact (mem_flagPointSet d z.2).mpr ⟨f, Or.inr h2⟩
            · exact (mem_flagPointSet d z.2).mpr ⟨f, Or.inl h2⟩
    · intro hz
      rcases hz with h | h
      · exact h.1
      · exact Or.inl h
  rw [hsplit]
  have hR1 : (R ∩ (flagPointSet d ×ˢ flagPointSet d)).Finite :=
    (flagPointSet_prod_finite d).subset fun _ hz => hz.2
  exact hR1.isClosed.union isClosed_diagonal

/-- The glued relation, as an equivalence relation. -/
theorem gluedRel_equivalence (d : NodalCurve ι Flag X) : Equivalence (gluedRel d) where
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

/-- **The glued space is compact.**  The quotient of a compact space is compact, so the glued curve
is compact as soon as the finitely many normalization components are compact. -/
theorem isCompact_gluedCurve (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [Finite ι] [∀ i, CompactSpace (X i)] : IsCompact (Set.univ : Set (gluedCurve d)) :=
  isCompact_univ

/-- The generated relation relates two points of the disjoint union only when they are equal or
when both of them are flag points. -/
theorem gluedRel_flagPoints (d : NodalCurve ι Flag X) {a b : ComponentUnion X}
    (h : gluedRel d a b) : a = b ∨ (a ∈ flagPointSet d ∧ b ∈ flagPointSet d) := by
  rcases h with h | ⟨f, hf⟩
  · exact Or.inl h
  · rcases hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, Or.inl ha⟩,
        (mem_flagPointSet d b).mpr ⟨f, Or.inr hb⟩⟩
    · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, Or.inr ha⟩,
        (mem_flagPointSet d b).mpr ⟨f, Or.inl hb⟩⟩

/-- **The node set.**  The image of the flag points in the glued curve: the singular locus of the
nodal curve. -/
def nodeSet (d : NodalCurve ι Flag X) : Set (gluedCurve d) :=
  Quotient.mk (gluedRelSetoid d) '' flagPointSet d

/-- The node set is the image of the flag pairs: a point of the glued curve is a node exactly when
it is the image of one of the two points of a flag pair. -/
theorem mem_nodeSet (d : NodalCurve ι Flag X) {q : gluedCurve d} :
    q ∈ nodeSet d ↔ ∃ f : Flag,
      q = Quotient.mk (gluedRelSetoid d) (fstPoint d f) ∨
        q = Quotient.mk (gluedRelSetoid d) (sndPoint d f) := by
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
  Quotient.mk (gluedRelSetoid d) (fstPoint d f)

/-- **The fibres of the flag-pair map.**  Two flag pairs determine the same node of the glued
curve exactly when they are the same flag pair, so every fibre of `nodeOfFlag` is a singleton. -/
theorem nodeOfFlag_eq_iff (d : NodalCurve ι Flag X) (f g : Flag) :
    nodeOfFlag d f = nodeOfFlag d g ↔ f = g := by
  constructor
  · intro h
    have h' : gluedRel d (fstPoint d f) (fstPoint d g) :=
      (Quotient.eq (r := gluedRelSetoid d)).mp h
    rcases h' with h' | ⟨c, hc⟩
    · exact fstPoint_injective d f g h'
    · rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 (fstPoint_ne_sndPoint d g c)
      · exact absurd h1 (fstPoint_ne_sndPoint d f c)
  · intro h
    subst h
    rfl

/-- **The flag-pair map to the node set is injective.**  Distinct flag pairs give distinct nodes,
because the flag points are pairwise distinct. -/
theorem nodeOfFlag_injective (d : NodalCurve ι Flag X) : Function.Injective (nodeOfFlag d) := by
  intro f g h
  exact (nodeOfFlag_eq_iff d f g).mp h

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
      (gluedRel_of_flagPoints d (f := f) (g := f) (Or.inl rfl) (Or.inr rfl)).mpr rfl
    rcases hxf with hxf | hxf
    · change Quotient.mk (gluedRelSetoid d) (fstPoint d f) = q
      rw [← hxf]
      exact hqx
    · change Quotient.mk (gluedRelSetoid d) (fstPoint d f) = q
      rw [← ((Quotient.eq (r := gluedRelSetoid d)).mpr (gluedRel_symm d hglue))]
      rw [← hxf]
      exact hqx
  · intro hq
    obtain ⟨f, _, hqf⟩ := hq
    rw [nodeSet]
    exact (Set.mem_image _ _ _).mpr
      ⟨fstPoint d f, (mem_flagPointSet d _).mpr ⟨f, Or.inl rfl⟩, hqf⟩

/-- **Every node of the glued curve is the node of a flag pair.**  Together with the injectivity of
`nodeOfFlag` and the description of the node set as the image of the flag pairs, this says that
the nodes of the glued curve are in bijection with the flag pairs, which are the edges of the
dual graph of the nodal curve. -/
theorem exists_flag_of_mem_nodeSet (d : NodalCurve ι Flag X) {q : gluedCurve d}
    (hq : q ∈ nodeSet d) : ∃ f : Flag, nodeOfFlag d f = q := by
  have hq' : q ∈ nodeOfFlag d '' (Set.univ : Set Flag) :=
    (nodeSet_eq_image_nodeOfFlag d) ▸ hq
  obtain ⟨f, _, hqf⟩ := (Set.mem_image _ _ _).mp hq'
  exact ⟨f, hqf⟩

/-- The node of a flag pair is a node of the glued curve. -/
theorem mem_nodeSet_of_nodeOfFlag (d : NodalCurve ι Flag X) (f : Flag) :
    nodeOfFlag d f ∈ nodeSet d := by
  rw [nodeSet_eq_image_nodeOfFlag]
  exact (Set.mem_image _ _ _).mpr ⟨f, Set.mem_univ _, rfl⟩

/-- The node set of the glued curve is finite: it is the image of the finite set of flag points. -/
theorem nodeSet_finite [Finite Flag] : (nodeSet d).Finite :=
  (flagPointSet_finite d).image _

/-- **The preimage of the node set.**  The quotient map sends a point of the disjoint union to a
node exactly when that point is a flag point: the preimage of the node set is the flag point set.
-/
theorem preimage_nodeSet (d : NodalCurve ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' nodeSet d = flagPointSet d := by
  ext x
  constructor
  · intro hx
    have hx' : Quotient.mk (gluedRelSetoid d) x ∈ nodeSet d := hx
    rw [nodeSet] at hx'
    obtain ⟨y, hyF, hqy⟩ :=
      (Set.mem_image (Quotient.mk (gluedRelSetoid d)) (flagPointSet d) _).mp hx'
    have hrel : gluedRel d y x := (Quotient.eq (r := gluedRelSetoid d)).mp hqy
    rcases gluedRel_flagPoints d hrel with heq | ⟨_, hxF⟩
    · exact heq ▸ hyF
    · exact hxF
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The node set is closed.**  The node set of the glued curve is a closed subset of it, so the
smooth locus, its complement, is open. -/
theorem isClosed_nodeSet (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] : IsClosed (nodeSet d) := by
  refine ⟨?_⟩
  have hiff : IsOpen ((nodeSet d)ᶜ)
      ↔ IsOpen ((Quotient.mk (gluedRelSetoid d)) ⁻¹' ((nodeSet d)ᶜ)) := by
    rw [isOpen_coinduced]
    rfl
  rw [hiff]
  rw [Set.preimage_compl, preimage_nodeSet]
  exact (flagPointSet_finite d).isClosed.isOpen_compl

/-- **The smooth locus.**  The complement of the node set in the glued curve: the points at which
the nodal curve is smooth. -/
def smoothLocus (d : NodalCurve ι Flag X) : Set (gluedCurve d) := (nodeSet d)ᶜ

/-- The smooth locus is open, being the complement of the closed node set. -/
theorem isOpen_smoothLocus (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] : IsOpen (smoothLocus d) :=
  (isClosed_nodeSet d).isOpen_compl

/-- **The preimage of the smooth locus.**  The quotient map sends a point of the disjoint union to
a smooth point exactly when that point is not a flag point: the preimage of the smooth locus is
the disjoint union of the normalization components minus the flag points. -/
theorem preimage_smoothLocus (d : NodalCurve ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' smoothLocus d = (flagPointSet d)ᶜ := by
  rw [smoothLocus, Set.preimage_compl, preimage_nodeSet]

/-- A point of the disjoint union that is not a flag point is not mapped to a node. -/
theorem not_mem_nodeSet_of_not_mem_flagPointSet {x : ComponentUnion X}
    (hx : x ∉ flagPointSet d) : Quotient.mk (gluedRelSetoid d) x ∉ nodeSet d := by
  intro hx'
  have hx'' : x ∈ (Quotient.mk (gluedRelSetoid d)) ⁻¹' nodeSet d := hx'
  rw [preimage_nodeSet] at hx''
  exact hx hx''

/-- The quotient map is injective away from the flag points. -/
theorem gluedCurveQuotientMap_injective_of_not_flagPoint {x y : ComponentUnion X}
    (hx : x ∉ flagPointSet d)
    (h : Quotient.mk (gluedRelSetoid d) x = Quotient.mk (gluedRelSetoid d) y) :
    x = y := by
  have hrel : gluedRel d x y := (Quotient.eq (r := gluedRelSetoid d)).mp h
  rcases gluedRel_flagPoints d hrel with heq | ⟨hxF, _⟩
  · exact heq
  · exact absurd hxF hx

/-- The quotient map, restricted to the smooth locus of the glued curve, i.e. to the preimage of
the smooth locus under the quotient map: by `preimage_smoothLocus`, the points of the disjoint
union of the normalization components that are not flag points. -/
def gluedCurveQuotientMapOnSmooth (d : NodalCurve ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' smoothLocus d → smoothLocus d :=
  (smoothLocus d).restrictPreimage (Quotient.mk (gluedRelSetoid d))

/-- **The quotient map is a homeomorphism of the smooth loci.**  The disjoint union of the
normalization components minus the flag points is homeomorphic to the smooth locus of the glued
curve, the complement of the node set; the homeomorphism is the restriction of the quotient map.
It is a quotient map, being the restriction of the quotient map to the preimage of the open smooth
locus, and it is injective away from the flag points
(`gluedCurveQuotientMap_injective_of_not_flagPoint`), so it is a homeomorphism. -/
theorem gluedCurveQuotientMapOnSmooth_isHomeomorph (d : NodalCurve ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [Finite Flag] :
    IsHomeomorph (gluedCurveQuotientMapOnSmooth d) := by
  refine isHomeomorph_iff_isQuotientMap_injective.2 ⟨?_, ?_⟩
  · exact Topology.IsQuotientMap.restrictPreimage_isOpen
      (isQuotientMap_quotient_mk' (s := gluedRelSetoid d)) (isOpen_smoothLocus d)
  · intro x y hxy
    have hxy' : Quotient.mk (gluedRelSetoid d) x.1 = Quotient.mk (gluedRelSetoid d) y.1 :=
      congrArg Subtype.val hxy
    have hxnotF : x.1 ∉ flagPointSet d := by
      have hxmem : x.1 ∈ (Quotient.mk (gluedRelSetoid d)) ⁻¹' smoothLocus d := x.2
      have hxmem' : x.1 ∈ (flagPointSet d)ᶜ := by
        rw [← preimage_smoothLocus d]
        exact hxmem
      exact hxmem'
    exact Subtype.ext (gluedCurveQuotientMap_injective_of_not_flagPoint d hxnotF hxy')

end TauCeti.ComplexCurveModuli
