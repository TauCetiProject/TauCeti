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
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Topology.Constructions.FiniteGluing

/-!
# The gluing quotient of a nodal curve at its flag pairs

A nodal curve is obtained by gluing smooth curves at pairs of points.  The gluing data is
recorded by *flag pairs*: a flag pair names two normalization components together with the point
of each of them that is identified.  This file builds the underlying topological space of such a
curve, the *gluing quotient*, and records its basic properties.

The model is the following.

* `NodalCurve` is the gluing data: an arbitrary family of normalization components `X i`
  (indexed by the type `ι`) together with an arbitrary family of flag pairs `f : Flag`.  A flag
  pair names the two components `fst f`, `snd f` and the points `fstPt f`, `sndPt f` of them that
  are identified.  The data carry one hypothesis: the flag points are pairwise distinct
  (`injective_flagPoints'`).  The two points of one flag pair are different, and no point of the
  disjoint union occurs in two different flag pairs.  This is what makes the data the data of a
  *nodal* curve and not of an arbitrary gluing of curves along points.  Finiteness of the flag
  pairs is not assumed by the data: it is assumed, as `[Finite Flag]`, by the theorems that need
  it, namely the finiteness of the node set, the closedness of the generated relation, the
  Hausdorffness of the glued space and the homeomorphism of the smooth loci.  The number of
  components is not assumed to be finite either; it is assumed, as `[Finite ι]`, by the
  compactness of the glued space.
* `Σ i, X i` is the disjoint union of the normalization components, with the coproduct topology.
  It is Hausdorff as soon as the components are (Mathlib's `Sigma.t2Space`).
* `flagRel` is the generating relation: the two points of one flag pair are related.
* A flag point belongs to a unique flag pair (`eq_of_flagPoint_mem`): two flag pairs never share
  a point of the disjoint union.  Consequently a chain of flag pairs has at most one step
  (`flagRel_chain`).
* `gluedRel` is the equivalence relation *generated* by the flag pairs: it is "the two points are
  equal, or they are the two points of one flag pair", which is `x = y ∨ flagRel d x y`.  It is
  symmetric and transitive (`gluedRel_symm`, `gluedRel_trans`), hence an equivalence relation
  (`gluedRel_equivalence`), and it relates two points only when they are equal or when both of
  them are flag points (`eq_or_mem_flagPointSet_of_gluedRel`).  It is also exactly the equivalence
  closure `Relation.EqvGen` of the generating relation (`gluedRel_iff_eqvGen`).
* `GluedCurve` is the quotient of the disjoint union by that relation: the underlying space of
  the nodal curve.  It is the `Quotient` of the disjoint union by the setoid `gluedRelSetoid`,
  with the quotient topology: a subset of the glued curve is open exactly when its inverse image
  under the quotient map `Quotient.mk (gluedRelSetoid d)` is open in the disjoint union.  The
  quotient map is continuous (`continuous_quotient_mk'`) and identifies two points exactly when
  the generated relation relates them (`mk_eq_mk_iff`).
* `nodeSet` is the image of the flag points in the glued curve.  It is the image of the flag
  pairs (`nodeSet_eq_range_nodeOfFlag`), it is finite (`nodeSet_finite`) and it is closed
  (`isClosed_nodeSet`).  The map `nodeOfFlag` sends a flag pair to its node; two flag pairs have
  the same node exactly when they are the same flag pair (`nodeOfFlag_inj`), so `nodeOfFlag` is
  injective (`nodeOfFlag_injective`).
* `smoothLocus` is the complement of the node set in the glued curve.  It is open
  (`isOpen_smoothLocus`), and it is the image of the components minus their flag points under the
  quotient map (`image_quotient_mk_compl`).  The quotient map restricts to a homeomorphism from
  the disjoint union of the normalization components minus their flag points onto the smooth
  locus (`isHomeomorph_gluedCurveQuotientMapOnSmooth`): the restriction is an open embedding
  (`isOpenEmbedding_gluedCurveQuotientMapOnSmooth`) and is injective away from the flag points
  (`eq_of_quotient_mk_eq_of_notMem_flagPointSet`).

The node set and the smooth locus are *intended* to be the singular locus and the smooth locus of
the nodal curve.  This file only builds the underlying topological space, so the two names are
names: nothing here is a statement about singularities or about smoothness.

**Scope.**  What is proved is:

* the glued space is built: it is the quotient of the disjoint union of the normalization
  components by the generated relation, endowed with the quotient topology; the quotient map is
  continuous;
* the generated relation is closed (`isClosed_gluedRel`);
* the glued space is Hausdorff (`t2Space_GluedCurve`), and it is compact when the normalization
  components are (`compactSpace_GluedCurve`);
* the node set, the image of the flag pairs, is closed, and the quotient map identifies the
  disjoint union minus the flag points homeomorphically with the complement of the node set;
* the nodes of the glued curve are in bijection with the flag pairs: `nodeOfFlag` is injective
  (`nodeOfFlag_injective`) and its image is the node set (`nodeSet_eq_range_nodeOfFlag`), so every
  node is the node of a flag pair.

What is **not** proved here:

* the **biholomorphic** refinement of the smooth-locus statement: the glued space carries no
  complex structure on its smooth locus, so there is nothing for a biholomorphism to be a
  morphism between.
* the **dual graph** of the nodal curve: the flag pairs are the edges of the dual graph of a
  nodal curve, and the nodes of the glued curve are in bijection with the flag pairs, but the
  graph itself, with its vertices and its incidence relations, is not built in this file.

## References

* Enrico Arbarello, Maurizio Cornalba, Phillip A. Griffiths, *Geometry of Algebraic Curves,
  Volume II* (Grundlehren der mathematischen Wissenschaften 331, Springer, 2007), Chapter X,
  "Nodal curves", for a nodal curve as obtained by gluing the normalization components at pairs of
  points, and for its dual graph.
* Qing Liu, *Algebraic Geometry and Arithmetic Curves* (Oxford Graduate Texts in Mathematics 6,
  2002), §4.1, in particular §4.1.2 on the normalization, for the normalization of a curve and
  the finite map it induces to the curve.
* `TauCeti/Topology/Constructions/FiniteGluing.lean`, the topological carrier of a nodal curve:
  the quotient of the normalization by the relation identifying each node flag with its partner.
  The closedness, the Hausdorffness and the open embedding of the quotient map used above are
  taken from that file.
* `TauCeti/AlgebraicGeometry/Curves/DualGraph/Basic.lean`, the dual graph of a nodal curve.
-/

public noncomputable section

open Set Topology

namespace TauCeti

namespace NodalGluing

variable {ι : Type*} {Flag : Type*} {X : ι → Type*}

/-- The disjoint union of the normalization components of a nodal curve. -/
abbrev ComponentUnion {ι : Type*} (X : ι → Type*) := Sigma X

/-- The point of the disjoint union selected by a flag pair and a boolean: `false` selects the
first point of the flag pair, `true` the second.  This is the function whose injectivity is the
hypothesis on the gluing data. -/
def flagPointOf {ι Flag : Type*} {X : ι → Type*} (fst snd : Flag → ι)
    (fstPt : ∀ f : Flag, X (fst f)) (sndPt : ∀ f : Flag, X (snd f))
    (p : Flag × Bool) : ComponentUnion X :=
  if p.2 then ⟨snd p.1, sndPt p.1⟩ else ⟨fst p.1, fstPt p.1⟩

/-- The gluing data of a nodal curve: the flag pairs at which the normalization components are
glued.  A flag pair `f` names the two components `fst f` and `snd f` together with the points
`fstPt f` and `sndPt f` of those components that are identified.

The field `injective_flagPoints'` says that the flag points are pairwise distinct: the two points
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
  injective_flagPoints' : Function.Injective (flagPointOf fst snd fstPt sndPt)

variable (d : NodalCurve ι Flag X)

/-- The first point of a flag pair, as a point of the disjoint union of the components. -/
def fstPoint (d : NodalCurve ι Flag X) (f : Flag) : ComponentUnion X := ⟨d.fst f, d.fstPt f⟩

/-- The second point of a flag pair, as a point of the disjoint union of the components. -/
def sndPoint (d : NodalCurve ι Flag X) (f : Flag) : ComponentUnion X := ⟨d.snd f, d.sndPt f⟩

/-- The two points of a flag pair, selected by a boolean: `false` selects the first point of the
flag pair, `true` the second. -/
def flagPoint (d : NodalCurve ι Flag X) (p : Flag × Bool) : ComponentUnion X :=
  flagPointOf d.fst d.snd d.fstPt d.sndPt p

/-- **The flag points are pairwise distinct.**  The points of the disjoint union that are glued --
the flag points -- are pairwise distinct: the two points of one flag pair are different, and no
point occurs in two different flag pairs. -/
theorem flagPoint_injective (d : NodalCurve ι Flag X) : Function.Injective (flagPoint d) :=
  d.injective_flagPoints'

/-- The first point of a flag pair is the flag point selected by `false`. -/
@[simp] theorem flagPoint_false (d : NodalCurve ι Flag X) (f : Flag) :
    flagPoint d (f, false) = fstPoint d f := by
  simp [flagPoint, flagPointOf, fstPoint]

/-- The second point of a flag pair is the flag point selected by `true`. -/
@[simp] theorem flagPoint_true (d : NodalCurve ι Flag X) (f : Flag) :
    flagPoint d (f, true) = sndPoint d f := by
  simp [flagPoint, flagPointOf, sndPoint]

/-- Two flag pairs with the same first point are the same flag pair. -/
theorem fstPoint_injective (d : NodalCurve ι Flag X) : Function.Injective (fstPoint d) := by
  intro f g h
  have h' : flagPoint d (f, false) = flagPoint d (g, false) := by simpa using h
  exact (Prod.ext_iff.mp (flagPoint_injective d h')).1

/-- Two flag pairs with the same second point are the same flag pair. -/
theorem sndPoint_injective (d : NodalCurve ι Flag X) : Function.Injective (sndPoint d) := by
  intro f g h
  have h' : flagPoint d (f, true) = flagPoint d (g, true) := by simpa using h
  exact (Prod.ext_iff.mp (flagPoint_injective d h')).1

/-- The first point of a flag pair is never the second point of a flag pair: a flag pair never
pairs a point with itself. -/
theorem fstPoint_ne_sndPoint (d : NodalCurve ι Flag X) (f g : Flag) :
    fstPoint d f ≠ sndPoint d g := by
  intro h
  have h' : flagPoint d (f, false) = flagPoint d (g, true) := by simpa using h
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
  · exact fstPoint_injective d (hp.symm.trans hq)
  · exact absurd (hp.symm.trans hq) (fstPoint_ne_sndPoint d f g)
  · exact absurd (hp.symm.trans hq) (sndPoint_ne_fstPoint d f g)
  · exact sndPoint_injective d (hp.symm.trans hq)

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
glued together exactly when they are equal, or when they are the two points of one flag pair;
this is `x = y ∨ flagRel d x y`.  Because the flag points are pairwise distinct, no chain of flag
pairs has more than one step, so this is exactly the relation generated by the flag pairs. -/
def gluedRel (d : NodalCurve ι Flag X) (x y : ComponentUnion X) : Prop :=
  x = y ∨ flagRel d x y

/-- The glued relation is symmetric. -/
theorem gluedRel_symm (d : NodalCurve ι Flag X) {x y : ComponentUnion X} (h : gluedRel d x y) :
    gluedRel d y x :=
  h.imp Eq.symm (flagRel_symm d)

/-- The glued relation is transitive. -/
theorem gluedRel_trans (d : NodalCurve ι Flag X) {x y z : ComponentUnion X}
    (h₁ : gluedRel d x y) (h₂ : gluedRel d y z) : gluedRel d x z := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inr (h₁.symm ▸ h₂)
  · exact Or.inr (h₂ ▸ h₁)
  · exact Or.inl (flagRel_chain d h₁ h₂)

/-- The generating relation is contained in the glued relation. -/
theorem flagRel_le_gluedRel (d : NodalCurve ι Flag X) : flagRel d ≤ gluedRel d :=
  fun _ _ h => Or.inr h

/-- **The relation between two flag points.**  Two flag points of the disjoint union are related
by `gluedRel` exactly when they belong to the same flag pair. -/
theorem gluedRel_iff_of_flagPoints (d : NodalCurve ι Flag X) {f g : Flag}
    {p q : ComponentUnion X}
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

/-- The glued relation, as an equivalence relation. -/
theorem gluedRel_equivalence (d : NodalCurve ι Flag X) : Equivalence (gluedRel d) where
  refl := fun _ => Or.inl rfl
  symm := fun h => gluedRel_symm d h
  trans := fun h₁ h₂ => gluedRel_trans d h₁ h₂

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
    -- The equivalence closure of a relation contained in an equivalence relation stays inside it.
    exact (gluedRel_equivalence d).eqvGen_iff.mp
      (Relation.EqvGen.mono (flagRel_le_gluedRel d) x y h)

/-- The points of the disjoint union that occur in a flag pair: the range of the flag points. -/
def flagPointSet (d : NodalCurve ι Flag X) : Set (ComponentUnion X) :=
  Set.range (flagPoint d)

/-- A point of the disjoint union is a flag point when it occurs in a flag pair. -/
@[simp] theorem mem_flagPointSet (d : NodalCurve ι Flag X) (x : ComponentUnion X) :
    x ∈ flagPointSet d ↔ ∃ f : Flag, x = fstPoint d f ∨ x = sndPoint d f := by
  rw [flagPointSet, Set.mem_range]
  constructor
  · rintro ⟨⟨f, b⟩, hx⟩
    cases b with
    | false =>
      refine ⟨f, Or.inl ?_⟩
      simpa using hx.symm
    | true =>
      refine ⟨f, Or.inr ?_⟩
      simpa using hx.symm
  · rintro ⟨f, hx | hx⟩
    · exact ⟨(f, false), (flagPoint_false d f).symm.trans hx.symm⟩
    · exact ⟨(f, true), (flagPoint_true d f).symm.trans hx.symm⟩

/-- The flag points of `d` form a finite set. -/
theorem flagPointSet_finite [Finite Flag] : (flagPointSet d).Finite :=
  Set.finite_range (flagPoint d)

/-- The generated relation relates two points of the disjoint union only when they are equal or
when both of them are flag points. -/
theorem eq_or_mem_flagPointSet_of_gluedRel (d : NodalCurve ι Flag X) {a b : ComponentUnion X}
    (h : gluedRel d a b) : a = b ∨ (a ∈ flagPointSet d ∧ b ∈ flagPointSet d) := by
  rcases h with h | ⟨f, hf⟩
  · exact Or.inl h
  · rcases hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, Or.inl ha⟩,
        (mem_flagPointSet d b).mpr ⟨f, Or.inr hb⟩⟩
    · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, Or.inr ha⟩,
        (mem_flagPointSet d b).mpr ⟨f, Or.inl hb⟩⟩

/-- The generated relation as a setoid: the equivalence relation on the disjoint union of the
normalization components that glues the points of the flag pairs together. -/
def gluedRelSetoid (d : NodalCurve ι Flag X) : Setoid (ComponentUnion X) :=
  Setoid.mk (gluedRel d) (gluedRel_equivalence d)

/-- The relation of the setoid is the generated relation. -/
@[simp] theorem gluedRelSetoid_r (d : NodalCurve ι Flag X) (x y : ComponentUnion X) :
    gluedRelSetoid d x y ↔ gluedRel d x y :=
  Iff.rfl

/-- **The glued space.**  The quotient of the disjoint union of the normalization components by the
generated relation: the underlying topological space of the nodal curve.  The topology is the
quotient topology, i.e. the finest topology making the quotient map continuous. -/
abbrev GluedCurve (d : NodalCurve ι Flag X) :=
  Quotient (gluedRelSetoid d)

/-- The quotient map identifies two points of the disjoint union exactly when the generated
relation relates them. -/
@[simp] theorem mk_eq_mk_iff (d : NodalCurve ι Flag X) (x y : ComponentUnion X) :
    Quotient.mk (gluedRelSetoid d) x = Quotient.mk (gluedRelSetoid d) y ↔ gluedRel d x y :=
  (Quotient.eq).trans (gluedRelSetoid_r d x y)

/-- **The node set.**  The image of the flag points in the glued curve.  It is intended to be the
singular locus of the nodal curve, but this file only builds the underlying topological space. -/
def nodeSet (d : NodalCurve ι Flag X) : Set (GluedCurve d) :=
  Quotient.mk (gluedRelSetoid d) '' flagPointSet d

/-- The node point of a flag pair: the image of its first point in the glued curve. -/
abbrev nodeOfFlag (d : NodalCurve ι Flag X) (f : Flag) : GluedCurve d :=
  Quotient.mk (gluedRelSetoid d) (fstPoint d f)

/-- The first point of a flag pair is sent to its node. -/
@[simp] theorem mk_fstPoint (d : NodalCurve ι Flag X) (f : Flag) :
    Quotient.mk (gluedRelSetoid d) (fstPoint d f) = nodeOfFlag d f :=
  rfl

/-- The second point of a flag pair is sent to the same node as the first one. -/
@[simp] theorem mk_sndPoint (d : NodalCurve ι Flag X) (f : Flag) :
    Quotient.mk (gluedRelSetoid d) (sndPoint d f) = nodeOfFlag d f := by
  rw [← mk_fstPoint]
  refine Quotient.sound ?_
  exact (gluedRel_iff_of_flagPoints d (f := f) (g := f) (Or.inr rfl) (Or.inl rfl)).mpr rfl

/-- **The fibres of the flag-pair map.**  The first points of two flag pairs are glued exactly
when the two flag pairs are equal, so every fibre of `nodeOfFlag` is a singleton.  The statement is
in simp-normal form: the quotient map identifies two flag points exactly when the generated
relation relates them (`mk_eq_mk_iff`). -/
@[simp] theorem nodeOfFlag_inj (d : NodalCurve ι Flag X) (f g : Flag) :
    gluedRel d (fstPoint d f) (fstPoint d g) ↔ f = g := by
  constructor
  · intro h
    rcases h with h' | ⟨c, hc⟩
    · exact fstPoint_injective d h'
    · rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 (fstPoint_ne_sndPoint d g c)
      · exact absurd h1 (fstPoint_ne_sndPoint d f c)
  · intro h
    subst h
    exact Or.inl rfl

/-- **The flag-pair map to the node set is injective.**  Distinct flag pairs give distinct nodes,
because the flag points are pairwise distinct. -/
theorem nodeOfFlag_injective (d : NodalCurve ι Flag X) : Function.Injective (nodeOfFlag d) :=
  fun f g h =>
    (nodeOfFlag_inj d f g).mp ((mk_eq_mk_iff d (fstPoint d f) (fstPoint d g)).mp h)

/-- **The node set is the image of the flag pairs.**  The node set of the glued curve is the image
of the flag pairs under the quotient map. -/
theorem nodeSet_eq_range_nodeOfFlag (d : NodalCurve ι Flag X) :
    nodeSet d = Set.range (nodeOfFlag d) := by
  ext q
  constructor
  · intro hq
    -- A flag point is the first or the second point of a flag pair, and the two points of a flag
    -- pair have the same node.
    rw [nodeSet] at hq
    obtain ⟨x, hx, hqx⟩ := (Set.mem_image _ _ _).mp hq
    obtain ⟨f, hxf | hxf⟩ := (mem_flagPointSet d x).mp hx
    · refine ⟨f, ?_⟩
      rw [← mk_fstPoint, ← hxf]
      exact hqx
    · refine ⟨f, ?_⟩
      rw [← mk_sndPoint, ← hxf]
      exact hqx
  · intro hq
    obtain ⟨f, hqf⟩ := hq
    refine (Set.mem_image _ _ _).mpr ⟨fstPoint d f, ?_, ?_⟩
    · exact (mem_flagPointSet d _).mpr ⟨f, Or.inl rfl⟩
    · rw [mk_fstPoint]
      exact hqf

/-- The node set of the glued curve is finite: it is the image of the finite set of flag points. -/
theorem nodeSet_finite [Finite Flag] : (nodeSet d).Finite :=
  (flagPointSet_finite d).image _

/-- **The preimage of the node set.**  The quotient map sends a point of the disjoint union to a
node exactly when that point is a flag point: the preimage of the node set is the flag point set.
-/
@[simp] theorem preimage_nodeSet (d : NodalCurve ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' nodeSet d = flagPointSet d := by
  ext x
  constructor
  · intro hx
    rw [nodeSet] at hx
    obtain ⟨y, hyF, hqy⟩ :=
      (Set.mem_image (Quotient.mk (gluedRelSetoid d)) (flagPointSet d) _).mp hx
    have hrel : gluedRel d y x := (mk_eq_mk_iff d y x).mp hqy
    rcases eq_or_mem_flagPointSet_of_gluedRel d hrel with heq | ⟨_, hxF⟩
    · exact heq ▸ hyF
    · exact hxF
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The node set is closed.**  The node set of the glued curve is a closed subset of it, so the
smooth locus, its complement, is open. -/
theorem isClosed_nodeSet (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] : IsClosed (nodeSet d) := by
  rw [← (isQuotientMap_quotient_mk' (s := gluedRelSetoid d)).isClosed_preimage]
  change IsClosed ((Quotient.mk (gluedRelSetoid d)) ⁻¹' nodeSet d)
  rw [preimage_nodeSet]
  exact (flagPointSet_finite d).isClosed

/-- **The smooth locus.**  The complement of the node set in the glued curve.  It is intended to be
the locus of the nodal curve where it is smooth, but this file only builds the underlying
topological space. -/
def smoothLocus (d : NodalCurve ι Flag X) : Set (GluedCurve d) := (nodeSet d)ᶜ

/-- The smooth locus is open, being the complement of the closed node set. -/
theorem isOpen_smoothLocus (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] : IsOpen (smoothLocus d) :=
  (isClosed_nodeSet d).isOpen_compl

/-- **The preimage of the smooth locus.**  The quotient map sends a point of the disjoint union to
a smooth point exactly when that point is not a flag point: the preimage of the smooth locus is
the disjoint union of the normalization components minus the flag points. -/
@[simp] theorem preimage_smoothLocus (d : NodalCurve ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' smoothLocus d = (flagPointSet d)ᶜ := by
  rw [smoothLocus, Set.preimage_compl, preimage_nodeSet]

/-- **The generated relation identifies only flag points.**  Two distinct points of the disjoint
union are related by the generated relation only when both of them are flag points. -/
theorem gluedRelSetoid_of_ne (d : NodalCurve ι Flag X) :
    ∀ ⦃x y : ComponentUnion X⦄, gluedRelSetoid d x y → x ≠ y → x ∈ flagPointSet d := by
  intro x y h hne
  have hglued : gluedRel d x y := (gluedRelSetoid_r d x y).mp h
  rcases eq_or_mem_flagPointSet_of_gluedRel d (a := x) (b := y) hglued with heq | ⟨hx, _⟩
  · exact absurd heq hne
  · exact hx

/-- **The image of the components minus their flag points.**  The quotient map sends the disjoint
union of the normalization components minus their flag points onto the smooth locus of the glued
curve, the complement of the node set. -/
theorem image_quotient_mk_compl (d : NodalCurve ι Flag X) :
    Quotient.mk (gluedRelSetoid d) '' (flagPointSet d)ᶜ = smoothLocus d := by
  rw [Setoid.image_quotient_mk_compl (gluedRelSetoid d) (gluedRelSetoid_of_ne d), smoothLocus,
    nodeSet]

/-- **The generated relation is closed.**  The equivalence relation generated by the flag pairs is a
closed subset of the product of the disjoint union of the normalization components with itself. -/
theorem isClosed_gluedRel (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] :
    IsClosed {p : ComponentUnion X × ComponentUnion X | gluedRel d p.1 p.2} := by
  -- Away from the finitely many flag points the relation is the diagonal, and on the flag points
  -- it is a finite set: this is exactly the hypothesis of `Setoid.isClosed_setOf_rel`.
  exact Setoid.isClosed_setOf_rel (gluedRelSetoid d) (flagPointSet_finite d)
    (gluedRelSetoid_of_ne d)

/-- **The glued space is Hausdorff.**  The quotient of the disjoint union of the normalization
components by the generated relation is a Hausdorff space. -/
theorem t2Space_GluedCurve (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] : T2Space (GluedCurve d) :=
  Setoid.t2Space_quotient (gluedRelSetoid d) (flagPointSet_finite d) (gluedRelSetoid_of_ne d)

/-- **The glued space is compact.**  The quotient of the disjoint union of the normalization
components by the generated relation is a compact space when the components are. -/
theorem compactSpace_GluedCurve (d : NodalCurve ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] [Finite ι] : CompactSpace (GluedCurve d) :=
  Quotient.compactSpace

/-- **The quotient map is an open embedding away from the flag points.**  The quotient map
restricted to the disjoint union of the normalization components minus their flag points is an
open embedding. -/
theorem isOpenEmbedding_gluedCurveQuotientMapOnSmooth (d : NodalCurve ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [Finite Flag] :
    IsOpenEmbedding ((flagPointSet d)ᶜ.domRestrict (Quotient.mk (gluedRelSetoid d))) :=
  Setoid.isOpenEmbedding_domRestrict_quotient_mk (gluedRelSetoid d) (flagPointSet_finite d)
    (gluedRelSetoid_of_ne d)

/-- The quotient map is injective away from the flag points. -/
theorem eq_of_quotient_mk_eq_of_notMem_flagPointSet (d : NodalCurve ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [Finite Flag]
    {x y : ComponentUnion X} (hx : x ∉ flagPointSet d)
    (h : Quotient.mk (gluedRelSetoid d) x = Quotient.mk (gluedRelSetoid d) y) :
    x = y := by
  have hy : y ∉ flagPointSet d := by
    intro hy
    have hrel : gluedRel d x y := (mk_eq_mk_iff d x y).mp h
    rcases eq_or_mem_flagPointSet_of_gluedRel d (a := x) (b := y) hrel with heq | ⟨hxf, hyf⟩
    · exact hx (heq ▸ hy)
    · exact hx hxf
  -- The quotient map is an open embedding away from the flag points, hence injective there.
  have hemb := isOpenEmbedding_gluedCurveQuotientMapOnSmooth d
  have hxy := hemb.toIsEmbedding.injective (a₁ := ⟨x, Set.mem_compl hx⟩)
    (a₂ := ⟨y, Set.mem_compl hy⟩) (by
      rw [Set.domRestrict_eq, Function.comp_apply, Function.comp_apply]
      exact h)
  exact congrArg Subtype.val hxy

/-- The quotient map, restricted to the smooth locus of the glued curve, i.e. to the preimage of
the smooth locus under the quotient map: by `preimage_smoothLocus`, the points of the disjoint
union of the normalization components that are not flag points. -/
abbrev gluedCurveQuotientMapOnSmooth (d : NodalCurve ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' smoothLocus d → smoothLocus d :=
  (smoothLocus d).restrictPreimage (Quotient.mk (gluedRelSetoid d))

/-- **The quotient map is a homeomorphism of the smooth loci.**  The disjoint union of the
normalization components minus the flag points is homeomorphic to the smooth locus of the glued
curve, the complement of the node set; the homeomorphism is the restriction of the quotient map. -/
theorem isHomeomorph_gluedCurveQuotientMapOnSmooth (d : NodalCurve ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [Finite Flag] :
    IsHomeomorph (gluedCurveQuotientMapOnSmooth d) := by
  refine isHomeomorph_iff_isQuotientMap_injective.2 ⟨?_, ?_⟩
  · -- The restriction of the quotient map to the open smooth locus is a quotient map, and it is
    -- onto the smooth locus.
    refine ⟨(Topology.IsQuotientMap.restrictPreimage_isOpen
        (isQuotientMap_quotient_mk' (s := gluedRelSetoid d)) (isOpen_smoothLocus d)).isCoinducing,
      ?_⟩
    -- The restriction is onto the smooth locus, the image of the components minus the flag
    -- points.
    intro q
    cases q with
    | mk q hq =>
      have hq' : q ∈ Quotient.mk (gluedRelSetoid d) '' (flagPointSet d)ᶜ := by
        rw [image_quotient_mk_compl d]
        exact hq
      obtain ⟨x, hx, hqx⟩ := (Set.mem_image _ _ _).mp hq'
      have hxmem : x ∈ (Quotient.mk (gluedRelSetoid d)) ⁻¹' smoothLocus d := by
        rw [preimage_smoothLocus]
        exact hx
      refine ⟨Subtype.mk x hxmem, ?_⟩
      subst q
      rfl
  · intro x y hxy
    have hxy' : Quotient.mk (gluedRelSetoid d) x.1 = Quotient.mk (gluedRelSetoid d) y.1 :=
      congrArg Subtype.val hxy
    have hx : x.1 ∉ flagPointSet d := by simpa using x.2
    exact Subtype.ext (eq_of_quotient_mk_eq_of_notMem_flagPointSet d hx hxy')

end NodalGluing

end TauCeti
