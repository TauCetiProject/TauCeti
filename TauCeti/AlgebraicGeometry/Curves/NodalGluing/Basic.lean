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
public import TauCeti.Topology.Separation.Sigma
public import TauCeti.Topology.Constructions.FiniteGluing

/-!
# The gluing quotient of a nodal curve at its flag pairs

A nodal curve is obtained by gluing smooth curves at pairs of points.  The gluing data is
recorded by *flag pairs*: a flag pair names two normalization components together with the point
of each of them that is identified.  This file builds the underlying topological space of such a
curve, the *gluing quotient*, and records its basic properties.

The model is the following.

* `FlagPairData` is the gluing data: an arbitrary family of normalization components `X i`
  (indexed by the type `ι`) together with an arbitrary family of flag pairs `f : Flag`.  A flag
  pair names the two components `fst f`, `snd f` and the points `fstPt f`, `sndPt f` of them that
  are identified.  The data carry one hypothesis: the flag points are pairwise distinct
  (`flagPointOf_injective'`).  The two points of one flag pair are different, and no point of the
  disjoint union occurs in two different flag pairs.  This is what makes the data the data of a
  *nodal* curve and not of an arbitrary gluing of curves along points.  Finiteness of the flag
  pairs is not assumed by the data: it is assumed, as `[Finite Flag]`, by the finiteness of the
  flag points and of the node set, and -- together with the hypotheses that the components carry
  a topology and that they are T₁ -- by the closedness of the node set, the openness of the
  complement of the node set, the open embedding of the quotient map away from the flag points and
  the homeomorphism of the complement of the node set.  The closedness of the generated relation
  and the Hausdorffness of the glued space ask the components to be Hausdorff.  The number of
  components is not assumed to be finite either: the compactness of the glued space is not a
  separate declaration, it follows by instance inference from `[Finite ι]` together with
  `[∀ i, CompactSpace (X i)]`.
* `Σ i, X i` is the disjoint union of the normalization components, with the coproduct topology.
  It is Hausdorff as soon as the components are (Mathlib's `Sigma.t2Space`).
* `flagRel` is the generating relation: the two points of one flag pair are related.
* A flag point belongs to a unique flag pair (`eq_of_flagPoint_mem`): two flag pairs never share
  a point of the disjoint union.  Consequently any chain of flag pairs reduces to equality or to a
  single generating step (`eq_of_flagRel_of_flagRel`).
* `Marking d L` records marks on the curve labelled by `L`: pairwise distinct points of the
  disjoint union, none of them a flag point.
* `gluedRel` is the equivalence relation *generated* by the flag pairs: it is "the two points are
  equal, or they are the two points of one flag pair", which is `x = y ∨ flagRel d x y`.  It is
  symmetric and transitive (`gluedRel_symm`, `gluedRel_trans`), hence an equivalence relation
  (`gluedRel_equivalence`), and it relates two points only when they are equal or when both of
  them are flag points (`eq_or_mem_flagPointSet_of_gluedRel`).  It is also exactly the equivalence
  closure `Relation.EqvGen` of the generating relation (`gluedRel_iff_eqvGen`).  As a setoid it
  glues the two points of each flag pair (`gluedRelSetoid_fstPoint_sndPoint`), and glues the first
  point of a flag pair to nothing else (`eq_or_eq_of_gluedRelSetoid_fstPoint`).
* `GluedCurve` is the quotient of the disjoint union by that relation: the underlying space of
  the nodal curve.  It is the `Quotient` of the disjoint union by the setoid `gluedRelSetoid`,
  with the quotient topology: a subset of the glued curve is open exactly when its inverse image
  under the quotient map `Quotient.mk (gluedRelSetoid d)` is open in the disjoint union.  The
  quotient map is continuous (`continuous_quotient_mk'`) and identifies two points exactly when
  the generated relation relates them (Mathlib's `Quotient.eq`).  The glued curve is a quotient,
  so it has a lifting property: a map out of the disjoint union that takes the same value on the
  two points of every flag pair descends to a map out of the glued curve (`GluedCurve.lift`,
  `GluedCurve.lift_mk`, `GluedCurve.continuous_lift`).
* `nodeSet` is the image of the flag points in the glued curve.  It is the image of the flag
  pairs under `nodeOfFlag` (`nodeSet_eq_range_nodeOfFlag`), it is finite (`nodeSet_finite`) and it
  is closed (`isClosed_nodeSet`).  A point of the glued curve is a node exactly when it is the
  node of a flag pair (`mem_nodeSet`).  The map `nodeOfFlag` sends a flag pair to its node; two
  flag pairs have the same node exactly when they are the same flag pair (`nodeOfFlag_inj`), so
  `nodeOfFlag` is injective (`nodeOfFlag_injective`).
* the complement of the node set is written `(nodeSet d)ᶜ` throughout.  It is open
  (`isOpen_compl_nodeSet`), and it is the image of the components minus their flag points
  under the quotient map (`image_quotient_mk_compl`).  The quotient map restricts to a
  homeomorphism from the disjoint union of the normalization components minus their flag points
  onto the complement of the node set, because it is an open embedding there
  (`quotientMapOnComplNodeSetHomeomorph`).

The node set and its complement are *intended* to be the singular locus and the smooth locus of
the nodal curve.  This file only builds the underlying topological space, so the two names are
names: nothing here is a statement about singularities or about smoothness.

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

/-- The point of the disjoint union selected by a flag pair and a boolean: `false` selects the
first point of the flag pair, `true` the second.  This is the function whose injectivity is the
hypothesis on the gluing data. -/
def flagPointOf {ι Flag : Type*} {X : ι → Type*} (fst snd : Flag → ι)
    (fstPt : ∀ f : Flag, X (fst f)) (sndPt : ∀ f : Flag, X (snd f))
    (p : Flag × Bool) : Σ i, X i :=
  if p.2 then ⟨snd p.1, sndPt p.1⟩ else ⟨fst p.1, fstPt p.1⟩

-- The bodies of `flagPointOf`, `fstPoint` and `sndPoint` stay unexposed: the value lemmas below
-- are closed by `(rfl)`, written with the parentheses that suppress the automatic `@[defeq]` tag,
-- so that they export and import cleanly from this module.
/-- The flag point selected by `false` is the first point of the flag pair. -/
@[simp] theorem flagPointOf_false {ι Flag : Type*} {X : ι → Type*} (fst snd : Flag → ι)
    (fstPt : ∀ f : Flag, X (fst f)) (sndPt : ∀ f : Flag, X (snd f)) (f : Flag) :
    flagPointOf fst snd fstPt sndPt (f, false) = ⟨fst f, fstPt f⟩ :=
  (rfl)

/-- The flag point selected by `true` is the second point of the flag pair. -/
@[simp] theorem flagPointOf_true {ι Flag : Type*} {X : ι → Type*} (fst snd : Flag → ι)
    (fstPt : ∀ f : Flag, X (fst f)) (sndPt : ∀ f : Flag, X (snd f)) (f : Flag) :
    flagPointOf fst snd fstPt sndPt (f, true) = ⟨snd f, sndPt f⟩ :=
  (rfl)

/-- The gluing data of a nodal curve: the flag pairs at which the normalization components are
glued.  A flag pair `f` names the two components `fst f` and `snd f` together with the points
`fstPt f` and `sndPt f` of those components that are identified.

The field `flagPointOf_injective'` says that the flag points are pairwise distinct: the two points
of one flag pair are different, and no point of the disjoint union occurs in two different flag
pairs.  This is the hypothesis that makes the data the data of a nodal curve rather than of an
arbitrary gluing of curves along points.

The structure is bare gluing data: index maps and points on arbitrary types, with no topology
and no curve structure. -/
structure FlagPairData (ι : Type*) (Flag : Type*) (X : ι → Type*) where
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
  flagPointOf_injective' : Function.Injective (flagPointOf fst snd fstPt sndPt)

variable (d : FlagPairData ι Flag X)

/-- The first point of a flag pair, as a point of the disjoint union of the components. -/
def fstPoint (d : FlagPairData ι Flag X) (f : Flag) : Σ i, X i := ⟨d.fst f, d.fstPt f⟩

/-- The second point of a flag pair, as a point of the disjoint union of the components. -/
def sndPoint (d : FlagPairData ι Flag X) (f : Flag) : Σ i, X i := ⟨d.snd f, d.sndPt f⟩

-- These two are plain rewrite lemmas rather than `@[simp]` lemmas: `fstPoint` and `sndPoint` occur
-- on the left-hand side of `mk_fstPoint` and `mk_sndPoint`, so tagging them would take those steps
-- out of simp-normal form.
/-- The first point of a flag pair, with its two components. -/
theorem fstPoint_def (d : FlagPairData ι Flag X) (f : Flag) :
    fstPoint d f = ⟨d.fst f, d.fstPt f⟩ :=
  (rfl)

/-- The second point of a flag pair, with its two components. -/
theorem sndPoint_def (d : FlagPairData ι Flag X) (f : Flag) :
    sndPoint d f = ⟨d.snd f, d.sndPt f⟩ :=
  (rfl)

/-- The two points of a flag pair, selected by a boolean: `false` selects the first point of the
flag pair, `true` the second. -/
def flagPoint (d : FlagPairData ι Flag X) (p : Flag × Bool) : Σ i, X i :=
  flagPointOf d.fst d.snd d.fstPt d.sndPt p

/-- **The flag points are pairwise distinct.**  The points of the disjoint union that are glued --
the flag points -- are pairwise distinct: the two points of one flag pair are different, and no
point occurs in two different flag pairs. -/
theorem flagPoint_injective (d : FlagPairData ι Flag X) : Function.Injective (flagPoint d) :=
  d.flagPointOf_injective'

/-- The first point of a flag pair is the flag point selected by `false`. -/
@[simp] theorem flagPoint_false (d : FlagPairData ι Flag X) (f : Flag) :
    flagPoint d (f, false) = fstPoint d f := by
  simp only [flagPoint, flagPointOf_false, fstPoint_def]

/-- The second point of a flag pair is the flag point selected by `true`. -/
@[simp] theorem flagPoint_true (d : FlagPairData ι Flag X) (f : Flag) :
    flagPoint d (f, true) = sndPoint d f := by
  simp only [flagPoint, flagPointOf_true, sndPoint_def]

/-- Two flag pairs with the same first point are the same flag pair. -/
theorem fstPoint_injective (d : FlagPairData ι Flag X) : Function.Injective (fstPoint d) := by
  intro f g h
  have h' : flagPoint d (f, false) = flagPoint d (g, false) := by simpa using h
  exact (Prod.ext_iff.mp (flagPoint_injective d h')).1

/-- Two flag pairs with the same second point are the same flag pair. -/
theorem sndPoint_injective (d : FlagPairData ι Flag X) : Function.Injective (sndPoint d) := by
  intro f g h
  have h' : flagPoint d (f, true) = flagPoint d (g, true) := by simpa using h
  exact (Prod.ext_iff.mp (flagPoint_injective d h')).1

/-- The first point of a flag pair is never the second point of a flag pair: a flag pair never
pairs a point with itself. -/
theorem fstPoint_ne_sndPoint (d : FlagPairData ι Flag X) (f g : Flag) :
    fstPoint d f ≠ sndPoint d g := by
  intro h
  have h' : flagPoint d (f, false) = flagPoint d (g, true) := by simpa using h
  obtain ⟨_, hbt⟩ := Prod.ext_iff.mp (flagPoint_injective d h')
  simp at hbt

/-- A flag point belongs to a unique flag pair. -/
theorem eq_of_flagPoint_mem (d : FlagPairData ι Flag X) {f g : Flag} {p : Σ i, X i}
    (hp : p = fstPoint d f ∨ p = sndPoint d f)
    (hq : p = fstPoint d g ∨ p = sndPoint d g) : f = g := by
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact fstPoint_injective d (hp.symm.trans hq)
  · exact absurd (hp.symm.trans hq) (fstPoint_ne_sndPoint d f g)
  · exact absurd (hp.symm.trans hq) (fun h => fstPoint_ne_sndPoint d g f h.symm)
  · exact sndPoint_injective d (hp.symm.trans hq)

/-- The generating relation of the gluing: two points of the disjoint union are related when they
are the two points of one flag pair.  Its characterisation is `flagRel_def`. -/
def flagRel (d : FlagPairData ι Flag X) (x y : Σ i, X i) : Prop :=
  ∃ f : Flag, (x = fstPoint d f ∧ y = sndPoint d f) ∨ (x = sndPoint d f ∧ y = fstPoint d f)

/-- **The generating relation, characterised.**  Two points of the disjoint union are related by
the generating relation exactly when they are the two points of one flag pair, in either order. -/
theorem flagRel_def (d : FlagPairData ι Flag X) (x y : Σ i, X i) :
    flagRel d x y ↔ ∃ f : Flag, (x = fstPoint d f ∧ y = sndPoint d f) ∨
      (x = sndPoint d f ∧ y = fstPoint d f) :=
  Iff.rfl

/-- The generating relation is symmetric. -/
theorem flagRel_symm (d : FlagPairData ι Flag X) {x y : Σ i, X i} (h : flagRel d x y) :
    flagRel d y x := by
  obtain ⟨f, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩ := (flagRel_def d x y).mp h
  · exact (flagRel_def d y x).mpr ⟨f, Or.inr ⟨hy, hx⟩⟩
  · exact (flagRel_def d y x).mpr ⟨f, Or.inl ⟨hy, hx⟩⟩

/-- **The flag pairs form a matching.**  Two flag relations that meet in a point glue the same two
points: the flag points being pairwise distinct forces the two flag pairs to be equal, so every
chain of flag pairs reduces to equality or to a single generating step. -/
theorem eq_of_flagRel_of_flagRel (d : FlagPairData ι Flag X) {x y z : Σ i, X i}
    (h₁ : flagRel d x y) (h₂ : flagRel d y z) : x = z := by
  obtain ⟨f, hf⟩ := (flagRel_def d x y).mp h₁
  obtain ⟨g, hg⟩ := (flagRel_def d y z).mp h₂
  rcases hf with ⟨hxf, hyf⟩ | ⟨hxf, hyf⟩
  · rcases hg with ⟨hyg, hzg⟩ | ⟨hyg, hzg⟩
    · exact absurd (hyf.symm.trans hyg) (fun h => fstPoint_ne_sndPoint d g f h.symm)
    · have hfg : f = g := eq_of_flagPoint_mem d (p := y) (Or.inr hyf) (Or.inr hyg)
      exact hxf.trans ((congrArg (fun f => fstPoint d f) hfg).trans hzg.symm)
  · rcases hg with ⟨hyg, hzg⟩ | ⟨hyg, hzg⟩
    · have hfg : f = g := eq_of_flagPoint_mem d (p := y) (Or.inl hyf) (Or.inl hyg)
      exact hxf.trans ((congrArg (fun f => sndPoint d f) hfg).trans hzg.symm)
    · exact absurd (hyf.symm.trans hyg) (fstPoint_ne_sndPoint d f g)

/-- **The equivalence relation generated by the flag pairs.**  Two points of the disjoint union are
glued together exactly when they are equal, or when they are the two points of one flag pair.
Because the flag points are pairwise distinct, every chain of flag pairs reduces to equality or to
a single generating step, so this is exactly the relation generated by the flag pairs.  Its
characterisation is `gluedRel_def`. -/
def gluedRel (d : FlagPairData ι Flag X) (x y : Σ i, X i) : Prop := x = y ∨ flagRel d x y

/-- **The generated relation, characterised.**  Two points of the disjoint union are related by the
generated relation exactly when they are equal or when they are the two points of one flag pair. -/
theorem gluedRel_def (d : FlagPairData ι Flag X) (x y : Σ i, X i) :
    gluedRel d x y ↔ x = y ∨ flagRel d x y :=
  Iff.rfl

/-- The glued relation is symmetric. -/
theorem gluedRel_symm (d : FlagPairData ι Flag X) {x y : Σ i, X i} (h : gluedRel d x y) :
    gluedRel d y x := by
  rcases (gluedRel_def d x y).mp h with h | h
  · exact (gluedRel_def d y x).mpr (Or.inl h.symm)
  · exact (gluedRel_def d y x).mpr (Or.inr (flagRel_symm d h))

/-- The glued relation is transitive. -/
theorem gluedRel_trans (d : FlagPairData ι Flag X) {x y z : Σ i, X i}
    (h₁ : gluedRel d x y) (h₂ : gluedRel d y z) : gluedRel d x z := by
  rcases (gluedRel_def d x y).mp h₁ with h₁ | h₁ <;>
    rcases (gluedRel_def d y z).mp h₂ with h₂ | h₂
  · exact (gluedRel_def d x z).mpr (Or.inl (h₁.trans h₂))
  · exact (gluedRel_def d x z).mpr (Or.inr (h₁.symm ▸ h₂))
  · exact (gluedRel_def d x z).mpr (Or.inr (h₂ ▸ h₁))
  · exact (gluedRel_def d x z).mpr (Or.inl (eq_of_flagRel_of_flagRel d h₁ h₂))

/-- The generating relation is contained in the glued relation. -/
theorem flagRel_le_gluedRel (d : FlagPairData ι Flag X) : flagRel d ≤ gluedRel d :=
  fun x y h => (gluedRel_def d x y).mpr (Or.inr h)

/-- **The relation between two flag points.**  Two flag points of the disjoint union are related
by `gluedRel` exactly when they belong to the same flag pair. -/
theorem gluedRel_iff_of_flagPoints (d : FlagPairData ι Flag X) {f g : Flag}
    {p q : Σ i, X i}
    (hp : p = fstPoint d f ∨ p = sndPoint d f)
    (hq : q = fstPoint d g ∨ q = sndPoint d g) :
    gluedRel d p q ↔ f = g := by
  constructor
  · intro h
    rcases (gluedRel_def d p q).mp h with h | ⟨c, hc⟩
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
    · exact (gluedRel_def d p q).mpr (Or.inl (hp.trans hq.symm))
    · exact (gluedRel_def d p q).mpr (Or.inr ⟨f, Or.inl ⟨hp, hq⟩⟩)
    · exact (gluedRel_def d p q).mpr (Or.inr ⟨f, Or.inr ⟨hp, hq⟩⟩)
    · exact (gluedRel_def d p q).mpr (Or.inl (hp.trans hq.symm))

/-- The glued relation, as an equivalence relation. -/
theorem gluedRel_equivalence (d : FlagPairData ι Flag X) : Equivalence (gluedRel d) where
  refl := fun x => (gluedRel_def d x x).mpr (Or.inl rfl)
  symm := fun h => gluedRel_symm d h
  trans := fun h₁ h₂ => gluedRel_trans d h₁ h₂

/-- **The generated relation is the equivalence closure of the generating relation.**  The
equivalence relation `gluedRel` generated by the flag pairs is exactly `Relation.EqvGen` of the
generating relation `flagRel`: two points of the disjoint union are glued together precisely when
the generating relation relates them, or when they are equal. -/
theorem gluedRel_iff_eqvGen (d : FlagPairData ι Flag X) (x y : Σ i, X i) :
    gluedRel d x y ↔ Relation.EqvGen (flagRel d) x y := by
  constructor
  · intro h
    rcases (gluedRel_def d x y).mp h with h | h
    · subst h
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h
  · intro h
    -- The equivalence closure of a relation contained in an equivalence relation stays inside it.
    exact (gluedRel_equivalence d).eqvGen_iff.mp
      (Relation.EqvGen.mono (flagRel_le_gluedRel d) x y h)

/-- The points of the disjoint union that occur in a flag pair: the range of the flag points. -/
def flagPointSet (d : FlagPairData ι Flag X) : Set (Σ i, X i) :=
  Set.range (flagPoint d)

/-- A point of the disjoint union is a flag point when it occurs in a flag pair. -/
@[simp] theorem mem_flagPointSet (d : FlagPairData ι Flag X) (x : Σ i, X i) :
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

/-- The flag point set is the range of the flag points. -/
theorem flagPointSet_eq_range (d : FlagPairData ι Flag X) :
    flagPointSet d = Set.range (flagPoint d) :=
  (rfl)

/-- **Flag points are the points glued to another point.**  A point of the disjoint union is a
flag point exactly when the generating relation relates it to some point. -/
theorem mem_flagPointSet_iff_exists_flagRel (d : FlagPairData ι Flag X) (x : Σ i, X i) :
    x ∈ flagPointSet d ↔ ∃ y, flagRel d x y := by
  rw [mem_flagPointSet]
  constructor
  · rintro ⟨f, hx | hx⟩
    · exact ⟨sndPoint d f, f, Or.inl ⟨hx, rfl⟩⟩
    · exact ⟨fstPoint d f, f, Or.inr ⟨hx, rfl⟩⟩
  · rintro ⟨y, f, ⟨hx, -⟩ | ⟨hx, -⟩⟩
    · exact ⟨f, Or.inl hx⟩
    · exact ⟨f, Or.inr hx⟩

/-- **The partner of a flag point.**  The generating relation relates the flag points selected by
`p` and `q` exactly when they are the two points of one flag pair: `q` is `p` with its boolean
negated. -/
theorem flagRel_flagPoint_iff (d : FlagPairData ι Flag X) (p q : Flag × Bool) :
    flagRel d (flagPoint d p) (flagPoint d q) ↔ q = (p.1, !p.2) := by
  obtain ⟨f, b⟩ := p
  obtain ⟨g, c⟩ := q
  simp only [flagRel_def, ← flagPoint_false, ← flagPoint_true, (flagPoint_injective d).eq_iff]
  cases b <;> cases c <;> simp [eq_comm]

/-- The flag points of `d` form a finite set. -/
theorem flagPointSet_finite [Finite Flag] : (flagPointSet d).Finite :=
  Set.finite_range (flagPoint d)

/-- **Marks** on a nodal curve presented by flag-pair data, labelled by `L`: pairwise distinct
points of the normalization, none of which is a flag point.  These are the smooth marks of the
curve: their images in the glued curve avoid the nodes. -/
structure Marking (d : FlagPairData ι Flag X) (L : Type*) where
  /-- The point of the normalization carrying a label. -/
  point : L → Σ i, X i
  /-- Distinct labels mark distinct points. -/
  point_injective : Function.Injective point
  /-- No mark is a flag point. -/
  point_notMem_flagPointSet (l : L) : point l ∉ flagPointSet d

/-- The generated relation relates two points of the disjoint union only when they are equal or
when both of them are flag points. -/
theorem eq_or_mem_flagPointSet_of_gluedRel (d : FlagPairData ι Flag X) {a b : Σ i, X i}
    (h : gluedRel d a b) : a = b ∨ (a ∈ flagPointSet d ∧ b ∈ flagPointSet d) := by
  rcases (gluedRel_def d a b).mp h with h | ⟨f, hf⟩
  · exact Or.inl h
  · rcases hf with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, Or.inl ha⟩,
        (mem_flagPointSet d b).mpr ⟨f, Or.inr hb⟩⟩
    · exact Or.inr ⟨(mem_flagPointSet d a).mpr ⟨f, Or.inr ha⟩,
        (mem_flagPointSet d b).mpr ⟨f, Or.inl hb⟩⟩

/-- The generated relation as a setoid: the equivalence relation on the disjoint union of the
normalization components that glues the points of the flag pairs together. -/
def gluedRelSetoid (d : FlagPairData ι Flag X) : Setoid (Σ i, X i) :=
  Setoid.mk (gluedRel d) (gluedRel_equivalence d)

/-- The relation of the setoid is the generated relation. -/
@[simp] theorem gluedRelSetoid_r (d : FlagPairData ι Flag X) (x y : Σ i, X i) :
    gluedRelSetoid d x y ↔ gluedRel d x y :=
  Iff.rfl

/-- The two points of a flag pair are glued. -/
theorem gluedRelSetoid_fstPoint_sndPoint (d : FlagPairData ι Flag X) (f : Flag) :
    gluedRelSetoid d (fstPoint d f) (sndPoint d f) :=
  (gluedRelSetoid_r d _ _).mpr ((gluedRel_def d _ _).mpr
    (Or.inr ((flagRel_def d _ _).mpr ⟨f, Or.inl ⟨rfl, rfl⟩⟩)))

/-- The first point of a flag pair is glued only to itself and to the second point. -/
theorem eq_or_eq_of_gluedRelSetoid_fstPoint (d : FlagPairData ι Flag X) {f : Flag}
    {w : Σ i, X i} (h : gluedRelSetoid d (fstPoint d f) w) :
    w = fstPoint d f ∨ w = sndPoint d f := by
  rcases (gluedRel_def d _ _).mp ((gluedRelSetoid_r d _ _).mp h) with h | h
  · exact Or.inl h.symm
  obtain ⟨g, ⟨hg, rfl⟩ | ⟨hg, -⟩⟩ := (flagRel_def d _ _).mp h
  · exact Or.inr (by rw [fstPoint_injective d hg])
  · exact (fstPoint_ne_sndPoint d f g hg).elim

/-- **The glued space.**  The quotient of the disjoint union of the normalization components by the
generated relation: the underlying topological space of the nodal curve.  The topology is the
quotient topology, i.e. the finest topology making the quotient map continuous. -/
abbrev GluedCurve (d : FlagPairData ι Flag X) :=
  Quotient (gluedRelSetoid d)

/-- A map out of the disjoint union that is constant on the two points of every flag pair is
constant on the classes of the generated relation. -/
private theorem lift_agree (d : FlagPairData ι Flag X) {Y : Type*} (g : (Σ i, X i) → Y)
    (hg : ∀ f, g (fstPoint d f) = g (sndPoint d f)) {x y : Σ i, X i}
    (hxy : gluedRel d x y) : g x = g y := by
  rcases (gluedRel_def d x y).mp hxy with hxy | ⟨f, hxy | hxy⟩
  · exact hxy ▸ rfl
  · exact (congrArg g hxy.1).trans ((hg f).trans (congrArg g hxy.2).symm)
  · exact (congrArg g hxy.1).trans ((hg f).symm.trans (congrArg g hxy.2).symm)

namespace GluedCurve

/-- **The lifting property of the glued curve.**  A map out of the disjoint union of the
normalization components that takes the same value on the two points of every flag pair descends
to a map out of the glued curve: the glued curve is the quotient of the disjoint union by the
relation identifying the two points of each flag pair. -/
def lift (d : FlagPairData ι Flag X) {Y : Type*}
    (g : (Σ i, X i) → Y) (hg : ∀ f, g (fstPoint d f) = g (sndPoint d f)) : GluedCurve d → Y :=
  Quotient.lift g (fun a b hab => lift_agree d g hg ((gluedRelSetoid_r d a b).mp hab))

/-- **The lift is the original map on the representatives.**  The lift of `g` to the glued curve
agrees with `g` on the image of a point of the disjoint union. -/
@[simp] theorem lift_mk (d : FlagPairData ι Flag X) {Y : Type*}
    (g : (Σ i, X i) → Y) (hg : ∀ f, g (fstPoint d f) = g (sndPoint d f)) (x : Σ i, X i) :
    GluedCurve.lift d g hg (Quotient.mk (gluedRelSetoid d) x) = g x := by
  unfold GluedCurve.lift
  exact Quotient.lift_mk g _ x

/-- **The lift is unique.**  A map out of the glued curve that agrees with `g` on the images
of the points of the disjoint union is the lift of `g`. -/
theorem lift_unique (d : FlagPairData ι Flag X) {Y : Type*}
    (g : (Σ i, X i) → Y) (hg : ∀ f, g (fstPoint d f) = g (sndPoint d f))
    (h : GluedCurve d → Y) (hh : ∀ x, h (Quotient.mk (gluedRelSetoid d) x) = g x) :
    h = GluedCurve.lift d g hg := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simpa using hh x

/-- **A continuous map descends to a continuous map.**  The lift of a continuous map out of the
disjoint union that is constant on the two points of every flag pair is continuous. -/
theorem continuous_lift (d : FlagPairData ι Flag X) [∀ i, TopologicalSpace (X i)]
    {Y : Type*} [TopologicalSpace Y]
    (g : (Σ i, X i) → Y) (hg : ∀ f, g (fstPoint d f) = g (sndPoint d f))
    (hcont : Continuous g) : Continuous (GluedCurve.lift d g hg) :=
  hcont.quotient_lift (fun a b hab => lift_agree d g hg ((gluedRelSetoid_r d a b).mp hab))

end GluedCurve

/-- **The node set.**  The image of the flag points in the glued curve.  It is intended to be the
singular locus of the nodal curve, but this file only builds the underlying topological space. -/
def nodeSet (d : FlagPairData ι Flag X) : Set (GluedCurve d) :=
  Quotient.mk (gluedRelSetoid d) '' flagPointSet d

/-- The node set is the image of the flag points under the quotient map. -/
theorem image_flagPointSet (d : FlagPairData ι Flag X) :
    Quotient.mk (gluedRelSetoid d) '' flagPointSet d = nodeSet d :=
  (rfl)

/-- The node point of a flag pair: the image of its first point in the glued curve. -/
def nodeOfFlag (d : FlagPairData ι Flag X) (f : Flag) : GluedCurve d :=
  Quotient.mk (gluedRelSetoid d) (fstPoint d f)

/-- The first point of a flag pair is sent to its node. -/
@[simp] theorem mk_fstPoint (d : FlagPairData ι Flag X) (f : Flag) :
    Quotient.mk (gluedRelSetoid d) (fstPoint d f) = nodeOfFlag d f := by
  rw [nodeOfFlag]

/-- The second point of a flag pair is sent to the same node as the first one. -/
@[simp] theorem mk_sndPoint (d : FlagPairData ι Flag X) (f : Flag) :
    Quotient.mk (gluedRelSetoid d) (sndPoint d f) = nodeOfFlag d f := by
  rw [← mk_fstPoint]
  refine Quotient.sound ?_
  exact (gluedRelSetoid_r d (sndPoint d f) (fstPoint d f)).mpr
    ((gluedRel_iff_of_flagPoints d (f := f) (g := f) (Or.inr rfl) (Or.inl rfl)).mpr rfl)

/-- The flag point selected by `p` is sent to the node of its flag pair `p.1`. -/
@[simp] theorem mk_flagPoint (d : FlagPairData ι Flag X) (p : Flag × Bool) :
    Quotient.mk (gluedRelSetoid d) (flagPoint d p) = nodeOfFlag d p.1 := by
  obtain ⟨f, b⟩ := p
  cases b <;> simp

/-- **The fibres of the flag-pair map.**  Two flag pairs have the same node exactly when they are
equal, so every non-empty fibre of `nodeOfFlag` is a singleton.  The fibres over the points that
are not nodes are empty. -/
@[simp] theorem nodeOfFlag_inj (d : FlagPairData ι Flag X) (f g : Flag) :
    nodeOfFlag d f = nodeOfFlag d g ↔ f = g := by
  simp only [nodeOfFlag, Quotient.eq, gluedRelSetoid_r]
  exact gluedRel_iff_of_flagPoints d (Or.inl rfl) (Or.inl rfl)

/-- **The flag-pair map to the node set is injective.**  Distinct flag pairs give distinct nodes,
because the flag points are pairwise distinct. -/
theorem nodeOfFlag_injective (d : FlagPairData ι Flag X) : Function.Injective (nodeOfFlag d) :=
  fun f g h => (nodeOfFlag_inj d f g).mp h

/-- **The membership of the node set.**  A point of the glued curve is a node exactly when it is
the node of a flag pair. -/
@[simp] theorem mem_nodeSet (d : FlagPairData ι Flag X) (q : GluedCurve d) :
    q ∈ nodeSet d ↔ ∃ f : Flag, nodeOfFlag d f = q := by
  rw [← image_flagPointSet, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hqx⟩
    obtain ⟨f, hxf | hxf⟩ := (mem_flagPointSet d x).mp hx
    · refine ⟨f, ?_⟩
      rw [← mk_fstPoint, ← hxf]
      exact hqx
    · refine ⟨f, ?_⟩
      rw [← mk_sndPoint, ← hxf]
      exact hqx
  · rintro ⟨f, hqf⟩
    refine ⟨fstPoint d f, (mem_flagPointSet d _).mpr ⟨f, Or.inl rfl⟩, ?_⟩
    rw [mk_fstPoint]
    exact hqf

/-- **The node set is the image of the flag pairs.**  The node set of the glued curve is the image
of the flag pairs under `nodeOfFlag`. -/
theorem nodeSet_eq_range_nodeOfFlag (d : FlagPairData ι Flag X) :
    nodeSet d = Set.range (nodeOfFlag d) :=
  Set.ext (mem_nodeSet d)

/-- The node set of the glued curve is finite: it is the image of the finite set of flag points. -/
theorem nodeSet_finite [Finite Flag] : (nodeSet d).Finite :=
  (flagPointSet_finite d).image _

/-- **The preimage of the node set.**  The quotient map sends a point of the disjoint union to a
node exactly when that point is a flag point: the preimage of the node set is the flag point set.
-/
@[simp] theorem preimage_nodeSet (d : FlagPairData ι Flag X) :
    (Quotient.mk (gluedRelSetoid d)) ⁻¹' nodeSet d = flagPointSet d := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_preimage] at hx
    -- The point `x` is sent to a node, so it is glued to the first point of a flag pair.
    obtain ⟨f, hxf⟩ := (mem_nodeSet d (Quotient.mk (gluedRelSetoid d) x)).mp hx
    have hrel : gluedRel d x (fstPoint d f) :=
      (gluedRelSetoid_r d x (fstPoint d f)).mp (Quotient.exact hxf.symm)
    rcases eq_or_mem_flagPointSet_of_gluedRel d hrel with heq | ⟨hxF, _⟩
    · exact (mem_flagPointSet d _).mpr ⟨f, Or.inl heq⟩
    · exact hxF
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The generated relation identifies only flag points.**  Two distinct points of the disjoint
union are related by the generated relation only when the first of them is a flag point. -/
theorem mem_flagPointSet_of_gluedRelSetoid_of_ne (d : FlagPairData ι Flag X) :
    ∀ ⦃x y : Σ i, X i⦄, gluedRelSetoid d x y → x ≠ y → x ∈ flagPointSet d := by
  intro x y h hne
  have hglued : gluedRel d x y := (gluedRelSetoid_r d x y).mp h
  rcases eq_or_mem_flagPointSet_of_gluedRel d (a := x) (b := y) hglued with heq | ⟨hx, _⟩
  · exact absurd heq hne
  · exact hx

/-- **The node set is closed.**  The node set of the glued curve is a closed subset of it, so its
complement is open. -/
theorem isClosed_nodeSet (d : FlagPairData ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T1Space (X i)] [Finite Flag] : IsClosed (nodeSet d) := by
  -- The quotient map is a closed map, so the image of the finite set of flag points is closed.
  rw [← image_flagPointSet]
  exact Setoid.isClosedMap_quotient_mk (gluedRelSetoid d) (flagPointSet_finite d)
    (mem_flagPointSet_of_gluedRelSetoid_of_ne d) (flagPointSet d) (flagPointSet_finite d).isClosed

/-- The complement of the node set is open, being the complement of the closed node set. -/
theorem isOpen_compl_nodeSet (d : FlagPairData ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T1Space (X i)] [Finite Flag] : IsOpen (nodeSet d)ᶜ :=
  (isClosed_nodeSet d).isOpen_compl

/-- **The image of the components minus their flag points.**  The quotient map sends the disjoint
union of the normalization components minus their flag points onto the complement of the node set
in the glued curve. -/
theorem image_quotient_mk_compl (d : FlagPairData ι Flag X) :
    Quotient.mk (gluedRelSetoid d) '' (flagPointSet d)ᶜ = (nodeSet d)ᶜ := by
  rw [Setoid.image_quotient_mk_compl (gluedRelSetoid d)
    (mem_flagPointSet_of_gluedRelSetoid_of_ne d), ← image_flagPointSet]

/-- **The generated relation is closed.**  The equivalence relation generated by the flag pairs is a
closed subset of the product of the disjoint union of the normalization components with itself. -/
theorem isClosed_gluedRel (d : FlagPairData ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] :
    IsClosed {p : (Σ i, X i) × (Σ i, X i) | gluedRel d p.1 p.2} := by
  -- Away from the finitely many flag points the relation is the diagonal, and on the flag points
  -- it is a finite set: this is exactly the hypothesis of `Setoid.isClosed_setOf_rel`.
  exact Setoid.isClosed_setOf_rel (gluedRelSetoid d) (flagPointSet_finite d)
    (mem_flagPointSet_of_gluedRelSetoid_of_ne d)

/-- **The glued space is Hausdorff.**  The quotient of the disjoint union of the normalization
components by the generated relation is a Hausdorff space, when the components are Hausdorff and
when there are finitely many flag pairs. -/
instance t2Space_gluedCurve (d : FlagPairData ι Flag X) [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] [Finite Flag] : T2Space (GluedCurve d) :=
  Setoid.t2Space_quotient (gluedRelSetoid d) (flagPointSet_finite d)
    (mem_flagPointSet_of_gluedRelSetoid_of_ne d)

/-- **The quotient map is an open embedding away from the flag points.**  The quotient map
restricted to the disjoint union of the normalization components minus their flag points is an
open embedding. -/
theorem isOpenEmbedding_domRestrict_quotient_mk (d : FlagPairData ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] [Finite Flag] :
    IsOpenEmbedding ((flagPointSet d)ᶜ.domRestrict (Quotient.mk (gluedRelSetoid d))) :=
  Setoid.isOpenEmbedding_domRestrict_quotient_mk (gluedRelSetoid d) (flagPointSet_finite d)
    (mem_flagPointSet_of_gluedRelSetoid_of_ne d)

/-- **The bundled homeomorphism of the complement of the node set.**  The quotient map, restricted
to the points of the disjoint union that are not flag points, is a homeomorphism from them onto
the complement of the node set in the glued curve. -/
def quotientMapOnComplNodeSetHomeomorph (d : FlagPairData ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] [Finite Flag] :
    ↑((flagPointSet d)ᶜ) ≃ₜ ↑((nodeSet d)ᶜ) :=
  (isOpenEmbedding_domRestrict_quotient_mk d).toIsEmbedding.toHomeomorph.trans
    (.setCongr (by rw [Set.range_domRestrict, image_quotient_mk_compl]))

/-- **The bundled homeomorphism acts by the quotient map.**  On the complement of the flag points,
the homeomorphism of the complement of the node set is the quotient map: it sends a point to its
class in the glued curve. -/
@[simp] theorem quotientMapOnComplNodeSetHomeomorph_apply (d : FlagPairData ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] [Finite Flag]
    (x : ↑((flagPointSet d)ᶜ)) :
    ((quotientMapOnComplNodeSetHomeomorph d x : ↑((nodeSet d)ᶜ)) : GluedCurve d) =
      Quotient.mk (gluedRelSetoid d) x := by
  rw [quotientMapOnComplNodeSetHomeomorph, Homeomorph.trans_apply]
  exact Topology.IsEmbedding.toHomeomorph_apply_coe
    (isOpenEmbedding_domRestrict_quotient_mk d).toIsEmbedding x

/-- **The inverse of the bundled homeomorphism lands in the same class.**  The inverse of the
homeomorphism of the complement of the node set sends a point of the complement to a point of the
disjoint union that represents it in the glued curve. -/
@[simp] theorem quotientMapOnComplNodeSetHomeomorph_symm_apply (d : FlagPairData ι Flag X)
    [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] [Finite Flag]
    (y : ↑((nodeSet d)ᶜ)) :
    Quotient.mk (gluedRelSetoid d)
        (((quotientMapOnComplNodeSetHomeomorph d).symm y : ↑((flagPointSet d)ᶜ)) : Σ i, X i) =
      (y : GluedCurve d) := by
  obtain ⟨x, rfl⟩ := (quotientMapOnComplNodeSetHomeomorph d).surjective y
  rw [Homeomorph.symm_apply_apply]
  exact (quotientMapOnComplNodeSetHomeomorph_apply d x).symm

end NodalGluing

end TauCeti
