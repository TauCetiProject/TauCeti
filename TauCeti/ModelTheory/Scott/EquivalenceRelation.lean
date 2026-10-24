/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Setoid.Partition
public import TauCeti.Data.Set.Card
public import TauCeti.ModelTheory.BackAndForth.Graph
public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Scott.ExtensionPair
public import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Scott analysis of equivalence relations

An equivalence relation `r` on `V` is presented in the language of graphs by the graph
`SimpleGraph.fromRel r`, in which two vertices are adjacent when they are distinct and
`r`-related. This graph is the disjoint union of complete graphs on the classes of `r`, and two
tuples have the same atomic type in it exactly when they have the same equalities and the same
`r`-relations between their entries (`Setoid.sameAtomicType_fromRel_iff`). So back-and-forth
equivalence for these graphs is back-and-forth equivalence for equivalence relations.

When every class is infinite, back-and-forth works as for pure sets: a new element related to an
old one is answered by a fresh element of the matching class, and a new element in a new class by
an element of a class not yet met. The only invariant is the number of classes, counted in
`ℕ∞`, so that all infinite numbers of classes count alike. For equivalence relations of every
cardinality this gives:

* if all classes of both relations are infinite and the two relations have the same number of
  classes in `ℕ∞`, tuples are back-and-forth equivalent at every level exactly when they have the
  same atomic type, and the two structures are potentially isomorphic;
* two countable equivalence relations with infinite classes and the same number of classes are
  isomorphic;
* an equivalence relation with infinite classes has internal Scott rank one;
* the number of classes in `ℕ∞` is invariant under potential isomorphism, and so is infiniteness
  of all classes, so the Scott sentence of a countable equivalence relation with infinite classes
  holds in an equivalence relation of any cardinality exactly when that relation has infinite
  classes and the same number of classes in `ℕ∞`.

For a countable type `ι`, the relation on `ι × ℕ` of having the same first coordinate has one
infinite class for each element of `ι`. Up to isomorphism it is the unique countable equivalence
relation with infinite classes and `ENat.card ι` classes: `ι := Fin k` gives `k` infinite
classes and `ι := ℕ` gives countably many.

For classes of arbitrary sizes, the complete invariant is the number of classes of each size: for
every `κ : ℕ∞`, the number `{c ∈ r.classes | c.encard = κ}.encard` of classes with `κ` elements.
A back-and-forth system matches entries of tuples lying in classes of equal sizes, so it
preserves these numbers. Conversely, when they agree, the pairs of tuples with the same atomic
type whose matching entries lie in classes of equal sizes form a back-and-forth system: a new
element of an old class is answered by an element of the matching class, which has the same size
and as many entries of the tuple, and an element of a new class of size `κ` by an element of a
class of size `κ` not yet met, since both relations have met equally many such classes. For
equivalence relations of every cardinality this gives:

* two equivalence relations are potentially isomorphic exactly when they have equally many
  classes of each size, so two countable equivalence relations are isomorphic exactly when they
  do;
* the Scott sentence of a countable equivalence relation holds in an equivalence relation of any
  cardinality exactly when the two have equally many classes of each size.

## Main results

* `Setoid.isExtensionPair_fromRel`: a relation with no more classes than a relation with
  infinite classes forms an extension pair with it.
* `Setoid.potentialIso_fromRel` and `Setoid.nonempty_relIso_of_infinite`.
* `Setoid.internalScottRank_fromRel_eq_one`.
* `Setoid.enatCard_quotient_eq_of_potentialIso` and `Setoid.infinite_of_potentialIso`.
* `Setoid.realize_scottSentence_fromRel_iff_of_infinite`.
* `TauCeti.nonempty_relIso_ker_fst_iff`.
* `Setoid.potentialIso_fromRel_iff` and `Setoid.nonempty_relIso_iff`: classification by the
  number of classes of each size.
* `Setoid.realize_scottSentence_fromRel_iff`.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, 1965.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe u u' u'' o

open FirstOrder FirstOrder.Language Fin TauCeti SimpleGraph

variable {V : Type u} {W : Type u'}

namespace Setoid

variable {r : Setoid V} {s : Setoid W}

/-- A one-point extension keeps the atomic type when the two new points have the same equalities
and the same relations to the old entries. -/
private theorem sameAtomicType_snoc {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b)
    {x : V} {y : W} (heq : ∀ i, a i = x ↔ b i = y) (hrel : ∀ i, r (a i) x ↔ s (b i) y) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    SameAtomicType (L := Language.graph) (snoc a x) (snoc b y) := by
  obtain ⟨ha, hr⟩ := (sameAtomicType_fromRel_iff r s a b).mp h
  have heq' (i) : x = a i ↔ y = b i := by rw [eq_comm, heq i, eq_comm]
  have hrel' (i) : r x (a i) ↔ s y (b i) := by rw [r.comm', hrel i, s.comm']
  refine (sameAtomicType_fromRel_iff r s _ _).mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · induction i using lastCases <;> induction j using lastCases <;> simp [ha, heq, heq']
  · induction i using lastCases <;> induction j using lastCases <;>
      simp [hr, hrel, hrel']

/-- Tuples with the same atomic type meet equally many classes. -/
private theorem encard_range_mk_eq {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b) :
    (Set.range (Quotient.mk r ∘ a)).encard = (Set.range (Quotient.mk s ∘ b)).encard := by
  obtain ⟨-, hrel⟩ := (sameAtomicType_fromRel_iff r s a b).mp h
  simpa only [Set.image_univ] using Set.encard_image_eq_encard_image_of_eq_iff
    (fun i j => by simpa [Quotient.eq] using hrel i j) Set.univ

/-- If `s` has at least as many classes as `r`, a new class of `r` beyond those met by `a` is
matched by a class of `s` beyond those met by a tuple `b` with the same atomic type. -/
private theorem exists_forall_not_rel {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b)
    (hcard : ENat.card (Quotient r) ≤ ENat.card (Quotient s)) {x : V} (hx : ∀ i, ¬r (a i) x) :
    ∃ y : W, ∀ i, ¬s (b i) y := by
  by_contra! hy
  have hsurj : Set.range (Quotient.mk s ∘ b) = Set.univ :=
    Set.eq_univ_of_forall fun q => Quotient.inductionOn q fun y =>
      (hy y).imp fun _ hi => Quotient.sound hi
  have hlt : (Set.range (Quotient.mk r ∘ a)).encard <
      (insert (Quotient.mk r x) (Set.range (Quotient.mk r ∘ a))).encard :=
    (Set.finite_range _).encard_lt_encard
      (Set.ssubset_insert fun ⟨i, hi⟩ => hx i (Quotient.exact hi))
  refine hlt.not_ge (Set.encard_le_card.trans (hcard.trans ?_))
  rw [encard_range_mk_eq h, hsurj, Set.encard_univ]

/-- If `s` has infinite classes and at least as many classes as `r`, tuples with the same atomic
type have matching one-point extensions on the `r` side. -/
theorem exists_sameAtomicType_snoc_fromRel (hs : ∀ y : W, {y' | s y y'}.Infinite)
    (hcard : ENat.card (Quotient r) ≤ ENat.card (Quotient s)) {n : ℕ} {a : Fin n → V}
    {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b)
    (x : V) :
    ∃ y : W, letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) (snoc a x) (snoc b y) := by
  obtain ⟨heq, hrel⟩ := (sameAtomicType_fromRel_iff r s a b).mp h
  by_cases hx : ∃ i, a i = x
  · -- An old element is answered by the matching old element.
    obtain ⟨i, rfl⟩ := hx
    exact ⟨b i, sameAtomicType_snoc h (fun j => heq j i) (fun j => hrel j i)⟩
  push Not at hx
  by_cases hc : ∃ i, r (a i) x
  · -- A new element of an old class is answered by a fresh element of the matching class.
    obtain ⟨i, hi⟩ := hc
    obtain ⟨y, hy, hyb⟩ := ((hs (b i)).sdiff (Set.finite_range b)).nonempty
    refine ⟨y, sameAtomicType_snoc h (fun j => ?_) (fun j => ?_)⟩
    · exact iff_of_false (hx j) fun hj => hyb ⟨j, hj⟩
    · rw [show r (a j) x ↔ r (a j) (a i) from ⟨fun h => r.trans' h (r.symm' hi),
        fun h => r.trans' h hi⟩, hrel j i]
      exact ⟨fun h => s.trans' h hy, fun h => s.trans' h (s.symm' hy)⟩
  · -- An element of a new class is answered by an element of a class not met by `b`.
    push Not at hc
    obtain ⟨y, hy⟩ := exists_forall_not_rel h hcard hc
    refine ⟨y, sameAtomicType_snoc h (fun j => ?_) (fun j => iff_of_false (hc j) (hy j))⟩
    exact iff_of_false (hx j) fun hj => hy j (hj ▸ s.refl' _)

/-- An equivalence relation with no more classes than an equivalence relation `s` with infinite
classes forms an extension pair with it, in the language of graphs. -/
theorem isExtensionPair_fromRel (hs : ∀ y : W, {y' | s y y'}.Infinite)
    (hcard : ENat.card (Quotient r) ≤ ENat.card (Quotient s)) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    Language.graph.IsExtensionPair V W :=
  letI := (fromRel r).structure
  letI := (fromRel s).structure
  isExtensionPair_iff_forall_exists_snoc.mpr fun h x =>
    exists_sameAtomicType_snoc_fromRel hs hcard h x

/-- Between equivalence relations with infinite classes and equally many classes, tuples are
back-and-forth equivalent at any level exactly when they have the same atomic type. -/
theorem bfEquiv_fromRel_iff_sameAtomicType (hr : ∀ x : V, {x' | r x x'}.Infinite)
    (hs : ∀ y : W, {y' | s y y'}.Infinite)
    (hcard : ENat.card (Quotient r) = ENat.card (Quotient s)) {α : Ordinal.{o}} {n : ℕ}
    {a : Fin n → V} {b : Fin n → W} :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    BFEquiv (L := Language.graph) α n a b ↔ SameAtomicType (L := Language.graph) a b :=
  letI := (fromRel r).structure
  letI := (fromRel s).structure
  ⟨BFEquiv.sameAtomicType, fun h => h.bfEquiv_of_isExtensionPair
    (isExtensionPair_fromRel hs hcard.le) (isExtensionPair_fromRel hr hcard.ge) α⟩

/-- Equivalence relations with infinite classes and equally many classes in `ℕ∞` are potentially
isomorphic, whatever their cardinalities. -/
theorem potentialIso_fromRel (hr : ∀ x : V, {x' | r x x'}.Infinite)
    (hs : ∀ y : W, {y' | s y y'}.Infinite)
    (hcard : ENat.card (Quotient r) = ENat.card (Quotient s)) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    PotentialIso (L := Language.graph) V W :=
  letI := (fromRel r).structure
  letI := (fromRel s).structure
  (isTupleBFSystem_sameAtomicType (isExtensionPair_fromRel hs hcard.le)
    (isExtensionPair_fromRel hr hcard.ge)
    ((sameAtomicType_fromRel_iff r s _ _).mpr ⟨finZeroElim, finZeroElim⟩)).potentialIso

/-- An isomorphism of equivalence relations makes their graphs potentially isomorphic. -/
private theorem potentialIso_fromRel_of_relIso (e : ⇑r ≃r ⇑s) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    PotentialIso (L := Language.graph) V W :=
  letI := (fromRel r).structure
  letI := (fromRel s).structure
  (Iso.toLanguageEquiv (G := fromRel r) (H := fromRel s) ⟨e.toEquiv, fun {_ _} => by
    simp only [fromRel_adj, RelIso.coe_fn_toEquiv, ne_eq, e.injective.eq_iff,
      e.map_rel_iff]⟩).potentialIso

/-- Countable equivalence relations whose graphs are potentially isomorphic are isomorphic. -/
private theorem nonempty_relIso_of_potentialIso [Countable V] [Countable W]
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      PotentialIso (L := Language.graph) V W) :
    Nonempty (⇑r ≃r ⇑s) := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  obtain ⟨e⟩ := countable_potentialIso_iff_iso.mp h
  refine ⟨⟨e.toEquiv, fun {x y} => ?_⟩⟩
  -- The pair `![x, y]` and its image under `e` have the same atomic type.
  obtain ⟨-, hrel⟩ := (sameAtomicType_fromRel_iff r s _ _).mp
    (e.bfEquiv (0 : Ordinal.{0}) ![x, y]).sameAtomicType
  exact (hrel 0 1).symm

/-- Two countable equivalence relations with infinite classes and equally many classes are
isomorphic. -/
theorem nonempty_relIso_of_infinite [Countable V] [Countable W]
    (hr : ∀ x : V, {x' | r x x'}.Infinite) (hs : ∀ y : W, {y' | s y y'}.Infinite)
    (hcard : ENat.card (Quotient r) = ENat.card (Quotient s)) : Nonempty (⇑r ≃r ⇑s) :=
  nonempty_relIso_of_potentialIso (potentialIso_fromRel hr hs hcard)

/-- An equivalence relation with infinite classes, of any cardinality, has internal Scott rank
one. -/
theorem internalScottRank_fromRel_eq_one (hr : ∀ x : V, {x' | r x x'}.Infinite) :
    letI := (fromRel r).structure
    internalScottRank (L := Language.graph) V = 1 :=
  letI := (fromRel r).structure
  (isExtensionPair_fromRel hr le_rfl).internalScottRank_eq_one

/-- Two elements have the same class exactly when they are related. -/
private theorem setOf_rel_eq_iff {x y : V} : {x' | r x x'} = {y' | r y y'} ↔ r x y :=
  ⟨fun h => (Set.ext_iff.mp h y).mpr (r.refl' y), fun h =>
    Set.ext fun _ => ⟨fun hx => r.trans' (r.symm' h) hx, fun hy => r.trans' h hy⟩⟩

/-- The class of an element is one of the classes of the relation. -/
private theorem setOf_rel_mem_classes (x : V) : {x' | r x x'} ∈ r.classes :=
  ⟨x, Set.ext fun _ => r.comm'⟩

/-- Tuples with the same atomic type have equally many entries in the classes of matching
entries. -/
private theorem encard_setOf_rel_inter_range_eq {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b) (i : Fin n) :
    ({x | r (a i) x} ∩ Set.range a).encard = ({y | s (b i) y} ∩ Set.range b).encard := by
  obtain ⟨heq, hrel⟩ := (sameAtomicType_fromRel_iff r s a b).mp h
  rw [← Set.image_preimage_eq_inter_range, ← Set.image_preimage_eq_inter_range,
    Set.encard_image_eq_encard_image_of_eq_iff heq]
  simp only [Set.preimage_ofPred_eq, hrel]

/-- A tuple back-and-forth system from `r` to `s` transfers every lower bound on the number of
elements of the class of an entry that are not entries of the tuple. -/
private theorem le_encard_setOf_rel_sdiff_range {S : Set (Σ n, (Fin n → V) × (Fin n → W))}
    (hS : letI := (fromRel r).structure; letI := (fromRel s).structure
      IsTupleBFSystem (L := Language.graph) S) (m : ℕ) {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (hab : ⟨n, a, b⟩ ∈ S) (i : Fin n) (hm : (m : ℕ∞) ≤ ({x | r (a i) x} \ Set.range a).encard) :
    (m : ℕ∞) ≤ ({y | s (b i) y} \ Set.range b).encard := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    -- Add an element `x` of the class that is not an entry of `a`; its partner `y` lies in the
    -- matching class without being an entry of `b`.
    obtain ⟨x, hxA⟩ := Set.nonempty_of_encard_ne_zero
      (s := {x | r (a i) x} \ Set.range a) fun h => by simp [h] at hm
    have ⟨hx, hxa⟩ := hxA
    obtain ⟨y, hy⟩ := hS.forth hab x
    obtain ⟨heq, hrel⟩ := (sameAtomicType_fromRel_iff r s _ _).mp (hS.sameAtomicType hy)
    have hyb : y ∉ Set.range b := by
      rintro ⟨j, rfl⟩
      exact hxa ⟨j, by simpa using (heq j.castSucc (last n)).mpr (by simp)⟩
    have hsy : s (b i) y := by simpa using (hrel i.castSucc (last n)).mp (by simpa using hx)
    have h := ih hy i.castSucc (by
      rw [snoc_castSucc, range_snoc, ← Set.union_singleton, ← Set.sdiff_sdiff,
        ← ENat.add_le_add_iff_right ENat.one_ne_top, Set.encard_sdiff_singleton_add_one hxA]
      exact_mod_cast hm)
    rw [snoc_castSucc, range_snoc, ← Set.union_singleton, ← Set.sdiff_sdiff] at h
    rw [← Set.encard_sdiff_singleton_add_one
      (⟨hsy, hyb⟩ : y ∈ {y | s (b i) y} \ Set.range b)]
    push_cast
    gcongr

/-- A tuple back-and-forth system from `r` to `s` matches entries of a tuple with entries in
classes of the same size, counted in `ℕ∞`. -/
private theorem encard_setOf_rel_eq_of_isTupleBFSystem
    {S : Set (Σ n, (Fin n → V) × (Fin n → W))}
    (hS : letI := (fromRel r).structure; letI := (fromRel s).structure
      IsTupleBFSystem (L := Language.graph) S) {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (hab : ⟨n, a, b⟩ ∈ S) (i : Fin n) :
    {x | r (a i) x}.encard = {y | s (b i) y}.encard := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  -- Split each class into the entries of the tuple it contains and the remaining elements.
  rw [← Set.encard_sdiff_add_encard_inter _ (Set.range a),
    ← Set.encard_sdiff_add_encard_inter _ (Set.range b)]
  congr 1
  · exact le_antisymm
      (ENat.forall_natCast_le_iff_le.mp fun m => le_encard_setOf_rel_sdiff_range hS m hab i)
      (ENat.forall_natCast_le_iff_le.mp fun m =>
        le_encard_setOf_rel_sdiff_range (r := s) (s := r) hS.symm m (a := b) (b := a) hab i)
  · exact encard_setOf_rel_inter_range_eq (hS.sameAtomicType hab) i

/-- A tuple back-and-forth system from `r` to `s` matches every finite family of classes of `r`
with as many classes of `s`. -/
private theorem enatCard_quotient_le_of_isTupleBFSystem
    {S : Set (Σ n, (Fin n → V) × (Fin n → W))}
    (hS : letI := (fromRel r).structure; letI := (fromRel s).structure
      IsTupleBFSystem (L := Language.graph) S) :
    ENat.card (Quotient r) ≤ ENat.card (Quotient s) := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  refine ENat.forall_natCast_le_iff_le.mp fun m hm => ?_
  rw [← Set.encard_univ] at hm
  obtain ⟨t, -, ht⟩ := Set.exists_subset_encard_eq hm
  obtain ⟨t, rfl⟩ := (Set.finite_of_encard_eq_coe ht).exists_finset_coe
  -- Pick one representative of each class in `t`, and match the tuple of representatives.
  let a : Fin t.card → V := fun i => (t.equivFin.symm i : Quotient r).out
  have ha : Set.range (Quotient.mk r ∘ a) = t := by
    refine Set.ext fun q => ⟨?_, fun hq => ⟨t.equivFin ⟨q, hq⟩, by simp [a]⟩⟩
    rintro ⟨i, rfl⟩
    simp [a]
  obtain ⟨b, hab⟩ := hS.exists_snd_mem a
  rw [← ht, ← ha, encard_range_mk_eq (hS.sameAtomicType hab)]
  exact Set.encard_le_card

/-- Potentially isomorphic equivalence relations have equally many classes in `ℕ∞`, whatever
their cardinalities. -/
theorem enatCard_quotient_eq_of_potentialIso
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      PotentialIso (L := Language.graph) V W) :
    ENat.card (Quotient r) = ENat.card (Quotient s) := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  obtain ⟨S', hS'⟩ := h.symm.exists_isTupleBFSystem
  exact (enatCard_quotient_le_of_isTupleBFSystem hS).antisymm
    (enatCard_quotient_le_of_isTupleBFSystem hS')

/-- Infiniteness of all classes passes from an equivalence relation to every equivalence relation
potentially isomorphic to it, whatever its cardinality. -/
theorem infinite_of_potentialIso (hr : ∀ x : V, {x' | r x x'}.Infinite)
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      PotentialIso (L := Language.graph) V W) (y : W) :
    {y' | s y y'}.Infinite := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  obtain ⟨a, hab⟩ := hS.exists_fst_mem ![y]
  simpa [← Set.encard_eq_top_iff, encard_setOf_rel_eq_of_isTupleBFSystem hS hab 0] using hr (a 0)

variable (s) in
/-- The Scott sentence of a countable equivalence relation with infinite classes holds in an
equivalence relation of any cardinality exactly when that relation has infinite classes and
equally many classes in `ℕ∞`. -/
theorem realize_scottSentence_fromRel_iff_of_infinite [Countable V]
    (hr : ∀ x : V, {x' | r x x'}.Infinite) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    SentenceInf.Realize (scottSentence (L := Language.graph) V) W ↔
      (∀ y : W, {y' | s y y'}.Infinite) ∧ ENat.card (Quotient r) = ENat.card (Quotient s) := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  refine ⟨fun h => ?_, fun ⟨hs, hcard⟩ => ?_⟩
  · have hp := potentialIso_of_realize_scottSentence V h
    exact ⟨infinite_of_potentialIso hr hp, enatCard_quotient_eq_of_potentialIso hp⟩
  · exact (infEquivAt_iff.mp ((potentialIso_fromRel hr hs hcard).infEquivAt ℕ) _).mp
      (realize_scottSentence_self V)

/-! ### Classification by the number of classes of each size -/

/-- If no size of class occurs more often in `r` than in `s`, the class of an element not related
to any entry of `a` is matched by a class of the same size not met by a tuple `b` with the same
atomic type whose matching entries lie in classes of equal sizes: the classes of that size met by
`a` and by `b` are equally many, and those met by `a` miss the class of `x`. -/
private theorem exists_forall_not_rel_encard_eq
    (hcount : ∀ κ : ℕ∞,
      {c ∈ r.classes | c.encard = κ}.encard ≤ {c ∈ s.classes | c.encard = κ}.encard)
    {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b)
    (hsize : ∀ i, {x | r (a i) x}.encard = {y | s (b i) y}.encard) {x : V}
    (hx : ∀ i, ¬r (a i) x) :
    ∃ y : W, (∀ i, ¬s (b i) y) ∧ {x' | r x x'}.encard = {y' | s y y'}.encard := by
  obtain ⟨-, hrel⟩ := (sameAtomicType_fromRel_iff r s a b).mp h
  let I := {i | {x' | r (a i) x'}.encard = {x' | r x x'}.encard}
  have hfg (i j) : {x' | r (a i) x'} = {x' | r (a j) x'} ↔
      {y' | s (b i) y'} = {y' | s (b j) y'} := by
    rw [setOf_rel_eq_iff, setOf_rel_eq_iff, hrel]
  have hlt : ((fun i => {y' | s (b i) y'}) '' I).encard <
      {c ∈ r.classes | c.encard = {x' | r x x'}.encard}.encard := by
    rw [← Set.encard_image_eq_encard_image_of_eq_iff hfg]
    refine ((Set.toFinite I).image _).encard_lt_encard ((Set.ssubset_iff_of_subset ?_).mpr
      ⟨_, ⟨setOf_rel_mem_classes x, rfl⟩, ?_⟩)
    · rintro _ ⟨i, hi, rfl⟩
      exact ⟨setOf_rel_mem_classes _, hi⟩
    · rintro ⟨i, -, hi⟩
      exact hx i (setOf_rel_eq_iff.mp hi)
  obtain ⟨_, ⟨⟨y, rfl⟩, hyκ⟩, hyI⟩ := Set.not_subset.mp fun hsub =>
    (hlt.trans_le (hcount _)).not_ge (Set.encard_le_encard hsub)
  have hcy : {z | s z y} = {y' | s y y'} := Set.ext fun _ => s.comm'
  refine ⟨y, fun i hi => hyI ⟨i, ?_, by simp only [setOf_rel_eq_iff.mpr hi, hcy]⟩,
    by rw [← hcy, hyκ]⟩
  simp only [I, Set.mem_ofPred_eq]
  rw [hsize i, setOf_rel_eq_iff.mpr hi, ← hcy, hyκ]

/-- If no size of class occurs more often in `r` than in `s`, tuples with the same atomic type
whose matching entries lie in classes of equal sizes have matching one-point extensions on the `r`
side with the same property. -/
private theorem exists_snoc_of_encard_classes_le
    (hcount : ∀ κ : ℕ∞,
      {c ∈ r.classes | c.encard = κ}.encard ≤ {c ∈ s.classes | c.encard = κ}.encard)
    {n : ℕ} {a : Fin n → V} {b : Fin n → W}
    (h : letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) a b)
    (hsize : ∀ i, {x | r (a i) x}.encard = {y | s (b i) y}.encard) (x : V) :
    ∃ y : W, (letI := (fromRel r).structure; letI := (fromRel s).structure
      SameAtomicType (L := Language.graph) (snoc a x) (snoc b y)) ∧
      ∀ i, {x' | r ((snoc a x : Fin (n + 1) → V) i) x'}.encard =
        {y' | s ((snoc b y : Fin (n + 1) → W) i) y'}.encard := by
  obtain ⟨heq, hrel⟩ := (sameAtomicType_fromRel_iff r s a b).mp h
  suffices ∃ y : W, (∀ i, a i = x ↔ b i = y) ∧ (∀ i, r (a i) x ↔ s (b i) y) ∧
      {x' | r x x'}.encard = {y' | s y y'}.encard by
    obtain ⟨y, hx, hr, hxy⟩ := this
    exact ⟨y, sameAtomicType_snoc h hx hr, fun i => by
      induction i using lastCases <;> simp [hsize, hxy]⟩
  by_cases hx : ∃ i, a i = x
  · -- An old element is answered by the matching old element.
    obtain ⟨i, rfl⟩ := hx
    exact ⟨b i, fun j => heq j i, fun j => hrel j i, hsize i⟩
  push Not at hx
  by_cases hc : ∃ i, r (a i) x
  · -- A new element of an old class is answered by an element of the matching class that is not
    -- an entry of `b`: the entries of `a` do not exhaust the class of `x`, and the matching class
    -- has the same size and as many entries of `b`.
    obtain ⟨i, hi⟩ := hc
    have hlt : ({y | s (b i) y} ∩ Set.range b).encard < {y | s (b i) y}.encard := by
      rw [← encard_setOf_rel_inter_range_eq h, ← hsize i]
      exact ((Set.finite_range a).inter_of_right _).encard_lt_encard
        ((Set.ssubset_iff_of_subset Set.inter_subset_left).mpr
          ⟨x, hi, fun ⟨_, j, hj⟩ => hx j hj⟩)
    obtain ⟨y, hy, hyb⟩ := Set.not_subset.mp fun hsub =>
      hlt.ne (congrArg Set.encard (Set.inter_eq_left.mpr hsub))
    refine ⟨y, fun j => iff_of_false (hx j) fun hj => hyb ⟨j, hj⟩, fun j => ?_, ?_⟩
    · exact ⟨fun h => s.trans' ((hrel j i).mp (r.trans' h (r.symm' hi))) hy,
        fun h => r.trans' ((hrel j i).mpr (s.trans' h (s.symm' hy))) hi⟩
    · rw [setOf_rel_eq_iff.mpr (r.symm' hi), setOf_rel_eq_iff.mpr (s.symm' hy)]
      exact hsize i
  · -- An element of a new class is answered by an element of a class of the same size that `b`
    -- does not meet.
    push Not at hc
    obtain ⟨y, hy, hxy⟩ := exists_forall_not_rel_encard_eq hcount h hsize hc
    exact ⟨y, fun i => iff_of_false (fun h => hc i (by subst h; exact r.refl' _))
      (fun h => hy i (by subst h; exact s.refl' _)), fun i => iff_of_false (hc i) (hy i), hxy⟩

/-- A tuple back-and-forth system from `r` to `s` matches every finite family of classes of `r` of
a given size with as many classes of `s` of that size. -/
private theorem encard_classes_le_of_isTupleBFSystem {S : Set (Σ n, (Fin n → V) × (Fin n → W))}
    (hS : letI := (fromRel r).structure; letI := (fromRel s).structure
      IsTupleBFSystem (L := Language.graph) S) (κ : ℕ∞) :
    {c ∈ r.classes | c.encard = κ}.encard ≤ {c ∈ s.classes | c.encard = κ}.encard := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  refine ENat.forall_natCast_le_iff_le.mp fun m hm => ?_
  obtain ⟨t, ht, htm⟩ := Set.exists_subset_encard_eq hm
  obtain ⟨t, rfl⟩ := (Set.finite_of_encard_eq_coe htm).exists_finset_coe
  -- Pick one element of each class in `t`, and match the tuple of these elements.
  choose x hx using fun c : t => (ht c.2).1
  let a : Fin t.card → V := fun i => x (t.equivFin.symm i)
  obtain ⟨b, hab⟩ := hS.exists_snd_mem a
  obtain ⟨-, hrel⟩ := (sameAtomicType_fromRel_iff r s a b).mp (hS.sameAtomicType hab)
  have ha (i) : {z | r (a i) z} = t.equivFin.symm i := by
    rw [hx]
    exact Set.ext fun _ => r.comm'
  have hrange : (fun i => {z | r (a i) z}) '' Set.univ = t := by
    refine Set.ext fun c => ⟨?_, fun hc => ⟨t.equivFin ⟨c, hc⟩, trivial, by simp [ha]⟩⟩
    rintro ⟨i, -, rfl⟩
    simp [ha]
  rw [← htm, ← hrange, Set.encard_image_eq_encard_image_of_eq_iff
    (g := fun i => {y | s (b i) y}) fun i j => by rw [setOf_rel_eq_iff, setOf_rel_eq_iff, hrel] ]
  refine Set.encard_le_encard ?_
  rintro _ ⟨i, -, rfl⟩
  refine ⟨setOf_rel_mem_classes _, ?_⟩
  rw [← encard_setOf_rel_eq_of_isTupleBFSystem hS hab i, ha]
  exact (ht (t.equivFin.symm i).2).2

/-- Two equivalence relations, of any cardinalities, are potentially isomorphic in the language of
graphs exactly when, for every `κ : ℕ∞`, they have equally many classes with `κ` elements, counted
in `ℕ∞`. -/
theorem potentialIso_fromRel_iff :
    (letI := (fromRel r).structure; letI := (fromRel s).structure
      PotentialIso (L := Language.graph) V W) ↔
      ∀ κ : ℕ∞, {c ∈ r.classes | c.encard = κ}.encard = {c ∈ s.classes | c.encard = κ}.encard := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  refine ⟨fun h κ => ?_, fun hcount => ?_⟩
  · obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
    exact (encard_classes_le_of_isTupleBFSystem hS κ).antisymm
      (encard_classes_le_of_isTupleBFSystem (r := s) (s := r) hS.symm κ)
  -- Pairs with the same atomic type whose matching entries lie in classes of equal sizes form a
  -- tuple back-and-forth system.
  refine IsTupleBFSystem.potentialIso (S := {p | SameAtomicType (L := Language.graph) p.2.1 p.2.2 ∧
    ∀ i, {x | r (p.2.1 i) x}.encard = {y | s (p.2.2 i) y}.encard})
    ⟨⟨(sameAtomicType_fromRel_iff r s _ _).mpr ⟨finZeroElim, finZeroElim⟩, finZeroElim⟩,
      And.left, ?_, ?_⟩
  · rintro n a b ⟨h, hsize⟩ x
    exact exists_snoc_of_encard_classes_le (fun κ => (hcount κ).le) h hsize x
  · rintro n a b ⟨h, hsize⟩ y
    obtain ⟨x, h', hsize'⟩ := exists_snoc_of_encard_classes_le (r := s) (s := r)
      (fun κ => (hcount κ).ge) h.symm (fun i => (hsize i).symm) y
    exact ⟨x, h'.symm, fun i => (hsize' i).symm⟩

/-- Two countable equivalence relations are isomorphic exactly when, for every `κ : ℕ∞`, they have
equally many classes with `κ` elements, counted in `ℕ∞`. -/
theorem nonempty_relIso_iff [Countable V] [Countable W] :
    Nonempty (⇑r ≃r ⇑s) ↔
      ∀ κ : ℕ∞, {c ∈ r.classes | c.encard = κ}.encard = {c ∈ s.classes | c.encard = κ}.encard :=
  ⟨fun ⟨e⟩ => potentialIso_fromRel_iff.mp (potentialIso_fromRel_of_relIso e),
    fun h => nonempty_relIso_of_potentialIso (potentialIso_fromRel_iff.mpr h)⟩

variable (s) in
/-- The Scott sentence of a countable equivalence relation holds in an equivalence relation of any
cardinality exactly when, for every `κ : ℕ∞`, the two relations have equally many classes with
`κ` elements, counted in `ℕ∞`. -/
theorem realize_scottSentence_fromRel_iff [Countable V] :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    SentenceInf.Realize (scottSentence (L := Language.graph) V) W ↔
      ∀ κ : ℕ∞, {c ∈ r.classes | c.encard = κ}.encard = {c ∈ s.classes | c.encard = κ}.encard := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  refine ⟨fun h => potentialIso_fromRel_iff.mp (potentialIso_of_realize_scottSentence V h),
    fun h => ?_⟩
  exact (infEquivAt_iff.mp ((potentialIso_fromRel_iff.mpr h).infEquivAt ℕ) _).mp
    (realize_scottSentence_self V)

end Setoid

namespace TauCeti

open Setoid

variable {ι : Type u''}

/-- A countable equivalence relation is isomorphic to the relation of having the same first
coordinate on `ι × ℕ`, for a countable type `ι`, exactly when all its classes are infinite and it
has `ENat.card ι` classes. -/
theorem nonempty_relIso_ker_fst_iff [Countable V] [Countable ι] {r : Setoid V} :
    Nonempty (⇑r ≃r ⇑(ker (Prod.fst : ι × ℕ → ι))) ↔
      (∀ x : V, {x' | r x x'}.Infinite) ∧ ENat.card (Quotient r) = ENat.card ι := by
  have hker (p : ι × ℕ) : {q | ker (Prod.fst : ι × ℕ → ι) p q}.Infinite :=
    Set.infinite_of_injective_forall_mem (Prod.mk_right_injective p.1) fun _ => ker_def.mpr rfl
  have hcard : ENat.card (Quotient (ker (Prod.fst : ι × ℕ → ι))) = ENat.card ι :=
    ENat.card_congr (quotientKerEquivOfSurjective _ Prod.fst_surjective)
  refine ⟨fun ⟨e⟩ => ?_, fun ⟨hr, hr'⟩ =>
    nonempty_relIso_of_infinite hr hker (hr'.trans hcard.symm)⟩
  let := (fromRel r).structure
  let := (fromRel (ker (Prod.fst : ι × ℕ → ι))).structure
  have hp := potentialIso_fromRel_of_relIso e
  exact ⟨infinite_of_potentialIso hker hp.symm,
    (enatCard_quotient_eq_of_potentialIso hp).trans hcard⟩

end TauCeti
