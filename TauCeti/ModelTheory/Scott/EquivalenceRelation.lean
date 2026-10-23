/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Range
public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.ExtensionPair
public import TauCeti.ModelTheory.BackAndForth.Graph
public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Scott.ExtensionPair
public import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Scott analysis of equivalence relations with infinite classes

An equivalence relation `r` on `V` is presented in the language of graphs by the graph
`SimpleGraph.fromRel r`, in which two vertices are adjacent when they are distinct and
`r`-related. This graph is the disjoint union of complete graphs on the classes of `r`, and two
tuples have the same atomic type in it exactly when they have the same equalities and the same
`r`-relations between their entries. So back-and-forth equivalence for these graphs is
back-and-forth equivalence for equivalence relations.

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

## Main results

* `Setoid.sameAtomicType_fromRel_iff`: atomic types of tuples are equalities and relations.
* `Setoid.isExtensionPair_fromRel`: a relation with no more classes than a relation with
  infinite classes forms an extension pair with it.
* `Setoid.potentialIso_fromRel` and `Setoid.nonempty_relIso_of_infinite`.
* `Setoid.internalScottRank_fromRel_eq_one`.
* `Setoid.enatCard_quotient_eq_of_potentialIso` and `Setoid.infinite_of_potentialIso`.
* `Setoid.realize_scottSentence_fromRel_iff`.
* `TauCeti.nonempty_relIso_ker_fst_iff`.

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

variable (r s) in
/-- Two tuples have the same atomic type in the graphs of equivalence relations exactly when they
have the same equalities and the same relations between their entries. -/
theorem sameAtomicType_fromRel_iff {n : ℕ} (a : Fin n → V) (b : Fin n → W) :
    letI := (fromRel r).structure
    letI := (fromRel s).structure
    SameAtomicType (L := Language.graph) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i j, r (a i) (a j) ↔ s (b i) (b j) := by
  rw [SimpleGraph.sameAtomicType_iff]
  refine and_congr_right fun heq => forall₂_congr fun i j => ?_
  by_cases h : a i = a j
  · simp [h, (heq i j).mp h]
  · simp [h, mt (heq i j).mpr h, r.comm' (x := a j), s.comm' (x := b j)]

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
  have hker : ker (Quotient.mk r ∘ a) = ker (Quotient.mk s ∘ b) := by
    ext i j
    simpa [ker_def, Quotient.eq] using hrel i j
  exact Set.encard_congr <| (quotientKerEquivRange _).symm.trans <|
    (Equiv.cast (congrArg Quotient hker)).trans (quotientKerEquivRange _)

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

/-- Two countable equivalence relations with infinite classes and equally many classes are
isomorphic. -/
theorem nonempty_relIso_of_infinite [Countable V] [Countable W]
    (hr : ∀ x : V, {x' | r x x'}.Infinite) (hs : ∀ y : W, {y' | s y y'}.Infinite)
    (hcard : ENat.card (Quotient r) = ENat.card (Quotient s)) : Nonempty (⇑r ≃r ⇑s) := by
  let := (fromRel r).structure
  let := (fromRel s).structure
  obtain ⟨e⟩ := countable_potentialIso_iff_iso.mp (potentialIso_fromRel hr hs hcard)
  refine ⟨⟨e.toEquiv, fun {x y} => ?_⟩⟩
  -- The pair `![x, y]` and its image under `e` have the same atomic type.
  obtain ⟨-, hrel⟩ := (sameAtomicType_fromRel_iff r s _ _).mp
    (e.bfEquiv (0 : Ordinal.{0}) ![x, y]).sameAtomicType
  exact (hrel 0 1).symm

/-- An equivalence relation with infinite classes, of any cardinality, has internal Scott rank
one. -/
theorem internalScottRank_fromRel_eq_one (hr : ∀ x : V, {x' | r x x'}.Infinite) :
    letI := (fromRel r).structure
    internalScottRank (L := Language.graph) V = 1 :=
  letI := (fromRel r).structure
  (isExtensionPair_fromRel hr le_rfl).internalScottRank_eq_one

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
  intro hfin
  -- Enumerate the class of `y` by a tuple `b`, match it, and add a fresh element of the matching
  -- class on the `r` side; its partner lies in the class of `y` without being an entry of `b`.
  let t := hfin.toFinset
  let b : Fin t.card → W := fun i => t.equivFin.symm i
  have hb {z : W} (hz : s y z) : ∃ i, b i = z :=
    ⟨t.equivFin ⟨z, hfin.mem_toFinset.mpr hz⟩, by simp [b]⟩
  obtain ⟨i₀, hi₀⟩ := hb (s.refl' y)
  obtain ⟨a, hab⟩ := hS.exists_fst_mem b
  obtain ⟨x, hx, hxa⟩ := ((hr (a i₀)).sdiff (Set.finite_range a)).nonempty
  obtain ⟨y', hy'⟩ := hS.forth hab x
  obtain ⟨heq, hrel⟩ := (sameAtomicType_fromRel_iff r s _ _).mp (hS.sameAtomicType hy')
  have hsy : s y y' := by
    have h₀ := hrel i₀.castSucc (last _)
    simp only [snoc_castSucc, snoc_last, hi₀] at h₀
    exact h₀.mp hx
  obtain ⟨j, rfl⟩ := hb hsy
  exact hxa ⟨j, by simpa using heq j.castSucc (last _)⟩

variable (s) in
/-- The Scott sentence of a countable equivalence relation with infinite classes holds in an
equivalence relation of any cardinality exactly when that relation has infinite classes and
equally many classes in `ℕ∞`. -/
theorem realize_scottSentence_fromRel_iff [Countable V] (hr : ∀ x : V, {x' | r x x'}.Infinite) :
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
  -- An isomorphism of the relations is an isomorphism of their graphs.
  have hp := (Iso.toLanguageEquiv (G := fromRel r) (H := fromRel (ker (Prod.fst : ι × ℕ → ι)))
    ⟨e.toEquiv, fun {_ _} => by
      simp only [fromRel_adj, RelIso.coe_fn_toEquiv, ne_eq, e.injective.eq_iff,
        e.map_rel_iff]⟩).potentialIso
  exact ⟨infinite_of_potentialIso hker hp.symm,
    (enatCard_quotient_eq_of_potentialIso hp).trans hcard⟩

end TauCeti
