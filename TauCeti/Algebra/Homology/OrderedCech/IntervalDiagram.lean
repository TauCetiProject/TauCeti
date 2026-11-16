/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.Algebra.Homology.OrderedCech
public import TauCeti.Algebra.Homology.TotalComplex.Basic
public import TauCeti.Order.Extension.Linear

import TauCeti.Data.Finset.Basic

/-!
# Interval diagrams and their flag totals

Let `S` be a partially ordered set. An *interval diagram* `A` on `S` (`TauCeti.IntervalDiagram`)
assigns an object `A[s, t]` to every interval `s ≤ t` of `S`, and an arrow `A[s, t] ⟶ A[s', t']`
to every inclusion `s ≤ s' ≤ t' ≤ t` of intervals, functorially. A *flag* of `S` is a chain
`s₀ < ⋯ < sₚ`; it spans the interval `[s₀, sₚ]`. For an interval diagram of chain complexes the
*total* (Pardon, Definition A.7.2) is the complex

`Tot A = ⨁ₚ ⨁_{s₀ < ⋯ < sₚ} A[s₀, sₚ][p]`

whose differential is the internal differential plus the alternating sum `∑ₖ (-1)ᵏ` of the arrows
of `A` to the flags with `sₖ` deleted. Implicit atlases glue local virtual chain complexes with
this finite homotopy colimit over the subsets of an index set.

The construction here proceeds in two steps.

* The *flag complex* `IntervalDiagram.flagComplex A` is the chain complex whose degree `p` term is
  the coproduct of the `A[s₀, sₚ]` over the flags with `p + 1` vertices, with the alternating
  deletion differential (`IntervalDiagram.flagComplexι_d`). It is the ordered Čech complex
  (`CategoryTheory.Functor.orderedCechComplex`) of the functor on finite sets of vertices which
  sends a flag to `A[s₀, sₚ]` and every other set to the empty coproduct
  (`IntervalDiagram.flagFunctor`). Ordered Čech complexes need a linear order on the vertices, and
  flags are recorded as finite sets of the linear extension `LinearExtension S`, which lists the
  vertices of every flag in the order of `S` (`IntervalDiagram.IsFlag.le_iff`). The sign `(-1)ᵏ`
  is the orientation of a simplex by the order of its vertices.
* For an interval diagram of chain complexes the flag complex is a first-quadrant bicomplex, and
  the total `IntervalDiagram.total A` is its total complex: flags with `p + 1` vertices sit in
  column `p`, raising the degree by `p`. The complexes are `ℕ`-graded chain complexes. A cochain
  complex bounded above, such as the relative chains `C_(d - q)` indexed by `q`, is one after
  reindexing, and then flag length `p` lowers the cochain degree by `p`, as in Pardon.

The two results are Pardon's Lemmas A.7.4 and A.7.3.

* **Quasi-isomorphisms of diagrams** (`IntervalDiagram.quasiIso_totalMap`). On a finite poset, a map
  of interval diagrams which is a quasi-isomorphism on every interval induces a
  quasi-isomorphism of totals. The map is a quasi-isomorphism on every column of the flag
  bicomplexes, since homology preserves finite coproducts
  (`HomologicalComplex.quasiIso_of_isColimit_cofan`), and the comparison of total complexes with
  quasi-isomorphic rows (`HomologicalComplex₂.quasiIso_total_map_of_rows`) applies to the flipped
  bicomplexes.
* **The top value computes the total** (`IntervalDiagram.quasiIso_topι`). On a finite poset with a
  greatest element `⊤`, if every arrow `A[s, t] ⟶ A[s, t']` shrinking an interval at its upper end
  is a quasi-isomorphism, then the inclusion `IntervalDiagram.topι A` of `A[⊤, ⊤]` in the total,
  as the summand of the one-vertex flag `⊤`, is a quasi-isomorphism. The upper extension
  `IntervalDiagram.upper A : [s, t] ↦ A[s, ⊤]` maps to `A` by such arrows
  (`IntervalDiagram.upperMap`), so its total is quasi-isomorphic to that of `A` by the first
  result. In the upper extension, adjoining `⊤` to a flag does not change its value, and
  `σ ↦ ± (σ ∪ {⊤})` contracts every row of its flag bicomplex onto `A[⊤, ⊤]`, the cone with
  vertex `⊤`.

## Main definitions

* `TauCeti.IntervalDiagram S C`: interval diagrams on `S` with values in `C`.
* `TauCeti.IntervalDiagram.IsFlag`, `TauCeti.IntervalDiagram.flagInterval`: flags and the
  intervals they span.
* `TauCeti.IntervalDiagram.flagComplex`, `TauCeti.IntervalDiagram.flagComplexι`: the flag complex
  and its summand inclusions.
* `TauCeti.IntervalDiagram.total`, `TauCeti.IntervalDiagram.totalMap`: the total and the maps
  induced on it by maps of interval diagrams.
* `TauCeti.IntervalDiagram.topι`: the inclusion of `A[⊤, ⊤]` in the total.

## Main results

* `TauCeti.IntervalDiagram.flagComplexι_d`: the alternating deletion differential.
* `TauCeti.IntervalDiagram.quasiIso_totalMap`: Pardon, Lemma A.7.4.
* `TauCeti.IntervalDiagram.quasiIso_topι`: Pardon, Lemma A.7.3.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. **20** (2016), 779–1034, Appendix A.7 (interval
  diagrams, Definitions A.7.1–A.7.2, and Lemmas A.7.3–A.7.4).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Finset

universe w v u

namespace TauCeti

namespace IntervalDiagram

variable {S : Type w} [PartialOrder S]

/-- A *flag* of `S` is a nonempty finite chain `s₀ < ⋯ < sₚ`. Flags are recorded as finite sets of
the linear extension `LinearExtension S`, whose order agrees with that of `S` on a chain
(`IntervalDiagram.IsFlag.le_iff`), so that the vertices of a flag are listed in the same order by
both. -/
structure IsFlag (s : Finset (LinearExtension S)) : Prop where
  nonempty : s.Nonempty
  total : ∀ a ∈ s, ∀ b ∈ s, ofLinearExtension a ≤ ofLinearExtension b ∨
    ofLinearExtension b ≤ ofLinearExtension a

namespace IsFlag

variable {s t : Finset (LinearExtension S)}

/-- On a flag the order of the linear extension is the order of `S`. -/
lemma le_iff (hs : IsFlag s) {a b : LinearExtension S} (ha : a ∈ s) (hb : b ∈ s) :
    a ≤ b ↔ ofLinearExtension a ≤ ofLinearExtension b := by
  refine ⟨fun hab ↦ ?_, le_of_ofLinearExtension_le⟩
  rcases hs.total a ha b hb with h | h
  · exact h
  · obtain rfl : b = a := le_antisymm (le_of_ofLinearExtension_le h) hab
    exact le_rfl

/-- A nonempty subset of a flag is a flag. -/
lemma mono (hs : IsFlag s) (hts : t ⊆ s) (ht : t.Nonempty) : IsFlag t :=
  ⟨ht, fun a ha b hb ↦ hs.total a (hts ha) b (hts hb)⟩

/-- A singleton is a flag. -/
lemma singleton (a : LinearExtension S) : IsFlag {a} :=
  ⟨singleton_nonempty a, by simp⟩

/-- The least vertex of a flag is below every vertex in `S`. -/
lemma min'_le (hs : IsFlag s) {a : LinearExtension S} (ha : a ∈ s) :
    ofLinearExtension (s.min' hs.nonempty) ≤ ofLinearExtension a :=
  (hs.le_iff (s.min'_mem hs.nonempty) ha).1 (s.min'_le a ha)

/-- The greatest vertex of a flag is above every vertex in `S`. -/
lemma le_max' (hs : IsFlag s) {a : LinearExtension S} (ha : a ∈ s) :
    ofLinearExtension a ≤ ofLinearExtension (s.max' hs.nonempty) :=
  (hs.le_iff ha (s.max'_mem hs.nonempty)).1 (s.le_max' a ha)

end IsFlag

/-- The interval `[s₀, sₚ]` spanned by a flag `s₀ < ⋯ < sₚ`. -/
def flagInterval {s : Finset (LinearExtension S)} (hs : IsFlag s) : NonemptyInterval S :=
  ⟨(ofLinearExtension (s.min' hs.nonempty), ofLinearExtension (s.max' hs.nonempty)),
    hs.min'_le (s.max'_mem hs.nonempty)⟩

@[simp]
lemma flagInterval_fst {s : Finset (LinearExtension S)} (hs : IsFlag s) :
    (flagInterval hs).fst = ofLinearExtension (s.min' hs.nonempty) := (rfl)

@[simp]
lemma flagInterval_snd {s : Finset (LinearExtension S)} (hs : IsFlag s) :
    (flagInterval hs).snd = ofLinearExtension (s.max' hs.nonempty) := (rfl)

/-- The interval of a subflag lies in the interval of the flag. -/
lemma flagInterval_mono {s t : Finset (LinearExtension S)} (hs : IsFlag s) (ht : IsFlag t)
    (hts : t ⊆ s) : flagInterval ht ≤ flagInterval hs :=
  NonemptyInterval.le_def.2 ⟨hs.min'_le (hts (t.min'_mem ht.nonempty)),
    hs.le_max' (hts (t.max'_mem ht.nonempty))⟩

/-- The interval of the singleton flag `{a}` is the one-point interval `[a, a]`. -/
@[simp]
lemma flagInterval_singleton (a : LinearExtension S) :
    flagInterval (IsFlag.singleton a) = NonemptyInterval.pure (ofLinearExtension a) := by
  ext <;> simp [flagInterval]

end IntervalDiagram

/-- An *interval diagram* on a partially ordered set `S` with values in a category `C` assigns an
object `A[s, t]` to each interval `s ≤ t` of `S`, and a morphism `A[s, t] ⟶ A[s', t']` to each
inclusion `s ≤ s' ≤ t' ≤ t` of intervals, functorially (Pardon, Definition A.7.1). Intervals are
ordered by inclusion (`NonemptyInterval.le_def`), so an interval diagram is a contravariant functor
on them. -/
abbrev IntervalDiagram (S : Type w) [PartialOrder S] (C : Type u) [Category.{v} C] :=
  (NonemptyInterval S)ᵒᵖ ⥤ C

namespace IntervalDiagram

variable {S : Type w} [PartialOrder S] {C : Type u} [Category.{v} C]

section Flags

variable [HasCoproducts.{w} C]

/-- The value of an interval diagram on a finite set `s` of vertices: `A[s₀, sₚ]` if `s` is a flag
`s₀ < ⋯ < sₚ`, and the empty coproduct otherwise. It is a coproduct indexed by the proofs that
`s` is a flag. -/
def flagObj (A : IntervalDiagram S C) (s : Finset (LinearExtension S)) : C :=
  ∐ fun h : ULift.{w} (PLift (IsFlag s)) ↦ A.obj (op (flagInterval h.down.down))

/-- The inclusion of `A[s₀, sₚ]` in `IntervalDiagram.flagObj A s` for a flag `s`. -/
def flagObjι (A : IntervalDiagram S C) {s : Finset (LinearExtension S)} (hs : IsFlag s) :
    A.obj (op (flagInterval hs)) ⟶ A.flagObj s :=
  Sigma.ι (fun h : ULift.{w} (PLift (IsFlag s)) ↦ A.obj (op (flagInterval h.down.down))) ⟨⟨hs⟩⟩

/-- Morphisms out of `IntervalDiagram.flagObj A s` are determined on the summand of a flag. -/
@[ext]
lemma flagObj_hom_ext (A : IntervalDiagram S C) {s : Finset (LinearExtension S)} {Y : C}
    {f g : A.flagObj s ⟶ Y} (h : ∀ hs : IsFlag s, A.flagObjι hs ≫ f = A.flagObjι hs ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ fun hs ↦ h hs.down.down

/-- The morphism out of `IntervalDiagram.flagObj A s` given on the summand of a flag. -/
def flagObjDesc (A : IntervalDiagram S C) {s : Finset (LinearExtension S)} {Y : C}
    (f : ∀ hs : IsFlag s, A.obj (op (flagInterval hs)) ⟶ Y) : A.flagObj s ⟶ Y :=
  Sigma.desc fun h ↦ f h.down.down

@[reassoc (attr := simp)]
lemma flagObjι_flagObjDesc (A : IntervalDiagram S C) {s : Finset (LinearExtension S)} {Y : C}
    (f : ∀ hs : IsFlag s, A.obj (op (flagInterval hs)) ⟶ Y) (hs : IsFlag s) :
    A.flagObjι hs ≫ A.flagObjDesc f = f hs :=
  Sigma.ι_comp_desc (fun h : ULift.{w} (PLift (IsFlag s)) ↦ f h.down.down) ⟨⟨hs⟩⟩

variable [HasZeroMorphisms C]

@[simp]
lemma flagObjDesc_zero (A : IntervalDiagram S C) {s : Finset (LinearExtension S)} {Y : C} :
    (A.flagObjDesc fun _ ↦ 0 : A.flagObj s ⟶ Y) = 0 := by
  ext
  simp

/-- The restriction `A[s₀, sₚ] ⟶ A[t₀, t_q]` from a flag `s` to a subset `t ⊆ s`, which is zero when
`t` is empty. -/
def flagRestrict (A : IntervalDiagram S C) {s t : Finset (LinearExtension S)} (hs : IsFlag s)
    (hts : t ⊆ s) : A.obj (op (flagInterval hs)) ⟶ A.flagObj t :=
  if ht : t.Nonempty then
    A.map (homOfLE (flagInterval_mono hs (hs.mono hts ht) hts)).op ≫
      A.flagObjι (hs.mono hts ht)
  else 0

lemma flagRestrict_of_isFlag (A : IntervalDiagram S C) {s t : Finset (LinearExtension S)}
    (hs : IsFlag s) (hts : t ⊆ s) (ht : IsFlag t) :
    A.flagRestrict hs hts =
      A.map (homOfLE (flagInterval_mono hs ht hts)).op ≫ A.flagObjι ht := by
  simp [flagRestrict, ht.nonempty]

/-- The functor `s ↦ IntervalDiagram.flagObj A s` on finite sets of vertices, whose ordered Čech
complex is the flag complex of `A`. An inclusion `t ⊆ s` of flags goes to the arrow of `A` for the
inclusion of their intervals. -/
abbrev flagFunctor (A : IntervalDiagram S C) : (Finset (LinearExtension S))ᵒᵖ ⥤ C where
  obj s := A.flagObj s.unop
  map f := A.flagObjDesc fun hs ↦ A.flagRestrict hs (leOfHom f.unop)
  map_id s := by
    ext hs
    rw [flagObjι_flagObjDesc, flagRestrict_of_isFlag A hs _ hs, Category.comp_id]
    -- The arrow of `A` for the identity inclusion of intervals is the identity.
    exact (congrArg (A.map ·) (Subsingleton.elim _ (𝟙 _))).trans (A.map_id _) ▸ Category.id_comp _
  map_comp {X Y Z} f g := by
    ext hs
    rw [flagObjι_flagObjDesc, flagObjι_flagObjDesc_assoc]
    by_cases hu : Z.unop.Nonempty
    · have hZY : Z.unop ⊆ Y.unop := leOfHom g.unop
      have hYX : Y.unop ⊆ X.unop := leOfHom f.unop
      have hmid := hs.mono hYX (hu.mono hZY)
      rw [flagRestrict_of_isFlag A hs _ (hs.mono (hZY.trans hYX) hu),
        flagRestrict_of_isFlag A hs _ hmid, Category.assoc, flagObjι_flagObjDesc,
        flagRestrict_of_isFlag A hmid _ (hmid.mono hZY hu), ← Category.assoc, ← A.map_comp]
      rfl
    · simp [flagRestrict, hu]

end Flags

/-- A flag with at least two vertices stays a flag when one vertex is deleted. -/
lemma IsFlag.erase {s : Finset (LinearExtension S)} (hs : IsFlag s) {p : ℕ} (hp : #s = p + 1 + 1)
    (i : LinearExtension S) : IsFlag (s.erase i) :=
  hs.mono (erase_subset i s) (by
    rw [← card_pos]
    have := pred_card_le_card_erase (s := s) (a := i)
    omega)

section Complex

variable [Preadditive C] [HasCoproducts.{w} C]

/-- The *flag complex* of an interval diagram `A`: in degree `p` it is the coproduct of the
`A[s₀, sₚ]` over the flags `s₀ < ⋯ < sₚ` of `S`, and its differential sends the summand of a flag
to the alternating sum `∑ₖ (-1)ᵏ` of the arrows of `A` to the flags with `sₖ` deleted
(`IntervalDiagram.flagComplexι_d`). It is the ordered Čech complex of
`IntervalDiagram.flagFunctor A`. -/
abbrev flagComplex (A : IntervalDiagram S C) : ChainComplex C ℕ :=
  A.flagFunctor.orderedCechComplex

/-- The inclusion of the summand `A[s₀, sₚ]` of a flag `s` with `p + 1` vertices in the degree `p`
term of the flag complex. -/
def flagComplexι (A : IntervalDiagram S C) {p : ℕ} {s : Finset (LinearExtension S)}
    (hs : IsFlag s) (hp : #s = p + 1) : A.obj (op (flagInterval hs)) ⟶ A.flagComplex.X p :=
  A.flagObjι hs ≫ A.flagFunctor.orderedCechComplexι ⟨s, hp⟩

/-- Morphisms out of a term of the flag complex agree when they agree on the summand of every
flag. -/
@[ext]
lemma flagComplex_hom_ext (A : IntervalDiagram S C) {p : ℕ} {Y : C}
    {f g : A.flagComplex.X p ⟶ Y}
    (h : ∀ (s : Finset (LinearExtension S)) (hs : IsFlag s) (hp : #s = p + 1),
      A.flagComplexι hs hp ≫ f = A.flagComplexι hs hp ≫ g) : f = g := by
  refine Functor.orderedCechComplex_hom_ext _ fun ⟨s, hp⟩ ↦ A.flagObj_hom_ext fun hs ↦ ?_
  simpa only [flagComplexι, Category.assoc] using h s hs hp

/-- The flag complex differential on the summand of a flag `s = {s₀ < ⋯ < sₚ₊₁}` is the
alternating sum of the arrows of `A` to the flags `s ∖ {sₖ}`, with sign `(-1)ᵏ`, where `k` is the
number of vertices of `s` below the deleted one. -/
@[reassoc]
lemma flagComplexι_d (A : IntervalDiagram S C) {p : ℕ} {s : Finset (LinearExtension S)}
    (hs : IsFlag s) (hp : #s = p + 1 + 1) :
    A.flagComplexι hs hp ≫ A.flagComplex.d (p + 1) p =
      ∑ i : s, ((-1 : ℤ) ^ #{j ∈ s | j < i.1}) •
        A.map (homOfLE (flagInterval_mono hs (hs.erase hp i.1) (erase_subset _ _))).op ≫
          A.flagComplexι (hs.erase hp i.1)
            (by rw [card_erase_of_mem i.2, hp, Nat.add_sub_cancel]) := by
  simp only [flagComplexι, Category.assoc]
  rw [Functor.ι_orderedCechComplex_d, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, flagObjι_flagObjDesc_assoc,
    flagRestrict_of_isFlag A hs _ (hs.erase hp i.1), Category.assoc]

end Complex

section Desc

variable [Preadditive C] [HasCoproducts.{w} C]

/-- The morphism out of the degree `p` term of the flag complex given on the summand of every
flag with `p + 1` vertices. -/
def flagComplexDesc (A : IntervalDiagram S C) {p : ℕ} {Y : C}
    (f : ∀ (s : Finset (LinearExtension S)) (hs : IsFlag s), #s = p + 1 →
      (A.obj (op (flagInterval hs)) ⟶ Y)) : A.flagComplex.X p ⟶ Y :=
  A.flagFunctor.orderedCechComplexDesc fun s ↦ A.flagObjDesc fun hs ↦ f s.1 hs s.2

@[reassoc (attr := simp)]
lemma flagComplexι_flagComplexDesc (A : IntervalDiagram S C) {p : ℕ} {Y : C}
    (f : ∀ (s : Finset (LinearExtension S)) (hs : IsFlag s), #s = p + 1 →
      (A.obj (op (flagInterval hs)) ⟶ Y))
    {s : Finset (LinearExtension S)} (hs : IsFlag s) (hp : #s = p + 1) :
    A.flagComplexι hs hp ≫ A.flagComplexDesc f = f s hs hp := by
  simp only [flagComplexι, flagComplexDesc, Category.assoc, Functor.ι_orderedCechComplexDesc]
  exact A.flagObjι_flagObjDesc _ hs

end Desc

section Map

variable [HasCoproducts.{w} C] [HasZeroMorphisms C] {A B E : IntervalDiagram S C}

/-- The map of the values on finite sets of vertices induced by a map of interval diagrams. -/
def flagFunctorMap (α : A ⟶ B) : A.flagFunctor ⟶ B.flagFunctor where
  app s := A.flagObjDesc fun hs ↦ α.app (op (flagInterval hs)) ≫ B.flagObjι hs
  naturality s t f := by
    ext hs
    simp only [flagObjι_flagObjDesc_assoc, Category.assoc, flagObjι_flagObjDesc]
    by_cases ht : t.unop.Nonempty
    · rw [flagRestrict_of_isFlag A hs _ (hs.mono (leOfHom f.unop) ht),
        flagRestrict_of_isFlag B hs _ (hs.mono (leOfHom f.unop) ht), Category.assoc,
        flagObjι_flagObjDesc, NatTrans.naturality_assoc]
    · simp [flagRestrict, ht]

@[reassoc (attr := simp)]
lemma flagObjι_flagFunctorMap_app (α : A ⟶ B) {s : (Finset (LinearExtension S))ᵒᵖ}
    (hs : IsFlag s.unop) :
    A.flagObjι hs ≫ (flagFunctorMap α).app s = α.app (op (flagInterval hs)) ≫ B.flagObjι hs :=
  A.flagObjι_flagObjDesc (fun hs ↦ α.app (op (flagInterval hs)) ≫ B.flagObjι hs) hs

@[simp]
lemma flagFunctorMap_id (A : IntervalDiagram S C) : flagFunctorMap (𝟙 A) = 𝟙 A.flagFunctor := by
  ext s : 2
  exact A.flagObj_hom_ext fun hs ↦ by simp

@[simp]
lemma flagFunctorMap_comp (α : A ⟶ B) (β : B ⟶ E) :
    flagFunctorMap (α ≫ β) = flagFunctorMap α ≫ flagFunctorMap β := by
  ext s : 2
  exact A.flagObj_hom_ext fun hs ↦ by simp

end Map

section ComplexMap

variable [Preadditive C] [HasCoproducts.{w} C] {A B E : IntervalDiagram S C}

/-- The chain map of flag complexes induced by a map of interval diagrams, acting summand by
summand (`IntervalDiagram.flagComplexι_flagComplexMap_f`). -/
def flagComplexMap (α : A ⟶ B) : A.flagComplex ⟶ B.flagComplex :=
  NatTrans.orderedCechComplexMap (flagFunctorMap α)

@[reassoc (attr := simp)]
lemma flagComplexι_flagComplexMap_f (α : A ⟶ B) {p : ℕ} {s : Finset (LinearExtension S)}
    (hs : IsFlag s) (hp : #s = p + 1) :
    A.flagComplexι hs hp ≫ (flagComplexMap α).f p =
      α.app (op (flagInterval hs)) ≫ B.flagComplexι hs hp := by
  simp only [flagComplexι, flagComplexMap, Category.assoc, NatTrans.ι_orderedCechComplexMap_f]
  exact flagObjι_flagFunctorMap_app_assoc α (s := op s) hs _

@[simp]
lemma flagComplexMap_id (A : IntervalDiagram S C) : flagComplexMap (𝟙 A) = 𝟙 A.flagComplex := by
  ext
  simp

@[simp]
lemma flagComplexMap_comp (α : A ⟶ B) (β : B ⟶ E) :
    flagComplexMap (α ≫ β) = flagComplexMap α ≫ flagComplexMap β := by
  ext
  simp

end ComplexMap

section Total

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteCoproducts D]
  [HasCoproducts.{w} D] {A B E : IntervalDiagram S (ChainComplex D ℕ)}

/-- The *total* of an interval diagram `A` of chain complexes (Pardon, Definition A.7.2): in degree
`n` it is the direct sum of the degree `q` terms of `A[s₀, sₚ]` over the flags `s₀ < ⋯ < sₚ` of
`S` and the degrees with `p + q = n`. It is the total complex of the flag complex, a first-quadrant
bicomplex whose column `p` collects the flags with `p + 1` vertices. -/
abbrev total (A : IntervalDiagram S (ChainComplex D ℕ)) : ChainComplex D ℕ :=
  HomologicalComplex₂.total A.flagComplex (ComplexShape.down ℕ)

/-- The chain map of totals induced by a map of interval diagrams. -/
def totalMap (α : A ⟶ B) : A.total ⟶ B.total :=
  HomologicalComplex₂.total.map (flagComplexMap α) (ComplexShape.down ℕ)

@[simp]
lemma totalMap_id (A : IntervalDiagram S (ChainComplex D ℕ)) : totalMap (𝟙 A) = 𝟙 A.total := by
  simp [totalMap]

@[simp]
lemma totalMap_comp (α : A ⟶ B) (β : B ⟶ E) :
    totalMap (α ≫ β) = totalMap α ≫ totalMap β := by
  simp [totalMap, HomologicalComplex₂.total.map_comp]

end Total

section Upper

variable [OrderTop S]

/-- The interval `[s, ⊤]` with the same lower end as `I = [s, t]`. -/
def upperInterval (I : NonemptyInterval S) : NonemptyInterval S :=
  ⟨(I.fst, ⊤), le_top⟩

@[simp]
lemma upperInterval_fst (I : NonemptyInterval S) : (upperInterval I).fst = I.fst := (rfl)

@[simp]
lemma upperInterval_snd (I : NonemptyInterval S) : (upperInterval I).snd = ⊤ := (rfl)

lemma upperInterval_mono {I J : NonemptyInterval S} (h : I ≤ J) :
    upperInterval I ≤ upperInterval J :=
  NonemptyInterval.le_def.2 ⟨(NonemptyInterval.le_def.1 h).1, le_rfl⟩

lemma le_upperInterval (I : NonemptyInterval S) : I ≤ upperInterval I :=
  NonemptyInterval.le_def.2 ⟨le_rfl, le_top⟩

lemma upperInterval_le_upperInterval_iff {I J : NonemptyInterval S} :
    upperInterval J ≤ upperInterval I ↔ I.fst ≤ J.fst := by
  simp [NonemptyInterval.le_def, upperInterval]

/-- The interval diagram `[s, t] ↦ A[s, ⊤]`, whose arrows `A[s, ⊤] ⟶ A[s', ⊤]` are those of `A`.
Its arrows between intervals with the same lower end are identities. -/
abbrev upper (A : IntervalDiagram S C) : IntervalDiagram S C where
  obj I := A.obj (op (upperInterval I.unop))
  map f := A.map (homOfLE (upperInterval_mono (leOfHom f.unop))).op
  map_id _ := (congrArg (A.map ·) (Subsingleton.elim _ _)).trans (A.map_id _)
  map_comp _ _ := (congrArg (A.map ·) (Subsingleton.elim _ _)).trans (A.map_comp _ _)

/-- The map `A[s, ⊤] ⟶ A[s, t]` from the upper extension of `A` to `A`. -/
def upperMap (A : IntervalDiagram S C) : A.upper ⟶ A where
  app I := A.map (homOfLE (le_upperInterval I.unop)).op
  naturality _ _ _ := by
    simp only [← A.map_comp]
    rfl

@[simp]
lemma upperMap_app (A : IntervalDiagram S C) (I : (NonemptyInterval S)ᵒᵖ) :
    A.upperMap.app I = A.map (homOfLE (le_upperInterval I.unop)).op := (rfl)

end Upper

section Cone

/-! ### The cone on the top vertex

For the upper extension `B = IntervalDiagram.upper A` of an interval diagram, adjoining the top
vertex `⊤` to a flag `σ` does not change `B[σ₀, σₚ] = A[σ₀, ⊤]`. So the maps `σ ↦ ± (σ ∪ {⊤})` form
a contracting homotopy of the flag complex of `B` onto its summand `B[⊤, ⊤] = A[⊤, ⊤]`, the cone
with vertex `⊤`. All the coefficients are arrows `A[s, ⊤] ⟶ A[s', ⊤]` of `A`, and any two such
arrows with the same source and target agree. -/

variable [Preadditive C] [HasCoproducts.{w} C] [OrderTop S] (A : IntervalDiagram S C)

/-- The top vertex, as an element of the linear extension. -/
private abbrev topVertex : LinearExtension S := toLinearExtension (⊤ : S)

private lemma isFlag_insert_topVertex {σ : Finset (LinearExtension S)}
    (hσ : ∀ a ∈ σ, ∀ b ∈ σ, ofLinearExtension a ≤ ofLinearExtension b ∨
      ofLinearExtension b ≤ ofLinearExtension a) :
    IsFlag (insert (topVertex (S := S)) σ) where
  nonempty := insert_nonempty _ _
  total a ha b hb := by
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Or.inl le_rfl
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)
    · exact hσ a ha b hb

private lemma IsFlag.insert_topVertex {σ : Finset (LinearExtension S)} (hσ : IsFlag σ) :
    IsFlag (insert topVertex σ) :=
  isFlag_insert_topVertex hσ.total

private lemma IsFlag.insert_topVertex_erase {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (k : LinearExtension S) : IsFlag (insert topVertex (σ.erase k)) :=
  isFlag_insert_topVertex fun a ha b hb ↦
    hσ.total a (mem_of_mem_erase ha) b (mem_of_mem_erase hb)

/-- Adjoining `⊤` to a flag does not lower the least vertex. -/
private lemma upper_le_of_subset_insert {σ τ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hτ : IsFlag τ) (h : τ ⊆ insert topVertex σ) :
    upperInterval (flagInterval hτ) ≤ upperInterval (flagInterval hσ) := by
  rw [upperInterval_le_upperInterval_iff, flagInterval_fst, flagInterval_fst]
  rcases mem_insert.1 (h (τ.min'_mem hτ.nonempty)) with hm | hm
  · simp [hm]
  · exact hσ.min'_le hm

/-- The arrow `A[s, ⊤] ⟶ A[s', ⊤]` of the upper extension for `s ≤ s'`. -/
private def coef {I J : NonemptyInterval S} (h : upperInterval J ≤ upperInterval I) :
    A.upper.obj (op I) ⟶ A.upper.obj (op J) :=
  A.map (homOfLE h).op

omit [Preadditive C] [HasCoproducts.{w} C] in
@[reassoc]
private lemma coef_comp {I J K : NonemptyInterval S} (h : upperInterval J ≤ upperInterval I)
    (h' : upperInterval K ≤ upperInterval J) :
    coef A h ≫ coef A h' = coef A (h'.trans h) := by
  rw [coef, coef, coef, ← A.map_comp]
  rfl

omit [Preadditive C] [HasCoproducts.{w} C] in
private lemma upper_map_eq_coef {I J : NonemptyInterval S} (h : J ≤ I) :
    A.upper.map (homOfLE h).op = coef A (upperInterval_mono h) := (rfl)

omit [Preadditive C] [HasCoproducts.{w} C] in
private lemma coef_refl {I : NonemptyInterval S} (h : upperInterval I ≤ upperInterval I) :
    coef A h = 𝟙 _ :=
  (congrArg (A.map ·) (Subsingleton.elim _ _)).trans (A.map_id _)

/-- The summand inclusion of a flag in degree `p`, or zero if the flag does not have `p + 1`
vertices. -/
private def single (p : ℕ) {σ : Finset (LinearExtension S)} (hσ : IsFlag σ) :
    A.upper.obj (op (flagInterval hσ)) ⟶ A.upper.flagComplex.X p :=
  if hp : #σ = p + 1 then A.upper.flagComplexι hσ hp else 0

private lemma single_of_card_eq {p : ℕ} {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = p + 1) : single A p hσ = A.upper.flagComplexι hσ hp := by
  simp [single, hp]

private lemma single_of_card_ne {p : ℕ} {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ ≠ p + 1) : single A p hσ = 0 := by
  simp [single, hp]

private lemma coef_single_congr {p : ℕ} {I : NonemptyInterval S}
    {σ τ : Finset (LinearExtension S)} (hσ : IsFlag σ) (hτ : IsFlag τ) (e : σ = τ)
    (h : upperInterval (flagInterval hσ) ≤ upperInterval I)
    (h' : upperInterval (flagInterval hτ) ≤ upperInterval I) :
    coef A h ≫ single A p hσ = coef A h' ≫ single A p hτ := by
  subst e
  rfl

private lemma hom_ext {p : ℕ} {Y : C} {f g : A.upper.flagComplex.X p ⟶ Y}
    (h : ∀ (σ : Finset (LinearExtension S)) (hσ : IsFlag σ), #σ = p + 1 →
      single A p hσ ≫ f = single A p hσ ≫ g) : f = g :=
  flagComplex_hom_ext A.upper fun σ hσ hp ↦ by
    simpa only [single_of_card_eq A hσ hp] using h σ hσ hp

private lemma single_d {p : ℕ} {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = p + 1 + 1) :
    single A (p + 1) hσ ≫ A.upper.flagComplex.d (p + 1) p =
      ∑ i ∈ σ, ((-1 : ℤ) ^ #{j ∈ σ | j < i}) •
        (coef A (upper_le_of_subset_insert hσ (hσ.erase hp i)
            ((erase_subset _ _).trans (subset_insert _ _))) ≫ single A p (hσ.erase hp i)) := by
  rw [single_of_card_eq A hσ hp, flagComplexι_d, ← sum_coe_sort σ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [single_of_card_eq A _ (by rw [card_erase_of_mem i.2, hp, Nat.add_sub_cancel])]
  rfl

/-- The components of the contracting homotopy: the summand of `σ` goes to `± (σ ∪ {⊤})`. -/
private def homotopy (p j : ℕ) : A.upper.flagComplex.X p ⟶ A.upper.flagComplex.X j :=
  A.upper.flagComplexDesc fun σ hσ _ ↦ ((-1 : ℤ) ^ #{k ∈ σ | k < topVertex}) •
    (coef A (upper_le_of_subset_insert hσ hσ.insert_topVertex subset_rfl) ≫
      single A j hσ.insert_topVertex)

private lemma single_homotopy {p : ℕ} (j : ℕ) {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = p + 1) :
    single A p hσ ≫ homotopy A p j = ((-1 : ℤ) ^ #{k ∈ σ | k < topVertex}) •
      (coef A (upper_le_of_subset_insert hσ hσ.insert_topVertex subset_rfl) ≫
        single A j hσ.insert_topVertex) := by
  rw [single_of_card_eq A hσ hp, homotopy, flagComplexι_flagComplexDesc]

/-- The sum `∑ₖ ± ((σ ∖ {σₖ}) ∪ {⊤})`, which is both the homotopy after the differential on `σ` and
the remainder of the differential after the homotopy. -/
private def coneFace (p : ℕ) {σ : Finset (LinearExtension S)} (hσ : IsFlag σ) :
    A.upper.obj (op (flagInterval hσ)) ⟶ A.upper.flagComplex.X p :=
  ∑ k ∈ σ, ((-1 : ℤ) ^ #{j ∈ σ | j < k} * (-1) ^ #{j ∈ σ.erase k | j < topVertex}) •
    (coef A (upper_le_of_subset_insert hσ (hσ.insert_topVertex_erase k)
        (insert_subset_insert _ (erase_subset _ _))) ≫
      single A p (hσ.insert_topVertex_erase k))

private lemma single_homotopy_d_of_notMem {p : ℕ} {σ : Finset (LinearExtension S)}
    (hσ : IsFlag σ) (hp : #σ = p + 1) (hc : topVertex ∉ σ) :
    single A p hσ ≫ homotopy A p (p + 1) ≫ A.upper.flagComplex.d (p + 1) p =
      single A p hσ - coneFace A p hσ := by
  rw [← Category.assoc, single_homotopy A _ hσ hp, Preadditive.zsmul_comp, Category.assoc,
    single_d A hσ.insert_topVertex (by rw [card_insert_of_notMem hc, hp]), sum_insert hc,
    Preadditive.comp_add, smul_add, coneFace, sub_eq_add_neg, ← sum_neg_distrib,
    Preadditive.comp_sum, Finset.smul_sum, Preadditive.comp_zsmul, coef_comp_assoc,
    coef_single_congr A _ hσ (erase_insert hc) _ (le_refl _), coef_refl, Category.id_comp,
    smul_smul, filter_insert]
  simp only [lt_irrefl, ↓reduceIte]
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hck : topVertex ≠ k := fun h ↦ hc (h ▸ hk)
  rw [Preadditive.comp_zsmul, coef_comp_assoc, smul_smul,
    neg_one_pow_card_filter_lt_mul_insert hc hk, neg_smul,
    coef_single_congr A _ (hσ.insert_topVertex_erase k) (erase_insert_of_ne hck)]

private lemma single_homotopy_of_mem {p : ℕ} {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = p + 1) (hc : topVertex ∈ σ) : single A p hσ ≫ homotopy A p (p + 1) = 0 := by
  rw [single_homotopy A _ hσ hp,
    single_of_card_ne A _ (by rw [insert_eq_of_mem hc, hp]; omega), comp_zero, smul_zero]

private lemma single_d_homotopy {p : ℕ} {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = p + 1 + 1) :
    single A (p + 1) hσ ≫ A.upper.flagComplex.d (p + 1) p ≫ homotopy A p (p + 1) =
      coneFace A (p + 1) hσ := by
  rw [← Category.assoc, single_d A hσ hp, Preadditive.sum_comp, coneFace]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Preadditive.zsmul_comp, Category.assoc,
    single_homotopy A _ _ (by rw [card_erase_of_mem hk, hp]; rfl), Preadditive.comp_zsmul,
    coef_comp_assoc, smul_smul]

private lemma coneFace_of_mem {p : ℕ} {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = p + 1) (hc : topVertex ∈ σ) : coneFace A p hσ = single A p hσ := by
  rw [coneFace, sum_eq_single topVertex]
  · rw [coef_single_congr A _ hσ (insert_erase hc) _ (le_refl _), coef_refl, Category.id_comp,
      filter_erase, erase_eq_of_notMem (by simp), ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul]
  · intro k hk hkc
    rw [single_of_card_ne A _ (by
      rw [insert_eq_of_mem (mem_erase.2 ⟨Ne.symm hkc, hc⟩), card_erase_of_mem hk, hp]; omega),
      comp_zero, smul_zero]
  · exact fun h ↦ (h hc).elim

/-- On a pair of vertices the signs `(-1)ᵏ` of the two deletions cancel. -/
private lemma sum_neg_one_pow_card_filter_lt_of_card_eq_two {α : Type*} [LinearOrder α]
    {σ : Finset α} (h : #σ = 0 + 1 + 1) : ∑ i ∈ σ, (-1 : ℤ) ^ #{j ∈ σ | j < i} = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 h
  rw [sum_pair hab]
  rcases hab.lt_or_gt with h | h
  · simp [filter_insert, filter_singleton, h, h.not_gt]
  · simp [filter_insert, filter_singleton, h, h.not_gt]

private lemma coneFace_zero {σ : Finset (LinearExtension S)} (hσ : IsFlag σ) (hp : #σ = 0 + 1) :
    coneFace A 0 hσ = coef A (upper_le_of_subset_insert hσ (IsFlag.singleton topVertex)
      (singleton_subset_iff.2 (mem_insert_self _ _))) ≫
        single A 0 (IsFlag.singleton topVertex) := by
  obtain ⟨a, rfl⟩ := card_eq_one.1 hp
  rw [coneFace, sum_singleton, coef_single_congr A (hσ.insert_topVertex_erase a)
    (IsFlag.singleton topVertex) (by rw [erase_singleton, insert_empty]) _
    (upper_le_of_subset_insert hσ (IsFlag.singleton topVertex)
      (singleton_subset_iff.2 (mem_insert_self _ _)))]
  simp [filter_singleton]

/-- The value `A[⊤, ⊤]` of the upper extension at the top interval. -/
private abbrev topObj : C := A.upper.obj (op (NonemptyInterval.pure ⊤))

private lemma upper_pure_top_le (I : NonemptyInterval S) :
    upperInterval (NonemptyInterval.pure (⊤ : S)) ≤ upperInterval I :=
  upperInterval_le_upperInterval_iff.2 le_top

private lemma upper_flagInterval_topVertex_le :
    upperInterval (flagInterval (IsFlag.singleton (topVertex (S := S)))) ≤
      upperInterval (NonemptyInterval.pure ⊤) :=
  upperInterval_le_upperInterval_iff.2 (by simp)

/-- The augmentation in degree `0`: the summand `A[s, ⊤]` of a vertex `s` goes to `A[⊤, ⊤]`. -/
private def augmentationX : A.upper.flagComplex.X 0 ⟶ topObj A :=
  A.upper.flagComplexDesc fun _ hσ _ ↦ coef A (upper_pure_top_le (flagInterval hσ))

private lemma single_augmentationX {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = 0 + 1) :
    single A 0 hσ ≫ augmentationX A = coef A (upper_pure_top_le (flagInterval hσ)) := by
  rw [single_of_card_eq A hσ hp, augmentationX, flagComplexι_flagComplexDesc]

private lemma d_augmentationX : A.upper.flagComplex.d 1 0 ≫ augmentationX A = 0 := by
  refine hom_ext A fun σ hσ hp ↦ ?_
  rw [comp_zero, ← Category.assoc, single_d A hσ hp, Preadditive.sum_comp]
  have h := sum_neg_one_pow_card_filter_lt_of_card_eq_two hp
  calc _ = ∑ i ∈ σ, ((-1 : ℤ) ^ #{j ∈ σ | j < i}) •
        coef A (upper_pure_top_le (flagInterval hσ)) := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Preadditive.zsmul_comp, Category.assoc,
          single_augmentationX A _ (by rw [card_erase_of_mem hi, hp]), coef_comp]
    _ = 0 := by rw [← Finset.sum_smul, h, zero_smul]

variable [HasZeroObject C]

/-- The augmentation of the flag complex of the upper extension onto `A[⊤, ⊤]`, placed in
degree `0`. -/
private def augmentation : A.upper.flagComplex ⟶ (ChainComplex.single₀ C).obj (topObj A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentationX A, d_augmentationX A⟩

/-- The section of the augmentation: `A[⊤, ⊤]` goes to the summand of the vertex `⊤`. -/
private def section_ : (ChainComplex.single₀ C).obj (topObj A) ⟶ A.upper.flagComplex :=
  (ChainComplex.fromSingle₀Equiv _ _).symm
    (coef A upper_flagInterval_topVertex_le ≫ single A 0 (IsFlag.singleton topVertex))

private lemma single_augmentation_f_zero {σ : Finset (LinearExtension S)} (hσ : IsFlag σ)
    (hp : #σ = 0 + 1) :
    single A 0 hσ ≫ (augmentation A).f 0 ≫ (HomologicalComplex.singleObjXSelf _ 0 _).hom =
      coef A (upper_pure_top_le (flagInterval hσ)) := by
  rw [← single_augmentationX A hσ hp]
  simp [augmentation]

private lemma ι_section_f_zero :
    (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ (section_ A).f 0 =
      coef A upper_flagInterval_topVertex_le ≫ single A 0 (IsFlag.singleton topVertex) := by
  simp [section_]

private lemma section_comp_augmentation : section_ A ≫ augmentation A = 𝟙 _ := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [← cancel_epi (HomologicalComplex.singleObjXSelf _ 0 _).inv,
    ← cancel_mono (HomologicalComplex.singleObjXSelf _ 0 _).hom, HomologicalComplex.comp_f,
    Category.assoc, Category.assoc, reassoc_of% ι_section_f_zero, Category.assoc,
    single_augmentation_f_zero A _ (card_singleton _), coef_comp, coef_refl,
    HomologicalComplex.id_f, Category.id_comp, Iso.inv_hom_id]

private lemma id_sub_augmentation_comp_section :
    𝟙 _ - augmentation A ≫ section_ A =
      Homotopy.nullHomotopicMap' fun i j (_ : (ComplexShape.down ℕ).Rel j i) ↦ homotopy A i j := by
  ext (_ | p) : 1
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (ComplexShape.down_mk 1 0 rfl)
      (fun l h ↦ by simp at h)]
    refine hom_ext A fun σ hσ hp ↦ ?_
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      Preadditive.comp_sub, Category.comp_id,
      ← Iso.hom_inv_id_assoc (HomologicalComplex.singleObjXSelf _ 0 _) ((section_ A).f 0),
      reassoc_of% single_augmentation_f_zero A hσ hp, ι_section_f_zero, coef_comp_assoc,
      ← coneFace_zero A hσ hp]
    by_cases hc : topVertex ∈ σ
    · rw [coneFace_of_mem A hσ hp hc, sub_self, ← Category.assoc,
        single_homotopy_of_mem A hσ hp hc, zero_comp]
    · rw [single_homotopy_d_of_notMem A hσ hp hc]
  · rw [Homotopy.nullHomotopicMap'_f (ComplexShape.down_mk (p + 2) (p + 1) rfl)
      (ComplexShape.down_mk (p + 1) p rfl)]
    refine hom_ext A fun σ hσ hp ↦ ?_
    simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, HomologicalComplex.comp_f,
      section_, ChainComplex.fromSingle₀Equiv_symm_apply_f_succ, comp_zero, sub_zero,
      Category.comp_id, Preadditive.comp_add, single_d_homotopy A hσ hp]
    by_cases hc : topVertex ∈ σ
    · rw [coneFace_of_mem A hσ hp hc, ← Category.assoc, single_homotopy_of_mem A hσ hp hc,
        zero_comp, add_zero]
    · rw [single_homotopy_d_of_notMem A hσ hp hc, add_sub_cancel]

/-- The flag complex of the upper extension of an interval diagram is chain homotopy equivalent to
its value `A[⊤, ⊤]` on the top interval, placed in degree `0`. -/
private def upperHomotopyEquiv :
    HomotopyEquiv A.upper.flagComplex ((ChainComplex.single₀ C).obj (topObj A)) where
  hom := augmentation A
  inv := section_ A
  homotopyHomInvId := (Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (id_sub_augmentation_comp_section A)).trans
      (Homotopy.nullHomotopy' _))).symm
  homotopyInvHomId := Homotopy.ofEq (section_comp_augmentation A)

end Cone


section Top

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteCoproducts D]
  [HasCoproducts.{w} D] [OrderTop S]

lemma flagInterval_singleton_top :
    flagInterval (IsFlag.singleton (toLinearExtension (⊤ : S))) = NonemptyInterval.pure ⊤ := by
  simp

/-- The inclusion of `A[⊤, ⊤]` as the summand of the one-vertex flag `⊤` in the column `0` of the
flag complex. -/
private def topFlagι (A : IntervalDiagram S (ChainComplex D ℕ)) :
    A.obj (op (NonemptyInterval.pure ⊤)) ⟶ A.flagComplex.X 0 :=
  A.map (homOfLE flagInterval_singleton_top.le).op ≫
    A.flagComplexι (IsFlag.singleton (toLinearExtension (⊤ : S))) (card_singleton _)

/-- The inclusion of `A[⊤, ⊤]` in the total of an interval diagram on a poset with a greatest
element, as the summand of the one-vertex flag `⊤`. -/
def topι (A : IntervalDiagram S (ChainComplex D ℕ)) :
    A.obj (op (NonemptyInterval.pure ⊤)) ⟶ A.total where
  f q := (topFlagι A).f q ≫
    HomologicalComplex₂.ιTotal A.flagComplex (ComplexShape.down ℕ) 0 q q (zero_add q)
  comm' := by
    rintro _ q rfl
    rw [Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), zero_add,
      HomologicalComplex₂.d₂_eq _ _ 0 (ComplexShape.down_mk _ _ rfl) q (by simp),
      ← Category.assoc, ← (topFlagι A).comm]
    simp

lemma topι_f (A : IntervalDiagram S (ChainComplex D ℕ)) (q : ℕ) :
    A.topι.f q = (A.map (homOfLE flagInterval_singleton_top.le).op ≫
      A.flagComplexι (IsFlag.singleton (toLinearExtension (⊤ : S))) (card_singleton _)).f q ≫
        HomologicalComplex₂.ιTotal A.flagComplex (ComplexShape.down ℕ) 0 q q (zero_add q) :=
  (rfl)

end Top

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D] [HasCoproducts.{w} D] [Finite S]
  {A B : IntervalDiagram S (ChainComplex D ℕ)}

/-- A map of interval diagrams which is a quasi-isomorphism on every interval is a
quasi-isomorphism on every column of the flag complexes. -/
lemma quasiIso_flagComplexMap_f (α : A ⟶ B) [∀ I, QuasiIso (α.app I)] (p : ℕ) :
    QuasiIso ((flagComplexMap α).f p) := by
  have : Fintype (LinearExtension S) := @Fintype.ofFinite S _
  have (s : Finset (LinearExtension S)) : QuasiIso ((flagFunctorMap α).app (op s)) :=
    HomologicalComplex.quasiIso_of_isColimit_cofan (coproductIsCoproduct _)
      (coproductIsCoproduct _) (fun h : ULift.{w} (PLift (IsFlag s)) ↦
        α.app (op (flagInterval h.down.down))) _
      fun h ↦ flagObjι_flagFunctorMap_app α (s := op s) h.down.down
  exact HomologicalComplex.quasiIso_of_isColimit_cofan
    (A.flagFunctor.isColimitOrderedCechComplexCofan p)
    (B.flagFunctor.isColimitOrderedCechComplexCofan p)
    (fun s : {s : Finset (LinearExtension S) // #s = p + 1} ↦ (flagFunctorMap α).app (op s.1)) _
    fun s ↦ NatTrans.ι_orderedCechComplexMap_f (flagFunctorMap α) s

/-- **A map of interval diagrams which is a quasi-isomorphism on every interval induces a
quasi-isomorphism of totals** (Pardon, Lemma A.7.4). -/
theorem quasiIso_totalMap (α : A ⟶ B) [∀ I, QuasiIso (α.app I)] : QuasiIso (totalMap α) := by
  -- The rows of the flipped bicomplexes are the columns of the flag complexes.
  let ψ : HomologicalComplex₂.flip A.flagComplex ⟶ HomologicalComplex₂.flip B.flagComplex :=
    (HomologicalComplex₂.flipFunctor D _ _).map (flagComplexMap α)
  have hψ : QuasiIso (HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ)) :=
    HomologicalComplex₂.quasiIso_total_map_of_rows ψ fun q ↦ quasiIso_flagComplexMap_f α q
  have hcomm :
      (HomologicalComplex₂.totalFlipIso A.flagComplex (ComplexShape.down ℕ)).hom ≫ totalMap α =
        HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ) ≫
          (HomologicalComplex₂.totalFlipIso B.flagComplex (ComplexShape.down ℕ)).hom := by
    ext n q p h
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc, HomologicalComplex₂.ιTotal_map_assoc,
      HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
    simp only [totalMap]
    -- `HomologicalComplex₂.ιTotal_totalFlipIso_f_hom` states the sign with types that agree with
    -- the goal only up to unfolding the total complex, so the sign is moved with `erw`.
    erw [Linear.units_smul_comp, HomologicalComplex₂.ιTotal_map, Linear.comp_units_smul]
    rfl
  rw [← quasiIso_iff_comp_left
      (HomologicalComplex₂.totalFlipIso A.flagComplex (ComplexShape.down ℕ)).hom, hcomm]
  infer_instance

section Top

variable [OrderTop S]

omit [Finite S] in
private lemma upper_topι_comp_totalMap_upperMap (A : IntervalDiagram S (ChainComplex D ℕ)) :
    A.upper.topι ≫ totalMap A.upperMap = A.topι := by
  ext q : 1
  rw [HomologicalComplex.comp_f, topι_f, topι_f, Category.assoc, totalMap,
    HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← HomologicalComplex.comp_f,
    Category.assoc, flagComplexι_flagComplexMap_f, upperMap_app, ← Category.assoc, ← A.map_comp]
  rfl

omit [Finite S] in
private lemma quasiIso_upper_topι (A : IntervalDiagram S (ChainComplex D ℕ)) :
    QuasiIso A.upper.topι := by
  let e := upperHomotopyEquiv A
  have he : e.hom = augmentation A := rfl
  have hT := HomologicalComplex₂.quasiIso_totalAugmentation_of_rows e.hom fun q ↦
    ((HomologicalComplex.eval D (ComplexShape.down ℕ) q).mapHomotopyEquiv e).quasiIso_hom
  have hid : A.upper.topι ≫ HomologicalComplex₂.totalAugmentation A.upper.flagComplex _
      (HomologicalComplex₂.d_comp_f_zero_singleObjXSelf_hom _ e.hom) = 𝟙 _ := by
    ext q : 1
    rw [HomologicalComplex.comp_f, topι_f, Category.assoc,
      HomologicalComplex₂.ιTotal_totalAugmentation_f_zero, ← HomologicalComplex.comp_f]
    congr 1
    rw [Category.assoc, ← single_of_card_eq A _ (card_singleton _), he,
      single_augmentation_f_zero A _ (card_singleton _), upper_map_eq_coef, coef_comp, coef_refl]
  rw [← quasiIso_iff_comp_right _ (HomologicalComplex₂.totalAugmentation A.upper.flagComplex _
    (HomologicalComplex₂.d_comp_f_zero_singleObjXSelf_hom _ e.hom)), hid]
  infer_instance

/-- **The top value of an interval diagram computes its total** (Pardon, Lemma A.7.3). Let `S` be a
finite poset with a greatest element `⊤`, and let `A` be an interval diagram of chain complexes on
`S` whose arrows `A[s, t] ⟶ A[s, t']` shrinking an interval at its upper end are
quasi-isomorphisms. Then the inclusion of `A[⊤, ⊤]` in the total of `A` is a quasi-isomorphism. -/
theorem quasiIso_topι (A : IntervalDiagram S (ChainComplex D ℕ))
    (hA : ∀ ⦃I J : NonemptyInterval S⦄ (h : I ≤ J), I.fst = J.fst →
      QuasiIso (A.map (homOfLE h).op)) : QuasiIso A.topι := by
  have (I : (NonemptyInterval S)ᵒᵖ) : QuasiIso (A.upperMap.app I) :=
    hA (le_upperInterval I.unop) rfl
  have := quasiIso_totalMap A.upperMap
  have hc : QuasiIso (A.upper.topι ≫ totalMap A.upperMap) := by
    rw [quasiIso_iff_comp_right]
    exact quasiIso_upper_topι A
  exact upper_topι_comp_totalMap_upperMap A ▸ hc

end Top

end Abelian

end IntervalDiagram

end TauCeti
