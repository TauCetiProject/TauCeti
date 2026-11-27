/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.Algebra.Homology.OrderedCech.Cone
public import TauCeti.Algebra.Homology.TotalComplex.Additive
public import TauCeti.Algebra.Homology.TotalComplex.Basic
public import TauCeti.Order.Extension.Linear

/-!
# Interval diagrams and their flag totals

Let `S` be a partially ordered set. An *interval diagram* `A` on `S` (`TauCeti.IntervalDiagram`)
assigns an object `A[s, t]` to every interval `s ≤ t` of `S`, and an arrow `A[s, t] ⟶ A[s', t']`
to every inclusion `s ≤ s' ≤ t' ≤ t` of intervals, functorially. A *flag* of `S` is a chain
`s₀ < ⋯ < sₚ`; it spans the interval `[s₀, sₚ]`. For an interval diagram of chain complexes the
*total* (Pardon, Definition A.7.2) is the complex

`Tot A = ⨁ₚ ⨁_{s₀ < ⋯ < sₚ} A[s₀, sₚ][p]`

whose differential is the alternating sum `∑ₖ (-1)ᵏ` of the arrows of `A` to the flags with `sₖ`
deleted plus `(-1)ᵖ` times the internal differential, following the sign convention of Mathlib's
total complexes. Implicit atlases glue local virtual chain complexes with
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
  result. In the upper extension, adjoining `⊤` to a flag does not change its value, so its flag
  complex is the ordered Čech complex of a cone with vertex `⊤`, and `σ ↦ ± (σ ∪ {⊤})` contracts
  every row of its flag bicomplex onto `A[⊤, ⊤]`
  (`CategoryTheory.Functor.orderedCechHomotopyEquivOfVertex`).

## Main definitions

* `TauCeti.IntervalDiagram S C`: interval diagrams on `S` with values in `C`.
* `TauCeti.IntervalDiagram.IsFlag`, `TauCeti.IntervalDiagram.flagInterval`: flags and the
  intervals they span.
* `TauCeti.IntervalDiagram.flagComplex`, `TauCeti.IntervalDiagram.flagComplexι`: the flag complex
  and its summand inclusions.
* `TauCeti.IntervalDiagram.total`, `TauCeti.IntervalDiagram.totalMap`: the total and the maps
  induced on it by maps of interval diagrams, together the functor
  `TauCeti.IntervalDiagram.totalFunctor`.
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

/-- The least vertex of a flag is below each of its vertices in the order of `S`. -/
lemma min'_le (hs : IsFlag s) {a : LinearExtension S} (ha : a ∈ s) :
    ofLinearExtension (s.min' hs.nonempty) ≤ ofLinearExtension a :=
  (hs.le_iff (s.min'_mem hs.nonempty) ha).1 (s.min'_le a ha)

/-- The greatest vertex of a flag is above each of its vertices in the order of `S`. -/
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

/-- On a flag `s` the summand inclusion `A[s₀, sₚ] ⟶ IntervalDiagram.flagObj A s` is an
isomorphism, as the coproduct is indexed by the proofs that `s` is a flag. -/
instance isIso_flagObjι (A : IntervalDiagram S C) {s : Finset (LinearExtension S)}
    (hs : IsFlag s) : IsIso (A.flagObjι hs) :=
  ⟨A.flagObjDesc (Y := A.obj (op (flagInterval hs))) fun _ ↦ 𝟙 _, by simp, by
    ext hs'
    rw [flagObjι_flagObjDesc_assoc, Category.id_comp, Category.comp_id]⟩

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
    simp [flagRestrict_of_isFlag A hs _ hs]
  map_comp {X Y Z} f g := by
    ext hs
    rw [flagObjι_flagObjDesc, flagObjι_flagObjDesc_assoc]
    by_cases hu : Z.unop.Nonempty
    · have hZY : Z.unop ⊆ Y.unop := leOfHom g.unop
      have hYX : Y.unop ⊆ X.unop := leOfHom f.unop
      have hmid := hs.mono hYX (hu.mono hZY)
      rw [flagRestrict_of_isFlag A hs _ (hs.mono (hZY.trans hYX) hu),
        flagRestrict_of_isFlag A hs _ hmid, Category.assoc, flagObjι_flagObjDesc,
        flagRestrict_of_isFlag A hmid _ (hmid.mono hZY hu), ← Category.assoc, ← A.map_comp,
        ← op_comp, homOfLE_comp]
    · simp [flagRestrict, hu]

end Flags

/-- A flag with at least two vertices stays a flag when one vertex is deleted. -/
lemma IsFlag.erase {s : Finset (LinearExtension S)} (hs : IsFlag s) (hs₂ : 1 < #s)
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
      ∑ i : s, ((-1 : ℤ) ^ #{j ∈ s | j < i.val}) •
        A.map (homOfLE (flagInterval_mono hs (hs.erase (by omega) i.val) (erase_subset _ _))).op ≫
          A.flagComplexι (hs.erase (by omega) i.val)
            (by rw [card_erase_of_mem i.property, hp, Nat.add_sub_cancel]) := by
  simp only [flagComplexι, Category.assoc]
  rw [Functor.ι_orderedCechComplex_d, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, flagObjι_flagObjDesc_assoc,
    flagRestrict_of_isFlag A hs _ (hs.erase (by omega) i.val), Category.assoc]

end Complex

section Desc

variable [Preadditive C] [HasCoproducts.{w} C]

/-- The morphism out of the degree `p` term of the flag complex given on the summand of every
flag with `p + 1` vertices. -/
def flagComplexDesc (A : IntervalDiagram S C) {p : ℕ} {Y : C}
    (f : ∀ (s : Finset (LinearExtension S)) (hs : IsFlag s), #s = p + 1 →
      (A.obj (op (flagInterval hs)) ⟶ Y)) : A.flagComplex.X p ⟶ Y :=
  A.flagFunctor.orderedCechComplexDesc fun s ↦ A.flagObjDesc fun hs ↦ f s.val hs s.property

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

@[simp]
lemma flagComplexMap_zero : flagComplexMap (0 : A ⟶ B) = 0 := by
  ext
  simp

end ComplexMap

section Total

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteCoproducts D]
  [HasCoproducts.{w} D] {A B E : IntervalDiagram S (ChainComplex D ℕ)}

/-- The *total* of an interval diagram `A` of chain complexes (Pardon, Definition A.7.2): in degree
`n` it is the direct sum of the degree `q` terms of `A[s₀, sₚ]` over the flags `s₀ < ⋯ < sₚ` of
`S` and the degrees with `p + q = n`. It is the total complex of the flag complex, a first-quadrant
bicomplex whose column `p` collects the flags with `p + 1` vertices, so on column `p` the
differential is the alternating deletion sum plus `(-1)ᵖ` times the internal differential. -/
abbrev total (A : IntervalDiagram S (ChainComplex D ℕ)) : ChainComplex D ℕ :=
  HomologicalComplex₂.total A.flagComplex (ComplexShape.down ℕ)

/-- The chain map of totals induced by a map of interval diagrams. -/
def totalMap (α : A ⟶ B) : A.total ⟶ B.total :=
  HomologicalComplex₂.total.map (flagComplexMap α) (ComplexShape.down ℕ)

/-- The chain map of totals induced by `α` acts on the summand of each flag and degree by the
component of `α`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalMap (α : A ⟶ B) (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) =
      n) :
    HomologicalComplex₂.ιTotal A.flagComplex (ComplexShape.down ℕ) p q n h ≫ (totalMap α).f n =
      ((flagComplexMap α).f p).f q ≫
        HomologicalComplex₂.ιTotal B.flagComplex (ComplexShape.down ℕ) p q n h := by
  rw [totalMap, HomologicalComplex₂.ιTotal_map]

@[simp]
lemma totalMap_id (A : IntervalDiagram S (ChainComplex D ℕ)) : totalMap (𝟙 A) = 𝟙 A.total := by
  simp [totalMap]

@[simp]
lemma totalMap_comp (α : A ⟶ B) (β : B ⟶ E) :
    totalMap (α ≫ β) = totalMap α ≫ totalMap β := by
  simp [totalMap, HomologicalComplex₂.total.map_comp]

@[simp]
lemma totalMap_zero : totalMap (0 : A ⟶ B) = 0 := by
  rw [totalMap, flagComplexMap_zero, HomologicalComplex₂.total.map_zero]

variable (S D) in
/-- **The total of interval diagrams of chain complexes, as a functor**: an interval diagram goes
to its total (`IntervalDiagram.total`), and a map of interval diagrams to the induced chain map of
totals (`IntervalDiagram.totalMap`). Applied to a diagram of presheaves of chain complexes, after
`CategoryTheory.Functor.flip`, it forms the totals pointwise. -/
-- The body is exposed so that its values and maps are definitionally the totals and the maps of
-- totals (`totalFunctor_obj`, `totalFunctor_map`).
@[expose, simps]
def totalFunctor : IntervalDiagram S (ChainComplex D ℕ) ⥤ ChainComplex D ℕ where
  obj := total
  map := totalMap

instance : (totalFunctor S D).PreservesZeroMorphisms where
  map_zero _ _ := totalMap_zero

/-- The total of an interval diagram whose values are all zero is zero. -/
lemma isZero_total (h : ∀ I, IsZero (A.obj I)) : IsZero A.total :=
  (totalFunctor S D).map_isZero (Functor.isZero A h)

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
  map_id _ := by simp
  map_comp _ _ := by rw [← A.map_comp, ← op_comp, homOfLE_comp]

/-- The map `A[s, ⊤] ⟶ A[s, t]` from the upper extension of `A` to `A`. -/
def upperMap (A : IntervalDiagram S C) : A.upper ⟶ A where
  app I := A.map (homOfLE (le_upperInterval I.unop)).op
  naturality _ _ _ := by
    simp only [← A.map_comp]
    -- Morphisms in the poset of intervals are unique, so `congr 1` closes the goal.
    congr 1

@[simp]
lemma upperMap_app (A : IntervalDiagram S C) (I : (NonemptyInterval S)ᵒᵖ) :
    A.upperMap.app I = A.map (homOfLE (le_upperInterval I.unop)).op := (rfl)

end Upper

section Cone

/-! ### The cone on the top vertex

For the upper extension `B = IntervalDiagram.upper A` of an interval diagram, adjoining the top
vertex `⊤` to a flag `σ` does not change `B[σ₀, σₚ] = A[σ₀, ⊤]`. So the flag complex of `B` is the
ordered Čech complex of a cone with vertex `⊤`, which is chain homotopy equivalent to its value on
the one-vertex flag `⊤` (`CategoryTheory.Functor.orderedCechHomotopyEquivOfVertex`). -/

variable [Preadditive C] [HasCoproducts.{w} C] [OrderTop S] (A : IntervalDiagram S C)

/-- The top vertex, as an element of the linear extension. -/
private abbrev topVertex : LinearExtension S := toLinearExtension (⊤ : S)

private lemma IsFlag.insert_topVertex {σ : Finset (LinearExtension S)} (hσ : IsFlag σ) :
    IsFlag (insert (topVertex (S := S)) σ) where
  nonempty := insert_nonempty _ _
  total a ha b hb := by
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Or.inl le_rfl
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)
    · exact hσ.total a ha b hb

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
  rw [coef, coef, coef, ← A.map_comp, ← op_comp, homOfLE_comp]

omit [Preadditive C] [HasCoproducts.{w} C] in
private lemma upper_map_eq_coef {I J : NonemptyInterval S} (h : J ≤ I) :
    A.upper.map (homOfLE h).op = coef A (upperInterval_mono h) := (rfl)

omit [Preadditive C] [HasCoproducts.{w} C] in
private lemma coef_refl {I : NonemptyInterval S} (h : upperInterval I ≤ upperInterval I) :
    coef A h = 𝟙 _ := by
  simp [coef]

/-- Restricting the upper extension from `σ ∪ {⊤}` to a nonempty set `σ` of vertices is an
isomorphism: both are flags or neither is, with the same least vertex. -/
private lemma isIso_upper_flagFunctor_map (σ : Finset (LinearExtension S)) (hσ : σ.Nonempty) :
    IsIso (A.upper.flagFunctor.map (homOfLE (subset_insert topVertex σ)).op) := by
  refine ⟨A.upper.flagObjDesc fun hσ' ↦ coef A
      (upper_le_of_subset_insert hσ' hσ'.insert_topVertex subset_rfl) ≫
    A.upper.flagObjι hσ'.insert_topVertex, ?_, ?_⟩
  · ext hs
    have hσ' := hs.mono (subset_insert _ _) hσ
    rw [flagObjι_flagObjDesc_assoc, flagRestrict_of_isFlag _ hs _ hσ',
      Category.assoc, flagObjι_flagObjDesc, upper_map_eq_coef, coef_comp_assoc, coef_refl,
      Category.id_comp, Category.comp_id]
  · ext hσ'
    rw [flagObjι_flagObjDesc_assoc, Category.assoc, flagObjι_flagObjDesc,
      flagRestrict_of_isFlag _ _ _ hσ', upper_map_eq_coef, coef_comp_assoc, coef_refl,
      Category.id_comp, Category.comp_id]

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

/-- The inclusion of the top value in the total is natural in the interval diagram. -/
@[reassoc (attr := simp)]
lemma topι_totalMap {A B : IntervalDiagram S (ChainComplex D ℕ)} (α : A ⟶ B) :
    A.topι ≫ totalMap α = α.app (op (NonemptyInterval.pure ⊤)) ≫ B.topι := by
  -- `topι` is `topFlagι` followed by the inclusion of column `0` in the total.
  have h : topFlagι A ≫ (flagComplexMap α).f 0 =
      α.app (op (NonemptyInterval.pure ⊤)) ≫ topFlagι B := by
    simp [topFlagι]
  ext q : 1
  simp only [HomologicalComplex.comp_f, topι, Category.assoc, ιTotal_totalMap]
  rw [← HomologicalComplex.comp_f_assoc, h, HomologicalComplex.comp_f_assoc]

end Top

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D] [HasCoproducts.{w} D] [Finite S]
  {A B : IntervalDiagram S (ChainComplex D ℕ)}

/-- A map of interval diagrams which is a quasi-isomorphism on every interval is a
quasi-isomorphism on every column of the flag complexes. -/
lemma quasiIso_flagComplexMap_f (α : A ⟶ B) [∀ I, QuasiIso (α.app I)] (p : ℕ) :
    QuasiIso ((flagComplexMap α).f p) := by
  have : Fintype (LinearExtension S) := Fintype.ofFinite _
  have (s : Finset (LinearExtension S)) : QuasiIso ((flagFunctorMap α).app (op s)) :=
    HomologicalComplex.quasiIso_of_isColimit_cofan (coproductIsCoproduct _)
      (coproductIsCoproduct _) (fun h : ULift.{w} (PLift (IsFlag s)) ↦
        α.app (op (flagInterval h.down.down))) _
      fun h ↦ flagObjι_flagFunctorMap_app α (s := op s) h.down.down
  exact HomologicalComplex.quasiIso_of_isColimit_cofan
    (A.flagFunctor.isColimitOrderedCechComplexCofan p)
    (B.flagFunctor.isColimitOrderedCechComplexCofan p)
    (fun s : {s : Finset (LinearExtension S) // #s = p + 1} ↦ (flagFunctorMap α).app (op s.val)) _
    fun s ↦ NatTrans.ι_orderedCechComplexMap_f (flagFunctorMap α) s

/-- **A map of interval diagrams which is a quasi-isomorphism on every interval induces a
quasi-isomorphism of totals** (Pardon, Lemma A.7.4). On a finite poset, a map of interval diagrams
of chain complexes in an abelian category which is a quasi-isomorphism on every interval induces a
quasi-isomorphism of their totals. -/
theorem quasiIso_totalMap (α : A ⟶ B) [∀ I, QuasiIso (α.app I)] : QuasiIso (totalMap α) := by
  -- The rows of the flipped bicomplexes are the columns of the flag complexes.
  let ψ : HomologicalComplex₂.flip A.flagComplex ⟶ HomologicalComplex₂.flip B.flagComplex :=
    (HomologicalComplex₂.flipFunctor D _ _).map (flagComplexMap α)
  have hψ : QuasiIso (HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ)) :=
    HomologicalComplex₂.quasiIso_total_map_of_rows ψ fun q ↦ quasiIso_flagComplexMap_f α q
  have hcomm :
      (HomologicalComplex₂.totalFlipIso A.flagComplex (ComplexShape.down ℕ)).hom ≫ totalMap α =
        HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ) ≫
          (HomologicalComplex₂.totalFlipIso B.flagComplex (ComplexShape.down ℕ)).hom :=
    (HomologicalComplex₂.total_map_flip_totalFlipIso_hom (flagComplexMap α) _).symm
  rw [← quasiIso_iff_comp_left
      (HomologicalComplex₂.totalFlipIso A.flagComplex (ComplexShape.down ℕ)).hom, hcomm]
  infer_instance

section Top

variable [OrderTop S]

omit [Finite S] in
private lemma upper_topι_comp_totalMap_upperMap (A : IntervalDiagram S (ChainComplex D ℕ)) :
    A.upper.topι ≫ totalMap A.upperMap = A.topι := by
  ext q : 1
  rw [HomologicalComplex.comp_f, topι_f, topι_f, Category.assoc, ιTotal_totalMap,
    ← Category.assoc, ← HomologicalComplex.comp_f, Category.assoc, flagComplexι_flagComplexMap_f,
    upperMap_app, ← Category.assoc, ← A.map_comp, ← op_comp, homOfLE_comp]
  -- The intervals `upperInterval (pure ⊤)` and `pure ⊤` are both `[⊤, ⊤]` by definition.
  rfl

omit [Finite S] in
private lemma quasiIso_upper_topι (A : IntervalDiagram S (ChainComplex D ℕ)) :
    QuasiIso A.upper.topι := by
  -- The flag complex of the upper extension is the ordered Čech complex of a cone with vertex `⊤`.
  let e := A.upper.flagFunctor.orderedCechHomotopyEquivOfVertex (toLinearExtension ⊤)
    (isIso_upper_flagFunctor_map A)
  have hT := HomologicalComplex₂.quasiIso_totalAugmentation_of_rows e.hom fun q ↦
    ((HomologicalComplex.eval D (ComplexShape.down ℕ) q).mapHomotopyEquiv e).quasiIso_hom
  -- Through the augmentation, `topι` is the inclusion of `A[⊤, ⊤]` in the value on the flag `⊤`.
  have hid : A.upper.topι ≫ HomologicalComplex₂.totalAugmentation A.upper.flagComplex _
      (HomologicalComplex₂.d_comp_f_zero_singleObjXSelf_hom _ e.hom) =
        A.upper.map (homOfLE flagInterval_singleton_top.le).op ≫
          A.upper.flagObjι (IsFlag.singleton (toLinearExtension (⊤ : S))) := by
    ext q : 1
    rw [HomologicalComplex.comp_f, topι_f, Category.assoc,
      HomologicalComplex₂.ιTotal_totalAugmentation_f_zero, ← HomologicalComplex.comp_f]
    congr 1
    rw [flagComplexι, Category.assoc, Category.assoc,
      Functor.orderedCechComplexι_orderedCechHomotopyEquivOfVertex_hom_f_zero_assoc,
      Iso.inv_hom_id, Category.comp_id]
  have := homOfLE_isIso_of_eq flagInterval_singleton_top.le (flagInterval_singleton_top (S := S))
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
