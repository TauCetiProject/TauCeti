/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Symbols
public import TauCeti.ModelTheory.WellOrdering
import Mathlib.SetTheory.Cardinal.Regular
import TauCeti.ModelTheory.Scott.WellOrder
import TauCeti.ModelTheory.Sublanguage

/-!
# Definability of well-orderings of bounded countable type

For any binary relation symbol `lt` of an arbitrary language `L` and any countable ordinal `α < ω₁`,
there is an `L_{ω₁ω}` sentence `wellOrderTypeSentence lt α hα` whose models (of any cardinality, in
any universe) are precisely the structures in which `lt` is a well-order of order type `α`, and a
sentence `boundedWellOrderSentence lt α hα` whose models are precisely the structures in which `lt`
is a well-order of order type strictly below `α`.

The construction restricts to the single-relation sublanguage `symbSublang ∅ {⟨2, lt⟩}`, forms the
canonical Scott sentence of each countable well-order `(β.ToType, <)`, pushes it forward into `L`,
and takes the countable disjunction over `β < α`. Because potential isomorphism out of a
well-ordered structure is isomorphism without any cardinality restriction
(`TauCeti.realize_scottSentence_iff_of_isWellOrder`), these sentences characterize the well-order
type among all models, not only countable ones, and mention no function symbols and no relation
symbol other than `lt`.

Combined with `FirstOrder.Language.Sentenceω.wellFounded_boundedness` and
`FirstOrder.Language.Sentenceω.wellOrder_type_boundedness`, this gives an exact characterization:
the class of structures in which `lt` is a well-order of type `< α` is `L_{ω₁ω}`-definable (even
among countable nonempty structures) if and only if `α < ω₁`. Moreover, for every `α < ω₁` with
`α ≠ 1`, the bound `α` is sharp for `wellOrder_type_boundedness` applied to
`boundedWellOrderSentence lt α hα`.

## Main definitions

* `FirstOrder.Language.wellOrderTypeSentence`: an `L_{ω₁ω}` sentence characterizing structures
  well-ordered by `lt` of exact countable order type `α`.
* `FirstOrder.Language.boundedWellOrderSentence`: an `L_{ω₁ω}` sentence characterizing structures
  well-ordered by `lt` of order type strictly below a countable ordinal `α`.

## Main results

* `FirstOrder.Language.realize_wellOrderTypeSentence_iff` and
  `FirstOrder.Language.realize_wellOrderTypeSentence_iff_eq`: semantics of `wellOrderTypeSentence`
  across arbitrary universes and cardinalities.
* `FirstOrder.Language.realize_boundedWellOrderSentence_iff` and
  `FirstOrder.Language.realize_boundedWellOrderSentence_iff_lt`: semantics of
  `boundedWellOrderSentence` across arbitrary universes and cardinalities.
* `FirstOrder.Language.le_of_forall_type_lt_of_realize_boundedWellOrderSentence`: sharpness of the
  ordinal bound for `boundedWellOrderSentence`.
* `FirstOrder.Language.exists_sentenceω_realize_iff_isWellOrder_type_lt_iff` and
  `FirstOrder.Language.exists_sentenceω_realize_iff_isWellOrder_type_lt_countable_iff`: the class
  of well-orders of type `< α` is `L_{ω₁ω}`-definable iff `α < ω₁`.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, §4.4.
* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, in
  *The Theory of Models*, 1965.
-/

public section

universe u v w o

namespace FirstOrder.Language

open BoundedFormulaInf Structure Ordinal
open scoped Ordinal

variable {L : Language.{u, v}}

/-! ### Single-relation sublanguage helpers -/

/-- The single-relation sublanguage of `L` retaining only `lt`. -/
private abbrev ltSublang (lt : L.Relations 2) : Language.{u, v} :=
  symbSublang (∅ : Set (Σ n, L.Functions n)) {⟨2, lt⟩}

/-- The sole binary relation symbol of `ltSublang lt`. -/
private def ltSymb (lt : L.Relations 2) : (ltSublang lt).Relations 2 :=
  ⟨lt, Set.mem_singleton _⟩

/-- The `ltSublang lt`-structure on a type with `<`, interpreting `ltSymb lt` as `<`. -/
@[instance_reducible]
private def ltSublangStructure (lt : L.Relations 2) (α : Type*) [LT α] :
    (ltSublang lt).Structure α where
  funMap f := isEmptyElim f
  RelMap {n} _ xs :=
    match n, xs with
    | 2, xs => xs 0 < xs 1
    | _, _ => False

private theorem ltSublangStructure_relMap (lt : L.Relations 2) {α : Type*} [LT α]
    (R : (ltSublang lt).Relations 2) (xs : Fin 2 → α) :
    (ltSublangStructure lt α).RelMap R xs ↔ xs 0 < xs 1 :=
  Iff.rfl

private theorem nonempty_equiv_ltSublang_iff (lt : L.Relations 2) (α : Type o) [LT α]
    (M : Type w) [L.Structure M] :
    letI := ltSublangStructure lt α
    letI := (symbSublangIncl (∅ : Set (Σ n, L.Functions n)) {⟨2, lt⟩}).reduct M
    Nonempty (α ≃[ltSublang lt] M) ↔
      Nonempty ((· < · : α → α → Prop) ≃r fun x y : M => RelMap lt ![x, y]) := by
  let := ltSublangStructure lt α
  let ι := symbSublangIncl (∅ : Set (Σ n, L.Functions n)) {⟨2, lt⟩}
  let := ι.reduct M
  have hreduct (R : (ltSublang lt).Relations 2) (ys : Fin 2 → M) :
      (ι.reduct M).RelMap R ys ↔ RelMap lt ys := by
    have hR : R.val = lt := by simpa using Set.mem_singleton_iff.mp R.property
    have h := (ι.map_onRelation (M := M) R ys).symm
    rw [symbSublangIncl_onRelation, hR] at h
    exact Iff.of_eq h
  constructor
  · rintro ⟨e⟩
    refine ⟨⟨e.toEquiv, fun {a b} => ?_⟩⟩
    have hmap := e.map_rel (ltSymb lt) ![a, b]
    have hcomp : (e ∘ ![a, b]) = ![e.toEquiv a, e.toEquiv b] :=
      funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
    rw [hcomp, hreduct, ltSublangStructure_relMap] at hmap
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using hmap
  · rintro ⟨e⟩
    refine ⟨{ toEquiv := e.toEquiv, map_fun' := fun f => isEmptyElim f, map_rel' := ?_ }⟩
    intro n R xs
    rcases R with ⟨r, hr⟩
    rw [Set.mem_singleton_iff] at hr
    cases hr
    have hcomp : (e.toFun ∘ xs) = ![e (xs 0), e (xs 1)] :=
      funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
    rw [hcomp, hreduct, ltSublangStructure_relMap]
    exact e.map_rel_iff

private theorem type_eq_of_relMap_iff (lt : L.Relations 2) (γ : Ordinal.{w})
    [L.Structure γ.ToType] (hrel : ∀ x y : γ.ToType, RelMap lt ![x, y] ↔ x < y)
    (hwo : IsWellOrder γ.ToType (fun x y => RelMap lt ![x, y])) :
    @Ordinal.type γ.ToType (fun x y => RelMap lt ![x, y]) hwo = γ :=
  (RelIso.ordinalType_congr
    (⟨_root_.Equiv.refl _, fun {a b} => (hrel a b).symm⟩ :
      (fun x y : γ.ToType => RelMap lt ![x, y]) ≃r (· < ·))).trans (Ordinal.type_toType γ)

/-! ### Exact countable well-order type -/

/-- An `L_{ω₁ω}` sentence holding in a structure `M`, of any cardinality and in any universe,
precisely when `lt` well-orders `M` with order type equal to the countable ordinal `α`. -/
noncomputable def wellOrderTypeSentence (lt : L.Relations 2) (α : Ordinal.{o})
    (hα : α < ω₁) : L.Sentenceω :=
  letI := ltSublangStructure lt α.ToType
  haveI : Countable α.ToType := Cardinal.countable_toType_of_lt_omega_one hα
  haveI : Countable ({(⟨2, lt⟩ : Σ n, L.Relations n)} : Set _) :=
    (Set.countable_singleton _).to_subtype
  (symbSublangIncl (∅ : Set (Σ n, L.Functions n)) {⟨2, lt⟩}).onBoundedFormulaInf
    (TauCeti.scottSentence (L := ltSublang lt) α.ToType)

/-- `wellOrderTypeSentence` mentions no function symbols. -/
@[simp]
theorem functionsIn_wellOrderTypeSentence (lt : L.Relations 2) {α : Ordinal.{o}} (hα : α < ω₁) :
    (wellOrderTypeSentence lt α hα).functionsIn = ∅ := by
  rw [wellOrderTypeSentence, LHom.functionsIn_onBoundedFormulaInf]
  ext ⟨n, f⟩
  simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro s _
  exact isEmptyElim s.snd

/-- `wellOrderTypeSentence` mentions no relation symbol other than `lt`. -/
theorem relationsIn_wellOrderTypeSentence_subset (lt : L.Relations 2) {α : Ordinal.{o}}
    (hα : α < ω₁) : (wellOrderTypeSentence lt α hα).relationsIn ⊆ {⟨2, lt⟩} := by
  rw [wellOrderTypeSentence, LHom.relationsIn_onBoundedFormulaInf]
  rintro _ ⟨⟨n, r⟩, -, rfl⟩
  simpa only [symbSublangIncl_onRelation] using r.property

private theorem realize_wellOrderTypeSentence_iff_nonempty_relIso (lt : L.Relations 2)
    {α : Ordinal.{o}} (hα : α < ω₁) (M : Type w) [L.Structure M] :
    SentenceInf.Realize (wellOrderTypeSentence lt α hα) M ↔
      Nonempty ((· < · : α.ToType → α.ToType → Prop) ≃r fun x y : M => RelMap lt ![x, y]) := by
  let := ltSublangStructure lt α.ToType
  have : Countable α.ToType := Cardinal.countable_toType_of_lt_omega_one hα
  have : Countable ({(⟨2, lt⟩ : Σ n, L.Relations n)} : Set _) :=
    (Set.countable_singleton _).to_subtype
  have : IsWellOrder α.ToType (fun x y =>
      (ltSublangStructure lt α.ToType).RelMap (ltSymb lt) ![x, y]) := by
    simpa only [ltSublangStructure_relMap, Matrix.cons_val_zero, Matrix.cons_val_one] using
      (inferInstance : IsWellOrder α.ToType (· < ·))
  let ι := symbSublangIncl (∅ : Set (Σ n, L.Functions n)) {⟨2, lt⟩}
  let := ι.reduct M
  rw [wellOrderTypeSentence, ι.realize_sentenceInf_onBoundedFormulaInf,
    TauCeti.realize_scottSentence_iff_of_isWellOrder (L := ltSublang lt) α.ToType (ltSymb lt) M]
  exact nonempty_equiv_ltSublang_iff lt α.ToType M

/-- **Semantics of `wellOrderTypeSentence`.** A structure `M` of any cardinality, in any universe,
satisfies `wellOrderTypeSentence lt α hα` if and only if `lt` well-orders `M` with order type `α`
(after lifting both ordinals to `max o w`). -/
theorem realize_wellOrderTypeSentence_iff (lt : L.Relations 2) {α : Ordinal.{o}} (hα : α < ω₁)
    (M : Type w) [L.Structure M] :
    SentenceInf.Realize (wellOrderTypeSentence lt α hα) M ↔
      ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]),
        Ordinal.lift.{o} (@Ordinal.type M _ h) = Ordinal.lift.{w} α := by
  rw [realize_wellOrderTypeSentence_iff_nonempty_relIso lt hα M]
  constructor
  · rintro ⟨e⟩
    have hwo : IsWellOrder M (fun x y => RelMap lt ![x, y]) := e.symm.toRelEmbedding.isWellOrder
    refine ⟨hwo, ?_⟩
    simpa only [Ordinal.type_toType] using e.symm.ordinal_lift_type_eq
  · rintro ⟨hwo, htype⟩
    have htype' : Ordinal.lift.{w} (Ordinal.type (· < · : α.ToType → α.ToType → Prop)) =
        Ordinal.lift.{o} (@Ordinal.type M _ hwo) := by
      rw [Ordinal.type_toType]
      exact htype.symm
    exact (Ordinal.lift_type_eq.{o, w, 0}).mp htype'

/-- Same-universe specialization of `realize_wellOrderTypeSentence_iff`. -/
theorem realize_wellOrderTypeSentence_iff_eq (lt : L.Relations 2) {α : Ordinal.{w}} (hα : α < ω₁)
    (M : Type w) [L.Structure M] :
    SentenceInf.Realize (wellOrderTypeSentence lt α hα) M ↔
      ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]), @Ordinal.type M _ h = α := by
  simpa only [Ordinal.lift_id] using realize_wellOrderTypeSentence_iff lt hα M

/-- Every model of `wellOrderTypeSentence lt α hα` is well-ordered by `lt`. -/
theorem isWellOrder_of_realize_wellOrderTypeSentence (lt : L.Relations 2) {α : Ordinal.{o}}
    (hα : α < ω₁) {M : Type w} [L.Structure M]
    (h : SentenceInf.Realize (wellOrderTypeSentence lt α hα) M) :
    IsWellOrder M (fun x y => RelMap lt ![x, y]) :=
  ((realize_wellOrderTypeSentence_iff lt hα M).mp h).fst

/-- Every model of `wellOrderTypeSentence lt α hα`, in any universe, is countable. -/
theorem countable_of_realize_wellOrderTypeSentence (lt : L.Relations 2) {α : Ordinal.{o}}
    (hα : α < ω₁) {M : Type w} [L.Structure M]
    (h : SentenceInf.Realize (wellOrderTypeSentence lt α hα) M) : Countable M := by
  obtain ⟨e⟩ := (realize_wellOrderTypeSentence_iff_nonempty_relIso lt hα M).mp h
  have : Countable α.ToType := Cardinal.countable_toType_of_lt_omega_one hα
  exact e.toEquiv.surjective.countable

/-! ### Well-orderings of bounded countable type -/

/-- An `L_{ω₁ω}` sentence holding in a structure `M`, of any cardinality and in any universe,
precisely when `lt` well-orders `M` with order type strictly below the countable ordinal `α`.
It is the countable disjunction of `wellOrderTypeSentence lt β` over all `β < α`. -/
noncomputable def boundedWellOrderSentence (lt : L.Relations 2) (α : Ordinal.{o})
    (hα : α < ω₁) : L.Sentenceω :=
  haveI : Countable (Set.Iio α) := (Cardinal.countable_Iio_of_lt_omega_one hα).to_subtype
  BoundedFormulaInf.iSupAlong
    (TauCeti.IndexCoding.ofEncodableWith (Encodable.ofCountable (Set.Iio α)))
    fun β => wellOrderTypeSentence lt β.val (β.property.trans hα)

/-- `boundedWellOrderSentence` mentions no function symbols. -/
@[simp]
theorem functionsIn_boundedWellOrderSentence (lt : L.Relations 2) {α : Ordinal.{o}} (hα : α < ω₁) :
    (boundedWellOrderSentence lt α hα).functionsIn = ∅ := by
  rw [boundedWellOrderSentence, BoundedFormulaInf.functionsIn_iSupAlong]
  simp

/-- `boundedWellOrderSentence` mentions no relation symbol other than `lt`. -/
theorem relationsIn_boundedWellOrderSentence_subset (lt : L.Relations 2) {α : Ordinal.{o}}
    (hα : α < ω₁) : (boundedWellOrderSentence lt α hα).relationsIn ⊆ {⟨2, lt⟩} := by
  rw [boundedWellOrderSentence, BoundedFormulaInf.relationsIn_iSupAlong]
  exact Set.iUnion_subset fun β => relationsIn_wellOrderTypeSentence_subset lt (β.property.trans hα)

private theorem realize_boundedWellOrderSentence_iff_exists (lt : L.Relations 2)
    {α : Ordinal.{o}} (hα : α < ω₁) (M : Type w) [L.Structure M] :
    SentenceInf.Realize (boundedWellOrderSentence lt α hα) M ↔
      ∃ (β : Ordinal.{o}) (hβ : β < α),
        SentenceInf.Realize (wellOrderTypeSentence lt β (hβ.trans hα)) M := by
  simp only [boundedWellOrderSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iSupAlong, Subtype.exists, Set.mem_Iio]

/-- **Semantics of `boundedWellOrderSentence`.** A structure `M` of any cardinality, in any
universe, satisfies `boundedWellOrderSentence lt α hα` if and only if `lt` well-orders `M` with
order type strictly below `α` (after lifting both ordinals to `max o w`). -/
theorem realize_boundedWellOrderSentence_iff (lt : L.Relations 2) {α : Ordinal.{o}} (hα : α < ω₁)
    (M : Type w) [L.Structure M] :
    SentenceInf.Realize (boundedWellOrderSentence lt α hα) M ↔
      ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]),
        Ordinal.lift.{o} (@Ordinal.type M _ h) < Ordinal.lift.{w} α := by
  rw [realize_boundedWellOrderSentence_iff_exists]
  constructor
  · rintro ⟨β, hβα, hβ⟩
    obtain ⟨hwo, htype⟩ := (realize_wellOrderTypeSentence_iff lt (hβα.trans hα) M).mp hβ
    exact ⟨hwo, htype ▸ Ordinal.lift_lt.mpr hβα⟩
  · rintro ⟨hwo, hlt⟩
    obtain ⟨β, hβα, htype⟩ := Ordinal.lt_lift_iff.mp hlt
    exact ⟨β, hβα, (realize_wellOrderTypeSentence_iff lt (hβα.trans hα) M).mpr ⟨hwo, htype.symm⟩⟩

/-- Same-universe specialization of `realize_boundedWellOrderSentence_iff`. -/
theorem realize_boundedWellOrderSentence_iff_lt (lt : L.Relations 2) {α : Ordinal.{w}}
    (hα : α < ω₁) (M : Type w) [L.Structure M] :
    SentenceInf.Realize (boundedWellOrderSentence lt α hα) M ↔
      ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]), @Ordinal.type M _ h < α := by
  simpa only [Ordinal.lift_id] using realize_boundedWellOrderSentence_iff lt hα M

/-- Every model of `boundedWellOrderSentence lt α hα` is well-ordered by `lt`. -/
theorem isWellOrder_of_realize_boundedWellOrderSentence (lt : L.Relations 2) {α : Ordinal.{o}}
    (hα : α < ω₁) {M : Type w} [L.Structure M]
    (h : SentenceInf.Realize (boundedWellOrderSentence lt α hα) M) :
    IsWellOrder M (fun x y => RelMap lt ![x, y]) :=
  ((realize_boundedWellOrderSentence_iff lt hα M).mp h).fst

/-- Every model of `boundedWellOrderSentence lt α hα`, in any universe, is countable. -/
theorem countable_of_realize_boundedWellOrderSentence (lt : L.Relations 2) {α : Ordinal.{o}}
    (hα : α < ω₁) {M : Type w} [L.Structure M]
    (h : SentenceInf.Realize (boundedWellOrderSentence lt α hα) M) : Countable M := by
  obtain ⟨β, hβα, hβ⟩ := (realize_boundedWellOrderSentence_iff_exists lt hα M).mp h
  exact countable_of_realize_wellOrderTypeSentence lt (hβα.trans hα) hβ

/-! ### Sharpness and exact characterization of definable bounded well-orderings -/

/-- Any strict ordinal upper bound on the order types of models of `boundedWellOrderSentence lt α`
lies strictly above every nonzero ordinal `γ < α`. -/
theorem lt_of_forall_type_lt_of_realize_boundedWellOrderSentence (lt : L.Relations 2)
    {α β γ : Ordinal.{w}} (hα : α < ω₁)
    (hbound : ∀ (M : Type w) (inst : L.Structure M)
      (h : SentenceInf.Realize (boundedWellOrderSentence lt α hα) M),
      @Ordinal.type M (fun x y => RelMap lt ![x, y])
        (isWellOrder_of_realize_boundedWellOrderSentence lt hα h) < β)
    (hγ0 : 0 < γ) (hγα : γ < α) : γ < β := by
  have : Nonempty γ.ToType := nonempty_toType_iff.mpr hγ0.ne'
  let inst := relStructure lt (· < ·) (Classical.arbitrary γ.ToType)
  let := inst
  have hrel (x y : γ.ToType) : RelMap lt ![x, y] ↔ x < y := relMap_relStructure_self lt _ _ x y
  have hwo : IsWellOrder γ.ToType (fun x y => RelMap lt ![x, y]) := by
    simpa only [hrel] using (inferInstance : IsWellOrder γ.ToType (· < ·))
  have htype : @Ordinal.type γ.ToType (fun x y => RelMap lt ![x, y]) hwo = γ :=
    type_eq_of_relMap_iff lt γ hrel hwo
  have hsat : SentenceInf.Realize (boundedWellOrderSentence lt α hα) γ.ToType :=
    (realize_boundedWellOrderSentence_iff_lt lt hα γ.ToType).mpr ⟨hwo, htype.symm ▸ hγα⟩
  simpa only [htype] using hbound γ.ToType inst hsat

/-- **Sharpness of `wellOrder_type_boundedness`.** For every countable ordinal `α ≠ 1`, any
ordinal strictly bounding the order types of all models of `boundedWellOrderSentence lt α hα` is at
least `α`. The exception `α = 1` is necessary when `L` has constant symbols, since then no empty
`L`-structure exists and `boundedWellOrderSentence lt 1` has no models. -/
theorem le_of_forall_type_lt_of_realize_boundedWellOrderSentence (lt : L.Relations 2)
    {α β : Ordinal.{w}} (hα : α < ω₁) (hα1 : α ≠ 1)
    (hbound : ∀ (M : Type w) (inst : L.Structure M)
      (h : SentenceInf.Realize (boundedWellOrderSentence lt α hα) M),
      @Ordinal.type M (fun x y => RelMap lt ![x, y])
        (isWellOrder_of_realize_boundedWellOrderSentence lt hα h) < β) :
    α ≤ β := by
  by_contra hlt
  have hβα : β < α := not_le.mp hlt
  rcases eq_or_ne β 0 with rfl | hβ0
  · have h1le : (1 : Ordinal.{w}) ≤ α := by
      simpa using Order.succ_le_of_lt hβα
    have h1α : 1 < α := lt_of_le_of_ne h1le hα1.symm
    exact (not_lt.mpr zero_le)
      (lt_of_forall_type_lt_of_realize_boundedWellOrderSentence lt hα hbound zero_lt_one h1α)
  · exact (lt_irrefl β)
      (lt_of_forall_type_lt_of_realize_boundedWellOrderSentence lt hα hbound
        (pos_iff_ne_zero.mpr hβ0) hβα)

/-- **Exact definability characterization among countable nonempty structures.** There exists an
`L_{ω₁ω}` sentence holding in a countable nonempty structure in `Type w` precisely when `lt`
well-orders it with order type `< α` if and only if `α < ω₁`. -/
theorem exists_sentenceω_realize_iff_isWellOrder_type_lt_countable_iff (lt : L.Relations 2)
    (α : Ordinal.{w}) :
    (∃ φ : L.Sentenceω, ∀ (M : Type w) (_ : L.Structure M), Nonempty M → Countable M →
      (SentenceInf.Realize φ M ↔
        ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]), @Ordinal.type M _ h < α)) ↔
      α < ω₁ := by
  constructor
  · rintro ⟨φ, hφ⟩
    by_contra hα
    refine Sentenceω.not_forall_realize_relStructure_add_one (φ := φ) (lt := lt)
      (fun M _ hne hc h => ((hφ M _ hne hc).mp h).fst.wf)
      fun β hβ inst hrel hne hc hwo => ?_
    have hβ1α : β + 1 < α :=
      ((Cardinal.isSuccLimit_omega 1).add_one_lt hβ).trans_le (not_lt.mp hα)
    have htype : @Ordinal.type (β + 1).ToType (fun x y => RelMap lt ![x, y]) hwo = β + 1 :=
      type_eq_of_relMap_iff lt (β + 1) hrel hwo
    exact (hφ _ inst hne hc).mpr ⟨hwo, htype.symm ▸ hβ1α⟩
  · intro hα
    exact ⟨boundedWellOrderSentence lt α hα,
      fun M _ _ _ => realize_boundedWellOrderSentence_iff_lt lt hα M⟩

/-- **Exact definability characterization among all structures.** There exists an `L_{ω₁ω}`
sentence holding in a structure in `Type w`, of any cardinality, precisely when `lt` well-orders it
with order type `< α` if and only if `α < ω₁`. -/
theorem exists_sentenceω_realize_iff_isWellOrder_type_lt_iff (lt : L.Relations 2)
    (α : Ordinal.{w}) :
    (∃ φ : L.Sentenceω, ∀ (M : Type w) (_ : L.Structure M),
      SentenceInf.Realize φ M ↔
        ∃ h : IsWellOrder M (fun x y => RelMap lt ![x, y]), @Ordinal.type M _ h < α) ↔
      α < ω₁ :=
  ⟨fun ⟨φ, hφ⟩ => (exists_sentenceω_realize_iff_isWellOrder_type_lt_countable_iff lt α).mp
      ⟨φ, fun M inst _ _ => hφ M inst⟩,
    fun hα => ⟨boundedWellOrderSentence lt α hα,
      fun M _ => realize_boundedWellOrderSentence_iff_lt lt hα M⟩⟩

end FirstOrder.Language
