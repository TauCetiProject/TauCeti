/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.SetTheory.Descriptive.Antichain
import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated
import TauCeti.MeasureTheory.MeasurableSpace.Quotient

/-!
# Borel reducibility and smooth equivalence relations

An equivalence relation `E` on a measurable space `X` is **Borel reducible** to an equivalence
relation `F` on `Y` when some measurable `f : X → Y` satisfies `E x y ↔ F (f x) (f y)`: the classes
of `E` are then classified by the classes of `F`, through a Borel map. Borel reducibility is a
preorder across all measurable spaces, and it compares the complexity of classification
problems.

The simplest relations in this order are the equalities. `E` is **smooth** when it is Borel
reducible to equality on Cantor space `ℕ → Bool`, that is, when a Borel map into Cantor space
classifies its classes. The main characterization is that `E` is smooth exactly when countably
many `E`-invariant measurable sets separate its classes, which is to say that the quotient
`Quotient E`, with Mathlib's quotient σ-algebra, is countably separated. A Borel reduction descends
to a measurable injection of quotients, and Mathlib's measurable injection of a countably separated
space into Cantor space gives the converse.

Further facts:

* a reduction to a relation with Borel graph pulls the graph back, so a smooth relation is Borel;
* a reduction induces an injection of quotients, so `F` has at least as many classes as `E`;
* equality on a standard Borel space `X` reduces to equality on a standard Borel space `Y` iff
  `#X ≤ #Y`. If `X` is countable, any injection works, as a countable standard Borel space is
  discrete; otherwise both spaces are uncountable and the Borel isomorphism theorem identifies
  them. In particular, for uncountable standard Borel `Y`, smoothness is reducibility to equality
  on `Y`;
* a relation with countably many classes, each measurable, is smooth, and it is bireducible
  with equality on its quotient, whose σ-algebra is then discrete. Among relations with measurable
  classes, reducibility to a countable quotient is exactly comparison of the numbers of classes.
  The countable normal forms are equality on some `Fin n` (including `Fin 0` for the empty space)
  or on `ℕ`; no standard Borel hypothesis is needed;
* a Cantor antichain for `E` is a reduction of equality on Cantor space to `E`.

## Main definitions

* `Setoid.BorelReducible E F`: a measurable map `f` with `E x y ↔ F (f x) (f y)`.
* `Setoid.BorelBireducible E F`: each of `E` and `F` is Borel reducible to the other.
* `Setoid.IsSmooth E`: `E` is Borel reducible to equality on `ℕ → Bool`.

## Main results

* `Setoid.BorelReducible.trans`, `Setoid.BorelBireducible.symm`, `Setoid.BorelBireducible.trans`:
  the preorder and its equivalence.
* `Setoid.BorelReducible.exists_measurable_injective_quotient`,
  `Setoid.BorelReducible.lift_mk_quotient_le`: the induced injection of quotients.
* `Setoid.BorelReducible.measurableSet_setOf`, `Setoid.IsSmooth.measurableSet_setOf`: reductions
  pull back Borel graphs, and smooth relations are Borel.
* `Setoid.borelReducible_bot_bot_iff_lift_mk_le`: reductions between equalities on standard
  Borel spaces.
* `Setoid.isSmooth_iff_countablySeparated`: smoothness is countable separation of the quotient.
* `Setoid.isSmooth_iff_borelReducible_bot`: smoothness is reducibility to equality on any
  uncountable standard Borel space.
* `Setoid.isSmooth_of_countable_quotient`, `Setoid.borelBireducible_bot_quotient`: relations
  with countably many measurable classes.
* `Setoid.borelReducible_iff_lift_mk_quotient_le_of_countable`,
  `Setoid.borelBireducible_iff_lift_mk_quotient_eq_of_countable`: comparison of countable quotients.
* `Setoid.borelBireducible_bot_iff_nonempty_equiv_of_countable`: equality on a countable discrete
  space is a normal form precisely when that space bijects with the quotient.
* `Setoid.borelBireducible_bot_nat_iff`, `Setoid.exists_borelBireducible_bot_fin_or_nat`:
  the countably infinite and finite-or-countably-infinite normal forms, using
  `Setoid.borelBireducible_bot_quotient`.
* `Setoid.HasCantorAntichainOn.borelReducible_bot`: a Cantor antichain reduces equality on Cantor
  space.

## References

* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapter 5 (Borel
  reducibility and smooth equivalence relations).
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 15.6 (the Borel isomorphism theorem).
-/

public section

open Cardinal Function MeasurableSpace Set

universe u v w

namespace Setoid

variable {X : Type u} {Y : Type v} {Z : Type w} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] {E : Setoid X} {F : Setoid Y} {G : Setoid Z}

/-! ### Borel reducibility -/

/-- `E` is **Borel reducible** to `F`: some measurable map `f : X → Y` satisfies
`E x y ↔ F (f x) (f y)` for all `x` and `y`. -/
def BorelReducible (E : Setoid X) (F : Setoid Y) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y)

theorem borelReducible_iff :
    E.BorelReducible F ↔ ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y) :=
  Iff.rfl

/-- `E` is Borel reducible to `F` iff it is the pullback `F.comap f` along a measurable map. -/
theorem borelReducible_iff_exists_eq_comap :
    E.BorelReducible F ↔ ∃ f : X → Y, Measurable f ∧ E = F.comap f := by
  refine exists_congr fun f => and_congr_right fun _ => ?_
  rw [Setoid.ext_iff]
  simp [comap_rel]

/-- The pullback of `F` along a measurable map is Borel reducible to `F`. -/
theorem borelReducible_comap {f : X → Y} (hf : Measurable f) (F : Setoid Y) :
    (F.comap f).BorelReducible F :=
  borelReducible_iff_exists_eq_comap.2 ⟨f, hf, rfl⟩

@[refl]
protected theorem BorelReducible.refl (E : Setoid X) : E.BorelReducible E :=
  ⟨id, measurable_id, fun _ _ => Iff.rfl⟩

protected theorem BorelReducible.rfl : E.BorelReducible E :=
  .refl E

@[trans]
protected theorem BorelReducible.trans (h₁ : E.BorelReducible F) (h₂ : F.BorelReducible G) :
    E.BorelReducible G := by
  obtain ⟨f, hf, hfE⟩ := h₁
  obtain ⟨g, hg, hgF⟩ := h₂
  exact ⟨g ∘ f, hg.comp hf, fun x y => (hfE x y).trans (hgF _ _)⟩

/-- A Borel reduction of `E` to `F` descends to a measurable injection `Quotient E → Quotient F`,
for Mathlib's quotient σ-algebras. -/
theorem BorelReducible.exists_measurable_injective_quotient (h : E.BorelReducible F) :
    ∃ g : Quotient E → Quotient F, Measurable g ∧ Injective g := by
  obtain ⟨f, hf, hfE⟩ := h
  refine ⟨Quotient.lift (fun x => Quotient.mk F (f x))
    fun x y hxy => Quotient.sound ((hfE x y).1 hxy),
    measurable_from_quotient.2 (measurable_quotient_mk''.comp hf), fun a b hab => ?_⟩
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact Quotient.sound ((hfE _ _).2 (Quotient.exact hab))

/-- If `E` is Borel reducible to `F`, then `F` has at least as many classes as `E`. -/
theorem BorelReducible.lift_mk_quotient_le (h : E.BorelReducible F) :
    lift.{v} #(Quotient E) ≤ lift.{u} #(Quotient F) := by
  obtain ⟨g, -, hg⟩ := h.exists_measurable_injective_quotient
  exact lift_mk_le_lift_mk_of_injective hg

/-- If `E` is Borel reducible to `F`, on spaces in the same universe, then `F` has at least as
many classes as `E`. -/
theorem BorelReducible.mk_quotient_le {Y : Type u} [MeasurableSpace Y] {F : Setoid Y}
    (h : E.BorelReducible F) : #(Quotient E) ≤ #(Quotient F) := by
  simpa using h.lift_mk_quotient_le

/-- A Borel reduction pulls a Borel graph back: if `E` is Borel reducible to `F` and the graph of
`F` is measurable, so is the graph of `E`. -/
theorem BorelReducible.measurableSet_setOf (h : E.BorelReducible F)
    (hF : MeasurableSet {p : Y × Y | F p.1 p.2}) : MeasurableSet {p : X × X | E p.1 p.2} := by
  obtain ⟨f, hf, hfE⟩ := h
  have : {p : X × X | E p.1 p.2} = Prod.map f f ⁻¹' {p : Y × Y | F p.1 p.2} := by
    ext p
    exact hfE p.1 p.2
  rw [this]
  exact hF.preimage (hf.prodMap hf)

/-! ### Borel bireducibility -/

/-- `E` and `F` are **Borel bireducible**: each is Borel reducible to the other. -/
def BorelBireducible (E : Setoid X) (F : Setoid Y) : Prop :=
  E.BorelReducible F ∧ F.BorelReducible E

theorem borelBireducible_iff :
    E.BorelBireducible F ↔ E.BorelReducible F ∧ F.BorelReducible E :=
  Iff.rfl

@[refl]
protected theorem BorelBireducible.refl (E : Setoid X) : E.BorelBireducible E :=
  ⟨.rfl, .rfl⟩

protected theorem BorelBireducible.rfl : E.BorelBireducible E :=
  .refl E

@[symm]
protected theorem BorelBireducible.symm (h : E.BorelBireducible F) : F.BorelBireducible E :=
  ⟨h.2, h.1⟩

theorem borelBireducible_comm : E.BorelBireducible F ↔ F.BorelBireducible E :=
  ⟨.symm, .symm⟩

@[trans]
protected theorem BorelBireducible.trans (h₁ : E.BorelBireducible F)
    (h₂ : F.BorelBireducible G) : E.BorelBireducible G :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- Borel bireducible relations have equally many classes, allowing different universes. -/
theorem BorelBireducible.lift_mk_quotient_eq (h : E.BorelBireducible F) :
    lift.{v} #(Quotient E) = lift.{u} #(Quotient F) :=
  le_antisymm h.1.lift_mk_quotient_le h.2.lift_mk_quotient_le

/-! ### Reductions between equalities -/

/-- Equality on `X` reduces to equality on `Y` iff there is a measurable injection `X → Y`. -/
theorem borelReducible_bot_bot_iff :
    (⊥ : Setoid X).BorelReducible (⊥ : Setoid Y) ↔ ∃ f : X → Y, Measurable f ∧ Injective f := by
  simp only [borelReducible_iff, bot_def]
  exact exists_congr fun f => and_congr_right fun _ =>
    ⟨fun h x y hxy => (h x y).2 hxy, fun h x y => ⟨congrArg f, fun hxy => h hxy⟩⟩

/-- **Reductions between equalities on standard Borel spaces.** Equality on `X` reduces to
equality on `Y` iff `X` has at most as many points as `Y`. A countable standard Borel space is
discrete, so any injection is measurable; uncountable standard Borel spaces are Borel isomorphic. -/
theorem borelReducible_bot_bot_iff_lift_mk_le [StandardBorelSpace X] [StandardBorelSpace Y] :
    (⊥ : Setoid X).BorelReducible (⊥ : Setoid Y) ↔ lift.{v} #X ≤ lift.{u} #Y := by
  rw [borelReducible_bot_bot_iff]
  refine ⟨fun ⟨f, _, hf⟩ => lift_mk_le_lift_mk_of_injective hf, fun h => ?_⟩
  by_cases hX : Countable X
  · obtain ⟨e⟩ := lift_mk_le'.1 h
    exact ⟨e, measurable_of_countable e, e.injective⟩
  · have hY : ¬ Countable Y := fun hY => hX <| mk_le_aleph0_iff.1 <| lift_le_aleph0.1 <|
      h.trans (lift_le_aleph0.2 (mk_le_aleph0_iff.2 hY))
    let e := PolishSpace.measurableEquivOfNotCountable hX hY
    exact ⟨e, e.measurable, e.injective⟩

/-! ### Smooth equivalence relations -/

/-- `E` is **smooth**: it is Borel reducible to equality on Cantor space `ℕ → Bool`. -/
def IsSmooth (E : Setoid X) : Prop :=
  E.BorelReducible (⊥ : Setoid (ℕ → Bool))

theorem isSmooth_def : E.IsSmooth ↔ E.BorelReducible (⊥ : Setoid (ℕ → Bool)) :=
  Iff.rfl

/-- `E` is smooth iff a measurable map into Cantor space has the classes of `E` as its fibres. -/
theorem isSmooth_iff :
    E.IsSmooth ↔ ∃ f : X → ℕ → Bool, Measurable f ∧ ∀ x y, E x y ↔ f x = f y := by
  simp [IsSmooth, borelReducible_iff]

/-- A relation Borel reducible to a smooth relation is smooth. -/
theorem BorelReducible.isSmooth (h : E.BorelReducible F) (hF : F.IsSmooth) : E.IsSmooth :=
  h.trans hF

/-- **A smooth equivalence relation is Borel**: its graph is the preimage of the diagonal of Cantor
space. -/
theorem IsSmooth.measurableSet_setOf (h : E.IsSmooth) : MeasurableSet {p : X × X | E p.1 p.2} :=
  BorelReducible.measurableSet_setOf h <| by
    simpa only [bot_def] using measurableSet_eq_fun measurable_fst measurable_snd

/-- **Smoothness is countable separation.** `E` is smooth iff the quotient `Quotient E`, with
Mathlib's quotient σ-algebra, is countably separated: countably many `E`-invariant measurable sets
separate the classes of `E`. -/
theorem isSmooth_iff_countablySeparated : E.IsSmooth ↔ CountablySeparated (Quotient E) := by
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · obtain ⟨f, hf, hfE⟩ := isSmooth_iff.1 h
    refine CountablySeparated.of_injective
      (f := Quotient.lift f fun x y hxy => (hfE x y).1 hxy)
      (measurable_from_quotient.2 hf) fun a b hab => ?_
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound ((hfE _ _).2 hab)
  · obtain ⟨g, hg, hinj⟩ := measurable_injection_nat_bool_of_countablySeparated (Quotient E)
    exact isSmooth_iff.2 ⟨g ∘ Quotient.mk E, hg.comp measurable_quotient_mk'',
      fun x y => ⟨fun hxy => congrArg g (Quotient.sound hxy),
        fun hxy => Quotient.exact (hinj hxy)⟩⟩

/-- Equality on `X` is smooth iff `X` is countably separated. -/
theorem isSmooth_bot_iff : (⊥ : Setoid X).IsSmooth ↔ CountablySeparated X := by
  rw [IsSmooth, borelReducible_bot_bot_iff]
  exact ⟨fun ⟨f, hf, hinj⟩ => CountablySeparated.of_injective hf hinj,
    fun _ => measurable_injection_nat_bool_of_countablySeparated X⟩

/-- **Smoothness through any uncountable standard Borel space.** For an uncountable standard Borel
space `Y`, `E` is smooth iff it is Borel reducible to equality on `Y`: equality on `Y` and equality
on Cantor space are Borel isomorphic. -/
theorem isSmooth_iff_borelReducible_bot [StandardBorelSpace Y] (hY : ¬ Countable Y) :
    E.IsSmooth ↔ E.BorelReducible (⊥ : Setoid Y) := by
  let e := PolishSpace.measurableEquivNatBoolOfNotCountable hY
  have h₁ : (⊥ : Setoid (ℕ → Bool)).BorelReducible (⊥ : Setoid Y) :=
    borelReducible_bot_bot_iff.2 ⟨e.symm, e.symm.measurable, e.symm.injective⟩
  have h₂ : (⊥ : Setoid Y).BorelReducible (⊥ : Setoid (ℕ → Bool)) :=
    borelReducible_bot_bot_iff.2 ⟨e, e.measurable, e.injective⟩
  exact ⟨fun h => h.trans h₁, fun h => h.trans h₂⟩

/-! ### Countably many classes -/

/-- **Countably many measurable classes give a smooth relation.** If `E` has countably many
classes, each measurable, then `E` is smooth. -/
theorem isSmooth_of_countable_quotient [Countable (Quotient E)]
    (hE : ∀ x, MeasurableSet {y | E x y}) : E.IsSmooth := by
  have := measurableSingletonClass_quotient hE
  exact isSmooth_iff_countablySeparated.2 inferInstance

/-- If `E` has countably many classes, each measurable, then `E` is Borel bireducible with
equality on its quotient: the quotient map is a reduction one way, and a choice of
representatives, measurable because the quotient σ-algebra is discrete, is a reduction the other
way. -/
theorem borelBireducible_bot_quotient [Countable (Quotient E)]
    (hE : ∀ x, MeasurableSet {y | E x y}) : E.BorelBireducible (⊥ : Setoid (Quotient E)) := by
  have := measurableSingletonClass_quotient hE
  refine ⟨⟨Quotient.mk E, measurable_quotient_mk'', fun x y => ?_⟩,
    ⟨Quotient.out, measurable_of_countable _, fun q r => ?_⟩⟩
  · simp [Quotient.eq]
  · simp only [bot_def]
    exact ⟨fun h => h ▸ E.refl _, fun h => Quotient.out_equiv_out.1 h⟩

/-- Borel reducibility to a relation with countably many classes is exactly comparison of the
cardinalities of the quotients, provided all classes of the source relation are measurable. -/
theorem borelReducible_iff_lift_mk_quotient_le_of_countable [Countable (Quotient F)]
    (hE : ∀ x, MeasurableSet {y | E x y}) :
    E.BorelReducible F ↔ lift.{v} #(Quotient E) ≤ lift.{u} #(Quotient F) := by
  refine ⟨BorelReducible.lift_mk_quotient_le, fun h ↦ ?_⟩
  obtain ⟨f⟩ := lift_mk_le'.1 h
  have : Countable (Quotient E) := f.injective.countable
  have := measurableSingletonClass_quotient hE
  refine ⟨fun x => (f (Quotient.mk E x)).out,
    (measurable_of_countable (fun q : Quotient E => (f q).out)).comp measurable_quotient_mk'',
    fun x y => ?_⟩
  exact ⟨fun hxy => Quotient.out_equiv_out.2 (congrArg f (Quotient.sound hxy)),
    fun hxy => Quotient.exact (f.injective (Quotient.out_equiv_out.1 hxy))⟩

/-- Two relations with measurable classes, one with countably many classes, are Borel
bireducible exactly when their quotients have the same cardinality. -/
theorem borelBireducible_iff_lift_mk_quotient_eq_of_countable [Countable (Quotient F)]
    (hE : ∀ x, MeasurableSet {y | E x y}) (hF : ∀ x, MeasurableSet {y | F x y}) :
    E.BorelBireducible F ↔ lift.{v} #(Quotient E) = lift.{u} #(Quotient F) := by
  refine ⟨BorelBireducible.lift_mk_quotient_eq, fun h ↦ ?_⟩
  obtain ⟨e⟩ := lift_mk_eq'.1 h
  have : Countable (Quotient E) := Countable.of_equiv (Quotient F) e.symm
  exact borelBireducible_iff.2
    ⟨(borelReducible_iff_lift_mk_quotient_le_of_countable hE).2 h.le,
      (borelReducible_iff_lift_mk_quotient_le_of_countable hF).2 h.ge⟩

/-- A relation with measurable classes is Borel bireducible with equality on a countable
discrete measurable space precisely when its quotient bijects with that space. No countability
hypothesis on the quotient is needed. -/
theorem borelBireducible_bot_iff_nonempty_equiv_of_countable [Countable Y]
    [MeasurableSingletonClass Y] (hE : ∀ x, MeasurableSet {y | E x y}) :
    E.BorelBireducible (⊥ : Setoid Y) ↔ Nonempty (Quotient E ≃ Y) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · obtain ⟨e⟩ := lift_mk_eq'.1 h.lift_mk_quotient_eq
    exact ⟨e.trans quotientBotEquiv⟩
  · have : Countable (Quotient E) := Countable.of_equiv Y e.symm
    have := measurableSingletonClass_quotient hE
    have hquot : (⊥ : Setoid (Quotient E)).BorelBireducible (⊥ : Setoid Y) :=
      borelBireducible_iff.2
        ⟨borelReducible_bot_bot_iff.2 ⟨e, measurable_of_countable _, e.injective⟩,
          borelReducible_bot_bot_iff.2 ⟨e.symm, measurable_of_countable _, e.symm.injective⟩⟩
    exact (borelBireducible_bot_quotient hE).trans hquot

/-- Equality on the natural numbers is the normal form for a relation with measurable classes
exactly when the quotient is countably infinite. -/
theorem borelBireducible_bot_nat_iff (hE : ∀ x, MeasurableSet {y | E x y}) :
    E.BorelBireducible (⊥ : Setoid ℕ) ↔ Countable (Quotient E) ∧ Infinite (Quotient E) := by
  rw [borelBireducible_bot_iff_nonempty_equiv_of_countable hE]
  refine ⟨fun ⟨e⟩ ↦ ⟨Countable.of_equiv ℕ e.symm, Infinite.of_injective e.symm e.symm.injective⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

/-- A relation with countably many measurable classes is Borel bireducible with equality on
some `Fin n`, or with equality on `ℕ`. -/
theorem exists_borelBireducible_bot_fin_or_nat [Countable (Quotient E)]
    (hE : ∀ x, MeasurableSet {y | E x y}) :
    (∃ n : ℕ, E.BorelBireducible (⊥ : Setoid (Fin n))) ∨
      E.BorelBireducible (⊥ : Setoid ℕ) := by
  cases finite_or_infinite (Quotient E) with
  | inl h =>
    obtain ⟨n, hn⟩ := Finite.exists_equiv_fin (Quotient E)
    exact .inl ⟨n, (borelBireducible_bot_iff_nonempty_equiv_of_countable hE).2 hn⟩
  | inr h => exact .inr ((borelBireducible_bot_nat_iff hE).2 ⟨inferInstance, h⟩)

/-! ### Cantor antichains -/

/-- **A Cantor antichain reduces equality on Cantor space.** If `E` has a Cantor antichain on some
set, the antichain itself is a Borel reduction of equality on `ℕ → Bool` to `E`. -/
theorem HasCantorAntichainOn.borelReducible_bot [TopologicalSpace X] [BorelSpace X] {A : Set X}
    (h : E.HasCantorAntichainOn A) : (⊥ : Setoid (ℕ → Bool)).BorelReducible E := by
  obtain ⟨f, hf, -, hE⟩ := hasCantorAntichainOn_iff.1 h
  refine ⟨f, hf.measurable, fun a b => ?_⟩
  simp only [bot_def]
  exact ⟨fun hab => hab ▸ E.refl _, fun h => by_contra fun hab => hE a b hab h⟩

end Setoid
