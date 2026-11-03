/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.BorelReducibility
import TauCeti.MeasureTheory.MeasurableSpace.Quotient

/-!
# Borel reducibility for countable quotients

For equivalence relations with countably many measurable classes, Borel reducibility is
exactly comparison of the numbers of classes. In particular, such a relation is Borel
bireducible with equality on a finite ordinal or on the natural numbers. The finite case
includes the empty space, represented by equality on `Fin 0`.

Only measurability of the individual classes is required: the spaces need not be standard
Borel. The key input is `Setoid.borelBireducible_bot_quotient`: a countable quotient with
measurable classes has the discrete σ-algebra, so a choice of representatives is measurable.

## Main results

* `Setoid.borelReducible_iff_lift_mk_quotient_le_of_countable`: the order for countable quotients.
* `Setoid.borelBireducible_iff_lift_mk_quotient_eq_of_countable`: its equivalence classes.
* `Setoid.borelBireducible_bot_iff_nonempty_equiv_of_countable`: equality on a countable discrete
  space is a normal form precisely when that space bijects with the quotient.
* `Setoid.borelBireducible_bot_nat_iff`: the countably infinite normal form.
* `Setoid.exists_borelBireducible_bot_fin_or_nat`: the finite or countably infinite normal forms.

## References

* S. Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapter 5
  (the initial segment of the Borel reducibility order).
-/

public section

open Cardinal MeasurableSpace Set

universe u v

namespace Setoid

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {E : Setoid X} {F : Setoid Y}

/-- Borel reducibility to a relation with countably many classes is exactly comparison of the
cardinalities of the quotients, provided all classes of both relations are measurable. -/
theorem borelReducible_iff_lift_mk_quotient_le_of_countable [Countable (Quotient F)]
    (hE : ∀ x, MeasurableSet {y | E x y}) (hF : ∀ x, MeasurableSet {y | F x y}) :
    E.BorelReducible F ↔ lift.{v} #(Quotient E) ≤ lift.{u} #(Quotient F) := by
  refine ⟨BorelReducible.lift_mk_quotient_le, fun h ↦ ?_⟩
  obtain ⟨f⟩ := lift_mk_le'.1 h
  have : Countable (Quotient E) := f.injective.countable
  have := measurableSingletonClass_quotient hE
  have := measurableSingletonClass_quotient hF
  have hquot : (⊥ : Setoid (Quotient E)).BorelReducible (⊥ : Setoid (Quotient F)) :=
    borelReducible_bot_bot_iff_lift_mk_le.2 h
  obtain ⟨hE', -⟩ := borelBireducible_iff.1 (borelBireducible_bot_quotient hE)
  obtain ⟨-, hF'⟩ := borelBireducible_iff.1 (borelBireducible_bot_quotient hF)
  exact hE'.trans (hquot.trans hF')

/-- Two relations with measurable classes, one with countably many classes, are Borel
bireducible exactly when their quotients have the same cardinality. -/
theorem borelBireducible_iff_lift_mk_quotient_eq_of_countable [Countable (Quotient F)]
    (hE : ∀ x, MeasurableSet {y | E x y}) (hF : ∀ x, MeasurableSet {y | F x y}) :
    E.BorelBireducible F ↔ lift.{v} #(Quotient E) = lift.{u} #(Quotient F) := by
  refine ⟨BorelBireducible.lift_mk_quotient_eq, fun h ↦ ?_⟩
  obtain ⟨e⟩ := lift_mk_eq'.1 h
  have : Countable (Quotient E) := Countable.of_equiv (Quotient F) e.symm
  exact borelBireducible_iff.2
    ⟨(borelReducible_iff_lift_mk_quotient_le_of_countable hE hF).2 h.le,
      (borelReducible_iff_lift_mk_quotient_le_of_countable hF hE).2 h.ge⟩

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

end Setoid
