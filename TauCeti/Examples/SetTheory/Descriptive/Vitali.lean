/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.SetTheory.Descriptive.Vitali
import TauCeti.Topology.Baire.KuratowskiUlam
import TauCeti.Topology.Baire.Perfect

/-!
# Regression examples: the Vitali relation

These examples exercise the API of the Vitali relation `x - y ∈ ℚ` on `ℝ` from a downstream
module, through public statements only:

* it is a Borel equivalence relation with countable classes, and so is meagre in the plane, by
  meagreness of countable sets and the Kuratowski–Ulam theorem;
* generic ergodicity: the positive half-line is open, neither meagre nor comeagre, and so is not
  invariant;
* it is not smooth, and no relation above it is smooth;
* it lies strictly above equality on Cantor space, and has a perfect antichain;
* it has as many classes as equality on `ℝ`, but is not Borel reducible to it.
-/

open Cardinal Set Setoid TauCeti

-- The Vitali relation is a Borel equivalence relation with countable classes.
example : MeasurableSet {p : ℝ × ℝ | vitaliRel p.1 p.2} ∧ ∀ x, {y | vitaliRel x y}.Countable :=
  ⟨measurableSet_vitaliRel, countable_setOf_vitaliRel⟩

-- Its graph is meagre in the plane: every section is a countable class, hence meagre, and
-- Kuratowski–Ulam applies.
example : IsMeagre {p : ℝ × ℝ | vitaliRel p.1 p.2} :=
  measurableSet_vitaliRel.baireMeasurableSet.isMeagre_of_forall_isMeagre_curry_left fun x =>
    (countable_setOf_vitaliRel x).isMeagre

-- Generic ergodicity rules out invariance of a set that is neither meagre nor comeagre: the open
-- positive half-line is not invariant under rational translations.
example : Quotient.mk vitaliRel ⁻¹' (Quotient.mk vitaliRel '' Ioi 0) ≠ Ioi (0 : ℝ) := by
  intro hinv
  rcases isMeagre_or_mem_residual_of_vitaliRel_invariant
      measurableSet_Ioi.baireMeasurableSet hinv with h | h
  · exact not_isMeagre_of_isOpen isOpen_Ioi nonempty_Ioi h
  · -- the complement contains the nonempty open negative half-line
    exact not_isMeagre_of_isOpen isOpen_Iio nonempty_Iio
      (Filter.mem_of_superset h fun y hy hy' => lt_asymm hy hy')

-- No equivalence relation to which the Vitali relation is Borel reducible is smooth.
example {X : Type*} [MeasurableSpace X] {E : Setoid X} (h : vitaliRel.BorelReducible E) :
    ¬ E.IsSmooth :=
  fun hE => not_isSmooth_vitaliRel (h.isSmooth hE)

-- The Vitali relation lies strictly above equality on Cantor space.
example : (⊥ : Setoid (ℕ → Bool)).BorelReducible vitaliRel ∧
    ¬ vitaliRel.BorelReducible (⊥ : Setoid (ℕ → Bool)) :=
  ⟨borelReducible_bot_vitaliRel, isSmooth_def.not.1 not_isSmooth_vitaliRel⟩

-- Since `ℝ` is Polish, the Cantor antichain of the Vitali relation gives a nonempty perfect set of
-- reals with pairwise irrational differences.
example : vitaliRel.HasPerfectAntichainOn univ :=
  hasCantorAntichainOn_vitaliRel.hasPerfectAntichainOn

-- The Vitali relation and equality on `ℝ` both have continuum many classes, but the Vitali
-- relation is not Borel reducible to equality on `ℝ`, which is smooth.
example : #(Quotient vitaliRel) = #(Quotient (⊥ : Setoid ℝ)) ∧
    ¬ vitaliRel.BorelReducible (⊥ : Setoid ℝ) :=
  ⟨by rw [mk_quotient_vitaliRel, mk_congr quotientBotEquiv, mk_real],
    fun h => not_isSmooth_vitaliRel (h.isSmooth (isSmooth_bot_iff.2 inferInstance))⟩
