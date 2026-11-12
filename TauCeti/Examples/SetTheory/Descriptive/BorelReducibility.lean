/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Cardinality
import TauCeti.SetTheory.Descriptive.EZero

/-!
# Regression examples: Borel reducibility and smoothness

These examples exercise the Borel reducibility API from a downstream module, through public
statements only:

* equality on `ℝ` is smooth, and Borel bireducible with equality on Cantor space;
* equality of first coordinates on Cantor space is smooth, and has finite normal form `Fin 2`;
* equality of first coordinates on Baire space has countably infinite normal form `ℕ`;
* finite equality relations are classified by their size, including the empty space;
* `E₀` is Borel and not smooth, equality on Cantor space reduces to it, and no relation above it
  is smooth.
-/

open Setoid

-- Equality on `ℝ` is smooth, since `ℝ` is countably separated.
example : (⊥ : Setoid ℝ).IsSmooth :=
  isSmooth_bot_iff.2 inferInstance

-- Equality on `ℝ` and equality on Cantor space are Borel bireducible: `ℝ` is an uncountable
-- standard Borel space.
example : (⊥ : Setoid ℝ).BorelBireducible (⊥ : Setoid (ℕ → Bool)) :=
  borelBireducible_iff.2 ⟨isSmooth_def.1 (isSmooth_bot_iff.2 inferInstance),
    (isSmooth_iff_borelReducible_bot (Y := ℝ) not_countable).1 (isSmooth_def.2 .rfl)⟩

-- Equality of first coordinates on Cantor space is the pullback of equality on `Bool` along the
-- first coordinate, so it is smooth.
example : (Setoid.comap (fun x : ℕ → Bool => x 0) ⊥).IsSmooth :=
  (borelReducible_comap (measurable_pi_apply 0) ⊥).isSmooth (isSmooth_bot_iff.2 inferInstance)

-- The quotient of equality of first coordinates is `Bool`, hence the finite normal form is
-- equality on `Fin 2`. Constant sequences give a right inverse to evaluation.
example : (Setoid.ker (fun x : ℕ → Bool ↦ x 0)).BorelBireducible (⊥ : Setoid (Fin 2)) := by
  refine (borelBireducible_bot_iff_nonempty_equiv_of_countable ?_).2
    ⟨(quotientKerEquivOfRightInverse (fun x : ℕ → Bool ↦ x 0) (fun b _ ↦ b)
      (fun _ ↦ rfl)).trans finTwoEquiv.symm⟩
  intro x
  simpa only [ker_def] using
    (measurableSet_eq_fun measurable_const (measurable_pi_apply 0) :
      MeasurableSet {y : ℕ → Bool | x 0 = y 0})

-- The same computation for Baire space gives the countably infinite normal form.
example : (Setoid.ker (fun x : ℕ → ℕ ↦ x 0)).BorelBireducible (⊥ : Setoid ℕ) := by
  refine (borelBireducible_bot_iff_nonempty_equiv_of_countable ?_).2
    ⟨quotientKerEquivOfRightInverse (fun x : ℕ → ℕ ↦ x 0) (fun n _ ↦ n) (fun _ ↦ rfl)⟩
  intro x
  simpa only [ker_def] using
    (measurableSet_eq_fun measurable_const (measurable_pi_apply 0) :
      MeasurableSet {y : ℕ → ℕ | x 0 = y 0})

-- The normal forms have no repetitions, including at `n = 0`.
example (m n : ℕ) :
    (⊥ : Setoid (Fin m)).BorelBireducible (⊥ : Setoid (Fin n)) ↔ m = n := by
  rw [borelBireducible_bot_iff_nonempty_equiv_of_countable
    (fun x ↦ by simpa only [bot_def] using
      (measurableSet_eq_fun measurable_const measurable_id :
        MeasurableSet {y : Fin m | x = y}))]
  constructor
  · rintro ⟨e⟩
    exact Fin.equiv_iff_eq.1 ⟨quotientBotEquiv.symm.trans e⟩
  · rintro rfl
    exact ⟨quotientBotEquiv⟩

-- `E₀` is Borel, equality on Cantor space reduces to it, and it is not smooth.
example : MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | TauCeti.eZero p.1 p.2} ∧
    (⊥ : Setoid (ℕ → Bool)).BorelReducible TauCeti.eZero ∧ ¬ TauCeti.eZero.IsSmooth :=
  ⟨TauCeti.measurableSet_eZero, TauCeti.borelReducible_bot_eZero, TauCeti.not_isSmooth_eZero⟩

-- No relation to which `E₀` is Borel reducible is smooth.
example {X : Type*} [MeasurableSpace X] (E : Setoid X) (h : TauCeti.eZero.BorelReducible E) :
    ¬ E.IsSmooth :=
  TauCeti.not_isSmooth_of_borelReducible_eZero h
