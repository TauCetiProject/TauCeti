/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.SetTheory.Descriptive.EZero
import TauCeti.Topology.Baire.KuratowskiUlam
import TauCeti.Topology.Baire.Mycielski
import TauCeti.Topology.Baire.Perfect
import TauCeti.Topology.Perfect

/-!
# Regression examples: `E₀` and the category method on Cantor space

These examples exercise the Baire-category API on Cantor space from a downstream module, through
public statements only:

* a Borel equivalence relation on Cantor space with countable classes is meagre in the square,
  by meagreness of countable sets and the Kuratowski–Ulam theorem;
* the classes of `E₀` are countable and dense, so any two nonempty open sets contain
  `E₀`-related points, and no Cantor scheme of nonempty open sets has `E₀`-inequivalent
  siblings: a Cantor antichain for `E₀` cannot come from finite-stage separation;
* generic ergodicity: the cylinder of points starting with `true` is clopen, neither meagre nor
  comeagre, and so is not `E₀`-invariant;
* Mycielski's theorem applied to the meagre graph of `E₀` gives a continuous injection of Cantor
  space whose distinct points are `E₀`-inequivalent, recovering the existence of the explicit
  Cantor antichain `hasCantorAntichainOn_eZero` by a different route.
-/

open Set TauCeti PiNat

-- A Borel equivalence relation on Cantor space with countable classes is meagre in the square:
-- every section is a countable class, hence meagre, and Kuratowski–Ulam applies.
example {E : Setoid (ℕ → Bool)} (hE : MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | E p.1 p.2})
    (hc : ∀ x, {y | E x y}.Countable) :
    IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | E p.1 p.2} :=
  hE.baireMeasurableSet.isMeagre_of_forall_isMeagre_curry_left fun x => (hc x).isMeagre

-- The classes of `E₀` are countable and dense.
example (x : ℕ → Bool) : {y | eZero x y}.Countable ∧ Dense {y | eZero x y} :=
  ⟨countable_setOf_eZero x, dense_setOf_eZero x⟩

-- Any two nonempty open subsets of Cantor space contain `E₀`-related points.
example {U V : Set (ℕ → Bool)} (hV : IsOpen V) (hU : U.Nonempty) (hVne : V.Nonempty) :
    ∃ x ∈ U, ∃ y ∈ V, eZero x y := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hy, hxy⟩ := (dense_setOf_eZero x).inter_open_nonempty V hV hVne
  exact ⟨x, hx, y, hy, hxy⟩

-- Hence no Cantor scheme of nonempty open sets has `E₀`-inequivalent siblings, the hypothesis
-- of `CantorScheme.VanishingDiam.exists_antichain_map`.
example : ¬ ∃ A : List Bool → Set (ℕ → Bool), (∀ l, IsOpen (A l)) ∧ (∀ l, (A l).Nonempty) ∧
    ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ eZero x y := by
  rintro ⟨A, hAo, hAne, hcross⟩
  obtain ⟨x, hx⟩ := hAne [false]
  obtain ⟨y, hy, hxy⟩ := (dense_setOf_eZero x).inter_open_nonempty _ (hAo [true]) (hAne [true])
  exact hcross [] x hx y hy hxy

-- Generic ergodicity rules out invariance of a set that is neither meagre nor comeagre: the
-- clopen cylinder of points starting with `true` is not `E₀`-invariant.
example : Quotient.mk eZero ⁻¹' (Quotient.mk eZero '' wordCylinder [true]) ≠
    wordCylinder [true] := by
  intro hinv
  rcases isMeagre_or_mem_residual_of_eZero_invariant
      (isClopen_wordCylinder [true]).isClosed.measurableSet.baireMeasurableSet hinv with h | h
  · exact not_isMeagre_of_isOpen (isOpen_wordCylinder _) (wordCylinder_nonempty _) h
  · -- the complement contains the nonempty open cylinder of points starting with `false`
    refine not_isMeagre_of_isOpen (isOpen_wordCylinder [false]) (wordCylinder_nonempty _)
      (Filter.mem_of_superset h fun y hy hyf => ?_)
    rw [mem_wordCylinder_iff] at hy hyf
    simpa using (hy 0 (by simp)).symm.trans (hyf 0 (by simp))

-- Mycielski's theorem applied to the meagre graph of `E₀` gives a continuous injection of Cantor
-- space whose distinct points are `E₀`-inequivalent.
example : ∃ f : (ℕ → Bool) → ℕ → Bool, Continuous f ∧ Function.Injective f ∧
    ∀ a b, a ≠ b → ¬ eZero (f a) (f b) := by
  obtain ⟨f, hf, hinj, hfE⟩ := mycielski_prod isMeagre_eZero
  exact ⟨f, hf, hinj, fun a b hab => hfE a b hab⟩

-- In the vocabulary of Cantor antichains, this recovers `hasCantorAntichainOn_eZero` from the
-- meagreness of `E₀` alone.
example : eZero.HasCantorAntichainOn univ :=
  eZero.hasCantorAntichainOn_univ_of_isMeagre isMeagre_eZero

