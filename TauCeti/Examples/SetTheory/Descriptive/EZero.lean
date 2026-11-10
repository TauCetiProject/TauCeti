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
# Open splitting, limit avoidance and the category method for E₀

Although E₀ is meagre in the square, every pair of nonempty open sets contains related
points, since every class is dense. Thus an open Cantor scheme cannot have nonempty,
E₀-inequivalent siblings. In contrast, Mycielski's theorem produces a continuous Cantor
antichain by avoiding E₀ only at the limit. These examples distinguish the hypotheses
of finite-stage antichain extraction from the limit-avoidance theorem.

The remaining examples exercise the Baire-category API on Cantor space through public
statements only:

* a Borel equivalence relation on Cantor space with countable classes is meagre in the square,
  by meagreness of countable sets and the Kuratowski–Ulam theorem;
* the classes of E₀ are countable and dense;
* generic ergodicity: the cylinder of points starting with `true` is clopen, neither meagre nor
  comeagre, and so is not E₀-invariant;
* Mycielski's theorem applied to the meagre graph of E₀ gives a continuous injection of Cantor
  space whose distinct points are E₀-inequivalent.

See A. S. Kechris, *Classical Descriptive Set Theory*, Theorem 19.1 (Mycielski's theorem).
-/

open Set TauCeti PiNat

-- Even disjoint nonempty open sets cannot be separated by E₀-inequivalence.
example {U V : Set (ℕ → Bool)} (hU : U.Nonempty) (hV : V.Nonempty) (hoV : IsOpen V) :
    ∃ x ∈ U, ∃ y ∈ V, eZero x y := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hxy, hyV⟩ := (dense_setOf_eZero x).exists_mem_open hoV hV
  exact ⟨x, hx, y, hyV, hxy⟩

-- In particular, no open scheme with nonempty pieces has inequivalent siblings, even
-- without imposing nesting, vanishing diameters, or branch-intersection conditions.
example (A : List Bool → Set (ℕ → Bool)) (ho : ∀ l, IsOpen (A l))
    (hne : ∀ l, (A l).Nonempty) :
    ¬ (∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ eZero x y) := by
  intro hcross
  obtain ⟨x, hx⟩ := hne [false]
  obtain ⟨y, hxy, hy⟩ := (dense_setOf_eZero x).exists_mem_open (ho [true]) (hne [true])
  exact hcross [] x hx y hy hxy

-- Mycielski nevertheless gives a Cantor antichain, independently of the explicit
-- coordinate-repetition witness in `hasCantorAntichainOn_eZero`.
example : eZero.HasCantorAntichainOn univ :=
  eZero.hasCantorAntichainOn_univ_of_isMeagre isMeagre_eZero

-- A Borel equivalence relation on Cantor space with countable classes is meagre in the square:
-- every section is a countable class, hence meagre, and Kuratowski–Ulam applies.
example {E : Setoid (ℕ → Bool)} (hE : MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | E p.1 p.2})
    (hc : ∀ x, {y | E x y}.Countable) :
    IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | E p.1 p.2} :=
  hE.baireMeasurableSet.isMeagre_of_forall_isMeagre_curry_left fun x => (hc x).isMeagre

-- The classes of E₀ are countable and dense.
example (x : ℕ → Bool) : {y | eZero x y}.Countable ∧ Dense {y | eZero x y} :=
  ⟨countable_setOf_eZero x, dense_setOf_eZero x⟩

-- Generic ergodicity rules out invariance of a set that is neither meagre nor comeagre: the
-- clopen cylinder of points starting with `true` is not E₀-invariant.
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

-- Mycielski's theorem applied to the meagre graph of E₀ gives a continuous injection of Cantor
-- space whose distinct points are E₀-inequivalent.
example : ∃ f : (ℕ → Bool) → ℕ → Bool, Continuous f ∧ Function.Injective f ∧
    ∀ a b, a ≠ b → ¬ eZero (f a) (f b) := by
  obtain ⟨f, hf, hinj, hfE⟩ := mycielski_prod isMeagre_eZero
  exact ⟨f, hf, hinj, fun a b hab => hfE a b hab⟩
