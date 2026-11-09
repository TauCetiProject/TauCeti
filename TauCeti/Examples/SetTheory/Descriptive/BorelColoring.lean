/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Real.Cardinality
import TauCeti.SetTheory.Descriptive.BorelColoring
import TauCeti.SetTheory.Descriptive.EZero
import TauCeti.SetTheory.Descriptive.GSGraph
import TauCeti.SetTheory.Descriptive.SmallFamily.Basic

/-!
# Regression examples: countable Borel colorings

These examples exercise the coloring API from a downstream module, through public statements
only:

* inequality of first coordinates, on Cantor space and on Baire space, is colored by the first
  coordinate;
* the inequality relation on `ℝ` has no countable Borel coloring, since equality on `ℝ` has
  uncountably many classes;
* the inequivalence relation of `E₀` has no countable Borel coloring, since `E₀` has continuum
  many classes;
* for a Borel equivalence relation, the inequivalence relation has a countable Borel coloring
  exactly when there are countably many classes, and otherwise the family of all assignments
  `Fin 1 → X` is not small for it, the seed of the `G₀` construction;
* a relation with a loop has no coloring, and the empty set is independent for it;
* `G₀` has no measurable coloring by `ℕ`, while `gSGraph {[]}` is colored by the first
  coordinate;
* density is needed for exclusivity in the `G₀` dichotomy: the word set `{[]}` is sparse but not
  dense, the identity sends `orientedGS {[]}` to itself, and `orientedGS {[]}` has a countable
  Borel coloring.
-/

open MeasureTheory TauCeti

-- Inequality of first coordinates on Cantor space: the first coordinate is a two-color Borel
-- coloring.
example : SetRel.HasCountableBorelColoring {p : (ℕ → Bool) × (ℕ → Bool) | p.1 0 ≠ p.2 0} :=
  SetRel.hasCountableBorelColoring_iff.2
    ⟨fun x ↦ Encodable.encode (x 0),
      (measurable_of_countable Encodable.encode).comp (measurable_pi_apply 0),
      fun _ _ h heq ↦ h (Encodable.encode_injective heq)⟩

-- Inequality of first coordinates on Baire space: the first coordinate is a countable Borel
-- coloring.
example : SetRel.HasCountableBorelColoring {p : (ℕ → ℕ) × (ℕ → ℕ) | p.1 0 ≠ p.2 0} :=
  SetRel.hasCountableBorelColoring_iff.2 ⟨fun x ↦ x 0, measurable_pi_apply 0, fun _ _ h ↦ h⟩

-- Equality on `ℝ` has uncountably many classes, so its inequivalence relation, inequality, has no
-- countable Borel coloring.
example : ¬ SetRel.HasCountableBorelColoring {p : ℝ × ℝ | p.1 ≠ p.2} := by
  intro h
  have := (⊥ : Setoid ℝ).countable_quotient_of_hasCountableBorelColoring_not
    (by simpa [Setoid.bot_def] using h)
  exact Cardinal.not_countable_real
    (Set.countable_univ_iff.2 Setoid.quotientBotEquiv.symm.injective.countable)

-- For a Borel equivalence relation, whose classes are therefore Borel, the inequivalence relation
-- has a countable Borel coloring exactly when there are countably many classes.
example {X : Type*} [MeasurableSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E p.1 p.2}) :
    SetRel.HasCountableBorelColoring {p : X × X | ¬ E p.1 p.2} ↔ Countable (Quotient E) :=
  Setoid.hasCountableBorelColoring_not_iff.trans
    (and_iff_left fun _ ↦ measurable_prodMk_left hE)

-- With uncountably many classes, the family of all one-point assignments is not small for the
-- inequivalence relation.
example {X : Type*} [MeasurableSpace X] (E : Setoid X) (hc : ¬ Countable (Quotient E)) :
    ¬ SetRel.IsSmallFamily {p : X × X | ¬ E p.1 p.2} (Set.univ : Set (Fin 1 → X)) :=
  SetRel.isSmallFamily_univ_iff.not.2 fun h ↦
    hc (E.countable_quotient_of_hasCountableBorelColoring_not h)

-- The diagonal relation on `ℕ` has a loop at every point, so it has no coloring, although the
-- empty set is still independent for it.
example : ¬ SetRel.HasCountableBorelColoring (SetRel.id : SetRel ℕ ℕ) ∧
    (SetRel.id : SetRel ℕ ℕ).IsIndependent ∅ :=
  ⟨SetRel.not_hasCountableBorelColoring_of_mem (x := 0) rfl, SetRel.IsIndependent.empty⟩

-- `E₀` has continuum many classes, so its inequivalence relation has no countable Borel coloring.
example : ¬ SetRel.HasCountableBorelColoring {p : (ℕ → Bool) × (ℕ → Bool) | ¬ eZero p.1 p.2} := by
  intro h
  have := eZero.countable_quotient_of_hasCountableBorelColoring_not h
  have hle := Cardinal.mk_le_aleph0 (α := Quotient eZero)
  rw [mk_quotient_eZero] at hle
  exact Cardinal.aleph0_lt_continuum.not_ge hle

-- `G₀` has no measurable coloring by `ℕ`.
example : ¬ ∃ c : gZero.Coloring ℕ, Measurable c :=
  not_exists_measurable_coloring_gZero

-- `gSGraph {[]}` has a continuous coloring by `Bool`, and adjacent points differ at the first
-- coordinate.
example : ∃ c : (gSGraph {[]}).Coloring Bool, Continuous c :=
  exists_continuous_coloring_gSGraph (by simp)

example {a b : ℕ → Bool} (h : (gSGraph {[]}).Adj a b) : a 0 ≠ b 0 := by
  have key {a b : ℕ → Bool} (h : (a, b) ∈ orientedGS {[]}) : a 0 ≠ b 0 := by
    obtain ⟨s, rfl, -, rfl⟩ := mem_orientedGS_iff_exists_flipAt.1 h
    simp [PiNat.flipAt_apply_self]
  exact (gSGraph_adj_iff.1 h).elim key fun h ↦ (key h).symm

-- Density is needed for exclusivity in the `G₀` dichotomy: `{[]}` is sparse but not dense, the
-- identity is a continuous homomorphism from `orientedGS {[]}` to itself, and yet
-- `orientedGS {[]}` has a countable Borel coloring.
example : SparseWords {[]} ∧ ¬ DenseWords {[]} ∧
    SetRel.HasCountableBorelColoring (orientedGS {[]}) ∧
    ∃ φ : (ℕ → Bool) → ℕ → Bool, Continuous φ ∧
      ∀ ⦃y z⦄, (y, z) ∈ orientedGS {[]} → (φ y, φ z) ∈ orientedGS {[]} := by
  have hfin : (List.length '' {([] : List Bool)}).Finite := by simp
  exact ⟨sparseWords_iff.2 (by simp), fun h ↦ h.infinite_image_length hfin,
    hasCountableBorelColoring_orientedGS hfin, id, continuous_id, fun _ _ h ↦ h⟩
