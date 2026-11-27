/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.NotBorel
public import TauCeti.ModelTheory.RelationalConfiguration.UnravelOrder
public import TauCeti.ModelTheory.RelationalConfiguration.UnravelTree

/-!
# Examples: non-Borel isomorphism relations

The coded graphs, the coded linear orders and the coded trees are Borel complete, so their
isomorphism relations are not Borel. The empty class has the empty, Borel, isomorphism relation,
consistently with its not being Borel complete. At depth `0`, the codes of `ω` and of `ω · 2`
witness the failure of uniform back-and-forth separation.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration Set

-- Isomorphism of coded graphs is not Borel.
example : ¬ MeasurableSet {p : graphClass × graphClass | classIso graphClass p.1 p.2} :=
  not_measurableSet_classIso_of_borelComplete borelComplete_graphClass

-- Isomorphism of coded linear orders is not Borel.
example : ¬ MeasurableSet {p : linearOrderClass (V := ℕ) × linearOrderClass (V := ℕ) |
    classIso linearOrderClass p.1 p.2} :=
  not_measurableSet_classIso_of_borelComplete borelComplete_linearOrderClass

-- Isomorphism of coded trees is not Borel.
example : ¬ MeasurableSet {p : treeClass (V := ℕ) × treeClass (V := ℕ) |
    classIso treeClass p.1 p.2} :=
  not_measurableSet_classIso_of_borelComplete borelComplete_treeClass

-- The empty class has a Borel isomorphism relation and is not Borel complete.
example : MeasurableSet {p : (∅ : Set (RelationalConfiguration Language.order ℕ)) ×
      (∅ : Set (RelationalConfiguration Language.order ℕ)) | classIso ∅ p.1 p.2} ∧
    ¬ BorelComplete (∅ : Set (RelationalConfiguration Language.order ℕ)) :=
  ⟨Set.Subsingleton.measurableSet fun p ↦ p.1.property.elim, not_borelComplete_empty⟩

-- At every countable depth, two non-isomorphic coded linear orders are back-and-forth equivalent.
example : ∃ c ∈ linearOrderClass (V := ℕ), ∃ d ∈ linearOrderClass (V := ℕ),
    ¬ isoSetoid Language.order ℕ c d ∧ bfEquivSetoid Language.order ℕ (0 : Ordinal.{0}) c d :=
  exists_not_isoSetoid_bfEquivSetoid (Ordinal.omega_pos 1)
