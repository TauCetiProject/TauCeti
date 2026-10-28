/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Gδ subspaces of Polish spaces are standard Borel

A Gδ subset of a Polish space, with the subspace σ-algebra, is a standard Borel space. This is
the measurable counterpart of `IsGδ.polishSpace`, used to treat sets cut out by countably many
open conditions as standard Borel spaces in their own right.
-/

public section

/-- A Gδ subset of a Polish space is a standard Borel space for the subspace σ-algebra. -/
theorem IsGδ.standardBorelSpace {α : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : IsGδ s) : StandardBorelSpace s :=
  hs.measurableSet.standardBorel
