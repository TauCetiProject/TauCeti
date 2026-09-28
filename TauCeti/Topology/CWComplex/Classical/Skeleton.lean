/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Skeletal objects of relative CW complexes

The stages of a relative CW complex's skeletal filtration, bundled as topological spaces.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

open Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The `n`-th stage of the skeletal filtration, as an object of `TopCat`. -/
abbrev skeletonObj (n : ℕ) : TopCat.{w} := TopCat.of (skeletonLT C (n : ℕ∞) : Set X)

end TauCeti
