/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Basic topological lemmas for the one-point compactification

Mathlib characterizes open images under the canonical inclusion `X → OnePoint X`
(`OnePoint.isOpen_image_coe`). This file records the singleton specialization: a point of `X` is
isolated in `OnePoint X` if and only if it is isolated in `X` (`OnePoint.isOpen_singleton_coe`).
-/

public section

open Set

namespace OnePoint

/-- A singleton `{x}` of a point of `X` is open in `OnePoint X` if and only if `{x}` is open
in `X`. -/
@[simp]
theorem isOpen_singleton_coe {X : Type*} [TopologicalSpace X] {x : X} :
    IsOpen ({(x : OnePoint X)} : Set (OnePoint X)) ↔ IsOpen ({x} : Set X) := by
  rw [← image_singleton, isOpen_image_coe]

end OnePoint
