/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Topology.Sets.Opens
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# `Lᵖ` seminorm and `MemLp` under restriction to the top open set

Spaces of functions on an open set `Ω : Opens α` are defined over `μ.restrict (Ω : Set α)`. When `f`
itself mentions `μ.restrict (⊤ : Opens α)` in its type (such as the coercion of an `Lᵖ` or Sobolev
class on `⊤`), rewriting directly with `MeasureTheory.Measure.restrict_coe_opens_top` produces an
ill-typed motive. The non-dependent lemmas `TauCeti.eLpNorm_restrict_coe_opens_top` and
`TauCeti.memLp_restrict_coe_opens_top` rewrite only the measure argument of `eLpNorm` and `MemLp`.
-/

public section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {α ε : Type*} {_ : MeasurableSpace α} [TopologicalSpace α] [ENorm ε] [TopologicalSpace ε]

/-- Restricting a measure to `(⊤ : Opens α)` leaves `eLpNorm` unchanged, without rewriting inside
the function argument. -/
theorem eLpNorm_restrict_coe_opens_top (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm f p (μ.restrict ((⊤ : Opens α) : Set α)) = eLpNorm f p μ := by
  rw [μ.restrict_coe_opens_top]

/-- Restricting a measure to `(⊤ : Opens α)` leaves `MemLp` unchanged, without rewriting inside the
function argument. -/
theorem memLp_restrict_coe_opens_top {f : α → ε} {p : ℝ≥0∞} {μ : Measure α} :
    MemLp f p (μ.restrict ((⊤ : Opens α) : Set α)) ↔ MemLp f p μ := by
  rw [μ.restrict_coe_opens_top]

end TauCeti
