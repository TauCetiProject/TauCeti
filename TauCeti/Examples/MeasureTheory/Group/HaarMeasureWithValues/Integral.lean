/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Rat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.Topology.Algebra.Group.Basic
import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Integral

/-!
# Examples of integration against a Haar measure with values in a ring

This file tests `TauCeti.HaarMeasureWithValues.integral`:

* the integral of the indicator `1_U • a` is `μ(U) a`, for scalar and module coefficients;
* a zero indicator has integral zero, and every integral vanishes over the zero coefficient ring;
* with a finite discrete group and counting volume, the integral is `∑_g f(g)`;
* for `C₂ = {1, s}` with counting volume, the integral is `f(1) + f(s)`, with values in `ℤ` and in
  the `ℚ`-module `ℚ × ℚ`.
-/

open TopologicalSpace LocallyConstant

namespace TauCeti.HaarMeasureWithValues

variable {A G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-! ### 1. Indicators -/

section Indicator

variable [CommRing A] (μ : HaarMeasureWithValues A G) (U : CompactOpens G)

example (a : A) :
    μ.integral ⟨compactOpenIndicator U a, compactOpenIndicator_mem_compactlySupported U a⟩ =
      μ U * a := by
  simp

example {M : Type*} [AddCommGroup M] [Module A M] (m : M) :
    μ.integral ⟨compactOpenIndicator U m, compactOpenIndicator_mem_compactlySupported U m⟩ =
      μ U • m := by
  simp

example {M : Type*} [AddCommGroup M] [Module A M] :
    μ.integral ⟨compactOpenIndicator U (0 : M), compactOpenIndicator_mem_compactlySupported U 0⟩ =
      0 := by
  have h : (⟨compactOpenIndicator U (0 : M), compactOpenIndicator_mem_compactlySupported U 0⟩ :
      compactlySupported A G M) = 0 :=
    Subtype.ext (compactOpenIndicator_zero U)
  rw [h, map_zero]

/-- Over the zero ring every integral vanishes. -/
example (ν : HaarMeasureWithValues PUnit G) (f : compactlySupported PUnit G PUnit) :
    ν.integral f = 0 :=
  Subsingleton.elim _ _

end Indicator

/-! ### 2. Finite discrete groups with counting volume -/

section Discrete

variable [DiscreteTopology G] [Fintype G] [CommRing A] (μ : HaarMeasureWithValues A G)

/-- Counting volume gives each point volume `1`, so the integral is the sum of the values. -/
example (h1 : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
    (f : compactlySupported A G A) :
    μ.integral f = ∑ g, (f : LocallyConstant G A) g := by
  rw [integral_eq_smul_sum_of_discrete, h1, one_smul]

end Discrete

/-! ### 3. The group of order two -/

section C2

/-- With counting volume on `C₂ = {1, s}`, the integral is `f(1) + f(s)`. -/
example (μ : HaarMeasureWithValues ℤ (Multiplicative (ZMod 2)))
    (h1 : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
    (f : compactlySupported ℤ (Multiplicative (ZMod 2)) ℤ) :
    μ.integral f = (f : LocallyConstant (Multiplicative (ZMod 2)) ℤ) 1 +
      (f : LocallyConstant (Multiplicative (ZMod 2)) ℤ) (Multiplicative.ofAdd 1) := by
  rw [integral_eq_smul_sum_of_discrete, h1, one_smul,
    Fintype.sum_eq_add 1 (Multiplicative.ofAdd 1) (by decide) fun x hx ↦ by
      fin_cases x
      exacts [(hx.1 rfl).elim, (hx.2 rfl).elim]]

/-- With counting volume on `C₂` and values in the `ℚ`-module `ℚ × ℚ`, the integral is the vector
sum `f(1) + f(s)`. -/
example (μ : HaarMeasureWithValues ℚ (Multiplicative (ZMod 2)))
    (h1 : μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ = 1)
    (f : compactlySupported ℚ (Multiplicative (ZMod 2)) (ℚ × ℚ)) :
    μ.integral f = (f : LocallyConstant (Multiplicative (ZMod 2)) (ℚ × ℚ)) 1 +
      (f : LocallyConstant (Multiplicative (ZMod 2)) (ℚ × ℚ)) (Multiplicative.ofAdd 1) := by
  rw [integral_eq_smul_sum_of_discrete, h1, one_smul,
    Fintype.sum_eq_add 1 (Multiplicative.ofAdd 1) (by decide) fun x hx ↦ by
      fin_cases x
      exacts [(hx.1 rfl).elim, (hx.2 rfl).elim]]

end C2

end TauCeti.HaarMeasureWithValues
