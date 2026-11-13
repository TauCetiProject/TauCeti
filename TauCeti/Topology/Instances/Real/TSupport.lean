/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Support

/-!
# Supports inside an open interval and a strip

A function on `ℝ` whose topological support is contained in `(0, R)` has its support inside
`(0, R')` for some `R' < R`: the support is closed and the interval is a ball in a proper space.

A function on a strip `ℝ × X` vanishing whenever the first coordinate lies outside `(a, b)` has
its topological support in the closed strip `[a, b] × X`, so it vanishes near every point outside
that strip.

## Main results

* `TauCeti.exists_lt_tsupport_subset_Ioo`: the support shrinks to `(0, R')` with `R' < R`.
* `TauCeti.eventuallyEq_zero_of_forall_fst_notMem_Icc`: a function on `ℝ × X` vanishing for
  `s ∉ (a, b)` vanishes near every point whose first coordinate is outside `[a, b]`.
-/

public section

namespace TauCeti

open Metric Set
open scoped Topology

variable {R : ℝ} {F : Type*} [Zero F]

/-- A test function `ψ` supported in `(0, R)` is supported in some `(0, R')` with `R' < R`. -/
lemma exists_lt_tsupport_subset_Ioo (hR : 0 < R) {ψ : ℝ → F}
    (hψs : tsupport ψ ⊆ Ioo 0 R) : ∃ R', 0 < R' ∧ R' < R ∧ tsupport ψ ⊆ Ioo 0 R' := by
  have hball : Ioo (0 : ℝ) R = ball (R / 2) (R / 2) := by
    rw [Real.ball_eq_Ioo]
    congr 1 <;> ring
  obtain ⟨r, hr, hψr⟩ :=
    exists_pos_lt_subset_ball (half_pos hR) (isClosed_tsupport ψ) (hball ▸ hψs)
  rw [Real.ball_eq_Ioo] at hψr
  exact ⟨R / 2 + r, by linarith [hr.1], by linarith [hr.2],
    hψr.trans (Ioo_subset_Ioo (by linarith [hr.2]) le_rfl)⟩

/-- A function on `ℝ × X` vanishing for `s ∉ (a, b)` vanishes near every point with `s ∉ [a, b]`,
outside the closed strip `[a, b] × X` containing its support. -/
theorem eventuallyEq_zero_of_forall_fst_notMem_Icc {X : Type*} [TopologicalSpace X]
    {f : ℝ × X → F} {a b : ℝ} (hf : ∀ s x, s ∉ Ioo a b → f (s, x) = 0) {z : ℝ × X}
    (hz : z.1 ∉ Icc a b) : f =ᶠ[𝓝 z] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz <|
    closure_minimal (t := Prod.fst ⁻¹' Icc a b) (Function.support_subset_iff'.2 fun w hw ↦
      hf w.1 w.2 fun h ↦ hw (Ioo_subset_Icc_self h)) (isClosed_Icc.preimage continuous_fst) h

end TauCeti
