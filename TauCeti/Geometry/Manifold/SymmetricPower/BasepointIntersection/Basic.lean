/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Geometry.Manifold.SymmetricPower

/-!
# Holomorphic intersections with the basepoint divisor

For a complex curve `α`, the tuples in `Sym α n` containing a fixed point `z` form the
basepoint divisor. Near a point of this divisor, its elementary-symmetric chart equation is a
nonzero affine complex-linear functional. Composing that equation with an analytic curve gives
a holomorphic scalar function. Its order of vanishing is positive at a divisor intersection;
unless the curve lies locally in the divisor, that intersection is isolated.

This is the local positivity input for basepoint multiplicities of holomorphic disks in the
symmetric power. It does not identify the order with a global intersection number.

The divisor and its local equation are developed in
`TauCeti.Geometry.Manifold.SymmetricPower`. For the role of the basepoint divisor in Heegaard
Floer theory, see Ozsváth--Szabó, *Holomorphic disks and topological invariants for closed
three-manifolds*, §2.
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [T2Space α] [ChartedSpace ℂ α] {n : ℕ}

/-- An analytic curve through the basepoint divisor has a local holomorphic equation for that
intersection. Its nonzero linear part comes from the elementary-symmetric chart, and the
equation vanishes exactly when the unordered tuple contains the basepoint near the parameter. -/
theorem exists_analyticAt_basepointDivisor_equation
    (z : α) (f : ℂ → Sym α n) (w : ℂ)
    (hf : ContinuousAt f w)
    (ha : AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (hz : f w ∈ Sym.basepointDivisor z) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (b : ℂ) (g : ℂ → ℂ),
      ℓ ≠ 0 ∧ g = (fun t => ℓ (symChartAt (K := ℂ) (f w) (f t)) - b) ∧
      AnalyticAt ℂ g w ∧ g w = 0 ∧
      ∀ᶠ t in 𝓝 w, (f t ∈ Sym.basepointDivisor z ↔ g t = 0) := by
  let C := symChartAt (K := ℂ) (f w)
  have hw : f w ∈ C.source := mem_symChartAt_source (K := ℂ) (f w)
  obtain ⟨ℓ, b, hℓne, hℓ⟩ :=
    exists_continuousLinearMap_ne_zero_mem_iff_symChartAt (K := ℂ) z (f w)
      ⟨f w, hw, hz⟩
  refine ⟨ℓ, b, fun t => ℓ (C (f t)) - b, hℓne, rfl, ?_, ?_, ?_⟩
  · exact ((ℓ.analyticAt _).comp ha).sub analyticAt_const
  · exact sub_eq_zero.mpr ((hℓ (f w) hw).mp hz)
  · filter_upwards [hf.preimage_mem_nhds (C.open_source.mem_nhds hw)] with t ht
    simpa only [sub_eq_zero] using hℓ (f t) ht

/-- A holomorphic curve that meets the basepoint divisor has positive order of vanishing in a
local affine equation with nonzero linear part. If the order is finite, the curve avoids the
divisor at all sufficiently close other parameters; infinite order means local containment. -/
theorem basepointDivisor_intersection_order
    (z : α) (f : ℂ → Sym α n) (w : ℂ)
    (hf : ContinuousAt f w)
    (ha : AnalyticAt ℂ (fun t => symChartAt (K := ℂ) (f w) (f t)) w)
    (hz : f w ∈ Sym.basepointDivisor z) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (b : ℂ) (g : ℂ → ℂ),
      ℓ ≠ 0 ∧ g = (fun t => ℓ (symChartAt (K := ℂ) (f w) (f t)) - b) ∧
      AnalyticAt ℂ g w ∧
      (∀ᶠ t in 𝓝 w, (f t ∈ Sym.basepointDivisor z ↔ g t = 0)) ∧
      analyticOrderAt g w ≠ 0 ∧
      (analyticOrderAt g w = ⊤ ↔ ∀ᶠ t in 𝓝 w, f t ∈ Sym.basepointDivisor z) ∧
      (analyticOrderAt g w ≠ ⊤ →
        ∀ᶠ t in 𝓝[≠] w, f t ∉ Sym.basepointDivisor z) := by
  obtain ⟨ℓ, b, g, hℓne, hgeq, hg, hgw, hmem⟩ :=
    exists_analyticAt_basepointDivisor_equation z f w hf ha hz
  refine ⟨ℓ, b, g, hℓne, hgeq, hg, hmem, hg.analyticOrderAt_ne_zero.mpr hgw, ?_, ?_⟩
  · rw [analyticOrderAt_eq_top]
    constructor
    · intro hzero
      filter_upwards [hmem, hzero] with t ht hzt
      exact ht.mpr hzt
    · intro hdiv
      filter_upwards [hmem, hdiv] with t ht hzt
      exact ht.mp hzt
  · intro hfinite
    rcases hg.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact (hfinite (analyticOrderAt_eq_top.mpr hzero)).elim
    · filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, hne] with t ht hgt
      exact fun hzt => hgt (ht.mp hzt)

end TauCeti

end
