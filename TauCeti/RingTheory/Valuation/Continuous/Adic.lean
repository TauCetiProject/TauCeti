/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology
import TauCeti.RingTheory.Valuation.SpanPow

/-!
# Continuity of real valuations on adic rings

Let `A` be a ring whose topology is the `I`-adic one, for an ideal `I = Ideal.span s`. A valuation
`v : Valuation A ℝ≥0` that is at most `1` on `I` and at most some `c < 1` on the generators `s` is
continuous: by `Valuation.map_le_pow_of_mem_span_pow_succ` it is at most `c ^ N` on `I ^ (N + 1)`,
and these open ideals form a basis of neighbourhoods of `0`. This is how rank-one points of adic
spectra, such as the Gauss points of `Spa(A_inf, A_inf)`, are shown to be continuous.

## Main results

* `Valuation.isContinuous_of_isAdic` : the continuity criterion.
-/

public section

open scoped NNReal

namespace Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] {v : Valuation A ℝ≥0} {s : Set A}
  {c : ℝ≥0}

/-- **Continuity of real valuations on adic rings.** If the topology of `A` is the `I`-adic one
for `I = Ideal.span s`, a valuation `v : Valuation A ℝ≥0` that is at most `1` on `I` and at most
some `c < 1` on `s` is continuous. -/
theorem isContinuous_of_isAdic (hI : IsAdic (Ideal.span s)) (h1 : ∀ a ∈ Ideal.span s, v a ≤ 1)
    (hc : c < 1) (hs : ∀ t ∈ s, v t ≤ c) : v.IsContinuous := by
  have : IsTopologicalRing A := hI ▸ (Ideal.span s).nonarchimedean.toIsTopologicalRing
  refine isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  obtain ⟨N, hN⟩ := NNReal.exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr hγ) hc
  exact AddSubgroup.isOpen_mono (H₁ := (Ideal.span s ^ (N + 1)).toAddSubgroup)
    (H₂ := v.ltAddSubgroup (Units.mk0 γ hγ))
    (fun a ha ↦ (v.map_le_pow_of_mem_span_pow_succ hs h1 ha).trans_lt hN) (hI.isOpen_pow _)

end Valuation
