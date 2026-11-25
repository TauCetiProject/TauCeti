/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.LowPass

/-!
# The closure of the Schwartz functions in the Besov spaces `B^s_{p,q}`, `q < ∞`

For a finite fine index `q`, an element `u` of the inhomogeneous Besov space `B^s_{p,q}` lies in
the closure of the Schwartz functions exactly when each of its Littlewood–Paley blocks `Δⱼ u` is
an `Lᵖ` limit of Schwartz functions
(`TauCeti.BesovSpace.mem_closure_range_toBesovSpaceCLM_iff`). This holds for every
`1 ≤ p ≤ ∞`, including `p = ∞`. For `p < ∞` the condition on the blocks always holds, which
recovers the density of the Schwartz functions in `B^s_{p,q}` for `p, q < ∞`
(`SchwartzMap.denseRange_toBesovSpaceCLM`). This is the `q < ∞` counterpart of the
characterisation of the little Besov space `b^s_{p,∞}` (`TauCeti.BesovSpace.mem_littleBesov_iff`).

Both finiteness conditions matter. For `q = ∞` the closure of the Schwartz functions is the
little Besov space `b^s_{p,∞}` (`TauCeti.BesovSpace.littleBesov`), cut out by the additional
decay `2^{js} ‖Δⱼ u‖_p → 0`, which a general element of `B^s_{p,∞}` does not have. For `p = ∞`
the closure of the Schwartz functions in `L^∞` consists of continuous functions vanishing at
infinity, and the constant function `1`, whose block `Δ₀ 1` is `1`, is not of this kind.

## The argument

For `q < ∞` the dyadic partial sums `S_m u = ∑_{k < m} Δₖ u` converge to `u` in `B^s_{p,q}`
(`TauCeti.BesovSpace.tendsto_partialSumCLM`). If the blocks of `u` are `Lᵖ` limits of Schwartz
functions, so is the finite sum `S_m u` (`TauCeti.BesovSpace.lowPass_mem_closure_range_toLp`);
being band-limited, it lies in the little Besov space `b^{s+1}_{p,∞}`
(`TauCeti.BesovSpace.mem_littleBesov_of_toDistr_eq`), the closure of the Schwartz functions in
`B^{s+1}_{p,∞}`. The continuous inclusion `B^{s+1}_{p,∞} ⊆ B^s_{p,q}` maps it into the closure of
the Schwartz functions in `B^s_{p,q}`, and so does the limit `u` of the `S_m u`.

## Main declarations

* `TauCeti.BesovSpace.mem_closure_range_toBesovSpaceCLM_iff`: for `q < ∞`, `u` is a limit of
  Schwartz functions in `B^s_{p,q}` exactly when its blocks are limits of Schwartz functions in
  `Lᵖ`.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.3.3.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
-/

public section

noncomputable section

open Filter Topology MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **The closure of the Schwartz functions in `B^s_{p,q}`, `q < ∞`, is cut out by the blocks:**
`u` is a limit of Schwartz functions in `B^s_{p,q}` exactly when every block `Δⱼ u` is a limit of
Schwartz functions in `Lᵖ`. For `q = ∞` the closure is the little Besov space, which also requires
the decay `2^{js} ‖Δⱼ u‖_p → 0` (`TauCeti.BesovSpace.mem_littleBesov_iff`). -/
theorem mem_closure_range_toBesovSpaceCLM_iff (hq : q ≠ ∞) {u : BesovSpace F φ s p q} :
    u ∈ closure (Set.range (SchwartzMap.toBesovSpaceCLM F φ s p q)) ↔
      ∀ j, u.block j ∈ closure (Set.range fun f : 𝓢(E, F) ↦ f.toLp p) := by
  refine ⟨block_mem_closure_of_mem_closure_range_toBesovSpaceCLM, fun hblock ↦ ?_⟩
  obtain ⟨L, hL⟩ := exists_littlewoodPaleyBlock_lowPass_eq_zero (F := F) (φ := φ)
  refine isClosed_closure.mem_of_tendsto (tendsto_partialSumCLM hq u)
    (Eventually.of_forall fun m ↦ ?_)
  -- `S_m u` comes from `B^{s+1}_{p,∞}`, where it is a band-limited `Lᵖ` limit of Schwartz
  -- functions and hence lies in the little Besov space `b^{s+1}_{p,∞}`.
  obtain ⟨x, hx⟩ := partialSumCLM_mem_range_inclusionOfLT (lt_add_one s) ∞ m u
  have hxw : x.toDistr = u.lowPass m := by
    rw [coe_lowPass, littlewoodPaleyLowPass_apply, ← toDistr_partialSumCLM, ← hx,
      toDistr_inclusionOfLT]
  have hxl := mem_littleBesov_of_toDistr_eq hxw (lowPass_mem_closure_range_toLp hblock m)
    fun k hk ↦ hL u m k hk
  rw [← SetLike.mem_coe, coe_littleBesov] at hxl
  rw [← hx]
  exact map_mem_closure_range_toBesovSpaceCLM _ (toDistr_inclusionOfLT _) hxl

end TauCeti.BesovSpace
