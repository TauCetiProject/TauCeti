/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Jet
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Small restriction on a subspace of finite codimension

If the first `n + 1` derivatives of a bounded holomorphic function vanish at the centre of
a disc of radius `R`, its norm on the concentric disc of radius `r < R` is at most
`(r / R) ^ (n + 1)` times its bound on the larger disc. Thus restriction is arbitrarily
small after imposing finitely many linear conditions. The subspace is the kernel of a
finite jet, so its finite codimension is part of the conclusion, rather than an assumption.

This is the local estimate used in finite-cover proofs of finiteness of analytic cohomology.
The proof uses Mathlib's higher-order Schwarz lemma and its derivative characterization of
vanishing order; no Banach space of bounded holomorphic functions is introduced.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §14, for the use of small restriction
  outside a finite-dimensional space of Taylor coefficients.
-/

public noncomputable section

open Asymptotics Filter Metric Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

/-- Use the inherited additive group, matching the group fixed by the jet map when forming
submodule quotients. -/
local instance (U : Opens ℂ) : AddCommGroup (holomorphicFunctions U) := inferInstance

variable {U : Opens ℂ} {a : ℂ} {R r M : ℝ}

/-- Higher-order Schwarz estimate on the kernel of a finite jet. The bound is uniform on
the smaller closed disc, and only boundedness on the larger open disc is required. -/
theorem norm_le_mul_pow_of_mem_ker_jet (hR : 0 < R) (hU : ball a R ⊆ U)
    (hr : r < R) (n : ℕ) (f : holomorphicFunctions U)
    (hf : f ∈ (jet (hU (mem_ball_self hR)) (n + 1)).ker)
    (hM : ∀ z ∈ ball a R, ‖extend f z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall a r) :
    ‖extend f z‖ ≤ M * (r / R) ^ (n + 1) := by
  have ha := hU (mem_ball_self hR)
  have hana := (analyticOnNhd_extend (Subset.refl _) f) a ha
  have horder := (jet_eq_zero_iff ha (n + 1) f).mp (LinearMap.mem_ker.mp hf)
  obtain ⟨g, hg, heq⟩ := (natCast_le_analyticOrderAt hana).mp horder
  have hf0 : extend f a = 0 := by
    simpa using heq.self_of_nhds
  have hbig : (extend f) =O[𝓝 a] fun w ↦ ‖w - a‖ ^ (n + 1) := by
    have h := (isBigO_refl (fun w : ℂ ↦ (w - a) ^ (n + 1)) (𝓝 a)).smul
      (hg.continuousAt.tendsto.isBigO_one ℂ)
    have h' : extend f =O[𝓝 a] fun w ↦ (w - a) ^ (n + 1) := by
      simpa only [smul_eq_mul, mul_one] using
        h.congr' (Filter.EventuallyEq.symm heq) EventuallyEq.rfl
    simpa only [norm_pow] using h'.norm_right
  have hlittle : (fun w ↦ extend f w - extend f a) =o[𝓝 a] fun w ↦ ‖w - a‖ ^ n := by
    simpa only [hf0, sub_zero] using
      hbig.trans_isLittleO (isLittleO_pow_sub_pow_sub a n.lt_succ_self)
  have hest := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    ((differentiableOn_extend f).mono hU)
    (fun w hw ↦ by simpa [hf0, mem_closedBall, dist_zero_right] using hM w hw)
    hlittle (closedBall_subset_ball hr hz)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a (mem_ball_self hR))
  simpa only [hf0, dist_zero_right] using hest.trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg dist_nonneg hR.le)
        (div_le_div_of_nonneg_right (mem_closedBall.mp hz) hR.le) _) hM0)

/-- Restriction from a disc to a strictly smaller concentric closed disc is arbitrarily
small on a subspace of finite codimension. Its elements satisfy the same estimate for
every bound `M` on the original disc. -/
theorem exists_finiteDimensional_quotient_norm_le (hR : 0 < R) (hU : ball a R ⊆ U)
    (hr0 : 0 ≤ r) (hr : r < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Submodule ℂ (holomorphicFunctions U),
      FiniteDimensional ℂ (holomorphicFunctions U ⧸ K) ∧
      ∀ f ∈ K, ∀ M : ℝ, (∀ z ∈ ball a R, ‖extend f z‖ ≤ M) →
        ∀ z ∈ closedBall a r, ‖extend f z‖ ≤ ε * M := by
  have hq0 : 0 ≤ r / R := div_nonneg hr0 hR.le
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hr
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually
    (gt_mem_nhds hε) |>.exists
  let K := (jet (hU (mem_ball_self hR)) (n + 1)).ker
  refine ⟨K, inferInstance, fun f hf M hM z hz ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a (mem_ball_self hR))
  refine (norm_le_mul_pow_of_mem_ker_jet hR hU hr n f hf hM hz).trans ?_
  rw [mul_comm ε M]
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ n)).trans hn.le) hM0

end TauCeti.HolomorphicFunctions
