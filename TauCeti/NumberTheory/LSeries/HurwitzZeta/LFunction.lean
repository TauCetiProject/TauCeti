/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Continuation
public import TauCeti.NumberTheory.LSeries.ZMod.LFunction
import TauCeti.Data.ZMod.Count
import TauCeti.NumberTheory.LSeries.HurwitzZeta.ZetaComparison

/-!
# Finite complex-Hurwitz decomposition of continued periodic L-functions

Reindexing `ZMod N` over positive residue representatives `a ∈ Finset.Icc 1 N` expresses
`ZMod.LFunction Φ s` (for `Φ : ZMod N → ℂ`, applying in particular to any Dirichlet character
`χ : DirichletCharacter ℂ N`, whose `χ.LFunction` is definitionally `ZMod.LFunction χ`) in terms
of the continued complex Hurwitz zeta function `TauCeti.complexHurwitzZeta s ((a : ℂ) / N)` away
from `s = 1`, and at `s = 1` as well when `∑ j, Φ j = 0` (including all nontrivial Dirichlet
characters), where the common polar term cancels.

See `TauCeti.NumberTheory.LSeries.ZMod.LFunction` for the underlying circle-Hurwitz and transport
lemmas, and `TauCeti.NumberTheory.LSeries.HurwitzZeta.ZMod` for the convergent
`TauCeti.complexHurwitzSeries` decomposition.

## Main results

* `ZMod.LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for `s ≠ 1 ∨ ∑ j, Φ j = 0` in terms of `TauCeti.complexHurwitzZeta`.
-/

public section

open Complex Filter Set
open scoped Topology

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- When `s ≠ 1` or `∑ j, Φ j = 0`, `ZMod.LFunction Φ s` is `(N : ℂ) ^ (-s)` times the finite sum
of `Φ a * TauCeti.complexHurwitzZeta s (a / N)` over `a ∈ {1, ..., N}`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) := by
  have hne : ∀ {w : ℂ}, w ≠ 1 →
      ZMod.LFunction Φ w =
        (N : ℂ) ^ (-w) *
          ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzZeta w ((a : ℂ) / N) := by
    intro w hw
    refine LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta Φ w fun a ha => ?_
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    simpa [Complex.ofReal_div, Complex.ofReal_natCast] using
      TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hw
        ⟨div_pos (Nat.cast_pos.mpr ha1) hN, (div_le_one hN).mpr (Nat.cast_le.mpr haN)⟩
  rcases ne_or_eq s 1 with hs_ne | rfl
  · exact hne hs_ne
  · have hΦ : ∑ j, Φ j = 0 := hs.neg_resolve_left rfl
    have hsum : ∑ a ∈ Finset.Icc 1 N, Φ a = 0 := by rwa [← ZMod.sum_eq_sum_Icc]
    let g : ℂ → ℂ → ℂ := fun w c =>
      TauCeti.complexHurwitzZeta w c - (Complex.Gamma w)⁻¹ / (w - 1)
    let R : ℂ → ℂ := fun w =>
      (N : ℂ) ^ (-w) * ∑ a ∈ Finset.Icc 1 N, Φ a * g w ((a : ℂ) / N)
    have hR_eq (w : ℂ) :
        R w = (N : ℂ) ^ (-w) *
          ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzZeta w ((a : ℂ) / N) := by
      dsimp [R, g]
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
    have hL_cont : ContinuousAt (ZMod.LFunction Φ) 1 :=
      (ZMod.differentiableAt_LFunction Φ 1 (Or.inr hΦ)).continuousAt
    have hR_cont : ContinuousAt R 1 := by
      refine ContinuousAt.mul ?_ (tendsto_finsetSum _ fun a ha => ?_)
      · exact ContinuousAt.const_cpow continuousAt_neg (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
      · have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        have hre : 0 < ((a : ℂ) / N).re := by
          have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
          simpa using div_pos (Nat.cast_pos.mpr ha1) hN
        have hg : AnalyticAt ℂ (fun w => g w ((a : ℂ) / N)) 1 :=
          (TauCeti.analyticOnNhd_complexHurwitzZeta_sub_inv_Gamma_div (1, (a : ℂ) / N) hre).comp
            (f := fun w : ℂ => (w, (a : ℂ) / N)) (analyticAt_id.prod analyticAt_const)
        exact continuousAt_const.mul hg.continuousAt
    have heq_nhdsNE : ZMod.LFunction Φ =ᶠ[𝓝[≠] 1] R :=
      eventually_mem_nhdsWithin.mono fun w hw => by rw [hne hw, hR_eq]
    rw [← hR_eq 1]
    exact ((hL_cont.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hR_cont).mp heq_nhdsNE).eq_of_nhds

end ZMod

end
