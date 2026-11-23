/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Laplacian.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.MeasureTheory.Function.LpSeminorm.Exp

/-!
# Regularity for the semilinear equation `Δv = c (exp v - 1) + g`

Let `E` be a finite-dimensional real inner product space of dimension at most three. If a bounded
real `C²` function `v ∈ L²(E)` solves

`Δv = c (exp v - 1) + g`

classically, with `g ∈ L² ∩ H^s`, then `v ∈ L² ∩ H^{s+2}`
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add`).
Since `v` is bounded, `exp v - 1` is square integrable (`MeasureTheory.MemLp.exp_sub_one`), so
`Δv ∈ L²` and elliptic regularity of the classical Laplacian
(`TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian`) gives `v ∈ H²`. From then on
`H^t(E)`, `t ≥ 2`, is closed under `w ↦ exp w - 1`
(`TemperedDistribution.exp_sub_one_mem_realSobolevFunctions`), so `Δv` gains regularity up to that
of `g`, and `v` gains two derivatives at each step. On the plane this equation is the scalar
equation `Δ log |α|² = (|α|² - 1) / 4` satisfied by the logarithmic modulus of a vortex section
away from its zeros, with `c = 1 / 4`.

## Main results

* `TemperedDistribution.mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add`:
  bounded `L²` solutions of `Δv = c (exp v - 1) + g`, with `g ∈ L² ∩ H^s`, lie in `L² ∩ H^{s+2}`,
  in dimension at most three.

## References

* M. E. Taylor, *Partial Differential Equations III*, 2nd ed., Springer, 2011, Chapter 13
  (composition estimates in `H^s`) and Chapter 14 (regularity for nonlinear elliptic equations).
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory Module
open scoped Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Regularity for `Δv = c (exp v - 1) + g`.** In dimension at most three, a bounded real `C²`
function `v ∈ L²(E)` solving `Δv = c (exp v - 1) + g` classically, with `g ∈ L² ∩ H^s`, lies in
`L² ∩ H^{s+2}`. -/
theorem mem_realSobolevFunctions_add_two_of_laplacian_eq_mul_exp_sub_one_add
    (hE : finrank ℝ E < 4) {s : ℝ} {v g : E → ℝ} {c C : ℝ} (hv : ContDiff ℝ 2 v)
    (hv2 : MemLp v 2 volume) (hvC : ∀ x, |v x| ≤ C) (hg : g ∈ realSobolevFunctions E s 2)
    (heq : ∀ x, Δ v x = c * (Real.exp (v x) - 1) + g x) :
    v ∈ realSobolevFunctions E (s + 2) 2 := by
  have hΔ : Δ v = c • (fun x ↦ Real.exp (v x) - 1) + g := by
    ext x
    simp only [heq x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmono {t t' : ℝ} (h : t' ≤ t) := realSobolevFunctions_mono (E := E) (p := 2)
    (by norm_num) (by norm_num) h
  -- The base case `v ∈ H²`: since `v` is bounded, `exp v - 1 ∈ L²`, so `Δv ∈ L²`.
  have hbase : v ∈ realSobolevFunctions E 2 2 := by
    have h := mem_realSobolevFunctions_add_two_of_laplacian (s := 0) hv
      (mem_realSobolevFunctions_zero_iff.2 hv2) (by
        rw [hΔ, mem_realSobolevFunctions_zero_iff]
        exact ((hv2.exp_sub_one (.of_forall hvC)).const_smul c).add
          (memLp_of_mem_realSobolevFunctions hg))
    rwa [zero_add] at h
  have hE' : (finrank ℝ E : ℝ) < 4 := by exact_mod_cast hE
  rcases le_or_gt s 0 with hs | hs
  · exact hmono (by linarith) hbase
  -- For `s > 0`, each step gains two derivatives up to the regularity of `g`:
  -- `v ∈ H^{min s (2n) + 2}` for every `n`.
  have hall (n : ℕ) : v ∈ realSobolevFunctions E (min s (2 * n) + 2) 2 := by
    induction n with
    | zero => exact hmono (by simp) hbase
    | succ n ih =>
      have ht : (finrank ℝ E : ℝ) < 2 * (min s (2 * n) + 2) := by
        have : (0 : ℝ) ≤ min s (2 * n) := le_min hs.le (by positivity)
        linarith
      have hr : min s (2 * ((n + 1 : ℕ) : ℝ)) ≤ min s (2 * n) + 2 := by
        rw [← min_add_add_right]
        exact le_min ((min_le_left _ _).trans (by linarith))
          ((min_le_right _ _).trans (by push_cast; linarith))
      have hexp := exp_sub_one_mem_realSobolevFunctions ht ih
      refine mem_realSobolevFunctions_add_two_of_laplacian hv (hmono hr ih) ?_
      rw [hΔ]
      exact add_mem (Submodule.smul_mem _ c (hmono hr hexp)) (hmono (min_le_left _ _) hg)
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  have h := hall n
  rwa [min_eq_left (by linarith)] at h

end TemperedDistribution
