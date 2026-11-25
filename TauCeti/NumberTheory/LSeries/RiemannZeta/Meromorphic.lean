/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Meromorphic.Order

/-!
# Meromorphy, pole order, and zeros of the Riemann zeta function

Mathlib's `riemannZeta` is analytic away from `s = 1` (`analyticOn_riemannZeta`) and
decomposes away from `1` as `(s - 1)⁻¹ + riemannZeta₀ s` with `riemannZeta₀` entire
(`riemannZeta_eq_inv_sub_add`, `differentiable_riemannZeta₀`). Consequently `riemannZeta` is
meromorphic on `ℂ`. Its residue at `s = 1` (`riemannZeta_residue_one`) reads off its simple pole
of order `-1` at `s = 1`, and analyticity away from `1` together with `riemannZeta_one_ne_zero`
characterizes positive meromorphic order by `riemannZeta s = 0`. Every closed disc whose radius
is less than the distance `|Im c|` from its centre `c` to the real axis avoids the pole, so
`riemannZeta` is analytic on it, and nonvanishing on `1 ≤ Re s`
(`riemannZeta_ne_zero_of_one_le_re`) puts every zero in `Re s < 1`.

## Main results

* `TauCeti.meromorphic_riemannZeta`: `riemannZeta` is meromorphic on `ℂ`.
* `TauCeti.meromorphicOrderAt_riemannZeta_one`: `meromorphicOrderAt riemannZeta 1 = -1`.
* `TauCeti.meromorphicOrderAt_riemannZeta_pos_iff`:
  `0 < meromorphicOrderAt riemannZeta s ↔ riemannZeta s = 0`.
* `TauCeti.analyticOnNhd_riemannZeta_closedBall`: analyticity on `closedBall c r` for
  `r < |Im c|`.
* `TauCeti.re_lt_one_of_riemannZeta_eq_zero`: every zero of `riemannZeta` has `Re s < 1`.
* `TauCeti.one_le_toNat_analyticOrderAt_riemannZeta`: at a zero of `riemannZeta` the analytic
  order is a positive natural number.

## References

* David Loeffler and Terence Tao, `riemannZeta_eq_inv_sub_add`, `differentiable_riemannZeta₀`
  and `riemannZeta_one_ne_zero` in `Mathlib.NumberTheory.Harmonic.ZetaAsymp`, for the
  decomposition `riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s` with entire remainder.
* David Loeffler, `analyticOn_riemannZeta` and the residue `riemannZeta_residue_one` in
  `Mathlib.NumberTheory.LSeries.RiemannZeta`.
* Michael Stoll, David Loeffler, and Terence Tao, `riemannZeta_ne_zero_of_one_le_re` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-- Mathlib's Riemann zeta function is meromorphic on `ℂ`. Away from `1` it is analytic
(`analyticOn_riemannZeta`), and near `1` it agrees on a punctured neighbourhood with
`(s - 1)⁻¹ + riemannZeta₀ s`. -/
@[fun_prop]
theorem meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · have h₀ : AnalyticAt ℂ riemannZeta₀ 1 := differentiable_riemannZeta₀.analyticAt 1
    refine (by fun_prop : MeromorphicAt (fun s : ℂ ↦ (s - 1)⁻¹ + riemannZeta₀ s) 1).congr ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
    exact (riemannZeta_eq_inv_sub_add hs).symm
  · exact (analyticOn_riemannZeta z hz).meromorphicAt

/-- The Riemann zeta function has a simple pole at `1`. -/
@[simp]
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = -1 := by
  simpa using (meromorphic_riemannZeta 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    one_ne_zero riemannZeta_residue_one

/-- The Riemann zeta function has positive meromorphic order at `s` if and only if
`riemannZeta s = 0`. -/
@[simp]
theorem meromorphicOrderAt_riemannZeta_pos_iff {s : ℂ} :
    0 < meromorphicOrderAt riemannZeta s ↔ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [meromorphicOrderAt_riemannZeta_one, riemannZeta_one_ne_zero]
  · exact (analyticOn_riemannZeta s hs).meromorphicOrderAt_pos_iff_eq_zero

/-- The Riemann zeta function is analytic on every closed disc `closedBall c r` with
`r < |c.im|`, since such a disc does not contain the pole `1`. -/
theorem analyticOnNhd_riemannZeta_closedBall {c : ℂ} {r : ℝ} (hr : r < |c.im|) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c r) :=
  analyticOn_riemannZeta.mono fun w hw h1 ↦ by
    subst h1
    have him : |c.im| ≤ ‖1 - c‖ := by simpa using abs_im_le_norm (1 - c)
    have hdist : ‖1 - c‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.1 hw
    linarith

/-- Every zero of the Riemann zeta function lies in the open half-plane `Re s < 1`. -/
theorem re_lt_one_of_riemannZeta_eq_zero {s : ℂ} (h : riemannZeta s = 0) : s.re < 1 :=
  not_le.mp fun hs ↦ riemannZeta_ne_zero_of_one_le_re hs h

/-- At a zero of `riemannZeta`, the analytic order is finite and positive, so its `toNat` is at
least `1`. It is finite because `riemannZeta` is meromorphic on the connected set `ℂ` and has
finite order `-1` at `1`. -/
theorem one_le_toNat_analyticOrderAt_riemannZeta {ρ : ℂ} (hρ : riemannZeta ρ = 0) :
    1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hρ
  have htop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
    meromorphic_riemannZeta.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ ρ) (by simp)
  have hpos := meromorphicOrderAt_riemannZeta_pos_iff.mpr hρ
  rw [(analyticOn_riemannZeta ρ hρ1).meromorphicOrderAt_eq] at htop hpos
  cases h : analyticOrderAt riemannZeta ρ with
  | top => simp [h] at htop
  | coe n =>
    simp only [h, ENat.map_natCast] at hpos
    simpa using Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hpos.ne')

end TauCeti
