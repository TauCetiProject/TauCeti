/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

/-!
# Polygonal interpolation on a uniform grid and its action

Given points `x 0, x 1, …, x N` of a real normed space and the uniform grid `t_k = a + k * h`
with step `h > 0`, the *polygonal interpolation* `TauCeti.polygonalInterpolation a h N x` is the
curve that passes through `x k` at time `t_k` and is affine on each cell `[t_k, t_(k+1)]`. It is
written as the sum `∑ k ≤ N, φ ((t - t_k) / h) • x k` against the hat function
`φ s = max 0 (1 - |s|)`, so that it depends continuously on the points and on the time jointly.

On the cell `[t_k, t_(k+1)]` the curve moves at the constant speed `‖x (k + 1) - x k‖ / h`, so its
`p`-action over `[a, a + N * h]` is the discrete action

`∑ k < N, ‖x (k + 1) - x k‖ ^ p * h ^ (1 - p)`

of the points. Conversely, by Hölder's inequality on each cell, the discrete action of the samples
of an absolutely continuous curve at the grid times is at most the action of the curve. The facts
about the interpolation are stated for every curve agreeing with the interpolation on
`[a, a + N * h]`, such as its restriction to that interval extended by constants. Interpolating
the points of a law on sequences turns it into a law on paths whose expected action is the
expected discrete action; this is how laws of random curves are built from couplings at finitely
many times, in the superposition principle for absolutely continuous curves of probability
measures.

## Main definitions

* `TauCeti.polygonalInterpolation a h N x`: the polygonal interpolation of `x 0, …, x N` on the
  grid `a + k * h`.

## Main results

* `TauCeti.polygonalInterpolation_eq_of_mem_Icc`: the affine formula on each cell.
* `TauCeti.polygonalInterpolation_grid`: the interpolation passes through `x k` at time
  `a + k * h`.
* `TauCeti.continuous_polygonalInterpolation`: joint continuity in the points and the time.
* `TauCeti.absolutelyContinuousOnInterval_of_eqOn_polygonalInterpolation`: the interpolation is
  absolutely continuous on `[a, a + N * h]`.
* `TauCeti.curveAction_of_eqOn_polygonalInterpolation`: its `p`-action is the discrete action of
  the points.
* `TauCeti.sum_edist_rpow_mul_rpow_one_sub_le_curveAction`: the discrete action of the samples of
  an absolutely continuous curve at the grid times is at most its action.

## References

* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120, proof of Theorem 5.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

variable {E : Type*} {a h t : ℝ} {N k : ℕ}

section Module

variable [AddCommGroup E] [Module ℝ E] {x : ℕ → E}

/-- The *polygonal interpolation* of the points `x 0, …, x N` on the uniform grid `a + k * h`:
the curve taking the value `x k` at time `a + k * h` and affine between consecutive grid times,
written with the hat functions `max 0 (1 - |t - (a + k * h)| / h)`. Outside `[a, a + N * h]` it
decays to `0` within one step. -/
def polygonalInterpolation (a h : ℝ) (N : ℕ) (x : ℕ → E) (t : ℝ) : E :=
  ∑ k ∈ Finset.range (N + 1), max 0 (1 - |t - (a + k * h)| / h) • x k

/-- The defining formula of the polygonal interpolation, as a sum against hat functions. -/
theorem polygonalInterpolation_def (a h : ℝ) (N : ℕ) (x : ℕ → E) (t : ℝ) :
    polygonalInterpolation a h N x t =
      ∑ k ∈ Finset.range (N + 1), max 0 (1 - |t - (a + k * h)| / h) • x k :=
  (rfl)

/-- A hat function vanishes at distance at least one step from its grid time. -/
private lemma max_zero_one_sub_abs_div_eq_zero {s : ℝ} (hh : 0 < h) (hs : h ≤ |s|) :
    max 0 (1 - |s| / h) = 0 :=
  max_eq_left (by rw [sub_nonpos, le_div_iff₀ hh]; linarith)

/-- **The affine formula on a cell.** On `[a + k * h, a + (k + 1) * h]`, for `k < N`, the
polygonal interpolation is the affine segment from `x k` to `x (k + 1)`. -/
theorem polygonalInterpolation_eq_of_mem_Icc (x : ℕ → E) (hh : 0 < h) (hk : k < N)
    (ht : t ∈ Icc (a + k * h) (a + (k + 1) * h)) :
    polygonalInterpolation a h N x t = x k + ((t - (a + k * h)) / h) • (x (k + 1) - x k) := by
  obtain ⟨ht₁, ht₂⟩ := ht
  rw [polygonalInterpolation_def, Finset.sum_eq_add k (k + 1) (by omega) ?_
    (fun h' ↦ absurd (Finset.mem_range.2 (by omega)) h')
    (fun h' ↦ absurd (Finset.mem_range.2 (by omega)) h')]
  · -- The two hat functions of the cell are the barycentric coordinates of `t`.
    have hk : max 0 (1 - |t - (a + k * h)| / h) = 1 - (t - (a + k * h)) / h := by
      rw [abs_of_nonneg (by linarith), max_eq_right]
      rw [sub_nonneg, div_le_one hh]
      linarith
    have hk' : max 0 (1 - |t - (a + ↑(k + 1) * h)| / h) = (t - (a + k * h)) / h := by
      push_cast
      rw [abs_of_nonpos (by linarith), max_eq_right]
      · field_simp
        ring
      · rw [sub_nonneg, div_le_one hh]
        linarith
    rw [hk, hk', sub_smul, one_smul, smul_sub]
    abel
  · -- Every other hat function vanishes on the cell.
    intro j _ hj
    rw [max_zero_one_sub_abs_div_eq_zero hh, zero_smul]
    rcases lt_or_gt_of_ne hj.1 with hjk | hjk
    · have hcast : ((j : ℝ) + 1) * h ≤ k * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) hh.le
      exact le_abs.2 (Or.inl (by linarith))
    · have hcast : ((k : ℝ) + 2) * h ≤ j * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show k + 2 ≤ j by omega)) hh.le
      exact le_abs.2 (Or.inr (by linarith))

/-- **The interpolation passes through the points.** At the grid time `a + k * h`, for `k ≤ N`,
the polygonal interpolation takes the value `x k`. -/
@[simp]
theorem polygonalInterpolation_grid (x : ℕ → E) (hh : 0 < h) (hk : k ≤ N) :
    polygonalInterpolation a h N x (a + k * h) = x k := by
  rw [polygonalInterpolation_def, Finset.sum_eq_single k
    (fun j _ hj ↦ ?_) (fun h' ↦ absurd (Finset.mem_range.2 (by omega)) h')]
  · simp
  · rw [max_zero_one_sub_abs_div_eq_zero hh, zero_smul]
    have hkj : 1 ≤ |(k : ℝ) - j| := by
      rcases lt_or_gt_of_ne hj with hjk | hjk
      · rw [abs_of_nonneg (by simp [hjk.le])]
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        linarith
      · rw [abs_of_nonpos (by simp [hjk.le])]
        have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hjk
        linarith
    calc h = 1 * h := (one_mul h).symm
      _ ≤ |(k : ℝ) - j| * h := mul_le_mul_of_nonneg_right hkj hh.le
      _ = |a + k * h - (a + j * h)| := by
        rw [show a + k * h - (a + j * h) = (k - j) * h by ring, abs_mul, abs_of_pos hh]

/-- The polygonal interpolation is jointly continuous in the points and the time. -/
@[fun_prop]
theorem continuous_polygonalInterpolation [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (a h : ℝ) (N : ℕ) :
    Continuous fun q : (ℕ → E) × ℝ ↦ polygonalInterpolation a h N q.1 q.2 := by
  simp_rw [polygonalInterpolation_def]
  fun_prop

end Module

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {x : ℕ → E}

/-- **Absolute continuity.** A curve that agrees with a polygonal interpolation on
`[a, a + N * h]` is absolutely continuous there. -/
theorem absolutelyContinuousOnInterval_of_eqOn_polygonalInterpolation {f : ℝ → E} (hh : 0 < h)
    (hf : EqOn f (polygonalInterpolation a h N x) (Icc a (a + N * h))) :
    AbsolutelyContinuousOnInterval f a (a + N * h) := by
  have hgrid {k : ℕ} (hk : k ≤ N) : f (a + k * h) = x k := by
    rw [hf ⟨by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)],
      by nlinarith [(Nat.cast_le (α := ℝ)).2 hk]⟩, polygonalInterpolation_grid x hh hk]
  refine AbsolutelyContinuousOnInterval.of_affine_subdivision (s := fun i : Fin (N + 1) ↦
    a + (i : ℕ) * h) (fun i j hij ↦ ?_) (by simp) (by simp) fun i t ht ↦ ?_
  · have : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    simp only
    nlinarith
  · simp only [Fin.val_castSucc, Fin.val_succ] at ht ⊢
    push_cast at ht
    have hi : (i : ℕ) < N := i.isLt
    rw [hgrid hi.le, hgrid hi, hf ⟨?_, ?_⟩, polygonalInterpolation_eq_of_mem_Icc x hh hi ?_]
    · push_cast
      congr 2
      ring
    · exact ht
    · nlinarith [ht.1, (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ (i : ℕ))]
    · have : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hi
      nlinarith [ht.2]

/-- On the interior of a cell, a curve agreeing with a polygonal interpolation moves at the
constant speed `‖x (k + 1) - x k‖ / h`. -/
private lemma metricDerivative_of_eqOn_polygonalInterpolation {f : ℝ → E} (hh : 0 < h)
    (hf : EqOn f (polygonalInterpolation a h N x) (Icc a (a + N * h))) (hk : k < N)
    (ht : t ∈ Ioo (a + k * h) (a + (k + 1) * h)) :
    metricDerivative f t = ‖h⁻¹ • (x (k + 1) - x k)‖ₑ := by
  have hcell : Icc (a + k * h) (a + (k + 1) * h) ⊆ Icc a (a + N * h) := by
    have h0 : (0 : ℝ) ≤ k * h := by positivity
    have h1 : ((k : ℝ) + 1) * h ≤ N * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
    exact Icc_subset_Icc (by linarith) (by linarith)
  -- Near `t`, the curve is the affine segment of the cell.
  have heq : (fun s ↦ x k + ((s - (a + k * h)) / h) • (x (k + 1) - x k)) =ᶠ[𝓝 t] f := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [hf (hcell hs), polygonalInterpolation_eq_of_mem_Icc x hh hk hs]
  have hderiv : HasDerivAt (fun s ↦ x k + ((s - (a + k * h)) / h) • (x (k + 1) - x k))
      (h⁻¹ • (x (k + 1) - x k)) t := by
    have := (((hasDerivAt_id t).sub_const (a + k * h)).div_const h).smul_const
      (x (k + 1) - x k)
    simpa [div_eq_inv_mul] using this.const_add (x k)
  exact (hderiv.congr_of_eventuallyEq heq.symm).metricDerivative_eq

/-- **The action of a polygonal interpolation is the discrete action.** For `0 ≤ p`, the
`p`-action over `[a, a + N * h]` of a curve agreeing there with the polygonal interpolation of
`x 0, …, x N` is `∑ k < N, d(x k, x (k + 1)) ^ p * h ^ (1 - p)`. -/
theorem curveAction_of_eqOn_polygonalInterpolation {f : ℝ → E} {p : ℝ} (hh : 0 < h)
    (hp : 0 ≤ p) (hf : EqOn f (polygonalInterpolation a h N x) (Icc a (a + N * h))) :
    curveAction p f a (a + N * h) =
      ∑ k ∈ Finset.range N, edist (x k) (x (k + 1)) ^ p * ENNReal.ofReal h ^ (1 - p) := by
  rw [curveAction_eq_sum_range p f hh.le]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.1 hk
  have hc0 : ENNReal.ofReal h ≠ 0 := by simpa using hh
  calc curveAction p f (a + k * h) (a + (k + 1) * h)
      = ∫⁻ _ in Ioo (a + k * h) (a + (k + 1) * h), ‖h⁻¹ • (x (k + 1) - x k)‖ₑ ^ p := by
        rw [curveAction_def, uIoc_of_le (by nlinarith), ← setLIntegral_congr Ioo_ae_eq_Ioc]
        exact setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by
          rw [metricDerivative_of_eqOn_polygonalInterpolation hh hf hk ht]
    _ = (ENNReal.ofReal h)⁻¹ ^ p * edist (x k) (x (k + 1)) ^ p * ENNReal.ofReal h := by
        rw [setLIntegral_const, Real.volume_Ioo, show a + (k + 1) * h - (a + k * h) = h by ring,
          enorm_smul, enorm_inv hh.ne', Real.enorm_of_nonneg hh.le, ← edist_eq_enorm_sub,
          edist_comm, ENNReal.mul_rpow_of_nonneg _ _ hp]
    _ = edist (x k) (x (k + 1)) ^ p * ENNReal.ofReal h ^ (1 - p) := by
        rw [ENNReal.rpow_sub _ _ hc0 ENNReal.ofReal_ne_top, ENNReal.rpow_one, ENNReal.inv_rpow,
          ENNReal.div_eq_inv_mul]
        ac_rfl

end Normed

/-- **The discrete action of grid samples is at most the action.** For `1 ≤ p` and a curve `γ` in
a pseudometric space, absolutely continuous on `[a, a + N * h]` with `h > 0`, the samples at the
grid times `a + k * h` satisfy `∑ k < N, d(γ (a + k * h), γ (a + (k + 1) * h)) ^ p * h ^ (1 - p) ≤
A_p(γ)`. Together with `TauCeti.curveAction_of_eqOn_polygonalInterpolation`, the polygonal
interpolation of the samples of a curve has at most the action of the curve. -/
theorem sum_edist_rpow_mul_rpow_one_sub_le_curveAction {X : Type*} [PseudoMetricSpace X]
    {γ : ℝ → X} {p : ℝ} (hh : 0 < h) (hp : 1 ≤ p)
    (hγ : AbsolutelyContinuousOnInterval γ a (a + N * h)) :
    ∑ k ∈ Finset.range N,
        edist (γ (a + k * h)) (γ (a + (k + 1) * h)) ^ p * ENNReal.ofReal h ^ (1 - p) ≤
      curveAction p γ a (a + N * h) := by
  rw [curveAction_eq_sum_range p γ hh.le]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hk := Finset.mem_range.1 hk
  have hgrid {j : ℕ} (hj : j ≤ N) : a + j * h ∈ uIcc a (a + N * h) := by
    have : (j : ℝ) * h ≤ N * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le
    exact mem_uIcc.2 (Or.inl ⟨by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)], by linarith⟩)
  have h1 := hgrid hk.le
  have h2 := hgrid (Nat.succ_le_of_lt hk)
  rw [Nat.cast_succ] at h2
  have hc0 : ENNReal.ofReal h ≠ 0 := by simpa using hh
  have hstep : edist (a + k * h) (a + (k + 1) * h) = ENNReal.ofReal h := by
    rw [edist_dist, Real.dist_eq, show a + k * h - (a + (k + 1) * h) = -h by ring, abs_neg,
      abs_of_pos hh]
  -- Hölder's estimate `d(γ s, γ u) ^ p ≤ |u - s| ^ (p - 1) * A_p(γ; s, u)` on each cell.
  calc edist (γ (a + k * h)) (γ (a + (k + 1) * h)) ^ p * ENNReal.ofReal h ^ (1 - p)
      ≤ ENNReal.ofReal h ^ (p - 1) * curveAction p γ (a + k * h) (a + (k + 1) * h) *
          ENNReal.ofReal h ^ (1 - p) := by
        gcongr
        rw [← hstep]
        exact hγ.edist_rpow_le_mul_curveAction hp h1 h2
    _ = curveAction p γ (a + k * h) (a + (k + 1) * h) := by
        rw [mul_comm, ← mul_assoc, ← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top,
          show 1 - p + (p - 1) = 0 by ring, ENNReal.rpow_zero, one_mul]

end TauCeti
