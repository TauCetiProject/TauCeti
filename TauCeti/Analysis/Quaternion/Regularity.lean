/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Quaternion.Fueter
import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
import TauCeti.Analysis.Quaternion.Cauchy.Potential

/-!
# Real analyticity and smoothness of Fueter regular functions

A function `f : ℍ → ℍ` that is pointwise left or right Fueter regular (assuming only the existence
of a real Fréchet derivative annihilated by `fueterLeft` or `fueterRight`, with no continuity of
the derivative assumed) is automatically real analytic, and hence `C^∞`, on every open set where it
is regular.

Around any interior point `dq x₀` of a coordinate box `Icc a b` whose faces lie at coordinate
distance at least `δ > 0` from `x₀`, the box Cauchy–Fueter representation identifies `f` throughout
the Euclidean ball `Metric.eball (dq x₀) ((√2 - 1) δ)` with `1 / (2π²)` times the boundary potential
`boxBoundarySum`. Expanding the kernel uniformly on each compact face yields a quantitative
`HasFPowerSeriesOnBall` expansion on that ball. Inscribing an axis-aligned cube of side `R` inside
any closed Euclidean ball `Metric.closedBall q₀ R` (`R > 0`), whose vertices lie at distance
`2 (R / 2) = R` from `q₀` and whose faces lie at distance `R / 2`, gives a convergent real power
series on `Metric.eball q₀ ((√2 - 1) (R / 2))`.

## Main declarations

* `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_box`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_box`: quantitative power-series expansion
  on `eball (dq x₀) ((√2 - 1) δ)` inside a coordinate box.
* `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_of_continuousOn_closedBall`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_of_continuousOn_closedBall`: quantitative
  power-series expansion on `eball q₀ ((√2 - 1) (R / 2))` from continuity on `closedBall q₀ R`
  and regularity on `ball q₀ R`.
* `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall_subset`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall_subset`: quantitative
  power-series expansion on `eball q₀ ((√2 - 1) (R / 2))` when `closedBall q₀ R ⊆ s`.
* `TauCeti.LeftFueterOn.analyticAt`, `TauCeti.RightFueterOn.analyticAt`,
  `TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`: local and open-set
  real analyticity of left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.contDiffAt`, `TauCeti.RightFueterOn.contDiffAt`,
  `TauCeti.LeftFueterOn.contDiffOn`, `TauCeti.RightFueterOn.contDiffOn`: `C^n` (in particular
  `C^∞` and `C^ω`) smoothness of left and right Fueter regular functions.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9 and the remark following it.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter Metric Set Topology
open scoped Quaternion ENNReal

namespace TauCeti

open TauCeti.Quaternion _root_.Quaternion

variable {f : ℍ → ℍ} {s : Set ℍ} {q q₀ : ℍ}

/-! ### Quantitative power series on coordinate boxes -/

private theorem coord_mem_Ioo_of_mem_eball {a b x₀ : Fin 4 → ℝ} {δ : ℝ} (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i)
    {q : ℍ} (hq : q ∈ eball (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ))) (i : Fin 4) :
    let x := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q
    a i < x i ∧ x i < b i := by
  intro x
  have hdx : dq x = q := dq_linearEquivTuple q
  have hnorm : ‖q - dq x₀‖ < (Real.sqrt 2 - 1) * δ := by
    rwa [mem_eball, edist_dist, dist_eq_norm,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)] at hq
  have hlt_δ : ‖dq (x - x₀)‖ < δ := by
    rw [dq.map_sub, hdx]
    exact hnorm.trans (mul_lt_of_lt_one_left hδ₀ (by linarith [Real.sqrt_two_lt_three_halves]))
  have habs : |x i - x₀ i| < δ := by
    simpa only [Pi.sub_apply] using (abs_apply_le_norm_dq (x - x₀) i).trans_lt hlt_δ
  obtain ⟨h1, h2⟩ := abs_lt.1 habs
  exact ⟨by linarith [ha i], by linarith [hb i]⟩

/-- Quantitative real power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` for a function
continuous on a closed coordinate box `dq '' Icc a b` and pointwise left Fueter regular in its open
interior, whenever `x₀` is an interior point of the box at coordinate distance at least `δ > 0`
from every face (`a i + δ ≤ x₀ i ≤ b i - δ`). -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_box
    {a b x₀ : Fin 4 → ℝ} (hf : LeftFueterOn f (dq '' pi univ fun i ↦ Ioo (a i) (b i)))
    (hc : ContinuousOn f (dq '' Icc a b)) {δ : ℝ} (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hab (i : Fin 4) : a i ≤ b i := by linarith [ha i, hb i]
  obtain ⟨p, hp⟩ := exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul (f := f) hδ₀
    (fun _ hq ↦ le_norm_sub_dq_of_mem_boxBoundarySet
      (fun i ↦ by rw [abs_sub_comm]; exact (ha i).trans (le_abs_self _))
      (fun i ↦ (hb i).trans (le_abs_self _)) hq)
    (fun i ↦ hc.integrableOn_dq_insertNth_Icc (hab i) le_rfl)
    (fun i ↦ hc.integrableOn_dq_insertNth_Icc le_rfl (hab i))
  refine ⟨(1 / (2 * Real.pi ^ 2) : ℝ) • p, (hp.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr
    fun q hq ↦ ?_⟩
  set x := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q
  have hdx : dq x = q := dq_linearEquivTuple q
  have hx := fun i ↦ coord_mem_Ioo_of_mem_eball hδ₀ ha hb hq i
  have hrep :=
    left_cauchyFueter_box hc (hf.mono sdiff_subset) (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)
  rw [hdx] at hrep
  exact hrep.symm

/-- Quantitative real power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` for a function
continuous on a closed coordinate box `dq '' Icc a b` and pointwise right Fueter regular in its
open interior, whenever `x₀` is an interior point of the box at coordinate distance at least
`δ > 0` from every face (`a i + δ ≤ x₀ i ≤ b i - δ`). -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_box
    {a b x₀ : Fin 4 → ℝ} (hf : RightFueterOn f (dq '' pi univ fun i ↦ Ioo (a i) (b i)))
    (hc : ContinuousOn f (dq '' Icc a b)) {δ : ℝ} (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hab (i : Fin 4) : a i ≤ b i := by linarith [ha i, hb i]
  obtain ⟨p, hp⟩ := exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel (f := f) hδ₀
    (fun _ hq ↦ le_norm_sub_dq_of_mem_boxBoundarySet
      (fun i ↦ by rw [abs_sub_comm]; exact (ha i).trans (le_abs_self _))
      (fun i ↦ (hb i).trans (le_abs_self _)) hq)
    (fun i ↦ hc.integrableOn_dq_insertNth_Icc (hab i) le_rfl)
    (fun i ↦ hc.integrableOn_dq_insertNth_Icc le_rfl (hab i))
  refine ⟨(1 / (2 * Real.pi ^ 2) : ℝ) • p, (hp.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr
    fun q hq ↦ ?_⟩
  set x := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q
  have hdx : dq x = q := dq_linearEquivTuple q
  have hx := fun i ↦ coord_mem_Ioo_of_mem_eball hδ₀ ha hb hq i
  have hrep :=
    right_cauchyFueter_box hc (hf.mono sdiff_subset) (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)
  rw [hdx] at hrep
  exact hrep.symm

/-! ### Quantitative power series on Euclidean balls -/

/-- Quantitative real power-series expansion on `eball q₀ ((√2 - 1) (R / 2))` for a function
continuous on `closedBall q₀ R` (`0 < R`) and pointwise left Fueter regular on `ball q₀ R`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_of_continuousOn_closedBall
    {R : ℝ} (hf : LeftFueterOn f (ball q₀ R)) (hc : ContinuousOn f (closedBall q₀ R))
    (hR : 0 < R) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  let x₀ := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q₀
  have hdx₀ : dq x₀ = q₀ := dq_linearEquivTuple q₀
  rw [← hdx₀] at hc hf ⊢
  exact (hf.mono (image_dq_pi_Ioo_subset_ball x₀ R)).exists_hasFPowerSeriesOnBall_box
    (hc.mono (image_dq_Icc_subset_closedBall x₀ R))
    (half_pos hR) (fun _ ↦ by linarith) (fun _ ↦ by linarith)

/-- Quantitative real power-series expansion on `eball q₀ ((√2 - 1) (R / 2))` for a function
continuous on `closedBall q₀ R` (`0 < R`) and pointwise right Fueter regular on `ball q₀ R`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_of_continuousOn_closedBall
    {R : ℝ} (hf : RightFueterOn f (ball q₀ R)) (hc : ContinuousOn f (closedBall q₀ R))
    (hR : 0 < R) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  let x₀ := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q₀
  have hdx₀ : dq x₀ = q₀ := dq_linearEquivTuple q₀
  rw [← hdx₀] at hc hf ⊢
  exact (hf.mono (image_dq_pi_Ioo_subset_ball x₀ R)).exists_hasFPowerSeriesOnBall_box
    (hc.mono (image_dq_Icc_subset_closedBall x₀ R))
    (half_pos hR) (fun _ ↦ by linarith) (fun _ ↦ by linarith)

/-- If `f` is left Fueter regular on a set `s` containing `closedBall q₀ R` (`0 < R`), then `f`
admits a convergent real power series on `eball q₀ ((√2 - 1) (R / 2))`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall_subset
    (hf : LeftFueterOn f s) {R : ℝ} (hR : 0 < R) (hs : closedBall q₀ R ⊆ s) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) :=
  (hf.mono (ball_subset_closedBall.trans hs)
    ).exists_hasFPowerSeriesOnBall_of_continuousOn_closedBall (hf.continuousOn.mono hs) hR

/-- If `f` is right Fueter regular on a set `s` containing `closedBall q₀ R` (`0 < R`), then `f`
admits a convergent real power series on `eball q₀ ((√2 - 1) (R / 2))`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_of_closedBall_subset
    (hf : RightFueterOn f s) {R : ℝ} (hR : 0 < R) (hs : closedBall q₀ R ⊆ s) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) :=
  (hf.mono (ball_subset_closedBall.trans hs)
    ).exists_hasFPowerSeriesOnBall_of_continuousOn_closedBall (hf.continuousOn.mono hs) hR

/-! ### Real analyticity and smoothness -/

/-- A function that is left Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem LeftFueterOn.analyticAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hs
  obtain ⟨p, hp⟩ := hf.exists_hasFPowerSeriesOnBall_of_closedBall_subset hR hball
  exact hp.analyticAt

/-- A function that is right Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem RightFueterOn.analyticAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hs
  obtain ⟨p, hp⟩ := hf.exists_hasFPowerSeriesOnBall_of_closedBall_subset hR hball
  exact hp.analyticAt

/-- **Left Fueter regular functions are real analytic.** If `f` is pointwise left Fueter regular on
an open set `s`, then `f` is real analytic (`AnalyticOnNhd ℝ`) on `s`. -/
theorem LeftFueterOn.analyticOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) :
    AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- **Right Fueter regular functions are real analytic.** If `f` is pointwise right Fueter regular
on an open set `s`, then `f` is real analytic (`AnalyticOnNhd ℝ`) on `s`. -/
theorem RightFueterOn.analyticOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) :
    AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function that is left Fueter regular on a neighbourhood of `q` is `C^n` (in particular `C^∞`
and `C^ω`) at `q`. -/
theorem LeftFueterOn.contDiffAt {n : WithTop ℕ∞} (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) :
    ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A function that is right Fueter regular on a neighbourhood of `q` is `C^n` (in particular `C^∞`
and `C^ω`) at `q`. -/
theorem RightFueterOn.contDiffAt {n : WithTop ℕ∞} (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) :
    ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A left Fueter regular function on an open set `s` is `C^n` (in particular `C^∞` and `C^ω`) on
`s`. -/
theorem LeftFueterOn.contDiffOn {n : WithTop ℕ∞} (hf : LeftFueterOn f s) (hs : IsOpen s) :
    ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-- A right Fueter regular function on an open set `s` is `C^n` (in particular `C^∞` and `C^ω`) on
`s`. -/
theorem RightFueterOn.contDiffOn {n : WithTop ℕ∞} (hf : RightFueterOn f s) (hs : IsOpen s) :
    ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

end TauCeti
