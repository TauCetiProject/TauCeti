/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Quaternion.Forms
public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.CStarAlgebra.Basic
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Analytic.Basic
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.IteratedFDeriv
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Quaternion.Analytic
import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
import TauCeti.Analysis.Quaternion.Reflection

/-!
# Real analyticity, smoothness, and uniqueness of Fueter regular functions

Every function that is pointwise left or right Fueter regular on an open subset of `ℍ` is real
analytic on neighbourhoods there (`LeftFueterOn.analyticOnNhd`, `RightFueterOn.analyticOnNhd`),
hence smooth of class `C^ω` and `C^∞` (`LeftFueterOn.contDiffOn`, `RightFueterOn.contDiffOn`), even
though `LeftFueterOn` and `RightFueterOn` assume only pointwise real Fréchet differentiability and
the first-order Fueter equation.

When `f` is pointwise left Fueter regular on an open coordinate box
`dq '' pi univ (fun i ↦ Ioo (a i) (b i))` and `dq x₀` lies at coordinate distance at least `δ > 0`
from every face, every shrunk closed cube `dq '' Icc (x₀ - r) (x₀ + r)` with `0 < r < δ` lies
strictly inside the open box, so `f` is continuous there. On `eball (dq x₀) ((√2 - 1) * r)`,
`left_cauchyFueter_box` identifies `f` with `(2π²)⁻¹` times the left box boundary potential,
which admits a convergent power series
(`exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul`). Passing to the canonical
symmetric Taylor series `n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀)` via
`HasFPowerSeriesOnBall.inv_factorial_smul_iteratedFDeriv` and exhausting `r → δ` via
`hasFPowerSeriesOnBall_of_forall_lt` yields a `HasFPowerSeriesOnBall` for `f` at `dq x₀` on the
full ball `eball (dq x₀) ((√2 - 1) * δ)` without any boundary continuity hypothesis
(`LeftFueterOn.hasFPowerSeriesOnBall_of_box`). Inscribing the open cube of half-side `R / 2` in an
open Euclidean ball `ball q₀ R` gives radius `(√2 - 1) * (R / 2)` for any function left Fueter
regular on `ball q₀ R` (`LeftFueterOn.hasFPowerSeriesOnBall_of_ball`). All right-sided counterparts
follow with the exact same radii and canonical Taylor series through the reflection
`q ↦ star (f (star q))` (`RightFueterOn.star_star`), the reflected coordinate boxes
(`image_star_image_dq_pi_Ioo`), and the real linear isometry `starₗᵢ ℝ`.

Combining real analyticity with the analytic identity principle yields the uniqueness principle on
preconnected open sets: two left (or right) Fueter regular functions that agree on `s ∩ t` for an
open set `t` meeting `s`, or share all iterated real Fréchet derivatives at one point, coincide
throughout the preconnected open domain `s`. Unlike in one complex variable, agreement on a set
with accumulation points does not suffice in four real dimensions:
`q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ)` is both left and right Fueter regular on `ℍ` and vanishes on the
two-dimensional subspace `{q | q.re = 0 ∧ q.imI = 0}`, every point of which is an accumulation
point, without vanishing identically.

## Main declarations

* `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_of_box`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_of_box`,
  `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_of_ball`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_of_ball`: quantitative canonical Taylor power-series
  expansions of Fueter regular functions on open boxes and open balls.
* `TauCeti.LeftFueterOn.analyticAt`, `TauCeti.RightFueterOn.analyticAt`,
  `TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`: real analyticity of
  left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.contDiffAt`, `TauCeti.RightFueterOn.contDiffAt`,
  `TauCeti.LeftFueterOn.contDiffOn`, `TauCeti.RightFueterOn.contDiffOn`: `C^n` (including `C^∞` and
  `C^ω`) smoothness of left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.eqOn_of_isPreconnected_of_eqOn_open`,
  `TauCeti.RightFueterOn.eqOn_of_isPreconnected_of_eqOn_open`,
  `TauCeti.LeftFueterOn.eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.RightFueterOn.eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.LeftFueterOn.eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq`,
  `TauCeti.RightFueterOn.eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq`: uniqueness principles
  for left and right Fueter regular functions on preconnected open sets.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9 and the following remark.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set Topology
open scoped ContDiff ENNReal Nat NNReal Pointwise

namespace TauCeti

open TauCeti.Quaternion

/-! ### Private transport and shrunk-cube helpers -/

private theorem hasFPowerSeriesOnBall_iteratedFDeriv_of_star_star {f : ℍ → ℍ} {q₀ : ℍ} {r : ℝ≥0∞}
    {P : FormalMultilinearSeries ℝ ℍ ℍ}
    (h : HasFPowerSeriesOnBall (fun q ↦ star (f (star q))) P (star q₀) r) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f q₀) q₀ r := by
  let u := (starₗᵢ ℝ : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearIsometry
  have hu (q : ℍ) : u q = star q := by
    rw [LinearIsometryEquiv.coe_toLinearIsometry, coe_starₗᵢ]
  rw [← hu q₀] at h
  refine ((u.toContinuousLinearMap.comp_hasFPowerSeriesOnBall h.compLinearIsometry).congr
    fun x _ ↦ ?_).inv_factorial_smul_iteratedFDeriv
  simp only [Function.comp_apply, LinearIsometry.coe_toContinuousLinearMap, hu, star_star]

private theorem integrableOn_boxFaces_of_continuousOn {a b : Fin 4 → ℝ} (hab : a ≤ b)
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' Icc a b)) (i : Fin 4) :
    IntegrableOn (fun z ↦ f (dq (i.insertNth (a i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) ∧
    IntegrableOn (fun z ↦ f (dq (i.insertNth (b i) z)))
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
  have hface {c : ℝ} (hca : a i ≤ c) (hcb : c ≤ b i) :
      IntegrableOn (fun z ↦ f (dq (i.insertNth c z)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
    (hc.comp (dq.continuous.comp (continuous_const.finInsertNth i continuous_id)).continuousOn
      fun z hz ↦ mem_image_of_mem dq (Fin.insertNth_mem_Icc.mpr ⟨⟨hca, hcb⟩, hz⟩)).integrableOn_Icc
  exact ⟨hface le_rfl (hab i), hface (hab i) le_rfl⟩

/-- On a strictly smaller closed cube `dq '' Icc (x₀ - r) (x₀ + r)` (`0 < r < δ`) inside an open
box of left Fueter regularity, `left_cauchyFueter_box` identifies `f` with a constant multiple of
the box boundary potential, yielding the canonical Taylor series on
`eball (dq x₀) ((√2 - 1) * r)`. -/
private theorem LeftFueterOn.hasFPowerSeriesOnBall_of_box_of_lt
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ r : ℝ}
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) (hr₀ : 0 < r) (hr : r < δ) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * r)) := by
  let a' : Fin 4 → ℝ := fun i ↦ x₀ i - r
  let b' : Fin 4 → ℝ := fun i ↦ x₀ i + r
  have hab' : a' ≤ b' := fun i ↦ by dsimp only [a', b']; linarith
  have hsub_closed : dq '' Icc a' b' ⊆ dq '' pi univ (fun i ↦ Ioo (a i) (b i)) := by
    refine image_mono fun x hx i _ ↦ ?_
    exact ⟨by linarith [hx.1 i, (hδ i).1], by linarith [hx.2 i, (hδ i).2]⟩
  have hsub_open : dq '' pi univ (fun i ↦ Ioo (a' i) (b' i)) ⊆
      dq '' pi univ (fun i ↦ Ioo (a i) (b i)) :=
    (image_mono (t := Icc a' b') fun _ hx ↦ ⟨fun i ↦ (hx i (mem_univ i)).1.le,
      fun i ↦ (hx i (mem_univ i)).2.le⟩).trans hsub_closed
  have hc' : ContinuousOn f (dq '' Icc a' b') :=
    hf.differentiableOn.continuousOn.mono hsub_closed
  have hf' : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a' i) (b' i))) := hf.mono hsub_open
  have hface (i : Fin 4) (z : Fin 3 → ℝ) (_ : z ∈ Icc (a' ∘ i.succAbove) (b' ∘ i.succAbove)) :
      r ≤ ‖dq (i.insertNth (a' i) z) - dq x₀‖ ∧ r ≤ ‖dq (i.insertNth (b' i) z) - dq x₀‖ := by
    refine ⟨?_, ?_⟩
    · exact (by rw [abs_of_nonpos] <;> dsimp only [a'] <;> linarith : r ≤ |a' i - x₀ i|).trans
        (by simpa using abs_sub_apply_le_norm_dq_sub (i.insertNth (a' i) z) x₀ i)
    · exact (by rw [abs_of_nonneg] <;> dsimp only [b'] <;> linarith : r ≤ |b' i - x₀ i|).trans
        (by simpa using abs_sub_apply_le_norm_dq_sub (i.insertNth (b' i) z) x₀ i)
  obtain ⟨P, hP⟩ := exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul
    (integrableOn_boxFaces_of_continuousOn hab' hc') hr₀ hface
  have hsqrt : Real.sqrt 2 - 1 < 1 := by
    have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by positivity)).2 (by norm_num)
    linarith
  refine ((hP.const_smul (c := 1 / (2 * Real.pi ^ 2))).congr
    fun q hq ↦ ?_).inv_factorial_smul_iteratedFDeriv
  -- Every point of `eball (dq x₀) ((√2 - 1) * r)` lies in the open cube `dq '' Ioo a' b'`.
  have hrad_pos : 0 < (Real.sqrt 2 - 1) * r := mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hr₀
  have hnorm : ‖q - dq x₀‖ < (Real.sqrt 2 - 1) * r := by
    rw [Metric.mem_eball, edist_dist, dist_eq_norm] at hq
    exact (ENNReal.ofReal_lt_ofReal_iff hrad_pos).1 hq
  have hnorm_r : ‖q - dq x₀‖ < r := hnorm.trans (by nlinarith)
  obtain ⟨x, rfl⟩ := dq_surjective q
  have hcoord (i : Fin 4) : |x i - x₀ i| < r :=
    (abs_sub_apply_le_norm_dq_sub x x₀ i).trans_lt hnorm_r
  have ha' (i : Fin 4) : a' i < x i := by dsimp only [a']; linarith [(abs_lt.1 (hcoord i)).1]
  have hb' (i : Fin 4) : x i < b' i := by dsimp only [b']; linarith [(abs_lt.1 (hcoord i)).2]
  exact (left_cauchyFueter_box hc' (hf'.mono sdiff_subset) ha' hb').symm

/-! ### Quantitative power-series expansions of Fueter regular functions -/

/-- If `f` is pointwise left Fueter regular on the open coordinate box
`dq '' pi univ (fun i ↦ Ioo (a i) (b i))` and `x₀` lies at coordinate distance at least `δ > 0`
from every face, then its canonical Taylor series
`n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀)` represents `f` on
`eball (dq x₀) ((√2 - 1) * δ)`. -/
theorem LeftFueterOn.hasFPowerSeriesOnBall_of_box
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ : ℝ}
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hδ₀ : 0 < δ) (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hc₀ : 0 < Real.sqrt 2 - 1 := sub_pos.2 Real.one_lt_sqrt_two
  refine hasFPowerSeriesOnBall_of_forall_lt (ENNReal.ofReal_pos.2 (mul_pos hc₀ hδ₀))
    fun r' hr' hlt ↦ ?_
  have hlt' : (r' : ℝ) < (Real.sqrt 2 - 1) * δ := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (mul_pos hc₀ hδ₀)] at hlt
  have ht : (r' : ℝ) / (Real.sqrt 2 - 1) < δ :=
    (div_lt_iff₀ hc₀).2 (by simpa [mul_comm] using hlt')
  simpa [mul_div_cancel₀ _ hc₀.ne'] using
    hf.hasFPowerSeriesOnBall_of_box_of_lt hδ (div_pos hr' hc₀) ht

/-- If `f` is pointwise right Fueter regular on the open coordinate box
`dq '' pi univ (fun i ↦ Ioo (a i) (b i))` and `x₀` lies at coordinate distance at least `δ > 0`
from every face, then its canonical Taylor series
`n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀)` represents `f` on
`eball (dq x₀) ((√2 - 1) * δ)`. -/
theorem RightFueterOn.hasFPowerSeriesOnBall_of_box
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ : ℝ}
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hδ₀ : 0 < δ) (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  let x₀' : Fin 4 → ℝ := fun i ↦ if i = 0 then x₀ 0 else -x₀ i
  let a' : Fin 4 → ℝ := fun i ↦ if i = 0 then a 0 else -b i
  let b' : Fin 4 → ℝ := fun i ↦ if i = 0 then b 0 else -a i
  have hf' : LeftFueterOn (fun q ↦ star (f (star q)))
      (dq '' pi univ (fun i ↦ Ioo (a' i) (b' i))) := by
    rw [← image_star_image_dq_pi_Ioo]
    exact hf.star_star
  have hδ' (i : Fin 4) : a' i + δ ≤ x₀' i ∧ x₀' i + δ ≤ b' i := by
    rcases eq_or_ne i 0 with rfl | hi
    · simpa [x₀', a', b'] using hδ 0
    · simp only [x₀', a', b', hi, ↓reduceIte]
      exact ⟨by linarith [(hδ i).2], by linarith [(hδ i).1]⟩
  have h := hf'.hasFPowerSeriesOnBall_of_box hδ₀ hδ'
  rw [← star_dq x₀] at h
  exact hasFPowerSeriesOnBall_iteratedFDeriv_of_star_star h

/-- If `f` is pointwise left Fueter regular on `ball q₀ R` (`R > 0`), then its canonical Taylor
series `n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f q₀` represents `f` on
`eball q₀ ((√2 - 1) * (R / 2))`. -/
theorem LeftFueterOn.hasFPowerSeriesOnBall_of_ball
    {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ} (hf : LeftFueterOn f (ball q₀ R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f q₀)
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  obtain ⟨x₀, rfl⟩ := dq_surjective q₀
  let a : Fin 4 → ℝ := fun i ↦ x₀ i - R / 2
  let b : Fin 4 → ℝ := fun i ↦ x₀ i + R / 2
  have hsub_open : dq '' pi univ (fun i ↦ Ioo (a i) (b i)) ⊆ ball (dq x₀) R := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    let m : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i : Fin 4 ↦ |x i - x₀ i|
    have hm_lt : m < R / 2 := (Finset.sup'_lt_iff Finset.univ_nonempty).2 fun i _ ↦ by
      have h1 : x₀ i - R / 2 < x i := (hx i (mem_univ i)).1
      have h2 : x i < x₀ i + R / 2 := (hx i (mem_univ i)).2
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    have hle : ‖dq x - dq x₀‖ ≤ 2 * m :=
      norm_dq_sub_le_two_mul_of_abs_sub_le fun i ↦
        Finset.le_sup' (f := fun j : Fin 4 ↦ |x j - x₀ j|) (Finset.mem_univ i)
    linarith
  exact (hf.mono hsub_open).hasFPowerSeriesOnBall_of_box (half_pos hR)
    (fun i ↦ ⟨by simp [a], by simp [b]⟩)

/-- If `f` is pointwise right Fueter regular on `ball q₀ R` (`R > 0`), then its canonical Taylor
series `n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f q₀` represents `f` on
`eball q₀ ((√2 - 1) * (R / 2))`. -/
theorem RightFueterOn.hasFPowerSeriesOnBall_of_ball
    {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ} (hf : RightFueterOn f (ball q₀ R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f q₀)
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  have hf' : LeftFueterOn (fun x ↦ star (f (star x))) (ball (star q₀) R) := by
    have h := hf.star_star
    rwa [Set.image_star, Metric.star_ball] at h
  exact hasFPowerSeriesOnBall_iteratedFDeriv_of_star_star
    (hf'.hasFPowerSeriesOnBall_of_ball hR)

/-! ### Real analyticity and smoothness -/

namespace LeftFueterOn

variable {f g : ℍ → ℍ} {s : Set ℍ} {q : ℍ}

/-- A function left Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem analyticAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hs
  exact ((hf.mono hball).hasFPowerSeriesOnBall_of_ball hR).analyticAt

/-- A function left Fueter regular on an open set is real analytic on neighbourhoods there. -/
theorem analyticOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) : AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function left Fueter regular on a neighbourhood of `q` is `C^n` at `q` for every `n`,
including `n = ∞` and `n = ω`. -/
theorem contDiffAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) {n : ℕ∞ω} : ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A function left Fueter regular on an open set is `C^n` there for every `n`, including `n = ∞`
and `n = ω`. -/
theorem contDiffOn (hf : LeftFueterOn f s) (hs : IsOpen s) {n : ℕ∞ω} : ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-! ### Uniqueness principle for left Fueter regular functions -/

/-- **Uniqueness principle (open-subset form).** Two left Fueter regular functions on a preconnected
open set `s` that agree on `s ∩ t` for an open set `t` meeting `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_eqOn_open
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {t : Set ℍ} (ht : IsOpen t) (hne : (s ∩ t).Nonempty) (hfg : EqOn f g (s ∩ t)) :
    EqOn f g s := by
  obtain ⟨q₀, hqs, hqt⟩ := hne
  exact (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc
    hqs (hfg.eventuallyEq_of_mem ((hs.inter ht).mem_nhds ⟨hqs, hqt⟩))

/-- If a left Fueter regular function on a preconnected open set `s` has all iterated real Fréchet
derivatives equal to `0` at one point of `s`, then it vanishes throughout `s`. -/
theorem eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : LeftFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfq₀ : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ hfq₀

/-- Two left Fueter regular functions on a preconnected open set `s` whose iterated real Fréchet
derivatives all agree at one point of `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfg : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ hfg

end LeftFueterOn

namespace RightFueterOn

variable {f g : ℍ → ℍ} {s : Set ℍ} {q : ℍ}

/-- A function right Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem analyticAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hs
  exact ((hf.mono hball).hasFPowerSeriesOnBall_of_ball hR).analyticAt

/-- A function right Fueter regular on an open set is real analytic on neighbourhoods there. -/
theorem analyticOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) : AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function right Fueter regular on a neighbourhood of `q` is `C^n` at `q` for every `n`,
including `n = ∞` and `n = ω`. -/
theorem contDiffAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q) {n : ℕ∞ω} : ContDiffAt ℝ n f q :=
  (hf.analyticAt hs).contDiffAt

/-- A function right Fueter regular on an open set is `C^n` there for every `n`, including `n = ∞`
and `n = ω`. -/
theorem contDiffOn (hf : RightFueterOn f s) (hs : IsOpen s) {n : ℕ∞ω} : ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-! ### Uniqueness principle for right Fueter regular functions -/

/-- **Uniqueness principle (open-subset form).** Two right Fueter regular functions on a
preconnected open set `s` that agree on `s ∩ t` for an open set `t` meeting `s` agree throughout
`s`. -/
theorem eqOn_of_isPreconnected_of_eqOn_open
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {t : Set ℍ} (ht : IsOpen t) (hne : (s ∩ t).Nonempty) (hfg : EqOn f g (s ∩ t)) :
    EqOn f g s := by
  obtain ⟨q₀, hqs, hqt⟩ := hne
  exact (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc
    hqs (hfg.eventuallyEq_of_mem ((hs.inter ht).mem_nhds ⟨hqs, hqt⟩))

/-- If a right Fueter regular function on a preconnected open set `s` has all iterated real Fréchet
derivatives equal to `0` at one point of `s`, then it vanishes throughout `s`. -/
theorem eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero
    (hf : RightFueterOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfq₀ : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = 0) : EqOn f 0 s :=
  (hf.analyticOnNhd hs).eqOn_zero_of_preconnected_of_forall_iteratedFDeriv_eq_zero hc hq₀ hfq₀

/-- Two right Fueter regular functions on a preconnected open set `s` whose iterated real Fréchet
derivatives all agree at one point of `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {q₀ : ℍ} (hq₀ : q₀ ∈ s) (hfg : ∀ n : ℕ, iteratedFDeriv ℝ n f q₀ = iteratedFDeriv ℝ n g q₀) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_forall_iteratedFDeriv_eq
    (hg.analyticOnNhd hs) hc hq₀ hfg

end RightFueterOn

end TauCeti
