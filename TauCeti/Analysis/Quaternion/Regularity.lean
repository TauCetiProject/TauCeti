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
import TauCeti.Analysis.Quaternion.Cauchy.Representation
import TauCeti.Analysis.Quaternion.Reflection
import TauCeti.Topology.Order.Interval

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

The same radius holds on a positively oriented affine parallelepiped `C = p + L([0, 1]⁴)` when `f`
is continuous on `C`, Fueter regular on its open interior, and the eight boundary faces lie at
Euclidean distance at least `δ > 0` from `dq x₀`: the ball `eball (dq x₀) ((√2 - 1) * δ)` lies
inside the open parallelepiped, where `left_cauchyFueter_affine` and `right_cauchyFueter_affine`
identify `f` with its boundary integral, whose eight face potentials expand into power series
(`LeftFueterOn.hasFPowerSeriesOnBall_affine`, `RightFueterOn.hasFPowerSeriesOnBall_affine`).

Combining real analyticity with the analytic identity principle yields the uniqueness principle on
preconnected open sets: two left (or right) Fueter regular functions that agree on `s ∩ t` for an
open set `t` meeting `s`, or share all iterated real Fréchet derivatives at one point, coincide
throughout the preconnected open domain `s`. Unlike in one complex variable, agreement on a set
with accumulation points does not suffice in four real dimensions:
`q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ)` is both left and right Fueter regular on `ℍ` and vanishes on the
two-dimensional subspace `{q | q.re = 0 ∧ q.imI = 0}`, every point of which is an accumulation
point, without vanishing identically
(`exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt`).

## Main declarations

* `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_of_box`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_of_box`,
  `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_of_ball`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_of_ball`: quantitative canonical Taylor power-series
  expansions of Fueter regular functions on open boxes and open balls.
* `TauCeti.LeftFueterOn.hasFPowerSeriesOnBall_affine`,
  `TauCeti.RightFueterOn.hasFPowerSeriesOnBall_affine`: the same expansions on positively oriented
  affine parallelepipeds whose boundary faces stay at Euclidean distance `δ` from the centre.
* `TauCeti.LeftFueterOn.analyticAt`, `TauCeti.RightFueterOn.analyticAt`,
  `TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`: real analyticity of
  left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.contDiffAt`, `TauCeti.RightFueterOn.contDiffAt`,
  `TauCeti.LeftFueterOn.contDiffOn`, `TauCeti.RightFueterOn.contDiffOn`: `C^n` (including `C^∞` and
  `C^ω`) smoothness of left and right Fueter regular functions.
* `TauCeti.LeftFueterOn.eqOn_of_isPreconnected_of_eqOn_open`,
  `TauCeti.RightFueterOn.eqOn_of_isPreconnected_of_eqOn_open`,
  `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq`,
  `TauCeti.RightFueterOn.eqOn_of_preconnected_of_eventuallyEq`,
  `TauCeti.LeftFueterOn.eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.RightFueterOn.eqOn_zero_of_isPreconnected_of_forall_iteratedFDeriv_eq_zero`,
  `TauCeti.LeftFueterOn.eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq`,
  `TauCeti.RightFueterOn.eqOn_of_isPreconnected_of_forall_iteratedFDeriv_eq`: uniqueness principles
  for left and right Fueter regular functions on preconnected open sets.
* `TauCeti.exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt`: a nonzero globally left
  and right Fueter regular function vanishing on a nonempty set of accumulation points.

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

/-! ### Private helpers for affine parallelepipeds -/

/-- If `u₀` lies in the open box `∏ i, Ioo (a i) (b i)` and every facet image under
`v ↦ dq (p + M v)` sits at distance at least `δ` from `dq (p + M u₀)`, then any `u` with
`‖dq (p + M u) - dq (p + M u₀)‖ < δ` also lies in `∏ i, Ioo (a i) (b i)` (otherwise the segment
`[u₀, u]` meets a facet at distance `t * ‖dq (p + M u) - dq (p + M u₀)‖ < δ`). -/
private theorem mem_pi_Ioo_of_norm_dq_sub_lt {a b p u₀ u : Fin 4 → ℝ}
    (M : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ)
    (ha : ∀ i, a i < u₀ i) (hb : ∀ i, u₀ i < b i)
    {δ : ℝ} (hδ : ∀ (j : Fin 4) {c : ℝ}, (c = a j ∨ c = b j) →
      ∀ w ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
        δ ≤ ‖dq (p + M (j.insertNth c w)) - dq (p + M u₀)‖)
    (hu_lt : ‖dq (p + M u) - dq (p + M u₀)‖ < δ) :
    u ∈ pi univ fun i ↦ Ioo (a i) (b i) := by
  by_contra hu
  -- Apply `IsOpen.exists_first_exit` to the segment `[u₀, u]` leaving the open box `V`.
  let V : Set (Fin 4 → ℝ) := pi univ fun i ↦ Ioo (a i) (b i)
  have hV_open : IsOpen V := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hV_sub : V ⊆ Icc a b := fun x hx ↦
    ⟨fun i ↦ (hx i (mem_univ i)).1.le, fun i ↦ (hx i (mem_univ i)).2.le⟩
  obtain ⟨t, ht, -, hv_not, hv_cl, -⟩ :=
    hV_open.exists_first_exit (γ := fun t : ℝ ↦ (1 - t) • u₀ + t • u) (a := 0) (b := 1)
      (by fun_prop) (by simp [V, ha, hb])
      ⟨1, right_mem_Icc.2 zero_le_one, by simpa [V] using hu⟩
  set v := (1 - t) • u₀ + t • u
  have hv_icc : v ∈ Icc a b := isClosed_Icc.closure_subset_iff.2 hV_sub hv_cl
  -- Identify the facet coordinate `j` where `v` meets `a j` or `b j`.
  have hv_ex : ∃ j : Fin 4, v j ∉ Ioo (a j) (b j) := by
    by_contra! hall
    exact hv_not fun j _ ↦ hall j
  obtain ⟨j, hj⟩ := hv_ex
  have hc : v j = a j ∨ v j = b j := by
    by_cases h1 : v j = a j
    · exact Or.inl h1
    · exact Or.inr (le_antisymm (hv_icc.2 j)
        (not_lt.1 fun hlt ↦ hj ⟨lt_of_le_of_ne' (hv_icc.1 j) h1, hlt⟩))
  have hseg : (1 - t) • u₀ + t • u = j.insertNth (v j) (j.removeNth v) :=
    (j.insertNth_self_removeNth v).symm
  have hw : j.removeNth v ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove) :=
    ⟨fun r ↦ hv_icc.1 (j.succAbove r), fun r ↦ hv_icc.2 (j.succAbove r)⟩
  -- Linearity scales the displacement from `dq (p + M u₀)` by `t ≤ 1`, contradicting `hδ`.
  have hlin : dq (p + M (j.insertNth (v j) (j.removeNth v))) - dq (p + M u₀) =
      t • (dq (p + M u) - dq (p + M u₀)) := by
    rw [← hseg, M.map_add, M.map_smul, M.map_smul]
    have hp_id : p + ((1 - t) • M u₀ + t • M u) = (1 - t) • (p + M u₀) + t • (p + M u) := by
      ext i; simp [Pi.add_apply, Pi.smul_apply]; ring
    rw [hp_id, map_add, map_smul, map_smul]
    module
  have hle : δ ≤ ‖t • (dq (p + M u) - dq (p + M u₀))‖ := hlin ▸ hδ j hc _ hw
  rw [norm_smul, Real.norm_of_nonneg ht.1] at hle
  have hlt : t * ‖dq (p + M u) - dq (p + M u₀)‖ < δ :=
    (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans_lt (by simpa using hu_lt)
  exact not_lt_of_ge hle hlt

/-- Power-series expansion on `eball q₀ ((√2 - 1) δ)` of a single compact `Icc` face Cauchy–Fueter
potential paired through `F` (left or right multiplication). -/
private theorem exists_hasFPowerSeriesOnBall_setIntegral_Icc
    {a b : Fin 3 → ℝ} {γ g : (Fin 3 → ℝ) → ℍ} {F : ℍ → ℍ → ℍ} {q₀ : ℍ} {δ : ℝ}
    (hF : ∀ (γ' : C(Icc a b, ℍ)) (_ : ∀ z, γ' z ≠ q₀) (_ : ∀ z, δ ≤ ‖γ' z - q₀‖)
        {g' : Icc a b → ℍ} (_ : Integrable g' (volume.comap Subtype.val)),
      ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
        HasFPowerSeriesOnBall
          (fun q ↦ ∫ z, F (cauchyFueterKernel (γ' z) q) (g' z) ∂volume.comap Subtype.val)
          P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)))
    (hγ : ContinuousOn γ (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hδ₀ : 0 < δ) (hδ : ∀ u ∈ Icc a b, δ ≤ ‖γ u - q₀‖) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall (fun q ↦ ∫ u in Icc a b, F (cauchyFueterKernel (γ u) q) (g u))
        P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  let γ' : C(Icc a b, ℍ) := ⟨fun z ↦ γ z.val, hγ.domRestrict⟩
  have hne : ∀ z : Icc a b, γ' z ≠ q₀ :=
    fun z ↦ sub_ne_zero.1 (norm_pos_iff.1 (hδ₀.trans_le (hδ z.val z.property)))
  obtain ⟨P, hP⟩ := hF γ' hne (fun z ↦ hδ z.val z.property)
    ((integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
      (hg.integrableOn_compact (μ := volume) isCompact_Icc))
  exact ⟨P, hP.congr fun q _ ↦
    integral_subtype_comap measurableSet_Icc fun u ↦ F (cauchyFueterKernel (γ u) q) (g u)⟩

/-- If `f` agrees on `eball q₀ ((√2 - 1) δ)` (`δ > 0`) with `(1 / (2π²))` times a finite sum of
upper-minus-lower compact `Icc` Cauchy–Fueter face potentials, then `f` admits its canonical
symmetric Taylor series on that ball. -/
private theorem hasFPowerSeriesOnBall_of_eq_smul_sum_sub_Icc
    {ι : Type*} [Fintype ι] {lo hi : ι → Fin 3 → ℝ}
    {γ₁ γ₀ g₁ g₀ : ι → (Fin 3 → ℝ) → ℍ} {F : ℍ → ℍ → ℍ} {f : ℍ → ℍ} {q₀ : ℍ} {δ : ℝ}
    (hF : ∀ (i : ι) (γ' : C(Icc (lo i) (hi i), ℍ))
        (_ : ∀ z, γ' z ≠ q₀) (_ : ∀ z, δ ≤ ‖γ' z - q₀‖)
        {g' : Icc (lo i) (hi i) → ℍ} (_ : Integrable g' (volume.comap Subtype.val)),
      ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
        HasFPowerSeriesOnBall
          (fun q ↦ ∫ z, F (cauchyFueterKernel (γ' z) q) (g' z) ∂volume.comap Subtype.val)
          P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)))
    (hγ₁ : ∀ i, ContinuousOn (γ₁ i) (Icc (lo i) (hi i)))
    (hγ₀ : ∀ i, ContinuousOn (γ₀ i) (Icc (lo i) (hi i)))
    (hg₁ : ∀ i, ContinuousOn (g₁ i) (Icc (lo i) (hi i)))
    (hg₀ : ∀ i, ContinuousOn (g₀ i) (Icc (lo i) (hi i)))
    (hδ₀ : 0 < δ)
    (hδ₁ : ∀ i, ∀ u ∈ Icc (lo i) (hi i), δ ≤ ‖γ₁ i u - q₀‖)
    (hδ₀' : ∀ i, ∀ u ∈ Icc (lo i) (hi i), δ ≤ ‖γ₀ i u - q₀‖)
    (heq : ∀ q ∈ Metric.eball q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)),
      f q = (1 / (2 * Real.pi ^ 2)) • ∑ i : ι,
        ((∫ u in Icc (lo i) (hi i), F (cauchyFueterKernel (γ₁ i u) q) (g₁ i u)) -
          ∫ u in Icc (lo i) (hi i), F (cauchyFueterKernel (γ₀ i u) q) (g₀ i u))) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f q₀)
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  choose P₁ hP₁ using fun i : ι ↦
    exists_hasFPowerSeriesOnBall_setIntegral_Icc (hF i) (hγ₁ i) (hg₁ i) hδ₀ (hδ₁ i)
  choose P₀ hP₀ using fun i : ι ↦
    exists_hasFPowerSeriesOnBall_setIntegral_Icc (hF i) (hγ₀ i) (hg₀ i) hδ₀ (hδ₀' i)
  have hsum := Finset.univ.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀))
    fun i _ ↦ (hP₁ i).sub (hP₀ i)
  exact ((hsum.const_smul (c := (1 / (2 * Real.pi ^ 2) : ℝ))).congr fun q hq ↦ by
    simpa [Pi.smul_apply, Pi.sub_apply] using (heq q hq).symm).inv_factorial_smul_iteratedFDeriv

/-- Any quaternion `q ∈ eball (dq x₀) ((√2 - 1) δ)` (`δ > 0`) is of the form `dq x` with
`‖dq x - dq x₀‖ < δ`. -/
private theorem exists_dq_eq_and_norm_sub_lt_of_mem_eball {x₀ : Fin 4 → ℝ} {q : ℍ} {δ : ℝ}
    (hδ₀ : 0 < δ)
    (hq : q ∈ Metric.eball (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ))) :
    ∃ x : Fin 4 → ℝ, dq x = q ∧ ‖dq x - dq x₀‖ < δ := by
  let x := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q
  have hqx : dq x = q := by simp [x, coe_dq]
  refine ⟨x, hqx, ?_⟩
  have h1 : ‖q - dq x₀‖ < (Real.sqrt 2 - 1) * δ := by
    rwa [Metric.mem_eball, edist_dist, dist_eq_norm,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)] at hq
  rw [hqx]
  nlinarith [Real.sqrt_two_lt_three_halves]

/-! ### Quantitative power-series expansions on affine parallelepipeds -/

/-- Quantitative Taylor power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of a function
continuous on a positively oriented affine parallelepiped and left Fueter regular on its interior,
whose eight boundary faces all lie at Euclidean distance at least `δ > 0` from `dq x₀`. -/
theorem LeftFueterOn.hasFPowerSeriesOnBall_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : LeftFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ (j : Fin 4) {c : ℝ}, (c = 0 ∨ c = 1) →
      ∀ u ∈ Icc (0 : Fin 3 → ℝ) 1, δ ≤ ‖dq (p + L (j.insertNth c u)) - dq x₀‖) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hface_cont (j : Fin 4) (c : ℝ) (hc' : c ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun u : Fin 3 → ℝ ↦
        ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
          f (dq (p + L (j.insertNth c u)))) (Icc 0 1) :=
    continuousOn_const.mul (hc.comp (by fun_prop) fun _ hu ↦
      mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩)))
  refine hasFPowerSeriesOnBall_of_eq_smul_sum_sub_Icc (F := (· * ·))
    (lo := fun _ ↦ 0) (hi := fun _ ↦ 1)
    (fun _ γ' hne hδ' {_} hg' ↦ ⟨_, hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul γ' hne
      hδ₀ hδ' hg'⟩)
    (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
    (fun j ↦ hface_cont j 1 (right_mem_Icc.2 zero_le_one))
    (fun j ↦ hface_cont j 0 (left_mem_Icc.2 zero_le_one))
    hδ₀ (fun j ↦ hδ j (Or.inr rfl)) (fun j ↦ hδ j (Or.inl rfl)) fun q hq ↦ ?_
  obtain ⟨x, rfl, hlt⟩ := exists_dq_eq_and_norm_sub_lt_of_mem_eball hδ₀ hq
  have hmem : L.symm (x - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1 :=
    mem_pi_Ioo_of_norm_dq_sub_lt (a := 0) (b := 1) (p := p) L.toLinearMap
      (fun i ↦ (hx₀ i (mem_univ i)).1) (fun i ↦ (hx₀ i (mem_univ i)).2)
      (by simpa using hδ) (by simpa using hlt)
  rw [left_cauchyFueter_affine (x₀ := x) hL hc (hf.mono sdiff_subset) hmem]
  simp only [ContinuousLinearMap.rawAffineBoundary_eq, ContinuousLinearMap.mulLeftRight_apply,
    mul_assoc, ContinuousLinearEquiv.coe_coe]

/-- Quantitative Taylor power-series expansion on `eball (dq x₀) ((√2 - 1) δ)` of a function
continuous on a positively oriented affine parallelepiped and right Fueter regular on its
interior. -/
theorem RightFueterOn.hasFPowerSeriesOnBall_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    {f : ℍ → ℍ} (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : RightFueterOn f (dq '' ((fun u ↦ p + L u) '' pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
    {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ (j : Fin 4) {c : ℝ}, (c = 0 ∨ c = 1) →
      ∀ u ∈ Icc (0 : Fin 3 → ℝ) 1, δ ≤ ‖dq (p + L (j.insertNth c u)) - dq x₀‖) :
    HasFPowerSeriesOnBall f (fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀))
      (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hface_cont (j : Fin 4) (c : ℝ) (hc' : c ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun u : Fin 3 → ℝ ↦
        f (dq (p + L (j.insertNth c u))) *
          ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) (Icc 0 1) :=
    (hc.comp (by fun_prop) fun _ hu ↦
      mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩))).mul
      continuousOn_const
  refine hasFPowerSeriesOnBall_of_eq_smul_sum_sub_Icc (F := fun k w ↦ w * k)
    (lo := fun _ ↦ 0) (hi := fun _ ↦ 1)
    (fun _ γ' hne hδ' {_} hg' ↦ ⟨_, hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel γ' hne
      hδ₀ hδ' hg'⟩)
    (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
    (fun j ↦ hface_cont j 1 (right_mem_Icc.2 zero_le_one))
    (fun j ↦ hface_cont j 0 (left_mem_Icc.2 zero_le_one))
    hδ₀ (fun j ↦ hδ j (Or.inr rfl)) (fun j ↦ hδ j (Or.inl rfl)) fun q hq ↦ ?_
  obtain ⟨x, rfl, hlt⟩ := exists_dq_eq_and_norm_sub_lt_of_mem_eball hδ₀ hq
  have hmem : L.symm (x - p) ∈ pi univ fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1 :=
    mem_pi_Ioo_of_norm_dq_sub_lt (a := 0) (b := 1) (p := p) L.toLinearMap
      (fun i ↦ (hx₀ i (mem_univ i)).1) (fun i ↦ (hx₀ i (mem_univ i)).2)
      (by simpa using hδ) (by simpa using hlt)
  rw [right_cauchyFueter_affine (x₀ := x) hL hc (hf.mono sdiff_subset) hmem]
  simp only [ContinuousLinearMap.rawAffineBoundary_eq, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearEquiv.coe_coe]

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

/-- **Identity principle for left Fueter regular functions.** Two functions left Fueter
regular on a connected open set that agree near one of its points agree on the whole set. -/
theorem eqOn_of_preconnected_of_eventuallyEq (hf : LeftFueterOn f s) (hg : LeftFueterOn g s)
    (hs : IsOpen s) (hc : IsPreconnected s) {q₀ : ℍ} (h₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc h₀ hfg

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

/-- **Identity principle for right Fueter regular functions.** Two functions right Fueter
regular on a connected open set that agree near one of its points agree on the whole set. -/
theorem eqOn_of_preconnected_of_eventuallyEq (hf : RightFueterOn f s) (hg : RightFueterOn g s)
    (hs : IsOpen s) (hc : IsPreconnected s) {q₀ : ℍ} (h₀ : q₀ ∈ s) (hfg : f =ᶠ[𝓝 q₀] g) :
    EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc h₀ hfg

end RightFueterOn

/-- Unlike one-variable holomorphic functions, a Fueter regular function on all of `ℍ` is not
determined by vanishing on a nonempty set whose every point is an accumulation point of that set:
there exist a nonzero globally left- and right-regular function `f` and such a zero set `Z`.
(The proof witnesses this with `q ↦ t + i x` on `{q | q.re = 0 ∧ q.imI = 0}`.) -/
theorem exists_leftFueterOn_and_rightFueterOn_univ_eqOn_zero_accPt :
    ∃ (f : ℍ → ℍ) (Z : Set ℍ),
      LeftFueterOn f univ ∧ RightFueterOn f univ ∧ Z.Nonempty ∧
      (∀ z ∈ Z, AccPt z (𝓟 Z)) ∧ EqOn f 0 Z ∧ f ≠ 0 := by
  refine ⟨fun q : ℍ ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ), {q : ℍ | q.re = 0 ∧ q.imI = 0},
    ?_, ?_, ⟨0, by simp⟩, ?_, ?_, ?_⟩
  · simpa using leftFueterOn_coeComplex_comp (U := univ) isOpen_univ differentiableOn_id
  · simpa using rightFueterOn_coeComplex_comp (U := univ) isOpen_univ differentiableOn_id
  · intro z hz
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    set w : ℍ := z + ⟨0, 0, ε / 2, 0⟩
    have hw_ne : w ≠ z := by
      intro heq
      have h := congrArg QuaternionAlgebra.imJ heq
      simp [w] at h
      linarith
    have hw_mem : w ∈ U := hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : w - z = dq ![0, 0, ε / 2, 0] := by ext <;> simp [w, dq_apply]
      rw [hsub]
      have hsq : ‖dq ![0, 0, ε / 2, 0]‖ ^ 2 = (ε / 2) ^ 2 := by
        rw [norm_dq_sq, Fin.sum_univ_four]
        simp
      have hnorm : ‖dq ![0, 0, ε / 2, 0]‖ = ε / 2 :=
        (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq
      linarith)
    exact ⟨w, ⟨hw_mem, by simp [w, hz.1], by simp [w, hz.2]⟩, hw_ne⟩
  · rintro z ⟨hre, him⟩
    ext <;> simp [hre, him]
  · intro hf0
    have h1 := congrFun hf0 1
    simpa using congrArg QuaternionAlgebra.re h1

end TauCeti
