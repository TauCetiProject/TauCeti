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
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.CStarAlgebra.Basic
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Analytic.Constructions
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
symmetric Taylor series `n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀)` and letting `r → δ`
yields a `HasFPowerSeriesOnBall` for `f` at `dq x₀` on the full ball
`eball (dq x₀) ((√2 - 1) * δ)` without any boundary continuity hypothesis
(`LeftFueterOn.exists_hasFPowerSeriesOnBall_of_box`). Inscribing the open cube of half-side `R / 2`
in an open Euclidean ball `ball q₀ R` gives radius `(√2 - 1) * (R / 2)` for any function left
Fueter regular on `ball q₀ R` (`LeftFueterOn.exists_hasFPowerSeriesOnBall_of_ball`). All
right-sided counterparts follow with the exact same radii through the reflection
`q ↦ star (f (star q))` (`RightFueterOn.star_star`), the reflected coordinate boxes
(`image_star_image_dq_pi_Ioo`), and the real linear isometry `starₗᵢ ℝ`.

Combining real analyticity with the analytic identity principle yields the uniqueness principle on
preconnected open sets: two left (or right) Fueter regular functions that agree on an open set
meeting the domain, or share all iterated real Fréchet derivatives at one point, coincide throughout
the preconnected open domain. Unlike in one complex variable, agreement on a set with accumulation
points does not suffice in four real dimensions: `q ↦ ((⟨q.re, q.imI⟩ : ℂ) : ℍ)` is both left and
right Fueter regular on `ℍ` and vanishes on the two-dimensional subspace
`{q | q.re = 0 ∧ q.imI = 0}`, every point of which is an accumulation point, without vanishing
identically.

## Main declarations

* `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_of_box`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_of_box`,
  `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall_of_ball`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall_of_ball`: quantitative power-series
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

open Filter Metric Quaternion Set Topology
open scoped ContDiff ENNReal Nat NNReal Pointwise

namespace TauCeti

open TauCeti.Quaternion

/-! ### Private conjugation transport helper -/

private theorem exists_hasFPowerSeriesOnBall_of_star_star {f : ℍ → ℍ} {q₀ : ℍ} {r : ℝ≥0∞}
    (h : ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall (fun q ↦ star (f (star q))) P (star q₀) r) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ, HasFPowerSeriesOnBall f P q₀ r := by
  obtain ⟨P, hP⟩ := h
  let u := (starₗᵢ ℝ : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearIsometry
  have hu (q : ℍ) : u q = star q := by
    rw [LinearIsometryEquiv.coe_toLinearIsometry, coe_starₗᵢ]
  rw [← hu q₀] at hP
  have hcomp := u.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hP.compLinearIsometry
  refine ⟨_, hcomp.congr fun x _ ↦ ?_⟩
  simp only [Function.comp_apply, LinearIsometry.coe_toContinuousLinearMap, hu, star_star]

/-! ### Quantitative power-series expansions of Fueter regular functions -/

/-- If `f` is pointwise left Fueter regular on the open coordinate box
`dq '' pi univ (fun i ↦ Ioo (a i) (b i))` and `x₀` lies at coordinate distance at least `δ > 0`
from every face, then `f` admits a convergent formal multilinear series on
`eball (dq x₀) ((√2 - 1) * δ)`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_of_box
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ : ℝ}
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hδ₀ : 0 < δ) (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hc₀ : 0 < Real.sqrt 2 - 1 := sub_pos.2 Real.one_lt_sqrt_two
  have hsqrt : Real.sqrt 2 - 1 < 1 := by
    have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by positivity)).2 (by norm_num)
    linarith
  have hshrunk (r : ℝ) (hr₀ : 0 < r) (hr : r < δ) :
      ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
        HasFPowerSeriesOnBall f P (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * r)) := by
    let a' : Fin 4 → ℝ := fun i ↦ x₀ i - r
    let b' : Fin 4 → ℝ := fun i ↦ x₀ i + r
    have hab' : a' ≤ b' := fun i ↦ by dsimp only [a', b']; linarith
    have hsub_closed : dq '' Icc a' b' ⊆ dq '' pi univ (fun i ↦ Ioo (a i) (b i)) := by
      refine image_mono fun x hx i _ ↦ ?_
      have h1 : x₀ i - r ≤ x i := hx.1 i
      have h2 : x i ≤ x₀ i + r := hx.2 i
      exact ⟨by linarith [(hδ i).1], by linarith [(hδ i).2]⟩
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
      · have h1 : r ≤ |a' i - x₀ i| := by
          dsimp only [a']
          rw [abs_of_nonpos] <;> linarith
        exact h1.trans (by simpa using abs_sub_apply_le_norm_dq_sub (i.insertNth (a' i) z) x₀ i)
      · have h2 : r ≤ |b' i - x₀ i| := by
          dsimp only [b']
          rw [abs_of_nonneg] <;> linarith
        exact h2.trans (by simpa using abs_sub_apply_le_norm_dq_sub (i.insertNth (b' i) z) x₀ i)
    obtain ⟨P, hP⟩ :=
      exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul hab' hc' hr₀ hface
    let cL : ℍ →L[ℝ] ℍ := (1 / (2 * Real.pi ^ 2)) • ContinuousLinearMap.id ℝ ℍ
    have hcP := cL.comp_hasFPowerSeriesOnBall hP
    refine ⟨_, hcP.congr fun q hq ↦ ?_⟩
    have hrad_pos : 0 < (Real.sqrt 2 - 1) * r := mul_pos hc₀ hr₀
    have hnorm : ‖q - dq x₀‖ < (Real.sqrt 2 - 1) * r := by
      rw [Metric.mem_eball, edist_dist, dist_eq_norm] at hq
      exact (ENNReal.ofReal_lt_ofReal_iff hrad_pos).1 hq
    have hnorm_r : ‖q - dq x₀‖ < r := hnorm.trans (by nlinarith)
    obtain ⟨x, rfl⟩ := dq_surjective q
    have hcoord (i : Fin 4) : |x i - x₀ i| < r :=
      (abs_sub_apply_le_norm_dq_sub x x₀ i).trans_lt hnorm_r
    have ha' (i : Fin 4) : a' i < x i := by
      dsimp only [a']
      linarith [(abs_lt.1 (hcoord i)).1]
    have hb' (i : Fin 4) : x i < b' i := by
      dsimp only [b']
      linarith [(abs_lt.1 (hcoord i)).2]
    simpa [cL] using (left_cauchyFueter_box hc' (hf'.mono sdiff_subset) ha' hb').symm
  have hmid {t : ℝ} (ht₀ : 0 ≤ t) (ht : t < (Real.sqrt 2 - 1) * δ) :
      ∃ r : ℝ, 0 < r ∧ r < δ ∧ t < (Real.sqrt 2 - 1) * r := by
    have hdiv : t / (Real.sqrt 2 - 1) < δ := (div_lt_iff₀ hc₀).2 (by simpa [mul_comm] using ht)
    refine ⟨(t / (Real.sqrt 2 - 1) + δ) / 2, by linarith [div_nonneg ht₀ hc₀.le], by linarith, ?_⟩
    have hlt : t / (Real.sqrt 2 - 1) < (t / (Real.sqrt 2 - 1) + δ) / 2 := by linarith
    have := (div_lt_iff₀ hc₀).1 hlt
    linarith
  let Q : FormalMultilinearSeries ℝ ℍ ℍ := fun n ↦ (n ! : ℝ)⁻¹ • iteratedFDeriv ℝ n f (dq x₀)
  refine ⟨Q, ?_, ENNReal.ofReal_pos.2 (mul_pos hc₀ hδ₀), ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_
    rw [← ENNReal.ofReal_coe_nnreal] at hρ
    have hρ_lt : (ρ : ℝ) < (Real.sqrt 2 - 1) * δ :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc₀ hδ₀)).1 hρ
    obtain ⟨r, hr₀, hr, hρr⟩ := hmid ρ.coe_nonneg hρ_lt
    obtain ⟨P, hP⟩ := hshrunk r hr₀ hr
    have hnorm (n : ℕ) : ‖Q n‖ ≤ ‖P n‖ := by
      refine ContinuousMultilinearMap.opNorm_le_bound
        (ContinuousMultilinearMap.opNorm_nonneg (P n)) fun v ↦ ?_
      rw [smul_apply, hP.iteratedFDeriv_eq_sum_of_completeSpace,
        norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
      calc (n ! : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin n), P n (fun i ↦ v (σ i))‖
        _ ≤ (n ! : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ‖P n (fun i ↦ v (σ i))‖ := by
            gcongr
            exact norm_sum_le _ _
        _ ≤ (n ! : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ‖P n‖ * ∏ i, ‖v (σ i)‖ := by
            gcongr
            exact (P n).le_opNorm _
        _ = (n ! : ℝ)⁻¹ * ∑ _σ : Equiv.Perm (Fin n), ‖P n‖ * ∏ i, ‖v i‖ := by
            congr 1
            refine Finset.sum_congr rfl fun σ _ ↦ ?_
            rw [Fintype.prod_equiv σ _ (fun i ↦ ‖v i‖) (fun _ ↦ rfl)]
        _ = ‖P n‖ * ∏ i, ‖v i‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
              nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero),
              one_mul]
    calc (ρ : ℝ≥0∞) = ENNReal.ofReal (ρ : ℝ) := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal ((Real.sqrt 2 - 1) * r) := ENNReal.ofReal_le_ofReal hρr.le
      _ ≤ P.radius := hP.r_le
      _ ≤ Q.radius := FormalMultilinearSeries.radius_le_of_le hnorm
  · intro y hy
    rw [Metric.mem_eball, edist_dist, dist_zero_right] at hy
    have hy_lt : ‖y‖ < (Real.sqrt 2 - 1) * δ :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc₀ hδ₀)).1 hy
    obtain ⟨r, hr₀, hr, hyr⟩ := hmid (norm_nonneg y) hy_lt
    obtain ⟨P, hP⟩ := hshrunk r hr₀ hr
    have hy' : y ∈ eball 0 (ENNReal.ofReal ((Real.sqrt 2 - 1) * r)) := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right]
      exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc₀ hr₀)).2 hyr
    simpa only [Q, smul_apply] using hP.hasSum_iteratedFDeriv hy'

/-- If `f` is pointwise right Fueter regular on the open coordinate box
`dq '' pi univ (fun i ↦ Ioo (a i) (b i))` and `x₀` lies at coordinate distance at least `δ > 0`
from every face, then `f` admits a convergent formal multilinear series on
`eball (dq x₀) ((√2 - 1) * δ)`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_of_box
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} {δ : ℝ}
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hδ₀ : 0 < δ) (hδ : ∀ i : Fin 4, a i + δ ≤ x₀ i ∧ x₀ i + δ ≤ b i) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
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
  have h := hf'.exists_hasFPowerSeriesOnBall_of_box hδ₀ hδ'
  rw [← star_dq x₀] at h
  exact exists_hasFPowerSeriesOnBall_of_star_star h

/-- A function pointwise left Fueter regular on `ball q₀ R` (`R > 0`) admits a convergent formal
multilinear series at `q₀` of radius at least `(√2 - 1) * (R / 2)`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall_of_ball
    {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ} (hf : LeftFueterOn f (ball q₀ R)) (hR : 0 < R) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
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
  exact (hf.mono hsub_open).exists_hasFPowerSeriesOnBall_of_box (half_pos hR)
    (fun i ↦ ⟨by simp [a], by simp [b]⟩)

/-- A function pointwise right Fueter regular on `ball q₀ R` (`R > 0`) admits a convergent formal
multilinear series at `q₀` of radius at least `(√2 - 1) * (R / 2)`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall_of_ball
    {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ} (hf : RightFueterOn f (ball q₀ R)) (hR : 0 < R) :
    ∃ P : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f P q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * (R / 2))) := by
  have hf' : LeftFueterOn (fun x ↦ star (f (star x))) (ball (star q₀) R) := by
    have h := hf.star_star
    rwa [Set.image_star, Metric.star_ball] at h
  exact exists_hasFPowerSeriesOnBall_of_star_star
    (hf'.exists_hasFPowerSeriesOnBall_of_ball hR)

/-! ### Real analyticity and smoothness -/

namespace LeftFueterOn

variable {f g : ℍ → ℍ} {s : Set ℍ} {q : ℍ}

/-- A function left Fueter regular on a neighbourhood of `q` is real analytic at `q`. -/
theorem analyticAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q) : AnalyticAt ℝ f q := by
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hs
  obtain ⟨_, hP⟩ := (hf.mono hball).exists_hasFPowerSeriesOnBall_of_ball hR
  exact hP.analyticAt

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
open set `s` that agree on an open set `t` meeting `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_eqOn_open
    (hf : LeftFueterOn f s) (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {t : Set ℍ} (ht : IsOpen t) (hne : (s ∩ t).Nonempty) (hfg : EqOn f g t) :
    EqOn f g s := by
  obtain ⟨q₀, hqs, hqt⟩ := hne
  exact (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc
    hqs (hfg.eventuallyEq_of_mem (ht.mem_nhds hqt))

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
  obtain ⟨_, hP⟩ := (hf.mono hball).exists_hasFPowerSeriesOnBall_of_ball hR
  exact hP.analyticAt

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
preconnected open set `s` that agree on an open set `t` meeting `s` agree throughout `s`. -/
theorem eqOn_of_isPreconnected_of_eqOn_open
    (hf : RightFueterOn f s) (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s)
    {t : Set ℍ} (ht : IsOpen t) (hne : (s ∩ t).Nonempty) (hfg : EqOn f g t) :
    EqOn f g s := by
  obtain ⟨q₀, hqs, hqt⟩ := hne
  exact (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc
    hqs (hfg.eventuallyEq_of_mem (ht.mem_nhds hqt))

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
