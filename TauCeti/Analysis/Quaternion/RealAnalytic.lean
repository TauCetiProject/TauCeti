/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Analytic
public import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Real analyticity of Fueter regular functions

A function that is left (or right) Fueter regular, in the pointwise sense, on an open set of
`ℍ` is real analytic there. Around a point `q₀` choose the coordinate cube of half-side `d`
centred at `q₀`, contained in the regularity domain. The box Cauchy–Fueter formula writes `f`
inside the cube as `1 / (2π²)` times the boundary sum of `G(q - p) * eᵢ * f(q)`, where `G` is the
Cauchy–Fueter kernel, the pole `p` is the evaluation point and `q` runs over the faces. As a
function of the pole, each face integral is a Cauchy–Fueter potential with a continuous density,
and it has a power series at `q₀` converging on the ball of radius `(√2 - 1) d`, because the
faces stay at distance at least `d` from `q₀`. That ball lies inside the open cube, so `f` has
the same power series there.

Consequences: Fueter regular functions on open sets are `C^∞` and satisfy the identity principle,
two regular functions on a connected open set that agree near one point agreeing everywhere.
Continuity of the derivative is never assumed.

## Main declarations

* `TauCeti.LeftFueterOn.exists_hasFPowerSeriesOnBall`,
  `TauCeti.RightFueterOn.exists_hasFPowerSeriesOnBall`: a function continuous on the closed ball
  of radius `2 * d` about `q₀` and regular inside it has a power series at `q₀` converging on the
  ball of radius `(√2 - 1) * d`.
* `TauCeti.LeftFueterOn.analyticOnNhd`, `TauCeti.RightFueterOn.analyticOnNhd`: real analyticity
  on open sets.
* `TauCeti.LeftFueterOn.contDiffOn`, `TauCeti.RightFueterOn.contDiffOn`: smoothness.
* `TauCeti.LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq` and its right counterpart: the
  identity principle.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9 and the remark after it.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Metric Set Filter
open scoped Quaternion Topology

namespace TauCeti

open TauCeti.Quaternion

/-! ### Power series of box potentials -/

section BoxPotentials

variable {a b x₀ : Fin 4 → ℝ} {δ : ℝ} {g : Fin 4 → (Fin 4 → ℝ) → ℍ}

/-- A face of the box `Icc a b` at coordinate distance at least `δ` from `x₀` stays at
Euclidean distance at least `δ` from `dq x₀`. -/
private theorem le_norm_dq_insertNth_sub (i : Fin 4) {c : ℝ} (hc : δ ≤ |c - x₀ i|)
    (x : Fin 3 → ℝ) : δ ≤ ‖dq (i.insertNth c x) - dq x₀‖ := by
  have h := abs_le_norm_dq (i.insertNth c x - x₀) i
  rw [Pi.sub_apply, Fin.insertNth_apply_same, map_sub] at h
  exact hc.trans h

/-- Each coordinate of the box `Icc a b` around `x₀` with face margins `δ` gives two faces at
coordinate distance at least `δ` from `x₀`. -/
private theorem le_abs_sub_of_face (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i)
    (i : Fin 4) : δ ≤ |b i - x₀ i| ∧ δ ≤ |a i - x₀ i| := by
  constructor
  · exact (hb i).trans (le_abs_self _)
  · exact (ha i).trans (by rw [abs_sub_comm]; exact le_abs_self _)

/-- A left Cauchy–Fueter box potential `q ↦ boxBoundarySum a b (fun i x ↦ G(dq x - q) * g i x)`
with densities continuous on the box has a power series at `dq x₀` converging on the ball of
radius `(√2 - 1) δ`, whenever every face lies at coordinate distance at least `δ > 0` from
`x₀`. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i)
    (hg : ∀ i, ContinuousOn (g i) (Icc a b)) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ, HasFPowerSeriesOnBall
      (fun q ↦ boxBoundarySum a b (fun i x ↦ cauchyFueterKernel (dq x) q * g i x)) p (dq x₀)
      (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hr : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)
  have hface (i : Fin 4) {c : ℝ} (hc : c ∈ Icc (a i) (b i)) (hcδ : δ ≤ |c - x₀ i|) :=
    exists_hasFPowerSeriesOnBall_setIntegral_cauchyFueterKernel_mul (μ := volume)
      (g := fun x ↦ g i (i.insertNth c x)) isCompact_Icc measurableSet_Icc
      (dq.continuous.comp (continuous_const.finInsertNth i continuous_id)).continuousOn hδ₀
      (fun x _ ↦ le_norm_dq_insertNth_sub i hcδ x)
      (((hg i).comp (continuous_const.finInsertNth i continuous_id).continuousOn
        fun _ hx ↦ Fin.insertNth_mem_Icc.2 ⟨hc, hx⟩).integrableOn_compact isCompact_Icc)
  have hab (i : Fin 4) : a i ≤ b i := by linarith [ha i, hb i]
  choose pb hpb using fun i ↦ hface i ⟨hab i, le_rfl⟩ (le_abs_sub_of_face ha hb i).1
  choose pa hpa using fun i ↦ hface i ⟨le_rfl, hab i⟩ (le_abs_sub_of_face ha hb i).2
  refine ⟨∑ i, (pb i - pa i), (Finset.univ.hasFPowerSeriesOnBall_fun_sum hr
    fun i _ ↦ (hpb i).sub (hpa i)).congr fun q _ ↦ ?_⟩
  simp only [boxBoundarySum_def, Pi.sub_apply, Function.comp_def, id_eq]

/-- A right Cauchy–Fueter box potential `q ↦ boxBoundarySum a b (fun i x ↦ g i x * G(dq x - q))`
with densities continuous on the box has a power series at `dq x₀` converging on the ball of
radius `(√2 - 1) δ`, whenever every face lies at coordinate distance at least `δ > 0` from
`x₀`. -/
theorem exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel (hδ₀ : 0 < δ)
    (ha : ∀ i, δ ≤ x₀ i - a i) (hb : ∀ i, δ ≤ b i - x₀ i)
    (hg : ∀ i, ContinuousOn (g i) (Icc a b)) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ, HasFPowerSeriesOnBall
      (fun q ↦ boxBoundarySum a b (fun i x ↦ g i x * cauchyFueterKernel (dq x) q)) p (dq x₀)
      (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hr : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hδ₀)
  have hface (i : Fin 4) {c : ℝ} (hc : c ∈ Icc (a i) (b i)) (hcδ : δ ≤ |c - x₀ i|) :=
    exists_hasFPowerSeriesOnBall_setIntegral_mul_cauchyFueterKernel (μ := volume)
      (g := fun x ↦ g i (i.insertNth c x)) isCompact_Icc measurableSet_Icc
      (dq.continuous.comp (continuous_const.finInsertNth i continuous_id)).continuousOn hδ₀
      (fun x _ ↦ le_norm_dq_insertNth_sub i hcδ x)
      (((hg i).comp (continuous_const.finInsertNth i continuous_id).continuousOn
        fun _ hx ↦ Fin.insertNth_mem_Icc.2 ⟨hc, hx⟩).integrableOn_compact isCompact_Icc)
  have hab (i : Fin 4) : a i ≤ b i := by linarith [ha i, hb i]
  choose pb hpb using fun i ↦ hface i ⟨hab i, le_rfl⟩ (le_abs_sub_of_face ha hb i).1
  choose pa hpa using fun i ↦ hface i ⟨le_rfl, hab i⟩ (le_abs_sub_of_face ha hb i).2
  refine ⟨∑ i, (pb i - pa i), (Finset.univ.hasFPowerSeriesOnBall_fun_sum hr
    fun i _ ↦ (hpb i).sub (hpa i)).congr fun q _ ↦ ?_⟩
  simp only [boxBoundarySum_def, Pi.sub_apply, Function.comp_def, id_eq]

end BoxPotentials

/-! ### Fueter regular functions -/

variable {f g : ℍ → ℍ} {s : Set ℍ} {q₀ : ℍ} {d : ℝ}

/-- The closed coordinate cube of half-side `d` about `x₀` maps into the closed ball of radius
`2 * d` about `dq x₀`. -/
private theorem dq_image_Icc_subset_closedBall (x₀ : Fin 4 → ℝ) (d : ℝ) :
    dq '' Icc (fun i ↦ x₀ i - d) (fun i ↦ x₀ i + d) ⊆ closedBall (dq x₀) (2 * d) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, dist_eq_norm, ← map_sub]
  refine norm_dq_le_two_mul fun i ↦ ?_
  rw [Pi.sub_apply, abs_le]
  constructor <;> linarith [hx.1 i, hx.2 i]

/-- The open coordinate cube of half-side `d` about `x₀` maps into the open ball of radius
`2 * d` about `dq x₀`. -/
private theorem dq_image_pi_Ioo_subset_ball (x₀ : Fin 4 → ℝ) (d : ℝ) :
    dq '' pi univ (fun i ↦ Ioo (x₀ i - d) (x₀ i + d)) ⊆ ball (dq x₀) (2 * d) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_ball, dist_eq_norm, ← map_sub]
  refine norm_dq_lt_two_mul fun i ↦ ?_
  rw [Pi.sub_apply, abs_lt]
  constructor <;> linarith [(hx i trivial).1, (hx i trivial).2]

/-- Points of the ball of radius `(√2 - 1) * d` about `dq x₀` lie in the open coordinate cube of
half-side `d` about `x₀`. -/
private theorem mem_pi_Ioo_of_mem_eball {x₀ x : Fin 4 → ℝ} (hd : 0 < d)
    (hx : dq x ∈ eball (dq x₀) (ENNReal.ofReal ((Real.sqrt 2 - 1) * d))) (i : Fin 4) :
    x₀ i - d < x i ∧ x i < x₀ i + d := by
  rw [mem_eball, edist_dist, dist_eq_norm,
    ENNReal.ofReal_lt_ofReal_iff (mul_pos (sub_pos.2 Real.one_lt_sqrt_two) hd), ← map_sub] at hx
  have hlt : |x i - x₀ i| < d := by
    have := abs_le_norm_dq (x - x₀) i
    simp only [Pi.sub_apply] at this
    nlinarith [Real.sqrt_two_lt_three_halves]
  constructor <;> linarith [abs_lt.1 hlt]

/-- **Power series of left Fueter regular functions.** A function continuous on the closed ball
of radius `2 * d` about `q₀` and left Fueter regular in the open ball has a power series at `q₀`
converging to it on the ball of radius `(√2 - 1) * d`. -/
theorem LeftFueterOn.exists_hasFPowerSeriesOnBall (hf : LeftFueterOn f (ball q₀ (2 * d)))
    (hc : ContinuousOn f (closedBall q₀ (2 * d))) (hd : 0 < d) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * d)) := by
  obtain ⟨x₀, rfl⟩ := dq_surjective q₀
  replace hc := hc.mono (dq_image_Icc_subset_closedBall x₀ d)
  obtain ⟨p, hp⟩ := exists_hasFPowerSeriesOnBall_boxBoundarySum_cauchyFueterKernel_mul hd
    (x₀ := x₀) (a := fun i ↦ x₀ i - d) (b := fun i ↦ x₀ i + d) (fun i ↦ by simp)
    (fun i ↦ by simp)
    (g := fun i x ↦ dq (Pi.single i 1) * f (dq x))
    fun i ↦ continuousOn_const.mul (hc.comp dq.continuous.continuousOn (mapsTo_image _ _))
  refine ⟨(1 / (2 * Real.pi ^ 2)) • p, hp.const_smul.congr fun q hq ↦ ?_⟩
  obtain ⟨x, rfl⟩ := dq_surjective q
  have hx := mem_pi_Ioo_of_mem_eball hd hq
  rw [Pi.smul_apply, left_cauchyFueter_box hc
    (hf.mono (sdiff_subset.trans (dq_image_pi_Ioo_subset_ball x₀ d)))
    (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)]
  simp only [mul_assoc]

/-- **Power series of right Fueter regular functions.** A function continuous on the closed ball
of radius `2 * d` about `q₀` and right Fueter regular in the open ball has a power series at `q₀`
converging to it on the ball of radius `(√2 - 1) * d`. -/
theorem RightFueterOn.exists_hasFPowerSeriesOnBall (hf : RightFueterOn f (ball q₀ (2 * d)))
    (hc : ContinuousOn f (closedBall q₀ (2 * d))) (hd : 0 < d) :
    ∃ p : FormalMultilinearSeries ℝ ℍ ℍ,
      HasFPowerSeriesOnBall f p q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * d)) := by
  obtain ⟨x₀, rfl⟩ := dq_surjective q₀
  replace hc := hc.mono (dq_image_Icc_subset_closedBall x₀ d)
  obtain ⟨p, hp⟩ := exists_hasFPowerSeriesOnBall_boxBoundarySum_mul_cauchyFueterKernel hd
    (x₀ := x₀) (a := fun i ↦ x₀ i - d) (b := fun i ↦ x₀ i + d) (fun i ↦ by simp)
    (fun i ↦ by simp)
    (g := fun i x ↦ f (dq x) * dq (Pi.single i 1))
    fun i ↦ (hc.comp dq.continuous.continuousOn (mapsTo_image _ _)).mul continuousOn_const
  refine ⟨(1 / (2 * Real.pi ^ 2)) • p, hp.const_smul.congr fun q hq ↦ ?_⟩
  obtain ⟨x, rfl⟩ := dq_surjective q
  have hx := mem_pi_Ioo_of_mem_eball hd hq
  rw [Pi.smul_apply, right_cauchyFueter_box hc
    (hf.mono (sdiff_subset.trans (dq_image_pi_Ioo_subset_ball x₀ d)))
    (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)]

/-- A function left Fueter regular on a neighbourhood of `q₀` is real analytic at `q₀`. -/
theorem LeftFueterOn.analyticAt (hf : LeftFueterOn f s) (hs : s ∈ 𝓝 q₀) :
    AnalyticAt ℝ f q₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hsub : closedBall q₀ (2 * (ε / 4)) ⊆ s := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨p, hp⟩ := (hf.mono (ball_subset_closedBall.trans hsub)).exists_hasFPowerSeriesOnBall
    (hf.mono hsub).differentiableOn.continuousOn (by positivity)
  exact hp.analyticAt

/-- A function right Fueter regular on a neighbourhood of `q₀` is real analytic at `q₀`. -/
theorem RightFueterOn.analyticAt (hf : RightFueterOn f s) (hs : s ∈ 𝓝 q₀) :
    AnalyticAt ℝ f q₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hsub : closedBall q₀ (2 * (ε / 4)) ⊆ s := (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨p, hp⟩ := (hf.mono (ball_subset_closedBall.trans hsub)).exists_hasFPowerSeriesOnBall
    (hf.mono hsub).differentiableOn.continuousOn (by positivity)
  exact hp.analyticAt

/-- **Real analyticity of left Fueter regular functions.** A function left Fueter regular on an
open set is real analytic there. -/
theorem LeftFueterOn.analyticOnNhd (hf : LeftFueterOn f s) (hs : IsOpen s) :
    AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- **Real analyticity of right Fueter regular functions.** A function right Fueter regular on
an open set is real analytic there. -/
theorem RightFueterOn.analyticOnNhd (hf : RightFueterOn f s) (hs : IsOpen s) :
    AnalyticOnNhd ℝ f s :=
  fun _ hq ↦ hf.analyticAt (hs.mem_nhds hq)

/-- A function left Fueter regular on an open set is smooth there, of every order including
`ω`. -/
theorem LeftFueterOn.contDiffOn (hf : LeftFueterOn f s) (hs : IsOpen s) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-- A function right Fueter regular on an open set is smooth there, of every order including
`ω`. -/
theorem RightFueterOn.contDiffOn (hf : RightFueterOn f s) (hs : IsOpen s) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n f s :=
  (hf.analyticOnNhd hs).contDiffOn_of_completeSpace

/-- **Identity principle for left Fueter regular functions.** Two functions left Fueter regular
on a connected open set that agree near one of its points agree on the whole set. -/
theorem LeftFueterOn.eqOn_of_preconnected_of_eventuallyEq (hf : LeftFueterOn f s)
    (hg : LeftFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s) (h₀ : q₀ ∈ s)
    (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc h₀ hfg

/-- **Identity principle for right Fueter regular functions.** Two functions right Fueter
regular on a connected open set that agree near one of its points agree on the whole set. -/
theorem RightFueterOn.eqOn_of_preconnected_of_eventuallyEq (hf : RightFueterOn f s)
    (hg : RightFueterOn g s) (hs : IsOpen s) (hc : IsPreconnected s) (h₀ : q₀ ∈ s)
    (hfg : f =ᶠ[𝓝 q₀] g) : EqOn f g s :=
  (hf.analyticOnNhd hs).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hs) hc h₀ hfg

end TauCeti
