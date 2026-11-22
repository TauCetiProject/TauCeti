/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Covering.DensityTheorem
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Analysis.BoundedVariation.DerivativeMeasure
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.VariationMeasure
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Dimension
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Variation and perimeter on the real line

On the real line the variational total variation `|Du|(Ω)` bounds the classical variation of
the Lebesgue values of `u`. If `x₀ ≤ x₁ ≤ ⋯ ≤ xₘ` are Lebesgue points of `u` with values
`v₀, …, vₘ`, in the sense that the mean oscillation `⨍_{B(xᵢ, r)} |u - vᵢ|` tends to zero, and
`[x₀, xₘ] ⊆ Ω`, then

`∑ᵢ |vᵢ₊₁ - vᵢ| ≤ |Du|(Ω)`

(`TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn`). The test function is a combination
`∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` of smooth steps `ψ = Real.smoothTransition`
with signs `εᵢ = sign (vᵢ - vᵢ₊₁)`. Since the steps decrease along the points, the
combination is bounded by the telescoping sum `ψ (c (y - x₀)) - ψ (c (y - xₘ)) ≤ 1`. Its
derivative is a combination of approximate identities concentrating to the right of the
points, so its pairing with `u` converges to `∑ᵢ |vᵢ₊₁ - vᵢ|` as `c → ∞`.

For the indicator of a set `s`, almost every point is a Lebesgue point with value `0` or `1`.
Counting alternations between points of `s` and of its complement gives the sharp
one-dimensional isoperimetric inequality and its rigidity:

* a null-measurable `s ⊆ ℝ` of positive finite measure has perimeter at least `2`
  (`TauCeti.Real.two_le_perimeter`);
* if `s` is null-measurable of finite measure and does not agree almost everywhere with any
  interval, then it has perimeter at least `4` (`TauCeti.Real.four_le_perimeter`);
* a nonempty bounded open interval has perimeter `2` (`TauCeti.Real.perimeter_Ioo`), and a
  null-measurable set of finite measure has perimeter `2` exactly when it agrees almost everywhere
  with such an interval (`TauCeti.Real.perimeter_eq_two_iff`).

These are the statements about almost every line section that slicing arguments for sets of
finite perimeter in higher dimensions apply: for a null-measurable set of finite volume, almost
every section of perimeter less than `4` is an interval of finite length up to a null set.

More locally, on any open interval `Ω ⊆ ℝ` (including open rays and the whole line), a set `s`
null-measurable for Lebesgue measure restricted to `Ω` whose perimeter with respect to Lebesgue
measure in `Ω` is strictly less than `1` is either null or conull in `Ω`
(`TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one`). Consequently, in any
one-dimensional real inner product space carrying an additive Haar measure, a set of locally finite
perimeter agrees almost everywhere on a sufficiently small ball around each point `x ∈ Ω` with `∅`,
`univ`, or a single half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}`
(`TauCeti.exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one`).

## Main results

* `TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn` and
  `TauCeti.Real.ofReal_abs_sub_le_totalVariationOn`: the variation of `u` along Lebesgue points in
  `Ω` (and between any two Lebesgue points) is at most `|Du|(Ω)`.
* `TauCeti.Real.two_le_perimeter`, `TauCeti.Real.four_le_perimeter`,
  `TauCeti.Real.perimeter_Ioo` and `TauCeti.Real.perimeter_eq_two_iff`.
* `TauCeti.Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one`: a null-measurable
  set on an open interval `Ω ⊆ ℝ` of perimeter strictly less than `1` in `Ω` is either null or
  conull there.
* `TauCeti.exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one`: local classification
  of sets of locally finite perimeter in dimension one.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.10 (functions of bounded variation of one variable).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (pointwise and essential variation in one variable).
-/

public section

open Filter Set MeasureTheory Metric TopologicalSpace TestFunction LineDeriv
open scoped Topology ENNReal Distributions BoundedContinuousFunction

namespace TauCeti.Real

/-- The combination `∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` of smooth steps at monotone
points, with coefficients of absolute value at most one, is bounded by one. -/
private theorem abs_sum_mul_smoothTransition_sub_le {m : ℕ} {x : Fin (m + 1) → ℝ}
    (hx : Monotone x) {ε : Fin m → ℝ} (hε : ∀ i, |ε i| ≤ 1) {c : ℝ} (hc : 0 ≤ c) (y : ℝ) :
    |∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ)))| ≤ 1 := by
  -- The steps decrease along the monotone points and telescope.
  have hd (i : Fin m) : 0 ≤ Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ)) :=
    sub_nonneg.2 (Real.smoothTransition.monotone (by gcongr; exact hx (Fin.castSucc_le_succ i)))
  calc _ ≤ ∑ i : Fin m, |ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
        Real.smoothTransition (c * (y - x i.succ)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, (Real.smoothTransition (c * (y - x i.castSucc)) -
        Real.smoothTransition (c * (y - x i.succ))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hd i)]
      exact mul_le_of_le_one_left (hd i) (hε i)
    _ = Real.smoothTransition (c * (y - x 0)) -
        Real.smoothTransition (c * (y - x (Fin.last m))) :=
      Fin.sum_univ_castSucc_sub_succ fun i => Real.smoothTransition (c * (y - x i))
    _ ≤ 1 := by
      linarith [Real.smoothTransition.le_one (c * (y - x 0)),
        Real.smoothTransition.nonneg (c * (y - x (Fin.last m)))]

/-- The combination of smooth steps at monotone points `x₀ ≤ ⋯ ≤ xₘ`, each rising on
`[xᵢ, xᵢ + c⁻¹]`, vanishes outside `[x₀, xₘ + c⁻¹]`. -/
private theorem sum_mul_smoothTransition_sub_eq_zero {m : ℕ} {x : Fin (m + 1) → ℝ}
    (hx : Monotone x) (ε : Fin m → ℝ) {c : ℝ} (hc : 0 < c) {y : ℝ}
    (hy : y ∉ Icc (x 0) (x (Fin.last m) + c⁻¹)) :
    ∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ))) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases not_and_or.1 hy with hy | hy
  · -- Left of every point all steps are `0`.
    have h (j) : Real.smoothTransition (c * (y - x j)) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith [hx (Fin.zero_le j)]))
    simp [h]
  · -- Right of every transition all steps are `1`.
    have h (j) : Real.smoothTransition (c * (y - x j)) = 1 := by
      refine Real.smoothTransition.one_of_one_le ?_
      calc (1 : ℝ) = c * c⁻¹ := (mul_inv_cancel₀ hc.ne').symm
        _ ≤ c * (y - x j) := by gcongr; linarith [hx (Fin.le_last j)]
    simp [h]

/-- The derivative of the smooth-step combination
`∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))`. -/
private theorem hasDerivAt_sum_mul_smoothTransition_sub {m : ℕ} (ε : Fin m → ℝ)
    (x : Fin (m + 1) → ℝ) {c : ℝ} (y : ℝ) :
    HasDerivAt (fun y => ∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
      Real.smoothTransition (c * (y - x i.succ))))
      (∑ i : Fin m, ε i * (c * deriv Real.smoothTransition (c * (y - x i.castSucc)) -
        c * deriv Real.smoothTransition (c * (y - x i.succ)))) y := by
  have hstep (p y : ℝ) : HasDerivAt (fun y => Real.smoothTransition (c * (y - p)))
      (c * deriv Real.smoothTransition (c * (y - p))) y :=
    (((hasDerivAt_id y).sub_const p).const_mul c).smoothTransition.congr_deriv
      (by rw [id, mul_one, mul_comm])
  exact HasDerivAt.fun_sum fun i _ => ((hstep _ y).sub (hstep _ y)).const_mul (ε i)

/-- The smooth-step combination `∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` is smooth. -/
private theorem contDiff_sum_mul_smoothTransition_sub {m : ℕ} {c : ℝ} (ε : Fin m → ℝ)
    (x : Fin (m + 1) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => ∑ i : Fin m, ε i *
      (Real.smoothTransition (c * (y - x i.castSucc)) -
        Real.smoothTransition (c * (y - x i.succ))) := by
  have hstep (p : ℝ) : ContDiff ℝ (⊤ : ℕ∞) fun y => Real.smoothTransition (c * (y - p)) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  exact ContDiff.sum fun i _ => contDiff_const.mul ((hstep _).sub (hstep _))

/-- **The smooth-step test function.** For monotone points `x₀ ≤ ⋯ ≤ xₘ` with
`[x₀, xₘ + c⁻¹] ⊆ Ω` and coefficients `|εᵢ| ≤ 1`, the combination
`∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` is a test function on `Ω` of sup norm at most one.
Its derivative pairs with `u` to the corresponding combination of the kernel pairings
`∫ c ψ'(c (y - xᵢ)) u y dy`, which is therefore at most `|Du|(Ω)`. -/
private theorem ofReal_sum_mul_sub_le_totalVariationOn {Ω : Opens ℝ} {u : ℝ → ℝ} {m : ℕ}
    {x : Fin (m + 1) → ℝ} (hx : Monotone x) {ε : Fin m → ℝ} (hε : ∀ i, |ε i| ≤ 1) {c : ℝ}
    (hc : 0 < c) (hΩ : Icc (x 0) (x (Fin.last m) + c⁻¹) ⊆ Ω)
    (hu : ∀ i, IntegrableOn u (closedBall (x i) c⁻¹)) :
    ENNReal.ofReal (∑ i : Fin m, ε i *
      ((∫ y, c * deriv Real.smoothTransition (c * (y - x i.castSucc)) * u y) -
        ∫ y, c * deriv Real.smoothTransition (c * (y - x i.succ)) * u y)) ≤
      totalVariationOn volume Ω u := by
  have hkint (i) : Integrable fun y => c * deriv Real.smoothTransition (c * (y - x i)) * u y := by
    simpa only [smul_eq_mul] using
      Real.smoothTransition.integrable_mul_deriv_mul_sub_smul hc (hu i)
  set I : ℝ → ℝ := fun p => ∫ y, c * deriv Real.smoothTransition (c * (y - p)) * u y
  set g : ℝ → ℝ := fun y => ∑ i : Fin m, ε i * (Real.smoothTransition (c * (y - x i.castSucc)) -
    Real.smoothTransition (c * (y - x i.succ)))
  have hgd (y) : HasDerivAt g _ y := hasDerivAt_sum_mul_smoothTransition_sub (c := c) ε x y
  have hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sum_mul_smoothTransition_sub ε x
  have hg0 (y) (hy : y ∉ Icc (x 0) (x (Fin.last m) + c⁻¹)) : g y = 0 :=
    sum_mul_smoothTransition_sub_eq_zero hx ε hc hy
  have hts : tsupport g ⊆ Ω :=
    (isClosed_Icc.closure_subset_iff.2 (Function.support_subset_iff'.2 hg0)).trans hΩ
  let T : 𝓓(Ω, ℝ) := ⟨g, hgsmooth, HasCompactSupport.intro isCompact_Icc hg0, hts⟩
  -- Its derivative pairs with `u` to the combination of the kernel pairings.
  have hpair : ∫ y, ∂_{(1 : ℝ)} T y * u y =
      ∑ i : Fin m, ε i * (I (x i.castSucc) - I (x i.succ)) := by
    have hT (y) : ∂_{(1 : ℝ)} T y = ∑ i : Fin m, ε i *
        (c * deriv Real.smoothTransition (c * (y - x i.castSucc)) -
          c * deriv Real.smoothTransition (c * (y - x i.succ))) := by
      rw [lineDerivOp_one_apply_eq_deriv, coe_mk, (hgd y).deriv]
    simp_rw [hT, Finset.sum_mul, mul_assoc, sub_mul]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_sub (hkint _) (hkint _)]
    · exact ((hkint _).sub (hkint _)).const_mul _
  have hTnorm : ‖(T : ℝ →ᵇ ℝ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 ((BoundedContinuousFunction.norm_le zero_le_one).2
      (abs_sum_mul_smoothTransition_sub_le hx hε hc.le))
  rw [← hpair]
  calc ENNReal.ofReal (∫ y, ∂_{(1 : ℝ)} T y * u y)
      ≤ ENNReal.ofReal |∫ y, ∂_{(1 : ℝ)} T y * u y| := ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ‖(1 : ℝ)‖ₑ * ‖(T : ℝ →ᵇ ℝ)‖ₑ * totalVariationOn volume Ω u :=
        ofReal_abs_integral_lineDeriv_mul_le_enorm_mul_enorm_mul_totalVariationOn T 1
    _ ≤ totalVariationOn volume Ω u := by
        rw [eNorm_one, one_mul]
        exact mul_le_of_le_one_left zero_le hTnorm

/-- **The variation along Lebesgue points is bounded by the total variation.** Let
`x₀ ≤ x₁ ≤ ⋯ ≤ xₘ` be points with `[x₀, xₘ] ⊆ Ω` at which `u` has Lebesgue values `vᵢ`, that
is, the mean oscillation `⨍_{B(xᵢ, r)} |u - vᵢ|` tends to zero as `r → 0`. Then
`∑ᵢ |vᵢ₊₁ - vᵢ| ≤ |Du|(Ω)`. -/
theorem ofReal_sum_abs_sub_le_totalVariationOn {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u Ω) {m : ℕ} {x v : Fin (m + 1) → ℝ} (hx : Monotone x)
    (hΩ : Icc (x 0) (x (Fin.last m)) ⊆ Ω)
    (hv : ∀ i, Tendsto (fun r => ⨍ y in closedBall (x i) r, ‖u y - v i‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal (∑ i : Fin m, |v i.succ - v i.castSucc|) ≤ totalVariationOn volume Ω u := by
  set K := Icc (x 0) (x (Fin.last m))
  have hxK (i) : x i ∈ K := ⟨hx (Fin.zero_le i), hx (Fin.le_last i)⟩
  obtain ⟨δ, hδ, hδΩ⟩ := isCompact_Icc.exists_cthickening_subset_open Ω.isOpen hΩ
  have huL : IntegrableOn u (cthickening δ K) :=
    hu.integrableOn_compact_subset hδΩ isCompact_Icc.cthickening
  -- The signs `ε i` are chosen so that `ε i (v i - v (i + 1)) = |v (i + 1) - v i|`.
  set ε : Fin m → ℝ := fun i => SignType.sign (v i.castSucc - v i.succ)
  have hε (i) : |ε i| ≤ 1 := by
    simp only [ε]
    cases SignType.sign (v i.castSucc - v i.succ) <;> simp
  -- The pairings of `u` with the rescaled kernels `c ψ'(c (y - p))` converge to the values.
  set I : ℝ → ℝ → ℝ := fun c p => ∫ y, c * deriv Real.smoothTransition (c * (y - p)) * u y
  have hlim : Tendsto (fun c => ∑ i : Fin m, ε i * (I c (x i.castSucc) - I c (x i.succ))) atTop
      (𝓝 (∑ i : Fin m, |v i.succ - v i.castSucc|)) := by
    have hI (i) : Tendsto (fun c => I c (x i)) atTop (𝓝 (v i)) := by
      simpa only [smul_eq_mul] using
        Real.smoothTransition.tendsto_integral_mul_deriv_mul_sub_smul ⟨cthickening δ K,
          mem_of_superset (closedBall_mem_nhds _ hδ) (closedBall_subset_cthickening (hxK i) δ),
          huL⟩ (hv i)
    refine tendsto_finsetSum _ fun i _ => ?_
    rw [abs_sub_comm, ← self_mul_sign, mul_comm]
    exact ((hI _).sub (hI _)).const_mul _
  -- For large `c` each combination is bounded by the smooth-step test function.
  refine le_of_tendsto (ENNReal.tendsto_ofReal hlim) ?_
  filter_upwards [eventually_gt_atTop δ⁻¹] with c hc
  have hc0 : 0 < c := lt_trans (inv_pos.2 hδ) hc
  have hball (p) (hp : p ∈ K) : closedBall p c⁻¹ ⊆ cthickening δ K :=
    (closedBall_subset_closedBall (inv_lt_of_inv_lt₀ hδ hc).le).trans
      (closedBall_subset_cthickening hp δ)
  refine ofReal_sum_mul_sub_le_totalVariationOn hx hε hc0 (fun y hy => hδΩ ?_)
    fun i => huL.mono_set (hball _ (hxK i))
  rcases le_total y (x (Fin.last m)) with h | h
  · exact self_subset_cthickening K ⟨hy.1, h⟩
  · refine hball _ (hxK (Fin.last m)) ?_
    rw [Real.closedBall_eq_Icc]
    exact ⟨by linarith [inv_pos.2 hc0], hy.2⟩

/-- **Two-point variation bound along Lebesgue points.** If `u` is locally integrable on `Ω` and
has Lebesgue values `v₀` at `x₀` and `v₁` at `x₁`, with `[x₀, x₁] ⊆ Ω` (regardless of order),
then `|v₁ - v₀| ≤ |Du|(Ω)`. -/
theorem ofReal_abs_sub_le_totalVariationOn {Ω : Opens ℝ} {u : ℝ → ℝ}
    (hu : LocallyIntegrableOn u Ω) {x₀ x₁ v₀ v₁ : ℝ}
    (hΩ : uIcc x₀ x₁ ⊆ Ω)
    (hv₀ : Tendsto (fun r => ⨍ y in closedBall x₀ r, ‖u y - v₀‖) (𝓝[>] 0) (𝓝 0))
    (hv₁ : Tendsto (fun r => ⨍ y in closedBall x₁ r, ‖u y - v₁‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal |v₁ - v₀| ≤ totalVariationOn volume Ω u := by
  wlog hle : x₀ ≤ x₁ generalizing x₀ x₁ v₀ v₁
  · rw [abs_sub_comm]
    exact this (uIcc_comm x₀ x₁ ▸ hΩ) hv₁ hv₀ (le_of_not_ge hle)
  have h := ofReal_sum_abs_sub_le_totalVariationOn hu (x := ![x₀, x₁]) (v := ![v₀, v₁])
    (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; exact hle)
    (by simpa [uIcc_of_le hle] using hΩ)
    fun i => by fin_cases i <;> assumption
  simpa [Fin.sum_univ_succ] using h

/-- Monotone Lebesgue points of the indicator of a measurable set `s` bound its perimeter from
below by the number of alternations between `s` and its complement. -/
private theorem ofReal_sum_le_perimeter {s : Set ℝ} (hs : MeasurableSet s) {m : ℕ}
    {x : Fin (m + 1) → ℝ} (hx : Monotone x)
    (hxs : ∀ i, Tendsto (fun r => ⨍ y in closedBall (x i) r,
      ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) (x i)‖) (𝓝[>] 0) (𝓝 0)) :
    ENNReal.ofReal (∑ i : Fin m,
      |s.indicator 1 (x i.succ) - s.indicator (1 : ℝ → ℝ) (x i.castSucc)|)
      ≤ perimeter volume ⊤ s := by
  have hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) ((⊤ : Opens ℝ) : Set ℝ) := by
    rw [Pi.one_def]
    exact ((locallyIntegrable_const 1).indicator hs).locallyIntegrableOn _
  rw [perimeter_def]
  exact ofReal_sum_abs_sub_le_totalVariationOn (v := fun i => s.indicator 1 (x i)) hu hx
    (by simp) hxs

/-- A null-measurable set agrees almost everywhere with a measurable set of the same perimeter
and measure. -/
private theorem exists_measurableSet_ae_eq {s : Set ℝ} (hs : NullMeasurableSet s) :
    ∃ t, MeasurableSet t ∧ s =ᵐ[volume] t ∧ perimeter volume ⊤ s = perimeter volume ⊤ t ∧
      volume s = volume t :=
  ⟨toMeasurable volume s, measurableSet_toMeasurable _ _, hs.toMeasurable_ae_eq.symm,
    perimeter_congr_ae (ae_restrict_of_ae hs.toMeasurable_ae_eq.symm),
    (measure_toMeasurable s).symm⟩

/-- A set `s ⊆ ℝ` of finite measure misses almost every point of each ray, so a property holding
almost everywhere holds at some point outside `s` to the left of `b` and at some point outside `s`
to the right of `b'`. -/
private theorem exists_notMem_lt_and_gt {s : Set ℝ} (hfin : volume s ≠ ∞) {P : ℝ → Prop}
    (hP : ∀ᵐ x, P x) (b b' : ℝ) : (∃ a < b, a ∉ s ∧ P a) ∧ ∃ c > b', c ∉ s ∧ P c := by
  obtain ⟨a, ⟨hab, has⟩, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := Iio b \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Iio hfin]; exact ENNReal.top_ne_zero)
    (ae_restrict_of_ae hP)
  obtain ⟨c, ⟨hb'c, hcs⟩, hc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := Ioi b' \ s)
    (by rw [measure_sdiff_eq_top Real.volume_Ioi hfin]; exact ENNReal.top_ne_zero)
    (ae_restrict_of_ae hP)
  exact ⟨⟨a, hab, has, ha⟩, c, hb'c, hcs, hc⟩

private theorem two_le_perimeter_of_measurableSet {s : Set ℝ} (hs : MeasurableSet s)
    (h0 : volume s ≠ 0) (hfin : volume s ≠ ∞) : 2 ≤ perimeter volume ⊤ s := by
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := s.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator hs)
  -- A Lebesgue point of `s`, with Lebesgue points of the complement on either side.
  obtain ⟨b, hbs, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae h0 (ae_restrict_of_ae hae)
  obtain ⟨⟨a, hab, has, ha⟩, c, hbc, hcs, hc⟩ := exists_notMem_lt_and_gt hfin hae b b
  have h := ofReal_sum_le_perimeter hs (x := ![a, b, c])
    (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i <;> simp [hab.le, hbc.le])
    (fun i => by fin_cases i <;> assumption)
  simpa [Fin.sum_univ_succ, has, hbs, hcs, one_add_one_eq_two] using h

private theorem four_le_perimeter_of_measurableSet {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (h : ∀ I : Set ℝ, I.OrdConnected → ¬s =ᵐ[volume] I) :
    4 ≤ perimeter volume ⊤ s := by
  set P : ℝ → Prop := fun x => Tendsto (fun r => ⨍ y in closedBall x r,
    ‖s.indicator 1 y - s.indicator (1 : ℝ → ℝ) x‖) (𝓝[>] 0) (𝓝 0)
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := s.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator hs)
  have hnull : volume {x | ¬P x} = 0 := ae_iff.1 hae
  -- Two Lebesgue points of `s` separated by a Lebesgue point of its complement.
  obtain ⟨b, z, b', hbz, hzb', hbs, hb, hzs, hz, hb's, hb'⟩ :
      ∃ b z b', b < z ∧ z < b' ∧ b ∈ s ∧ P b ∧ z ∉ s ∧ P z ∧ b' ∈ s ∧ P b' := by
    by_contra! hcon
    -- Otherwise `s` agrees a.e. with the interval spanned by its Lebesgue points.
    set I : Set ℝ := {y | ∃ b ∈ s, P b ∧ ∃ b' ∈ s, P b' ∧ b ≤ y ∧ y ≤ b'}
    have hI : I.OrdConnected := ⟨fun y₁ ⟨b, hbs, hb, _, _, _, hby, _⟩ y₂
      ⟨_, _, _, b', hb's, hb', _, hyb'⟩ y hy =>
        ⟨b, hbs, hb, b', hb's, hb', hby.trans hy.1, hy.2.trans hyb'⟩⟩
    have h₁ : s \ I ⊆ {x | ¬P x} := fun y ⟨hys, hyI⟩ hy =>
      hyI ⟨y, hys, hy, y, hys, hy, le_rfl, le_rfl⟩
    have h₂ : I \ s ⊆ {x | ¬P x} := fun y ⟨⟨b, hbs, hb, b', hb's, hb', hby, hyb'⟩, hys⟩ hy =>
      hcon b y b' (lt_of_le_of_ne hby (ne_of_mem_of_not_mem hbs hys))
        (lt_of_le_of_ne hyb' (ne_of_mem_of_not_mem hb's hys).symm) hbs hb hys hy hb's hb'
    exact h I hI (ae_eq_set.2 ⟨measure_mono_null h₁ hnull, measure_mono_null h₂ hnull⟩)
  -- Lebesgue points of the complement on either side.
  obtain ⟨⟨a, hab, has, ha⟩, c, hb'c, hcs, hc⟩ := exists_notMem_lt_and_gt hfin hae b b'
  have h := ofReal_sum_le_perimeter hs (x := ![a, b, z, b', c])
    (Fin.monotone_iff_le_succ.2 fun i => by
      fin_cases i <;> simp [hab.le, hbz.le, hzb'.le, hb'c.le])
    (fun i => by fin_cases i <;> assumption)
  have h4 : (1 + (1 + (1 + 1)) : ℝ) = 4 := by norm_num
  simpa [Fin.sum_univ_succ, has, hbs, hzs, hb's, hcs, h4] using h

/-- **The isoperimetric inequality on the line.** A null-measurable set of positive finite measure
in `ℝ` has perimeter at least two. -/
theorem two_le_perimeter {s : Set ℝ} (hs : NullMeasurableSet s) (h0 : volume s ≠ 0)
    (hfin : volume s ≠ ∞) : 2 ≤ perimeter volume ⊤ s := by
  obtain ⟨t, ht, -, hst, hvol⟩ := exists_measurableSet_ae_eq hs
  rw [hvol] at h0 hfin
  exact hst ▸ two_le_perimeter_of_measurableSet ht h0 hfin

/-- A null-measurable set of finite measure in `ℝ` that does not agree almost everywhere with any
interval has perimeter at least four. -/
theorem four_le_perimeter {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞)
    (h : ∀ I : Set ℝ, I.OrdConnected → ¬s =ᵐ[volume] I) : 4 ≤ perimeter volume ⊤ s := by
  obtain ⟨t, ht, hst, hP, hvol⟩ := exists_measurableSet_ae_eq hs
  rw [hvol] at hfin
  exact hP ▸ four_le_perimeter_of_measurableSet ht hfin fun I hI hI' => h I hI (hst.trans hI')

/-- A bounded open interval of `ℝ` has perimeter two. -/
theorem perimeter_Ioo {a b : ℝ} (hab : a < b) : perimeter volume ⊤ (Ioo a b) = 2 := by
  refine le_antisymm ?_ (two_le_perimeter measurableSet_Ioo.nullMeasurableSet (by simp [hab])
    (by simp))
  rw [perimeter_def, totalVariationOn_le_iff]
  intro φ hφ
  have hdiff : Differentiable ℝ φ := φ.contDiff.differentiable (by simp)
  have hint : ∫ x, divergenceCLM φ x * (Ioo a b).indicator 1 x = φ b - φ a := by
    simp_rw [divergenceCLM_apply_eq_deriv, ← indicator_mul_right, Pi.one_apply, mul_one]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hdiff x) ((φ.contDiff.continuous_deriv (by simp)).intervalIntegrable _ _)]
  rw [hint, ← ENNReal.ofReal_ofNat 2]
  refine ENNReal.ofReal_le_ofReal ?_
  have ha := hφ a
  have hb := hφ b
  rw [Real.norm_eq_abs, abs_le] at ha hb
  linarith

/-- **Equality in the isoperimetric inequality on the line.** A null-measurable set of finite
measure in `ℝ` has perimeter two exactly when it agrees almost everywhere with a nonempty bounded
open interval. -/
theorem perimeter_eq_two_iff {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s = 2 ↔ ∃ a b, a < b ∧ s =ᵐ[volume] Ioo a b := by
  refine ⟨fun h2 => ?_, fun ⟨a, b, hab, hsab⟩ => ?_⟩
  · -- A null set has perimeter zero, and otherwise a perimeter below four forces an interval.
    have h0 : volume s ≠ 0 := fun h0 => by
      rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.2 h0)), perimeter_empty] at h2
      norm_num at h2
    by_contra! hne
    refine absurd (four_le_perimeter hs hfin fun I hI hsI => ?_) (by rw [h2]; norm_num)
    obtain ⟨a, b, hab, hIab⟩ := hI.exists_ae_eq_Ioo ((measure_congr hsI).symm ▸ h0)
      ((measure_congr hsI).symm ▸ hfin)
    exact hne a b hab (hsI.trans hIab)
  · rw [perimeter_congr_ae (ae_restrict_of_ae hsab), perimeter_Ioo hab]

/-- A null-measurable set of finite length has perimeter at most two exactly when it agrees
almost everywhere with an interval, possibly empty. -/
theorem perimeter_le_two_iff {s : Set ℝ} (hs : NullMeasurableSet s) (hfin : volume s ≠ ∞) :
    perimeter volume ⊤ s ≤ 2 ↔ ∃ I : Set ℝ, I.OrdConnected ∧ s =ᵐ[volume] I := by
  refine ⟨fun hP ↦ ?_, fun ⟨I, hI, hsI⟩ ↦ ?_⟩
  · by_contra! hbad
    have hfour := four_le_perimeter hs hfin hbad
    have : (4 : ℝ≥0∞) ≤ 2 := hfour.trans hP
    norm_num at this
  · by_cases hzero : volume s = 0
    · rw [perimeter_congr_ae (ae_restrict_of_ae (ae_eq_empty.mpr hzero)), perimeter_empty]
      exact zero_le
    · obtain ⟨a, b, hab, hIab⟩ := hI.exists_ae_eq_Ioo
        ((measure_congr hsI).symm ▸ hzero) ((measure_congr hsI).symm ▸ hfin)
      exact (perimeter_eq_two_iff hs hfin).mpr ⟨a, b, hab, hsI.trans hIab⟩ |>.le

/-- **Local constancy below unit perimeter.** If a set `s ⊆ ℝ` is null-measurable on an open
interval `Ω ⊆ ℝ` and has perimeter strictly less than `1` in `Ω`, then either `s ∩ Ω` or
`Ω \ s` has measure zero. -/
theorem measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one {Ω : Opens ℝ}
    (hΩ : (Ω : Set ℝ).OrdConnected) {s : Set ℝ} (hs : NullMeasurableSet s (volume.restrict Ω))
    (hP : perimeter volume Ω s < 1) :
    volume (s ∩ Ω) = 0 ∨ volume ((Ω : Set ℝ) \ s) = 0 := by
  have hsI : NullMeasurableSet (s ∩ Ω) volume :=
    (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1 hs
  set t := toMeasurable volume (s ∩ Ω)
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have hst : (s ∩ Ω : Set ℝ) =ᵐ[volume] t := hsI.toMeasurable_ae_eq.symm
  have hstI : s =ᵐ[volume.restrict Ω] t :=
    eventuallyEqSet_iff.2 ((ae_restrict_iff' Ω.isOpen.measurableSet).2
      ((eventuallyEqSet_iff.1 hst).mono fun _ hy hyI => by simpa [hyI] using hy))
  have h1eq : volume (s ∩ Ω) = volume (t ∩ Ω) := by
    simpa [inter_assoc] using measure_congr (hst.inter (.refl _ (Ω : Set ℝ)))
  have h0eq : volume ((Ω : Set ℝ) \ s) = volume ((Ω : Set ℝ) \ t) := by
    have hdiff : (Ω : Set ℝ) \ (s ∩ Ω) = (Ω : Set ℝ) \ s := by ext y; simp
    rw [← hdiff]
    exact measure_congr ((Filter.EventuallyEqSet.refl _ (Ω : Set ℝ)).diff hst)
  -- Otherwise Lebesgue points of `t` and of its complement in `Ω` contribute at least `1`
  -- to the total variation on `Ω`.
  by_contra! hne
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume
    (f := t.indicator (1 : ℝ → ℝ)) ((locallyIntegrable_const 1).indicator ht)
  obtain ⟨y₁, ⟨hy₁t, hy₁I⟩, hy₁⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (s := t ∩ Ω)
    (h1eq ▸ hne.1) (ae_restrict_of_ae hae)
  obtain ⟨y₀, ⟨hy₀I, hy₀t⟩, hy₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := (Ω : Set ℝ) \ t) (h0eq ▸ hne.2) (ae_restrict_of_ae hae)
  simp only [indicator_of_mem hy₁t, Pi.one_apply] at hy₁
  simp only [indicator_of_notMem hy₀t] at hy₀
  have hu : LocallyIntegrableOn (t.indicator (1 : ℝ → ℝ)) Ω volume := by
    rw [Pi.one_def]
    exact ((locallyIntegrable_const 1).indicator ht).locallyIntegrableOn _
  have hle1 : (1 : ℝ≥0∞) ≤ perimeter volume Ω s := by
    rw [perimeter_congr_ae hstI, perimeter_def]
    simpa using ofReal_abs_sub_le_totalVariationOn hu (hΩ.uIcc_subset hy₀I hy₁I) hy₀ hy₁
  exact (not_le_of_gt hP) hle1

end TauCeti.Real

namespace TauCeti

section LocalClassification

open Module
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E}

/-- Around any `x ∈ Ω`, a set `s` of locally finite perimeter in `Ω` has volume-perimeter strictly
below `1` on a punctured ball `ball x r \ {x} ⊆ Ω`, by applying
`TauCeti.tendsto_totalVariationOn_ball_sdiff_singleton` to `|Dχ_s|`. -/
private theorem exists_ball_subset_and_perimeter_sdiff_singleton_lt_one
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) :
    ∃ r > 0, ball x r ⊆ Ω ∧
      perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1 := by
  obtain ⟨δ, hδ, hδΩ⟩ := nhds_basis_ball.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  set a := Measure.addHaarScalarFactor μ volume
  have ha0 : (a : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne'
  have hlim := tendsto_totalVariationOn_ball_sdiff_singleton hu hfin hx
  obtain ⟨r, hlt, hr, hrδ⟩ := ((hlim.eventually (gt_mem_nhds ha0.bot_lt)).and
    (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨r, hr, (ball_subset_ball hrδ.le).trans hδΩ, ?_⟩
  rw [← ENNReal.mul_lt_mul_iff_left ha0 ENNReal.coe_ne_top, one_mul, mul_comm,
    ← perimeter_eq_addHaarScalarFactor_mul volume, perimeter_def]
  exact hlt

/-- Along a linear isometry `e : E ≃ₗᵢ[ℝ] ℝ`, if `s` is null-measurable on `ball x r` (`r > 0`)
and has volume-perimeter strictly below `1` on `ball x r \ {x}`, then on the open half-ball
`ball x r ∩ {y | e y < e x}` either `s` or its complement is `μ`-null. -/
private theorem measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero (e : E ≃ₗᵢ[ℝ] ℝ) {r : ℝ}
    (hr : 0 < r) (hs : NullMeasurableSet s (μ.restrict (ball x r)))
    (hP : perimeter volume ⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ s < 1) :
    μ (s ∩ (ball x r ∩ {y | e y < e x})) = 0 ∨ μ ((ball x r ∩ {y | e y < e x}) \ s) = 0 := by
  set I := Ioo (e x - r) (e x)
  have hI : ball (e x) r ∩ Iio (e x) = I := by
    rw [Real.ball_eq_Ioo, Set.Ioo_inter_Iio, min_eq_right (le_add_of_nonneg_right hr.le)]
  have hpre : e ⁻¹' I = ball x r ∩ {y | e y < e x} := by
    rw [← hI, preimage_inter, e.preimage_ball, e.symm_apply_apply]
    rfl
  have hmaps : MapsTo e.symm (⟨I, isOpen_Ioo⟩ : Opens ℝ)
      (⟨ball x r \ {x}, isOpen_ball.sdiff isClosed_singleton⟩ : Opens E) := fun t ht => by
    have hmem : e.symm t ∈ ball x r ∩ {y | e y < e x} := by
      rw [← hpre]; simpa using ht
    exact ⟨hmem.1, fun h => (ne_of_lt hmem.2) (congrArg e h)⟩
  have hsB : NullMeasurableSet (s ∩ ball x r) volume :=
    ((nullMeasurableSet_restrict measurableSet_ball.nullMeasurableSet).1 hs).mono_ac
      (Measure.absolutelyContinuous_isAddHaarMeasure volume μ)
  have hsI : NullMeasurableSet (e.symm ⁻¹' s) (volume.restrict I) := by
    have h1 := (hsB.preimage e.symm.measurePreserving.quasiMeasurePreserving).mono
      (Measure.restrict_le_self : volume.restrict I ≤ volume)
    refine h1.congr (eventuallyEqSet_iff.2 ?_)
    exact (ae_restrict_mem measurableSet_Ioo).mono fun t ht => and_iff_left (hmaps ht).1
  have hPI : perimeter volume ⟨I, isOpen_Ioo⟩ (e.symm ⁻¹' s) < 1 :=
    (e.symm.perimeter_preimage_le e.symm.measurePreserving hmaps).trans_lt hP
  have hvol (A : Set ℝ) : volume (e ⁻¹' A) = volume A :=
    e.measurePreserving.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding A
  have hsymm : e ⁻¹' (e.symm ⁻¹' s) = s := e.toEquiv.preimage_symm_preimage s
  rcases Real.measure_inter_eq_zero_or_sdiff_eq_zero_of_perimeter_lt_one ordConnected_Ioo hsI
      hPI with h0 | h0
  · refine Or.inl (Measure.absolutelyContinuous_isAddHaarMeasure μ volume ?_)
    have heq : s ∩ (ball x r ∩ {y | e y < e x}) = e ⁻¹' (e.symm ⁻¹' s ∩ I) := by
      rw [preimage_inter, hsymm, hpre]
    simp only [Opens.coe_mk] at h0
    rw [heq, hvol, h0]
  · refine Or.inr (Measure.absolutelyContinuous_isAddHaarMeasure μ volume ?_)
    have heq : (ball x r ∩ {y | e y < e x}) \ s = e ⁻¹' (I \ e.symm ⁻¹' s) := by
      rw [preimage_sdiff, hsymm, hpre]
    simp only [Opens.coe_mk] at h0
    rw [heq, hvol, h0]

/-- Combining constancy on the two half-balls around `x` along `e : E ≃ₗᵢ[ℝ] ℝ` yields `∅`, `univ`,
or a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` almost everywhere on `ball x r`. -/
private theorem ae_eq_empty_or_univ_or_setOf_inner_lt_of_halves (e : E ≃ₗᵢ[ℝ] ℝ) {r : ℝ}
    (hL : μ (s ∩ (ball x r ∩ {y | e y < e x})) = 0 ∨ μ ((ball x r ∩ {y | e y < e x}) \ s) = 0)
    (hR : μ (s ∩ (ball x r ∩ {y | e x < e y})) = 0 ∨ μ ((ball x r ∩ {y | e x < e y}) \ s) = 0) :
    s =ᵐ[μ.restrict (ball x r)] (∅ : Set E) ∨ s =ᵐ[μ.restrict (ball x r)] univ ∨
      ∃ ν : E, ‖ν‖ = 1 ∧ s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫} := by
  have : Nontrivial E := ⟨⟨e.symm 1, 0, norm_ne_zero_iff.1 (by simp)⟩⟩
  have hnull (f : E ≃ₗᵢ[ℝ] ℝ) {A : Set E}
      (h₁ : μ (A ∩ (ball x r ∩ {y | f y < f x})) = 0)
      (h₂ : μ (A ∩ (ball x r ∩ {y | f x < f y})) = 0) :
      μ.restrict (ball x r) A = 0 := by
    rw [Measure.restrict_apply' measurableSet_ball]
    have hsub : A ∩ ball x r ⊆
        A ∩ (ball x r ∩ {y | f y < f x}) ∪ A ∩ (ball x r ∩ {y | f x < f y}) ∪ {x} :=
      fun y ⟨hyA, hyB⟩ => (lt_trichotomy (f y) (f x)).elim (fun h => .inl (.inl ⟨hyA, hyB, h⟩))
        fun h => h.elim (fun heq => .inr (f.injective heq)) fun hgt => .inl (.inr ⟨hyA, hyB, hgt⟩)
    exact measure_mono_null hsub (measure_union_null (measure_union_null h₁ h₂)
      (measure_singleton x))
  have hstep (f : E ≃ₗᵢ[ℝ] ℝ)
      (hlt : μ ((ball x r ∩ {y | f y < f x}) \ s) = 0)
      (hgt : μ (s ∩ (ball x r ∩ {y | f x < f y})) = 0) :
      ∃ ν : E, ‖ν‖ = 1 ∧ s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫} := by
    have hinner (y : E) : ⟪y, f.symm 1⟫ = f y := by simp [← f.inner_map_map]
    refine ⟨f.symm 1, by simp, ae_eq_set.2 ⟨?_, ?_⟩⟩
    · refine hnull f ?_ ?_
      · refine measure_mono_null ?_ measure_empty
        exact fun _ ⟨⟨_, hy⟩, _, h⟩ => hy (by simpa [hinner] using h)
      · refine measure_mono_null ?_ hgt
        exact fun _ ⟨hy, hyB⟩ => ⟨hy.1, hyB⟩
    · refine hnull f ?_ ?_
      · refine measure_mono_null ?_ hlt
        exact fun _ ⟨hy, hyB⟩ => ⟨hyB, hy.2⟩
      · refine measure_mono_null ?_ measure_empty
        exact fun _ ⟨⟨hy, _⟩, _, h⟩ => lt_asymm (by simpa [hinner] using hy) h
  rcases hL with hL0 | hL1 <;> rcases hR with hR0 | hR1
  · exact .inl (ae_eq_empty.2 (hnull e hL0 hR0))
  · refine .inr (.inr (hstep (e.trans (LinearIsometryEquiv.neg ℝ)) ?_ ?_))
    · simpa [neg_lt_neg_iff] using hR1
    · simpa [neg_lt_neg_iff] using hL0
  · exact .inr (.inr (hstep e hL1 hR0))
  · exact .inr (.inl (ae_eq_univ.2 (hnull e
      (by simpa [sdiff_eq_compl_inter, inter_comm] using hL1)
      (by simpa [sdiff_eq_compl_inter, inter_comm] using hR1))))

/-- **Local classification in dimension one.** Around every `x ∈ Ω`, a set `s` of locally finite
perimeter in `Ω` agrees `μ`-almost everywhere on some `ball x r ⊆ Ω` (`r > 0`) with `∅`, `univ`, or
a half-line `{y | ⟪y, ν⟫ < ⟪x, ν⟫}` (`‖ν‖ = 1`). -/
theorem exists_ae_eq_empty_or_univ_or_setOf_inner_lt_of_finrank_eq_one
    (hn : finrank ℝ E = 1) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hx : x ∈ Ω) :
    ∃ r > 0, ball x r ⊆ Ω ∧
      (s =ᵐ[μ.restrict (ball x r)] (∅ : Set E) ∨ s =ᵐ[μ.restrict (ball x r)] univ ∨
        ∃ ν : E, ‖ν‖ = 1 ∧ s =ᵐ[μ.restrict (ball x r)] {y | ⟪y, ν⟫ < ⟪x, ν⟫}) := by
  obtain ⟨r, hr, hrΩ, hP⟩ := exists_ball_subset_and_perimeter_sdiff_singleton_lt_one hu hfin hx
  obtain ⟨e⟩ := (nonempty_linearIsometryEquiv_iff_finrank_eq (𝕜 := ℝ) (E := E) (F := ℝ)).2
    (hn.trans (Module.finrank_self ℝ).symm)
  have hs : NullMeasurableSet s (μ.restrict (ball x r)) :=
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1
      hu.aestronglyMeasurable.aemeasurable).mono (Measure.restrict_mono hrΩ le_rfl)
  have hL := measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero e hr hs hP
  have hR := measure_inter_ball_inter_lt_eq_zero_or_sdiff_eq_zero
    (e.trans (LinearIsometryEquiv.neg ℝ)) hr hs hP
  have hR' : μ (s ∩ (ball x r ∩ {y | e x < e y})) = 0 ∨
      μ ((ball x r ∩ {y | e x < e y}) \ s) = 0 := by
    simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_neg, neg_lt_neg_iff]
      using hR
  exact ⟨r, hr, hrΩ, ae_eq_empty_or_univ_or_setOf_inner_lt_of_halves e hL hR'⟩

end LocalClassification

end TauCeti
