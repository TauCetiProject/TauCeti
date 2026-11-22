/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Analysis.BoundedVariation.DerivativeMeasure
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Distributional variation and Lebesgue points on the real line

On the real line the variational total variation `|Du|(Ω)` (`TauCeti.totalVariationOn`) bounds the
classical variation of the Lebesgue values of any locally integrable function `u`. If
`x₀ ≤ x₁ ≤ ⋯ ≤ xₘ` are Lebesgue points of `u` with values `v₀, …, vₘ`, in the sense that the
mean oscillation `⨍_{B(xᵢ, r)} |u - vᵢ|` tends to zero, and the closed interval `[x₀, xₘ]` lies
in `Ω`, then

`∑ᵢ |vᵢ₊₁ - vᵢ| ≤ |Du|(Ω)`

(`TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn`). In particular, if `x₀` and `x₁` are
Lebesgue points with values `v₀` and `v₁` such that the closed interval joining them lies in `Ω`,
then `|v₁ - v₀| ≤ |Du|(Ω)` (`TauCeti.Real.ofReal_abs_sub_le_totalVariationOn`). The test function
is a combination `∑ᵢ εᵢ (ψ (c (y - xᵢ)) - ψ (c (y - xᵢ₊₁)))` of smooth steps
`ψ = Real.smoothTransition` with signs `εᵢ = sign (vᵢ - vᵢ₊₁)`. Since the steps decrease along the
points, the combination is bounded by the telescoping sum `ψ (c (y - x₀)) - ψ (c (y - xₘ)) ≤ 1`.
Its derivative is a combination of approximate identities concentrating to the right of the points,
so its pairing with `u` converges to `∑ᵢ |vᵢ₊₁ - vᵢ|` as `c → ∞`.

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

end TauCeti.Real
