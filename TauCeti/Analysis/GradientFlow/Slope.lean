/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The descending slope of an energy

For an extended-real energy `φ : X → EReal` on an extended metric space, the *descending slope*
(or *local slope*) of `φ` at `x` is

`|∂φ|(x) = limsup_{y → x, y ≠ x} (φ x - φ y)⁺ / d(x, y)`,

the steepest rate at which `φ` can decrease near `x`. It is the metric replacement for the norm of
the gradient: for a function on a real normed space that is differentiable at `x`, the descending
slope is the operator norm of the derivative (`HasFDerivAt.descendingSlope_eq`). The descending
slope is the basic object of the theory of gradient flows in metric spaces of
Ambrosio–Gigli–Savaré: curves of maximal slope, the energy-dissipation inequality and the slope
estimates for minimizing movements are all phrased through it.

The positive part `(φ x - φ y)⁺` is `EReal.toENNReal (φ x - φ y)`. Ambrosio–Gigli–Savaré define
the slope only on the effective domain `{x | φ x ≠ ⊤}`; the formula here is total, and its value
off the effective domain carries no meaning.

## Main definitions

* `TauCeti.descendingSlope φ x`: the descending slope of `φ` at `x`, an extended nonnegative real.

## Main results

* `TauCeti.descendingSlope_le_of_eventually_le`: an upper bound for the slope from a local bound
  on the decrease of `φ`.
* `IsLocalMin.descendingSlope_eq_zero`: the slope vanishes at a local minimum.
* `LipschitzOnWith.descendingSlope_le` and `LipschitzWith.descendingSlope_le`: the slope of a
  function that is `K`-Lipschitz near `x` is at most `K`.
* `TauCeti.descendingSlope_const_mul`: positive homogeneity of the slope of real-valued
  functions.
* `HasFDerivAt.descendingSlope_eq`: on a real normed space the slope of a function differentiable
  at `x` is the norm of its derivative; `HasDerivAt.descendingSlope_eq` is the one-variable case.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 1, Section 1.2.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section EMetricSpace

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {x : X}

/-- The *descending slope* (or *local slope*) of an energy `φ` at `x`: the upper limit, as `y → x`
with `y ≠ x`, of the rate of decrease `(φ x - φ y)⁺ / d(x, y)`. At an isolated point the slope is
`0`. -/
def descendingSlope (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  limsup (fun y ↦ (φ x - φ y).toENNReal / edist x y) (𝓝[≠] x)

/-- The defining formula of the descending slope, as an upper limit of rates of decrease. -/
theorem descendingSlope_def (φ : X → EReal) (x : X) :
    descendingSlope φ x = limsup (fun y ↦ (φ x - φ y).toENNReal / edist x y) (𝓝[≠] x) :=
  (rfl)

/-- For a real-valued function, the positive part in the descending slope is
`ENNReal.ofReal (f x - f y)`. -/
theorem descendingSlope_coe (f : X → ℝ) (x : X) :
    descendingSlope (fun y ↦ (f y : EReal)) x =
      limsup (fun y ↦ ENNReal.ofReal (f x - f y) / edist x y) (𝓝[≠] x) := by
  simp only [descendingSlope_def, ← EReal.coe_sub, EReal.real_coe_toENNReal]

/-- If near `x` the energy decreases at most like `C * d(x, y)`, then the descending slope of `φ`
at `x` is at most `C`. -/
theorem descendingSlope_le_of_eventually_le {C : ℝ≥0∞}
    (h : ∀ᶠ y in 𝓝[≠] x, (φ x - φ y).toENNReal ≤ C * edist x y) : descendingSlope φ x ≤ C := by
  rw [descendingSlope_def]
  exact limsup_le_of_le (h := h.mono fun _ hy ↦ ENNReal.div_le_of_le_mul hy)

/-- The descending slope vanishes at a local minimum. -/
theorem _root_.IsLocalMin.descendingSlope_eq_zero (h : IsLocalMin φ x) :
    descendingSlope φ x = 0 :=
  nonpos_iff_eq_zero.1 <| descendingSlope_le_of_eventually_le <| by
    filter_upwards [nhdsWithin_le_nhds h] with y hy
    rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.2 hy)]
    exact bot_le

/-- The descending slope of a constant energy vanishes. -/
@[simp]
theorem descendingSlope_const (c : EReal) (x : X) : descendingSlope (fun _ ↦ c) x = 0 :=
  isLocalMin_const.descendingSlope_eq_zero

/-- The descending slope at `x` of a function that is `K`-Lipschitz on a neighbourhood of `x` is at
most `K`. -/
theorem _root_.LipschitzOnWith.descendingSlope_le {f : X → ℝ} {K : ℝ≥0} {s : Set X}
    (hf : LipschitzOnWith K f s) (hs : s ∈ 𝓝 x) :
    descendingSlope (fun y ↦ (f y : EReal)) x ≤ K := by
  refine descendingSlope_le_of_eventually_le ?_
  filter_upwards [nhdsWithin_le_nhds hs] with y hy
  rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
  calc ENNReal.ofReal (f x - f y) ≤ ENNReal.ofReal |f x - f y| :=
        ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = edist (f x) (f y) := by rw [edist_dist, Real.dist_eq]
    _ ≤ K * edist x y := hf (mem_of_mem_nhds hs) hy

/-- The descending slope of a `K`-Lipschitz function is at most `K` everywhere. -/
theorem _root_.LipschitzWith.descendingSlope_le {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : X) : descendingSlope (fun y ↦ (f y : EReal)) x ≤ K :=
  hf.lipschitzOnWith.descendingSlope_le univ_mem

/-- Scaling a real-valued function by `c ≥ 0` scales its descending slope by `c`. -/
theorem descendingSlope_const_mul {c : ℝ} (hc : 0 ≤ c) (f : X → ℝ) (x : X) :
    descendingSlope (fun y ↦ ((c * f y : ℝ) : EReal)) x =
      ENNReal.ofReal c * descendingSlope (fun y ↦ (f y : EReal)) x := by
  rw [descendingSlope_coe, descendingSlope_coe,
    ← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr 1 with y
  rw [← mul_sub, ENNReal.ofReal_mul hc, mul_div_assoc]

end EMetricSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E}

/-- The descending slope at `x` of a function differentiable at `x` is at most the norm of its
derivative. -/
private theorem descendingSlope_le_enorm_of_hasFDerivAt (hf : HasFDerivAt f f' x) :
    descendingSlope (fun y ↦ (f y : EReal)) x ≤ ‖f'‖ₑ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ descendingSlope_le_of_eventually_le ?_
  filter_upwards [nhdsWithin_le_nhds (hf.isLittleO.bound hε)] with y hy
  have h₁ : -f' (y - x) ≤ ‖f'‖ * ‖y - x‖ := (neg_le_abs _).trans (f'.le_opNorm _)
  have h₂ := (neg_le_abs _).trans (Real.norm_eq_abs _ ▸ hy)
  have key : f x - f y ≤ (‖f'‖ + ε) * ‖y - x‖ :=
    calc f x - f y = -(f y - f x - f' (y - x)) + -f' (y - x) := by ring
      _ ≤ ε * ‖y - x‖ + ‖f'‖ * ‖y - x‖ := add_le_add h₂ h₁
      _ = (‖f'‖ + ε) * ‖y - x‖ := by ring
  rw [← EReal.coe_sub, EReal.real_coe_toENNReal, edist_comm, edist_eq_enorm_sub]
  simpa [ENNReal.ofReal_mul (add_nonneg (norm_nonneg f') ε.coe_nonneg), ENNReal.ofReal_add,
    ofReal_norm] using ENNReal.ofReal_le_ofReal key

/-- The descending slope at `x` of a function differentiable at `x` is at least the norm of its
derivative: the function decreases at rate close to `‖f'‖` along a ray `t ↦ x - t • w` on which
`f'` nearly attains its norm. -/
private theorem enorm_le_descendingSlope_of_hasFDerivAt (hf : HasFDerivAt f f' x) :
    ‖f'‖ₑ ≤ descendingSlope (fun y ↦ (f y : EReal)) x := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg] at hr
  -- Choose a direction `w` with `‖w‖ < 1` along which `f'` exceeds `r`.
  obtain ⟨v, hv, hrv⟩ := f'.exists_lt_apply_of_lt_opNorm hr
  obtain ⟨w, hw, hrw⟩ : ∃ w : E, ‖w‖ < 1 ∧ (r : ℝ) < f' w := by
    rcases le_total 0 (f' v) with h | h
    · exact ⟨v, hv, by rwa [Real.norm_of_nonneg h] at hrv⟩
    · exact ⟨-v, by rwa [norm_neg], by rwa [map_neg, ← Real.norm_of_nonpos h]⟩
  have hw₀ : w ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hrw
    exact (r.coe_nonneg.trans_lt hrw).false
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw₀
  -- Along the ray `t ↦ x - t • w`, the rates of decrease tend to `f' w / ‖w‖ > r`.
  have hderiv : HasDerivAt (fun t : ℝ ↦ f (x - t • w)) (f' (-w)) 0 := by
    refine hf.comp_hasDerivAt_of_eq (x := (0 : ℝ)) ?_ (by simp)
    simpa using (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) w).const_sub x
  have hlim : Tendsto (fun t : ℝ ↦ (f x - f (x - t • w)) / (t * ‖w‖)) (𝓝[>] 0)
      (𝓝 (f' w / ‖w‖)) := by
    have := ((hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
      (nhdsWithin_mono _ fun t (ht : 0 < t) ↦ ht.ne')).neg.div_const ‖w‖
    refine (this.congr' (eventually_nhdsWithin_of_forall fun t (_ : 0 < t) ↦ ?_)).trans
      (by rw [map_neg, neg_neg])
    simp only [slope_def_field, zero_smul, sub_zero, ← neg_div, neg_sub, div_div]
  have hmap : Tendsto (fun t : ℝ ↦ x - t • w) (𝓝[>] 0) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (Continuous.tendsto' (by fun_prop) 0 x (by simp))
    · simpa [sub_eq_self] using smul_ne_zero ht.ne' hw₀
  have hquot : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (f x - f (x - t • w)) / edist x (x - t • w))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (f' w / ‖w‖))) := by
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hlim).congr'
      (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
    simp [edist_eq_enorm_sub, ← ofReal_norm, norm_smul, abs_of_pos ht,
      ENNReal.ofReal_div_of_pos (mul_pos ht hwpos)]
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (f' w / ‖w‖) := by
        refine ENNReal.ofReal_le_ofReal (hrw.le.trans ?_)
        exact le_div_self (r.coe_nonneg.trans hrw.le) hwpos hw.le
    _ = limsup (fun t : ℝ ↦ ENNReal.ofReal (f x - f (x - t • w)) / edist x (x - t • w))
          (𝓝[>] 0) := hquot.limsup_eq.symm
    _ ≤ descendingSlope (fun y ↦ (f y : EReal)) x := by
        rw [descendingSlope_coe]
        exact (limsup_comp (fun y ↦ ENNReal.ofReal (f x - f y) / edist x y) (fun t ↦ x - t • w)
          (𝓝[>] 0)).trans_le (limsup_le_limsup_of_le hmap)

/-- On a real normed space, the descending slope at `x` of a function with derivative `f'` at `x`
is the norm of `f'`: the function decreases fastest in the direction opposite to where `f'`
is largest. -/
theorem _root_.HasFDerivAt.descendingSlope_eq (hf : HasFDerivAt f f' x) :
    descendingSlope (fun y ↦ (f y : EReal)) x = ‖f'‖ₑ :=
  le_antisymm (descendingSlope_le_enorm_of_hasFDerivAt hf)
    (enorm_le_descendingSlope_of_hasFDerivAt hf)

/-- The descending slope at `t` of a real function of a real variable with derivative `D` at `t`
is `|D|`. -/
theorem _root_.HasDerivAt.descendingSlope_eq {g : ℝ → ℝ} {D t : ℝ} (hg : HasDerivAt g D t) :
    descendingSlope (fun u ↦ (g u : EReal)) t = ‖D‖ₑ := by
  rw [hg.hasFDerivAt.descendingSlope_eq]
  simp only [enorm_eq_nnnorm, ContinuousLinearMap.nnnorm_toSpanSingleton]

end NormedSpace

end TauCeti
