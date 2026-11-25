/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Examples.Planar
public import TauCeti.Analysis.Sobolev.W1p.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.Euclidean.Prod
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The harmonic function `r^{1/2} sin(θ/2)` on the slit disc

Let `u = TauCeti.PDE.slitSolution` be the function on the Euclidean plane given in polar
coordinates `x = (r cos θ, r sin θ)`, `0 ≤ θ ≤ 2π`, by

`u(x) = r^{1/2} sin(θ/2)`, that is, `u(x) = √((‖x‖ - x₀) / 2)`

(`TauCeti.PDE.slitSolution_polar`). It is the real part of `√(-z)` for `z = x₀ + i x₁`, so it is
harmonic off the closed ray `[0, ∞) × {0}`, and it vanishes exactly on that ray. On the slit disc
`Ω = B(0, 1) ∖ [0, 1) × {0}` (`TauCeti.slitUnitDisc`) it is therefore a classical solution of
Laplace's equation that is continuous on the closed disc, vanishes on the slit and equals
`sin(θ/2)` on the unit circle.

The tip of the slit makes the solution singular. Its gradient has length exactly `1 / (2 √‖x‖)`,
so:

* `u` is `1/2`-Hölder on the whole plane, but not `α`-Hölder for any `α > 1/2` on any part of the
  slit disc near the tip, where it equals `√t` at `(-t, 0)`;
* `u` lies in `W^{1,p}(Ω)` exactly for `p < 4`.

The slit disc is not a Lipschitz domain (`TauCeti.not_isLipschitzDomain_slitUnitDisc`). This is
the standard example showing that global regularity for the Dirichlet problem depends on the
boundary: at the tip of the slit, where the domain has a reentrant corner of opening `2π`, a
harmonic function vanishing on the nearby boundary can have its gradient outside `Lᵖ` for every
`p ≥ 4` and be no better than `1/2`-Hölder.

## Main declarations

* `TauCeti.PDE.slitSolution`: the function `√((‖x‖ - x₀) / 2)`, with
  `TauCeti.PDE.slitSolution_polar` (the polar form `r^{1/2} sin(θ/2)`),
  `TauCeti.PDE.slitSolution_toLp_neg_zero` (the value `√t` at `(-t, 0)`),
  `TauCeti.PDE.slitSolution_eq_zero_iff` (it vanishes exactly on `[0, ∞) × {0}`) and
  `TauCeti.PDE.slitSolution_le_sqrt_norm`.
* `TauCeti.PDE.harmonicAt_slitSolution`, `TauCeti.PDE.harmonicOnNhd_slitSolution_slitUnitDisc`:
  harmonicity off the ray, in particular on the slit disc.
* `TauCeti.PDE.norm_gradient_slitSolution`: `‖∇u(x)‖ = ‖x‖ ^ (-1/2) / 2` off the ray.
* `TauCeti.PDE.holderWith_slitSolution`, `TauCeti.PDE.not_holderOnWith_slitSolution`: `u` is
  `1/2`-Hölder with constant `1`, and no larger exponent works near the tip within the slit disc.
* `TauCeti.PDE.exists_w1p_value_ae_eq_slitSolution`: on a bounded open set off the ray, `u` lies
  in `W^{1,p}` for `p < 4`; `TauCeti.PDE.exists_w1p_value_ae_eq_slitSolution_iff`: on the slit
  disc, exactly then.

## References

* P. Grisvard, *Elliptic Problems in Nonsmooth Domains*, Chapter 4 (the singular solutions
  `r^{π/ω} sin(πθ/ω)` at a corner of opening `ω`; here `ω = 2π`).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set Real TopologicalSpace
open scoped NNReal ENNReal Topology Gradient

namespace TauCeti

namespace PDE

/-- The harmonic function `r^{1/2} sin(θ/2)` of the slit plane, `0 ≤ θ ≤ 2π`, written in
Cartesian coordinates as `√((‖x‖ - x₀) / 2)`. It vanishes on the ray `[0, ∞) × {0}`. -/
def slitSolution (x : WithLp 2 (ℝ × ℝ)) : ℝ :=
  √((‖x‖ - x.fst) / 2)

/-- Unfolding `TauCeti.PDE.slitSolution`. -/
theorem slitSolution_apply (x : WithLp 2 (ℝ × ℝ)) :
    slitSolution x = √((‖x‖ - x.fst) / 2) :=
  (rfl)

/-- The slit-plane solution is nonnegative. -/
theorem slitSolution_nonneg (x : WithLp 2 (ℝ × ℝ)) : 0 ≤ slitSolution x :=
  Real.sqrt_nonneg _

/-- The slit-plane solution is continuous on the whole plane. -/
theorem continuous_slitSolution : Continuous slitSolution :=
  ((continuous_norm.sub (WithLp.prod_continuous_ofLp 2 ℝ ℝ).fst).div_const 2).sqrt

/-- **The slit-plane solution vanishes exactly on the ray `[0, ∞) × {0}`.** -/
theorem slitSolution_eq_zero_iff {x : WithLp 2 (ℝ × ℝ)} :
    slitSolution x = 0 ↔ 0 ≤ x.fst ∧ x.snd = 0 := by
  rw [slitSolution, Real.sqrt_eq_zero',
    show (‖x‖ - x.fst) / 2 ≤ 0 ↔ ‖x‖ ≤ x.fst by constructor <;> intro h <;> linarith]
  constructor
  · intro h
    have h0 : 0 ≤ x.fst := (norm_nonneg x).trans h
    refine ⟨h0, ?_⟩
    have : ‖x‖ ^ 2 = x.fst ^ 2 + x.snd ^ 2 := by simp [WithLp.prod_norm_sq_eq_of_L2]
    nlinarith [norm_nonneg x, sq_nonneg x.snd]
  · rintro ⟨h0, h1⟩
    rw [WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero h1, Real.norm_of_nonneg h0]

/-- The slit-plane solution is positive exactly off the ray `[0, ∞) × {0}`. -/
theorem slitSolution_pos_iff {x : WithLp 2 (ℝ × ℝ)} :
    0 < slitSolution x ↔ x.fst < 0 ∨ x.snd ≠ 0 := by
  rw [(slitSolution_nonneg x).lt_iff_ne', Ne, slitSolution_eq_zero_iff, not_and_or, not_le]

/-- **Polar form of the slit-plane solution**: `u(r cos θ, r sin θ) = r^{1/2} sin(θ/2)` for
`r ≥ 0` and `0 ≤ θ ≤ 2π`. In particular it equals `sin(θ/2)` on the unit circle. -/
theorem slitSolution_polar {r θ : ℝ} (hr : 0 ≤ r) (hθ₀ : 0 ≤ θ) (hθ : θ ≤ 2 * π) :
    slitSolution (WithLp.toLp 2 (r * cos θ, r * sin θ)) = √r * sin (θ / 2) := by
  have hn : ‖WithLp.toLp 2 (r * cos θ, r * sin θ)‖ = r := by
    rw [← sq_eq_sq₀ (norm_nonneg _) hr, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [← mul_add, cos_sq_add_sin_sq, mul_one]
  have hs : 0 ≤ sin (θ / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hcos : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have h2 := cos_sq_add_sin_sq (θ / 2)
    have h3 := cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h3
    linarith
  have hsq : (r - r * (1 - 2 * sin (θ / 2) ^ 2)) / 2 = (√r * sin (θ / 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hr]
    ring
  rw [slitSolution, hn, WithLp.toLp_fst, hcos, hsq,
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg r) hs)]

/-- On the negative first axis the slit-plane solution is `√t` at `(-t, 0)`. -/
theorem slitSolution_toLp_neg_zero {t : ℝ} (ht : 0 ≤ t) :
    slitSolution (WithLp.toLp 2 (-t, 0)) = √t := by
  rw [slitSolution, WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero rfl, WithLp.toLp_fst,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg ht]
  ring_nf

/-- The slit-plane solution is at most `√‖x‖`. -/
theorem slitSolution_le_sqrt_norm (x : WithLp 2 (ℝ × ℝ)) : slitSolution x ≤ √‖x‖ :=
  Real.sqrt_le_sqrt (by linarith [(neg_le_abs x.fst).trans (WithLp.norm_fst_le (x := x))])

/-! ### Harmonicity -/

/-- The slit-plane solution is the real part of `√(-z)` for `z = x₀ + i x₁`, with the principal
branch of the square root. -/
private theorem slitSolution_eq_re_cpow (x : WithLp 2 (ℝ × ℝ)) :
    slitSolution x = ((-Complex.equivRealProdLp.symm x) ^ (2⁻¹ : ℂ)).re := by
  rw [Complex.cpow_inv_two_re, norm_neg, LinearIsometryEquiv.norm_map, Complex.neg_re,
    Complex.equivRealProdLp_symm_apply, slitSolution]
  simp [sub_eq_add_neg]

/-- The point `-(x₀ + i x₁)` lies in the slit plane of the principal branch exactly when `x` is
off the ray `[0, ∞) × {0}`. -/
private theorem neg_mem_slitPlane_iff {x : WithLp 2 (ℝ × ℝ)} :
    -Complex.equivRealProdLp.symm x ∈ Complex.slitPlane ↔ x.fst < 0 ∨ x.snd ≠ 0 := by
  simp [Complex.mem_slitPlane_iff]

/-- **The slit-plane solution is harmonic off the ray `[0, ∞) × {0}`**, as the real part of the
holomorphic function `√(-z)`. -/
theorem harmonicAt_slitSolution {x : WithLp 2 (ℝ × ℝ)} (hx : x.fst < 0 ∨ x.snd ≠ 0) :
    HarmonicAt slitSolution x := by
  have hF : AnalyticAt ℂ (fun z : ℂ => (-z) ^ (2⁻¹ : ℂ)) (Complex.equivRealProdLp.symm x) :=
    analyticAt_id.neg.cpow analyticAt_const (neg_mem_slitPlane_iff.2 hx)
  have hu : slitSolution = (fun z : ℂ => ((-z) ^ (2⁻¹ : ℂ)).re) ∘ Complex.equivRealProdLp.symm :=
    funext slitSolution_eq_re_cpow
  rw [hu, harmonicAt_comp_linearIsometryEquiv_right_iff]
  exact hF.harmonicAt_re

/-- The slit-plane solution is harmonic on the slit plane `ℝ² ∖ [0, ∞) × {0}`. -/
theorem harmonicOnNhd_slitSolution :
    InnerProductSpace.HarmonicOnNhd slitSolution {x | x.fst < 0 ∨ x.snd ≠ 0} :=
  fun _ hx => harmonicAt_slitSolution hx

/-- **The slit-plane solution is harmonic on the slit disc.** -/
theorem harmonicOnNhd_slitSolution_slitUnitDisc :
    InnerProductSpace.HarmonicOnNhd slitSolution slitUnitDisc :=
  fun _ hx => harmonicAt_slitSolution (slitUnitDisc_subset_setOf_fst_lt_zero_or_snd_ne_zero hx)

/-! ### The gradient -/

/-- **The gradient of the slit-plane solution has length `1 / (2 √‖x‖)`** off the ray
`[0, ∞) × {0}`. -/
theorem norm_gradient_slitSolution {x : WithLp 2 (ℝ × ℝ)} (hx : x.fst < 0 ∨ x.snd ≠ 0) :
    ‖∇ slitSolution x‖ = ‖x‖ ^ (-(2⁻¹ : ℝ)) / 2 := by
  set e := Complex.equivRealProdLp
  set z := e.symm x
  have hz : -z ∈ Complex.slitPlane := neg_mem_slitPlane_iff.2 hx
  have hF : HasDerivAt (fun w : ℂ => (-w) ^ (2⁻¹ : ℂ))
      (2⁻¹ * (-z) ^ ((2⁻¹ : ℂ) - 1) * -1) z :=
    ((hasDerivAt_id z).neg.cpow_const hz).congr_deriv (by simp)
  have hG := (Complex.reCLM.hasFDerivAt.comp z (hF.hasFDerivAt.restrictScalars ℝ)).comp x
    e.symm.toContinuousLinearEquiv.hasFDerivAt
  have hu := hG.congr_of_eventuallyEq (f₁ := slitSolution)
    (Filter.Eventually.of_forall fun y => slitSolution_eq_re_cpow y)
  -- The real part of a complex-linear functional has the same norm (`StrongDual.extendRCLikeₗᵢ`).
  have hre (c : ℂ) :
      ‖Complex.reCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ)‖ = ‖c‖ := by
    rw [← ContinuousLinearMap.norm_toSpanSingleton (𝕜 := ℂ) c,
      ← (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := ℂ)).symm.norm_map,
      StrongDual.extendRCLikeₗᵢ_symm_apply,
      show (RCLike.reCLM : ℂ →L[ℝ] ℝ) = Complex.reCLM from
        ContinuousLinearMap.ext fun _ => RCLike.re_to_complex]
  rw [gradient, LinearIsometryEquiv.norm_map, hu.fderiv,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e.symm, hre,
    show (2⁻¹ : ℂ) - 1 = ((-(2⁻¹ : ℝ) : ℝ) : ℂ) by push_cast; ring]
  simp only [norm_mul, Complex.norm_cpow_real]
  simp [z, div_eq_inv_mul]

/-- The slit-plane solution is continuously differentiable off the ray `[0, ∞) × {0}`. -/
private theorem contDiffOn_slitSolution :
    ContDiffOn ℝ 1 slitSolution {x | x.fst < 0 ∨ x.snd ≠ 0} := fun _ hx =>
  ((harmonicAt_slitSolution hx).1.of_le (by norm_num)).contDiffWithinAt

/-! ### Hölder continuity -/

/-- **The slit-plane solution is `1/2`-Hölder** on the whole plane, with constant `1`. By
`TauCeti.PDE.not_holderOnWith_slitSolution` no larger exponent works near the tip of the slit. -/
theorem holderWith_slitSolution : HolderWith 1 2⁻¹ slitSolution := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ y _ => ?_)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, NNReal.coe_inv, NNReal.coe_ofNat, ← one_div,
    ← Real.sqrt_eq_rpow, slitSolution, slitSolution]
  refine (Real.abs_sqrt_sub_sqrt_le _ _).trans (Real.sqrt_le_sqrt ?_)
  -- `|‖x‖ - ‖y‖| ≤ ‖x - y‖` and `|x₀ - y₀| ≤ ‖x - y‖`.
  have h1 := abs_norm_sub_norm_le x y
  have h2 : |x.fst - y.fst| ≤ ‖x - y‖ := by
    simpa using WithLp.norm_fst_le (x := x - y)
  rw [dist_eq_norm, ← sub_div, abs_div, abs_two]
  have h3 := abs_sub (‖x‖ - ‖y‖) (x.fst - y.fst)
  rw [show ‖x‖ - x.fst - (‖y‖ - y.fst) = ‖x‖ - ‖y‖ - (x.fst - y.fst) by ring]
  linarith

/-- The points `(-c t, 0)`, `c > 0`, tend to the tip of the slit within the slit disc as
`t → 0⁺`. -/
private theorem tendsto_toLp_neg_mul_nhdsWithin_slitUnitDisc (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => WithLp.toLp 2 (-(c * t), (0 : ℝ))) (𝓝[>] 0)
      (𝓝[slitUnitDisc] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hcont : Continuous fun t : ℝ => WithLp.toLp 2 (-(c * t), (0 : ℝ)) :=
      (WithLp.prod_continuous_toLp 2 ℝ ℝ).comp ((continuous_const.mul continuous_id).neg.prodMk
        continuous_const)
    convert (hcont.tendsto 0).mono_left nhdsWithin_le_nhds using 2
    rw [mul_zero, neg_zero, ← Prod.zero_eq_mk, WithLp.toLp_zero]
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / c by positivity)] with t ht
    have ht0 : 0 < c * t := mul_pos hc ht.1
    have ht1 : c * t < 1 := by
      have := (lt_div_iff₀' hc).1 ht.2
      linarith
    rw [mem_slitUnitDisc, WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero rfl]
    simp only [WithLp.toLp_fst, Real.norm_eq_abs, abs_neg, abs_of_pos ht0, mem_Ico]
    exact ⟨ht1, fun h => absurd h.1 (by linarith)⟩

/-- **The slit-plane solution is no better than `1/2`-Hölder at the tip.** For every exponent
`α > 1/2`, it is not `α`-Hölder, with any constant, on any set `s` containing the part of the slit
disc near the origin: at `(-t, 0)` and `(-2t, 0)` it takes the values `√t` and `√(2t)`. -/
theorem not_holderOnWith_slitSolution {α : ℝ≥0} (hα : 2⁻¹ < α) (C : ℝ≥0)
    {s : Set (WithLp 2 (ℝ × ℝ))} (hs : s ∈ 𝓝[slitUnitDisc] 0) :
    ¬ HolderOnWith C α slitSolution s := by
  intro h
  have hα' : (2⁻¹ : ℝ) < α := by exact_mod_cast hα
  have hray := tendsto_toLp_neg_mul_nhdsWithin_slitUnitDisc
  have hsmall : Filter.Tendsto (fun t : ℝ => (C : ℝ) * t ^ ((α : ℝ) - 2⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow (sub_pos.2 hα').ne'] using
      (((continuous_id.rpow_const fun _ => Or.inr (sub_pos.2 hα').le).tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds).const_mul (C : ℝ)
  have hsqrt2 : 1 < √2 := by
    rw [Real.lt_sqrt zero_le_one]
    norm_num
  obtain ⟨t, ht, ht1, ht2, htC⟩ := (eventually_mem_nhdsWithin.and
    (((hray 1 one_pos).eventually_mem hs).and (((hray 2 two_pos).eventually_mem hs).and
      (hsmall.eventually (gt_mem_nhds (sub_pos.2 hsqrt2)))))).exists
  have ht0 : (0 : ℝ) < t := ht
  have hdist :
      dist (WithLp.toLp 2 (-(2 * t), (0 : ℝ))) (WithLp.toLp 2 (-(1 * t), (0 : ℝ))) = t := by
    rw [dist_eq_norm, ← WithLp.toLp_sub, WithLp.prod_norm_eq_norm_fst_of_snd_eq_zero (by simp)]
    simp only [WithLp.toLp_fst, Prod.fst_sub, Real.norm_eq_abs]
    rw [show -(2 * t) - -(1 * t) = -t by ring, abs_neg, abs_of_pos ht0]
  have hd := h.dist_le ht2 ht1
  rw [hdist, Real.dist_eq, slitSolution_toLp_neg_zero (by positivity),
    slitSolution_toLp_neg_zero (by positivity), one_mul, Real.sqrt_mul zero_le_two] at hd
  -- `(√2 - 1) √t ≤ C t ^ α = (C t ^ (α - 1/2)) √t < (√2 - 1) √t`.
  have : (C : ℝ) * t ^ (α : ℝ) = ((C : ℝ) * t ^ ((α : ℝ) - 2⁻¹)) * √t := by
    rw [Real.sqrt_eq_rpow, ← one_div, mul_assoc, ← Real.rpow_add ht0, one_div, sub_add_cancel]
  rw [this] at hd
  nlinarith [Real.sqrt_pos.2 ht0, le_abs_self (√2 * √t - √t)]

/-! ### Sobolev integrability -/

/-- The gradient of the slit-plane solution is continuous off the ray `[0, ∞) × {0}`. -/
private theorem continuousOn_gradient_slitSolution :
    ContinuousOn (∇ slitSolution) {x | x.fst < 0 ∨ x.snd ≠ 0} :=
  (InnerProductSpace.toDual ℝ (WithLp 2 (ℝ × ℝ))).symm.continuous.comp_continuousOn
    (contDiffOn_slitSolution.continuousOn_fderiv_of_isOpen
      isOpen_setOf_fst_lt_zero_or_snd_ne_zero le_rfl)

/-- Powers of the length of the gradient of the slit-plane solution, off the ray
`[0, ∞) × {0}`. -/
private theorem norm_gradient_slitSolution_rpow {x : WithLp 2 (ℝ × ℝ)}
    (hx : x.fst < 0 ∨ x.snd ≠ 0) (q : ℝ) :
    ‖∇ slitSolution x‖ ^ q = 2⁻¹ ^ q * ‖x‖ ^ (-(2⁻¹ : ℝ) * q) := by
  rw [norm_gradient_slitSolution hx, div_eq_mul_inv,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg x) _) (by norm_num),
    ← Real.rpow_mul (norm_nonneg x), mul_comm]

/-- The gradient of the slit-plane solution is `p`-integrable on a bounded set off the ray
`[0, ∞) × {0}` when `p < 4`: its length `‖x‖ ^ (-1/2) / 2` is `p`-integrable near the origin of
the plane exactly in this range. -/
private theorem memLp_gradient_slitSolution {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p < 4)
    {Ω : Set (WithLp 2 (ℝ × ℝ))} (hΩm : MeasurableSet Ω) (hb : Bornology.IsBounded Ω)
    (hΩ : Ω ⊆ {x | x.fst < 0 ∨ x.snd ≠ 0}) :
    MemLp (∇ slitSolution) p (volume.restrict Ω) := by
  have hp' : p ≠ ∞ := (hp.trans ENNReal.ofNat_lt_top).ne
  have hpr : p.toReal < 4 := by
    simpa using (ENNReal.toReal_lt_toReal hp' (by norm_num)).2 hp
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : WithLp 2 (ℝ × ℝ))
  refine (integrable_norm_rpow_iff
    ((continuousOn_gradient_slitSolution.mono hΩ).aestronglyMeasurable hΩm) hp0 hp').1 ?_
  have hker : IntegrableOn (fun x : WithLp 2 (ℝ × ℝ) => ‖x‖ ^ (-(2⁻¹ : ℝ) * p.toReal)) Ω :=
    (integrableOn_norm_rpow_ball (by
      simp
      linarith)).mono_set hR
  exact IntegrableOn.congr_fun (hker.const_mul ((2 : ℝ)⁻¹ ^ p.toReal))
    (fun x hx => (norm_gradient_slitSolution_rpow (hΩ hx) _).symm) hΩm

/-- If the gradient of the slit-plane solution is `p`-integrable on the slit disc, then `p < 4`:
its length `‖x‖ ^ (-1/2) / 2` is not `4`-integrable near the tip. -/
private theorem lt_four_of_memLp_gradient_slitSolution {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hmem : MemLp (∇ slitSolution) p (volume.restrict slitUnitDisc)) : p < 4 := by
  have hint : IntegrableOn (fun x => ‖∇ slitSolution x‖ ^ p.toReal) slitUnitDisc :=
    hmem.integrable_norm_rpow hp0 hp
  have hpow : IntegrableOn (fun x : WithLp 2 (ℝ × ℝ) => ‖x‖ ^ (-(2⁻¹ : ℝ) * p.toReal))
      (ball 0 1) := by
    refine IntegrableOn.congr_set_ae (IntegrableOn.congr_fun
      (hint.const_mul ((2 : ℝ) ^ p.toReal)) (fun x hx => ?_) isOpen_slitUnitDisc.measurableSet)
      slitUnitDisc_ae_eq_ball.symm
    rw [norm_gradient_slitSolution_rpow
        (slitUnitDisc_subset_setOf_fst_lt_zero_or_snd_ne_zero hx), ← mul_assoc,
      ← Real.mul_rpow zero_le_two (by norm_num)]
    norm_num
  have := (integrableOn_norm_rpow_ball_iff zero_lt_one).1 hpow
  have hpr : p.toReal < 4 := by simp at this; linarith
  exact (ENNReal.toReal_lt_toReal hp (by norm_num)).1 (by simpa using hpr)

/-- **Sobolev integrability of the slit-plane solution.** On a bounded open set `Ω` off the ray
`[0, ∞) × {0}`, for instance the slit disc, the function `r^{1/2} sin(θ/2)` lies in `W^{1,p}(Ω)`
for every `1 ≤ p < 4`. -/
theorem exists_w1p_value_ae_eq_slitSolution {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p < 4)
    {Ω : Opens (WithLp 2 (ℝ × ℝ))} (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × ℝ))))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × ℝ))) ⊆ {x | x.fst < 0 ∨ x.snd ≠ 0}) :
    ∃ u : W1p volume Ω p,
      W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × ℝ)))] slitSolution := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : WithLp 2 (ℝ × ℝ))
  have : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × ℝ)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hu : MemLp slitSolution p (volume.restrict (Ω : Set (WithLp 2 (ℝ × ℝ)))) := by
    refine MemLp.of_bound continuous_slitSolution.aestronglyMeasurable (√R) ?_
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    rw [Real.norm_of_nonneg (slitSolution_nonneg x)]
    exact (slitSolution_le_sqrt_norm x).trans
      (Real.sqrt_le_sqrt (mem_ball_zero_iff.1 (hR hx)).le)
  exact (W1p.exists_value_gradient_ae_eq_of_contDiffOn (contDiffOn_slitSolution.mono hΩ) hu
    (memLp_gradient_slitSolution hp0 hp Ω.isOpen.measurableSet hb hΩ)).imp fun _ h => h.1

/-- **The slit-plane solution lies in `W^{1,p}` of the slit disc exactly for `p < 4`.** On the
slit disc `B(0, 1) ∖ [0, 1) × {0}` the harmonic function `r^{1/2} sin(θ/2)`, which is continuous
on the closed disc and vanishes on the slit, lies in `W^{1,p}` for `1 ≤ p < 4` and not for
`p ≥ 4`, including `p = ∞`: its gradient has length `1 / (2 √r)`. -/
theorem exists_w1p_value_ae_eq_slitSolution_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (∃ u : W1p volume ⟨slitUnitDisc, isOpen_slitUnitDisc⟩ p,
      W1p.value u =ᵐ[volume.restrict slitUnitDisc] slitSolution) ↔ p < 4 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun hp => exists_w1p_value_ae_eq_slitSolution hp
    (isBounded_ball.subset slitUnitDisc_subset_ball)
    slitUnitDisc_subset_setOf_fst_lt_zero_or_snd_ne_zero⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmem : MemLp (∇ slitSolution) p (volume.restrict slitUnitDisc) :=
    (Lp.memLp (W1p.gradient u)).ae_eq
      (W1p.gradient_ae_eq_of_contDiffOn u
        (contDiffOn_slitSolution.mono slitUnitDisc_subset_setOf_fst_lt_zero_or_snd_ne_zero) hu)
  rcases eq_or_ne p ∞ with rfl | hp
  · have : IsFiniteMeasure (volume.restrict slitUnitDisc) :=
      isFiniteMeasure_restrict.2
        ((isBounded_ball.subset slitUnitDisc_subset_ball).measure_lt_top.ne)
    exact absurd (lt_four_of_memLp_gradient_slitSolution (by norm_num) (by norm_num)
      (hmem.mono_exponent le_top)) (lt_irrefl 4)
  · exact lt_four_of_memLp_gradient_slitSolution hp0 hp hmem

end PDE

end TauCeti
