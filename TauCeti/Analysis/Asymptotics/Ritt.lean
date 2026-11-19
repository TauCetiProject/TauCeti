/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Ritt's theorem: differentiating order relations in sectors

Let `f` be holomorphic in the sector `S = {z | R < |z|, |ph z| < θ}` with `f(z) = O(|z|^ν)` as
`z → ∞` in `S`, where `ν` is real. Ritt's theorem (DLMF §2.1(ii)) states that
`f'(z) = O(|z|^(ν - 1))` as `z → ∞` in every closed subsector `|ph z| ≤ θ'` with `θ' < θ`, and
the same with `o` in place of `O`. Consequently a Poincaré expansion `f(z) ∼ ∑ aₙ z⁻ⁿ` in `S`
may be differentiated termwise in every such closed subsector.

The proof is Cauchy's estimate for the derivative on discs whose radii are a fixed multiple of
the distance of their centers to the vertex: such discs around points of the closed subsector
stay inside `S`, by compactness of the arc of unit directions of the subsector.

## Main results

* `Complex.exists_pos_forall_closedBall_abs_arg_lt`: discs of radius proportional to the norm of
  their centers in a closed sector stay in a larger open sector.
* `Complex.exists_pos_norm_deriv_le_of_sector_bound`: a power bound in an open sector gives a
  derivative bound with the next lower power in a closed subsector.
* `Asymptotics.isBigO_deriv_of_isBigO_sector`, `Asymptotics.isLittleO_deriv_of_isLittleO_sector`:
  Ritt's theorem with `O` and with `o`.
* `Asymptotics.HasAsymptoticExpansion.deriv_sector`: termwise differentiation of a Poincaré
  expansion at infinity in a sector.
* `Real.rpow_le_two_rpow_abs_mul`, `hasDerivAt_inv_pow`: auxiliary facts on real powers of
  comparable numbers and on the derivative of `z ↦ (z ^ n)⁻¹`.

The statements and proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`,
`DLMF/AsymptoticApproximations/Basics/Calculus.lean` and
`DLMFMathlib/Analysis/Complex/Sector.lean`, where the sectors may have any bisector.
-/

public section

noncomputable section

open Filter Metric Set Bornology Finset
open scoped Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `x / 2 ≤ y ≤ 2 x`, then `y ^ p ≤ 2 ^ |p| x ^ p`, for positive and negative exponents
alike. -/
theorem Real.rpow_le_two_rpow_abs_mul {x y p : ℝ} (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x) :
    y ^ p ≤ 2 ^ |p| * x ^ p := by
  rcases (by linarith : (0 : ℝ) ≤ x).eq_or_lt with rfl | hx
  · rw [show y = 0 by linarith]
    exact le_mul_of_one_le_left (Real.rpow_nonneg le_rfl p)
      (Real.one_le_rpow (by norm_num) (abs_nonneg p))
  rcases le_total 0 p with hp | hp
  · calc y ^ p ≤ (2 * x) ^ p := Real.rpow_le_rpow (by linarith) hyx hp
      _ = 2 ^ |p| * x ^ p := by rw [Real.mul_rpow (by norm_num) hx.le, abs_of_nonneg hp]
  · calc y ^ p ≤ (x / 2) ^ p := Real.rpow_le_rpow_of_nonpos (by positivity) hxy hp
      _ = 2 ^ |p| * x ^ p := by
        rw [Real.div_rpow hx.le (by norm_num), abs_of_nonpos hp, Real.rpow_neg (by norm_num)]
        ring

namespace Complex

/-- For `θ' < θ ≤ π`, the closed balls of radius `c ‖z‖` around the points `z ≠ 0` of the closed
sector `|arg z| ≤ θ'` stay in the open sector `|arg w| < θ`, for some `0 < c ≤ 1 / 2`. -/
theorem exists_pos_forall_closedBall_abs_arg_lt_of_le_pi {θ θ' : ℝ} (hθ : θ ≤ π)
    (hθ' : θ' < θ) : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ θ' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ := by
  let K : Set ℂ := (fun φ : ℝ => exp (φ * I)) '' Icc (-θ') θ'
  let U : Set ℂ := slitPlane ∩ (fun z : ℂ => |z.arg|) ⁻¹' Iio θ
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := continuousOn_arg.abs.isOpen_inter_preimage isOpen_slitPlane isOpen_Iio
  have hKU : K ⊆ U := by
    rintro _ ⟨φ, hφ, rfl⟩
    have ha : (exp (φ * I)).arg = φ := by
      rw [arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> linarith [hφ.1, hφ.2]
    refine ⟨mem_slitPlane_iff_arg.mpr ⟨by linarith [hφ.2], exp_ne_zero _⟩, ?_⟩
    rw [Set.mem_preimage, ha, Set.mem_Iio, abs_lt]
    constructor <;> linarith [hφ.1, hφ.2]
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_right _ _,
    fun z hz harg w hw => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzr : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz0.ne'
  rw [mem_closedBall, dist_eq_norm] at hw
  have hunit : z / (‖z‖ : ℂ) ∈ K := by
    refine ⟨z.arg, abs_le.mp harg, ?_⟩
    rw [eq_div_iff hzr, mul_comm, norm_mul_exp_arg_mul_I]
  have hdist : dist (w / (‖z‖ : ℂ)) (z / (‖z‖ : ℂ)) ≤ δ := by
    rw [dist_eq_norm, ← sub_div, norm_div, norm_real, Real.norm_of_nonneg hz0.le]
    exact ((div_le_iff₀ hz0).mpr hw).trans (min_le_left _ _)
  have hwU := (hδU (mem_cthickening_of_dist_le _ _ _ K hunit hdist)).2
  rwa [Set.mem_preimage, Set.mem_Iio, div_eq_mul_inv, ← ofReal_inv, arg_mul_real (inv_pos.mpr hz0)]
    at hwU

/-- For `θ' < θ`, the closed balls of radius `c ‖z‖` around the points `z ≠ 0` of the closed
sector `|arg z| ≤ θ'` stay in the open sector `|arg w| < θ`, for some `c > 0`, and the norms in
these balls lie between `‖z‖ / 2` and `2 ‖z‖`. -/
theorem exists_pos_forall_closedBall_abs_arg_lt {θ θ' : ℝ} (hθ' : θ' < θ) :
    ∃ c > 0, ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ θ' → ∀ w ∈ closedBall z (c * ‖z‖),
      |w.arg| < θ ∧ ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖z‖ := by
  obtain ⟨c, hc, hc2, h⟩ : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ θ' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ := by
    rcases le_or_gt θ π with hθ | hθ
    · exact exists_pos_forall_closedBall_abs_arg_lt_of_le_pi hθ hθ'
    · exact ⟨1 / 2, by norm_num, le_rfl, fun _ _ _ w _ => (abs_arg_le_pi w).trans_lt hθ⟩
  refine ⟨c, hc, fun z hz harg w hw => ⟨h z hz harg w hw, ?_⟩⟩
  rw [mem_closedBall, dist_eq_norm] at hw
  have hnear : ‖w - z‖ ≤ ‖z‖ / 2 := hw.trans (by nlinarith [norm_nonneg z])
  have h1 := norm_le_norm_add_norm_sub z w
  have h2 := norm_le_norm_add_norm_sub w z
  rw [norm_sub_rev] at h1
  constructor <;> linarith

/-- **Cauchy's estimate in a sector.** For `θ' < θ` there is `K > 0` such that every `f`
holomorphic on `{A < ‖w‖, |arg w| < θ}` and bounded there by `B ‖w‖ ^ ν` satisfies
`‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` for `2 max A 0 < ‖z‖` and `|arg z| ≤ θ'`. The constant does not
depend on `f`, `A` or `B`. -/
theorem exists_pos_norm_deriv_le_of_sector_bound {θ θ' : ℝ} (hθ' : θ' < θ) (ν : ℝ) :
    ∃ K > 0, ∀ (f : ℂ → E) (A B : ℝ),
      DifferentiableOn ℂ f {w | A < ‖w‖ ∧ |w.arg| < θ} →
      (∀ w, A < ‖w‖ → |w.arg| < θ → ‖f w‖ ≤ B * ‖w‖ ^ ν) →
      ∀ z : ℂ, 2 * max A 0 < ‖z‖ → |z.arg| ≤ θ' → ‖deriv f z‖ ≤ K * B * ‖z‖ ^ (ν - 1) := by
  obtain ⟨c, hc, hb⟩ := exists_pos_forall_closedBall_abs_arg_lt hθ'
  refine ⟨2 ^ |ν| / c, by positivity, fun f A B hf hbound z hz harg => ?_⟩
  have hz0 : 0 < ‖z‖ := by linarith [le_max_right A 0]
  have hzne : z ≠ 0 := norm_pos_iff.mp hz0
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hbound z (by linarith [le_max_left A 0]) (harg.trans_lt hθ')))
    (Real.rpow_pos_of_pos hz0 ν)
  have hsub : closedBall z (c * ‖z‖) ⊆ {w | A < ‖w‖ ∧ |w.arg| < θ} := fun w hw => by
    have h := hb z hzne harg w hw
    exact ⟨by linarith [le_max_left A 0, h.2.1], h.1⟩
  have hd := norm_deriv_le_of_forall_mem_sphere_norm_le (mul_pos hc hz0)
    (hf.diffContOnCl_ball hsub) (C := B * 2 ^ |ν| * ‖z‖ ^ ν) fun w hw => by
      have hwc := sphere_subset_closedBall hw
      have h := hb z hzne harg w hwc
      calc ‖f w‖ ≤ B * ‖w‖ ^ ν := hbound w (hsub hwc).1 h.1
        _ ≤ B * (2 ^ |ν| * ‖z‖ ^ ν) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_two_rpow_abs_mul h.2.1 h.2.2) hB
        _ = B * 2 ^ |ν| * ‖z‖ ^ ν := by ring
  refine hd.trans_eq ?_
  rw [Real.rpow_sub hz0, Real.rpow_one]
  field_simp

end Complex

namespace Asymptotics

open Complex

/-- The eventual form of Cauchy's estimate in a sector: for `θ' < θ` there is `K > 0` such that
an eventual bound `‖f z‖ ≤ B ‖z‖ ^ ν` as `z → ∞` in `|arg z| < θ`, for `f` holomorphic on
`{R < ‖z‖, |arg z| < θ}`, gives `‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` as `z → ∞` in `|arg z| ≤ θ'`. The
constant does not depend on `f`, `R` or `B`. -/
theorem exists_pos_eventually_norm_deriv_le_sector {θ θ' : ℝ} (hθ' : θ' < θ) (ν : ℝ) :
    ∃ K > 0, ∀ (f : ℂ → E) (R B : ℝ),
      DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ} →
      (∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}, ‖f z‖ ≤ B * ‖z‖ ^ ν) →
      ∀ᶠ z in cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}, ‖deriv f z‖ ≤ K * B * ‖z‖ ^ (ν - 1) := by
  obtain ⟨K, hK, hder⟩ := exists_pos_norm_deriv_le_of_sector_bound (E := E) hθ' ν
  refine ⟨K, hK, fun f R B hf hbound => ?_⟩
  obtain ⟨A, -, hA⟩ := (hasBasis_cobounded_norm.inf_principal _).eventually_iff.mp hbound
  refine (hasBasis_cobounded_norm.inf_principal _).eventually_iff.mpr
    ⟨2 * max (max A R) 0 + 1, trivial, fun z ⟨hz, harg⟩ => ?_⟩
  have hfn : DifferentiableOn ℂ f {w | max A R < ‖w‖ ∧ |w.arg| < θ} :=
    hf.mono fun w hw => ⟨(le_max_right A R).trans_lt hw.1, hw.2⟩
  refine hder f (max A R) B hfn (fun w hw hwa => ?_) z ((lt_add_one _).trans_le hz) harg
  exact hA ⟨((le_max_left A R).trans_lt hw).le, hwa⟩

/-- **Ritt's theorem** (DLMF §2.1(ii)): if `f` is holomorphic on `{R < ‖z‖, |arg z| < θ}` and
`f(z) = O(‖z‖ ^ ν)` as `z → ∞` in `|arg z| < θ`, then `f'(z) = O(‖z‖ ^ (ν - 1))` as `z → ∞` in
every closed subsector `|arg z| ≤ θ'` with `θ' < θ`. -/
theorem isBigO_deriv_of_isBigO_sector {f : ℂ → E} {R θ θ' ν : ℝ} (hθ' : θ' < θ)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ})
    (hO : f =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}] fun z => ‖z‖ ^ ν) :
    deriv f =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}] fun z => ‖z‖ ^ (ν - 1) := by
  obtain ⟨K, -, hb⟩ := exists_pos_eventually_norm_deriv_le_sector (E := E) hθ' ν
  obtain ⟨C, hbound⟩ := hO.bound
  refine IsBigO.of_bound (K * C) ?_
  have h := hb f R C hf (by
    filter_upwards [hbound] with z hz
    rwa [Real.norm_of_nonneg (by positivity)] at hz)
  filter_upwards [h] with z hz
  rwa [Real.norm_of_nonneg (by positivity)]

/-- **Ritt's theorem** with `o` (DLMF §2.1(ii)): if `f` is holomorphic on
`{R < ‖z‖, |arg z| < θ}` and `f(z) = o(‖z‖ ^ ν)` as `z → ∞` in `|arg z| < θ`, then
`f'(z) = o(‖z‖ ^ (ν - 1))` as `z → ∞` in every closed subsector `|arg z| ≤ θ'` with
`θ' < θ`. -/
theorem isLittleO_deriv_of_isLittleO_sector {f : ℂ → E} {R θ θ' ν : ℝ} (hθ' : θ' < θ)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ})
    (ho : f =o[cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}] fun z => ‖z‖ ^ ν) :
    deriv f =o[cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}] fun z => ‖z‖ ^ (ν - 1) := by
  obtain ⟨K, hK, hb⟩ := exists_pos_eventually_norm_deriv_le_sector (E := E) hθ' ν
  refine IsLittleO.of_bound fun ε hε => ?_
  have h := hb f R (ε / K) hf (by
    filter_upwards [ho.bound (div_pos hε hK)] with z hz
    rwa [Real.norm_of_nonneg (by positivity)] at hz)
  filter_upwards [h] with z hz
  rw [Real.norm_of_nonneg (by positivity)]
  rwa [mul_div_cancel₀ _ hK.ne'] at hz

/-- The derivative of `z ↦ (z ^ n)⁻¹` at `z ≠ 0` is `-n (z ^ (n + 1))⁻¹`. -/
theorem _root_.hasDerivAt_inv_pow {𝕜 : Type*} [NontriviallyNormedField 𝕜] {z : 𝕜} (hz : z ≠ 0)
    (n : ℕ) : HasDerivAt (fun w : 𝕜 => (w ^ n)⁻¹) (-(n : 𝕜) * (z ^ (n + 1))⁻¹) z := by
  convert hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz) using 1
  · funext w
    rw [zpow_neg, zpow_natCast]
  · rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    push_cast
    ring

/-- **Termwise differentiation** (DLMF §2.1(ii)): if `f` is holomorphic on
`{R < ‖z‖, |arg z| < θ}` with the Poincaré expansion `f(z) ∼ ∑ aₙ z⁻ⁿ` as `z → ∞` in
`|arg z| < θ`, then `f'(z) ∼ ∑ (-n aₙ) z⁻ⁿ⁻¹` as `z → ∞` in every closed subsector
`|arg z| ≤ θ'` with `θ' < θ`. -/
theorem HasAsymptoticExpansion.deriv_sector {f : ℂ → E} {a : ℕ → E} {R θ θ' : ℝ}
    (he : HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}) (fun n z => (z ^ n)⁻¹)
      a f)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖ ∧ |arg z| < θ}) (hθ' : θ' < θ) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'})
      (fun n z => (z ^ (n + 1))⁻¹) (fun n => -(n : ℂ) • a n) (deriv f) := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  set P : ℂ → E := fun z => ∑ n ∈ range N, (z ^ n)⁻¹ • a n
  have hP (z : ℂ) (hz : z ≠ 0) :
      HasDerivAt P (∑ n ∈ range N, (-(n : ℂ) * (z ^ (n + 1))⁻¹) • a n) z :=
    HasDerivAt.fun_sum fun n _ => (hasDerivAt_inv_pow hz n).smul_const (a n)
  have hS : {z : ℂ | max R 0 < ‖z‖ ∧ |arg z| < θ} ⊆ {z | R < ‖z‖ ∧ |arg z| < θ} :=
    fun z hz => ⟨(le_max_left R 0).trans_lt hz.1, hz.2⟩
  have hdiff : DifferentiableOn ℂ (fun z => f z - P z) {z | max R 0 < ‖z‖ ∧ |arg z| < θ} :=
    fun z hz => ((hf z (hS hz)).mono hS).sub (hP z (norm_pos_iff.mp
      ((le_max_right R 0).trans_lt hz.1))).differentiableAt.differentiableWithinAt
  have hrem : (fun z => f z - P z) =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| < θ}]
      fun z => ‖z‖ ^ (-(N : ℝ)) :=
    (he.isBigO N).trans <| isBigO_of_le _ fun z => by
      rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), Real.rpow_neg (norm_nonneg _),
        Real.rpow_natCast]
  have hscale : (fun z : ℂ => ‖z‖ ^ (-(N : ℝ) - 1)) =O[cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ'}]
      fun z => (z ^ (N + 1))⁻¹ := isBigO_of_le _ fun z => by
    rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity),
      show -(N : ℝ) - 1 = -((N + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  refine ((isBigO_deriv_of_isBigO_sector hθ' hdiff hrem).trans hscale).congr' ?_ .rfl
  obtain ⟨c, hc, hball⟩ := Complex.exists_pos_forall_closedBall_abs_arg_lt hθ'
  refine (hasBasis_cobounded_norm.inf_principal _).eventually_iff.mpr
    ⟨2 * max R 0 + 1, trivial, fun z ⟨hz, harg⟩ => ?_⟩
  have hz' : 2 * max R 0 + 1 ≤ ‖z‖ := hz
  have hzR : max R 0 < ‖z‖ := by linarith [le_max_right R 0]
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((le_max_right R 0).trans_lt hzR)
  have hnhds : {z | R < ‖z‖ ∧ |arg z| < θ} ∈ 𝓝 z := by
    refine mem_of_superset (closedBall_mem_nhds z (mul_pos hc (norm_pos_iff.mpr hz0)))
      fun w hw => ⟨?_, (hball z hz0 harg w hw).1⟩
    linarith [(hball z hz0 harg w hw).2.1, le_max_left R 0, le_max_right R 0]
  rw [((hf.differentiableAt hnhds).hasDerivAt.fun_sub (hP z hz0)).deriv]
  refine congrArg (deriv f z - ·) (sum_congr rfl fun n _ => ?_)
  rw [smul_smul, mul_comm]

end Asymptotics
