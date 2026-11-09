/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Symplectic.Floer.Graph
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The `log log` example: a `W^{1,∞}` pseudoholomorphic graph that is not `W^{2,∞}`

Elliptic bootstrapping for pseudoholomorphic curves gains a derivative for every finite exponent
`p > 2`: a `W^{1,p}` solution for a `C^ℓ` structure is `W^{ℓ+1,p}`. This file records the
classical example showing that the endpoint `p = ∞` fails. Let

`f(z) = z² log log (1 / ‖z‖)`

on the unit disc (`TauCeti.logLogExample`, equal to `0` at the origin). Writing `r = ‖z‖`:

* `f` is `C¹` on the unit disc (`TauCeti.contDiffOn_logLogExample`), so it is `W^{1,∞}` on every
  smaller disc;
* `\bar∂f(z) = z³ / (2 r² log r)` (`TauCeti.conjWirtingerDeriv_logLogExample_apply_one`), of size
  `r / (2 |log r|)` with first derivatives of size `1 / |log r|`, so `\bar∂f` is `C¹` on the unit
  disc (`TauCeti.contDiffOn_conjWirtingerDeriv_logLogExample`);
* the second derivative of `f` contains the term `2 log log (1 / r)` and is unbounded near the
  origin (`TauCeti.not_isBoundedUnder_norm_fderiv_fderiv_logLogExample`), so `f` is not `C²` at
  the origin (`TauCeti.not_contDiffAt_two_logLogExample`) and not `W^{2,∞}` near it.

For a real-differentiable `g : ℂ → ℂ`, the graph `z ↦ (z, g z)` is pseudoholomorphic for the
structure

`J_g(z, w)(v, a) = (i v, i a - 2 i \bar∂g(z) conj v)`

on `ℂ × ℂ` (`TauCeti.conjWirtingerGraphStructure`). This is Gromov's graph structure
`TauCeti.Floer.graphStructure` for the target structure `i` and the one-form `\bar∂g`, because the
graph solves the inhomogeneous equation `\bar∂u = \bar∂g`. It squares to `-1`
(`TauCeti.conjWirtingerGraphStructure_apply_apply`), is as regular as `\bar∂g`
(`TauCeti.contDiffOn_conjWirtingerGraphStructure`), and the graph satisfies `dG(i) = J_g dG(1)`
(`TauCeti.fderiv_graph_I_eq_conjWirtingerGraphStructure`), so it is `J_g`-holomorphic in the sense
of `TauCeti.IsJHolomorphicAt` (`TauCeti.isJHolomorphicAt_graph_conjWirtingerGraphAlmostComplex`).

For `g = f` the structure `J_f` is `C¹` over the unit disc
(`TauCeti.contDiffOn_conjWirtingerGraphStructure_logLogExample`) and the graph of `f` is
`J_f`-holomorphic there (`TauCeti.isJHolomorphicOn_graph_logLogExample`): a `W^{1,∞}` solution for
a `C¹` structure that is not `W^{2,∞}`.

## Implementation notes

The statements use classical derivatives: off the origin `f` is smooth, so its weak and classical
derivatives agree there, and unboundedness of the continuous classical second derivative on the
punctured disc is the failure of `W^{2,∞}`. The function `log log (1 / ‖z‖)` is handled as the
profile `s ↦ log (-(log s) / 2)` evaluated at `s = ‖z‖²`, so that all derivatives are computed by
the chain rule through the smooth map `z ↦ ‖z‖²`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.4
  (elliptic bootstrapping), and Section 8.1 (Gromov's graph construction).
-/

public section

open Complex ComplexConjugate Filter Metric Set Topology

namespace TauCeti

/-- The function `f(z) = z² log log (1 / ‖z‖)`. On the unit disc it is `C¹` with `C¹` conjugate
Wirtinger derivative but unbounded second derivative near the origin. At the origin the formula
evaluates to `0`; on the unit circle it is singular, and it is only studied on the unit disc. -/
@[expose] noncomputable def logLogExample (z : ℂ) : ℂ :=
  z ^ 2 * (Real.log (Real.log ‖z‖⁻¹) : ℂ)

section Profiles

/-- The profile `s ↦ log (-(log s) / 2)`, so that `log log (1 / ‖z‖)` is its value at `‖z‖²`. -/
private noncomputable def profile (s : ℝ) : ℝ := Real.log (-Real.log s / 2)

/-- The function `s ↦ (s log s)⁻¹`, the derivative of `profile` on `(0, 1)`. -/
private noncomputable def profileDeriv (s : ℝ) : ℝ := (s * Real.log s)⁻¹

/-- `log log (1 / ‖z‖)` is the profile evaluated at `‖z‖²`. -/
private theorem profile_norm_sq (z : ℂ) : profile (‖z‖ ^ 2) = Real.log (Real.log ‖z‖⁻¹) := by
  simp only [profile, Real.log_inv, Real.log_pow]
  congr 1
  push_cast
  ring

/-- The example as a monomial times a radial profile. -/
private theorem logLogExample_eq :
    logLogExample = fun z ↦ z ^ 2 * (profile (‖z‖ ^ 2) : ℂ) := by
  funext z
  rw [logLogExample, profile_norm_sq]

/-- `‖z‖² |(s log s)⁻¹| = |(log s)⁻¹|` at `s = ‖z‖²`, including at the origin. -/
private theorem norm_sq_mul_abs_profileDeriv (z : ℂ) :
    ‖z‖ ^ 2 * |profileDeriv (‖z‖ ^ 2)| = |(Real.log (‖z‖ ^ 2))⁻¹| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [profileDeriv, abs_inv, abs_mul, abs_of_pos (by positivity : 0 < ‖z‖ ^ 2), abs_inv]
  field_simp

/-- The profile is smooth on `(0, 1)`. -/
private theorem contDiffAt_profile {m : WithTop ℕ∞} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ContDiffAt ℝ m profile s := by
  have hlog : Real.log s < 0 := Real.log_neg hs hs1
  exact (Real.contDiffAt_log.2 (by linarith)).comp s
    ((Real.contDiffAt_log.2 hs.ne').neg.div_const 2)

/-- The derivative of the profile is smooth on `(0, 1)`. -/
private theorem contDiffAt_profileDeriv {m : WithTop ℕ∞} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ContDiffAt ℝ m profileDeriv s := by
  have hlog : Real.log s < 0 := Real.log_neg hs hs1
  exact (contDiffAt_id.mul (Real.contDiffAt_log.2 hs.ne')).inv (mul_ne_zero hs.ne' hlog.ne)

/-- The derivative of `s ↦ log (-(log s) / 2)` is `(s log s)⁻¹` on `(0, 1)`. -/
private theorem hasDerivAt_profile {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    HasDerivAt profile (profileDeriv s) s := by
  have hlog : Real.log s < 0 := Real.log_neg hs hs1
  have h1 : HasDerivAt (fun x ↦ -Real.log x / 2) (-s⁻¹ / 2) s :=
    (Real.hasDerivAt_log hs.ne').neg.div_const 2
  have h := h1.log (by linarith)
  rw [show profile = fun x ↦ Real.log (-Real.log x / 2) from rfl]
  convert h using 1
  simp only [profileDeriv]
  field_simp

/-- The derivative of `s ↦ (s log s)⁻¹` is `-(log s + 1) / (s log s)²` on `(0, 1)`. -/
private theorem hasDerivAt_profileDeriv {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    HasDerivAt profileDeriv (-(Real.log s + 1) / (s * Real.log s) ^ 2) s := by
  have hlog : Real.log s < 0 := Real.log_neg hs hs1
  exact (Real.hasDerivAt_mul_log hs.ne').fun_inv (mul_ne_zero hs.ne' hlog.ne)

end Profiles

section Radial

/-! ### Monomials times radial profiles

Derivatives of `z ↦ zⁿ C(‖z‖²)` for a real profile `C`. -/

variable {C : ℝ → ℝ} {c : ℝ} {z : ℂ}

/-- The derivative of a radial function `z ↦ C(‖z‖²)`. -/
private theorem hasFDerivAt_radial (h : HasDerivAt C c (‖z‖ ^ 2)) :
    HasFDerivAt (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ))
      (ofRealCLM ∘L (c • (2 • innerSL ℝ z))) z :=
  ofRealCLM.hasFDerivAt.comp z (h.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt)

/-- The derivative of `z ↦ C(‖z‖²)` in direction `v` is `2 C'(‖z‖²) Re (v conj z)`. -/
private theorem fderiv_radial_apply (h : HasDerivAt C c (‖z‖ ^ 2)) (v : ℂ) :
    fderiv ℝ (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ)) z v = (2 * c * (v * conj z).re : ℝ) := by
  rw [(hasFDerivAt_radial h).fderiv]
  simp [Complex.inner]
  ring

/-- The derivative of `z ↦ C(‖z‖²)` has norm at most `2 |C'(‖z‖²)| ‖z‖`. -/
private theorem norm_fderiv_radial_le (h : HasDerivAt C c (‖z‖ ^ 2)) :
    ‖fderiv ℝ (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ)) z‖ ≤ 2 * |c| * ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [fderiv_radial_apply h, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  calc |2| * |c| * |(v * conj z).re| ≤ 2 * |c| * ‖v * conj z‖ := by
        rw [abs_two]; gcongr; exact abs_re_le_norm _
    _ = 2 * |c| * ‖z‖ * ‖v‖ := by rw [norm_mul, Complex.norm_conj]; ring

/-- `\bar∂ C(‖z‖²) = C'(‖z‖²) z`. -/
private theorem conjWirtingerDeriv_radial_apply_one (h : HasDerivAt C c (‖z‖ ^ 2)) :
    conjWirtingerDeriv (fun w : ℂ ↦ (C (‖w‖ ^ 2) : ℂ)) z 1 = c * z := by
  rw [conjWirtingerDeriv_apply, fderiv_radial_apply h, fderiv_radial_apply h]
  apply Complex.ext <;> simp <;> ring

/-- The real derivative of `w ↦ wⁿ` has norm at most `n ‖z‖ⁿ⁻¹`. -/
private theorem norm_fderiv_pow_le (n : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun w : ℂ ↦ w ^ n) z‖ ≤ n * ‖z‖ ^ (n - 1) := by
  rw [((hasDerivAt_pow n z).hasFDerivAt.restrictScalars ℝ).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  simp [mul_comm]

variable (n : ℕ)

/-- `z ↦ zⁿ C(‖z‖²)` is as regular as `C` at `‖z‖²`. -/
private theorem contDiffAt_pow_mul_radial {m : WithTop ℕ∞} (hC : ContDiffAt ℝ m C (‖z‖ ^ 2)) :
    ContDiffAt ℝ m (fun w : ℂ ↦ w ^ n * (C (‖w‖ ^ 2) : ℂ)) z :=
  (contDiffAt_id.pow n).mul
    (ofRealCLM.contDiff.contDiffAt.comp z (hC.comp z (contDiffAt_id.norm_sq ℝ)))

/-- The product rule bound for the derivative of `z ↦ zⁿ C(‖z‖²)`. -/
private theorem norm_fderiv_pow_mul_radial_le (h : HasDerivAt C c (‖z‖ ^ 2)) :
    ‖fderiv ℝ (fun w : ℂ ↦ w ^ n * (C (‖w‖ ^ 2) : ℂ)) z‖ ≤
      ‖z‖ ^ n * (2 * |c| * ‖z‖) + |C (‖z‖ ^ 2)| * (n * ‖z‖ ^ (n - 1)) := by
  have hp : DifferentiableAt ℝ (fun w : ℂ ↦ w ^ n) z := by fun_prop
  rw [fderiv_fun_mul hp (hasFDerivAt_radial h).differentiableAt]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  · exact norm_fderiv_radial_le h
  · exact norm_fderiv_pow_le n z

/-- `\bar∂ (zⁿ C(‖z‖²)) = zⁿ C'(‖z‖²) z`, since `zⁿ` is holomorphic. -/
private theorem conjWirtingerDeriv_pow_mul_radial_apply_one (h : HasDerivAt C c (‖z‖ ^ 2)) :
    conjWirtingerDeriv (fun w : ℂ ↦ w ^ n * (C (‖w‖ ^ 2) : ℂ)) z 1 = z ^ n * (c * z) := by
  have hp : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z := by fun_prop
  rw [conjWirtingerDeriv_fun_mul (hp.restrictScalars ℝ) (hasFDerivAt_radial h).differentiableAt]
  simp [conjWirtingerDeriv_radial_apply_one h]

end Radial

section Limits

/-- A function on the unit disc that is `C¹` off the origin, has derivative `0` at the origin, and
whose derivative tends to `0` at the origin, is `C¹` on the disc. -/
private theorem contDiffOn_one_ball_of_tendsto_fderiv {g : ℂ → ℂ}
    (hg : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → ContDiffAt ℝ 1 g z)
    (h0 : HasFDerivAt g (0 : ℂ →L[ℝ] ℂ) 0)
    (hlim : Tendsto (fderiv ℝ g) (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 1 g (ball 0 1) := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · refine ContDiffAt.contDiffWithinAt ?_
    rw [contDiffAt_one_iff]
    refine ⟨fderiv ℝ g, ball 0 1, ball_mem_nhds _ one_pos, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
    · rcases eq_or_ne y 0 with rfl | hy0
      · refine (continuousWithinAt_compl_self.1 ?_).continuousWithinAt
        rw [ContinuousWithinAt, h0.fderiv]
        exact hlim
      · exact ((hg y hy hy0).fderiv_right (m := 0) le_rfl).continuousAt.continuousWithinAt
    · rcases eq_or_ne y 0 with rfl | hy0
      · rw [h0.fderiv]
        exact h0
      · exact ((hg y hy hy0).differentiableAt one_ne_zero).hasFDerivAt
  · exact (hg z hz hz0).contDiffWithinAt

/-- If `g z = k z * z` with `k z → 0` at the origin, then `g` has derivative `0` there. -/
private theorem hasFDerivAt_zero_of_tendsto {g k : ℂ → ℂ} (hgk : ∀ z, g z = k z * z)
    (hk : Tendsto k (𝓝 0) (𝓝 0)) : HasFDerivAt g (0 : ℂ →L[ℝ] ℂ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h := ((Asymptotics.isLittleO_one_iff (F := ℂ)).2 hk).mul_isBigO
    (Asymptotics.isBigO_refl (fun z : ℂ ↦ z) (𝓝 0))
  simpa [hgk] using h

/-- `‖z‖² → 0⁺` on the punctured plane. -/
private theorem tendsto_norm_sq_nhdsNE : Tendsto (fun z : ℂ ↦ ‖z‖ ^ 2) (𝓝[≠] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz ↦ ?_⟩
  · have h := ((by fun_prop : Continuous fun z : ℂ ↦ ‖z‖ ^ 2).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using h
  · have : 0 < ‖z‖ := norm_pos_iff.2 hz
    exact pow_pos this 2

/-- `(log ‖z‖²)⁻¹ → 0` on the punctured plane. -/
private theorem tendsto_inv_log_norm_sq :
    Tendsto (fun z : ℂ ↦ (Real.log (‖z‖ ^ 2))⁻¹) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_inv_atBot_zero.comp (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_sq_nhdsNE)

/-- `‖z‖ log ‖z‖ → 0` at the origin. -/
private theorem tendsto_norm_mul_log_norm :
    Tendsto (fun z : ℂ ↦ ‖z‖ * Real.log ‖z‖) (𝓝 0) (𝓝 0) := by
  simpa [Function.comp_def] using
    (Real.continuous_mul_log.comp continuous_norm).tendsto (0 : ℂ)

/-- Points near the origin have small norm. -/
private theorem eventually_norm_lt (ε : ℝ) (hε : 0 < ε) : ∀ᶠ z in 𝓝 (0 : ℂ), ‖z‖ < ε := by
  simpa using (continuous_norm.tendsto (0 : ℂ)).eventually (gt_mem_nhds (a := ε) (by simpa))

/-- For `0 ≤ r < e⁻¹`, `|log log (1 / r)| ≤ log (1 / r)`. -/
private theorem abs_log_log_inv_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < Real.exp (-1)) :
    |Real.log (Real.log r⁻¹)| ≤ -Real.log r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hlog : Real.log r < -1 := (Real.log_lt_iff_lt_exp hr).2 hr1
  have hx : 1 < Real.log r⁻¹ := by rw [Real.log_inv]; linarith
  rw [abs_of_pos (Real.log_pos hx)]
  have := Real.log_le_sub_one_of_pos (zero_lt_one.trans hx)
  rw [Real.log_inv] at this ⊢
  linarith

/-- On the punctured unit disc, `‖z‖²` lies in `(0, 1)`. -/
private theorem norm_sq_mem {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    0 < ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < 1 :=
  ⟨pow_pos (norm_pos_iff.2 hz0) 2, pow_lt_one₀ (norm_nonneg z) hz1 two_ne_zero⟩

end Limits

section Example

/-- The example is smooth on the punctured unit disc. -/
private theorem contDiffAt_logLogExample {m : WithTop ℕ∞} {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : ‖z‖ < 1) :
    ContDiffAt ℝ m logLogExample z := by
  obtain ⟨hs0, hs1⟩ := norm_sq_mem hz0 hz1
  rw [logLogExample_eq]
  exact contDiffAt_pow_mul_radial 2 (contDiffAt_profile hs0 hs1)

/-- The example has derivative `0` at the origin. -/
private theorem hasFDerivAt_logLogExample_zero :
    HasFDerivAt logLogExample (0 : ℂ →L[ℝ] ℂ) 0 := by
  refine hasFDerivAt_zero_of_tendsto (k := fun z ↦ z * (Real.log (Real.log ‖z‖⁻¹) : ℂ))
    (fun z ↦ by simp only [logLogExample]; ring) ?_
  have h0 := tendsto_norm_mul_log_norm.abs
  rw [abs_zero] at h0
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_norm_lt _ (Real.exp_pos (-1))] with z hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖z‖ * |Real.log (Real.log ‖z‖⁻¹)| ≤ ‖z‖ * -Real.log ‖z‖ := by
        gcongr; exact abs_log_log_inv_le (norm_nonneg z) hz
    _ = -(‖z‖ * Real.log ‖z‖) := by ring
    _ ≤ |‖z‖ * Real.log ‖z‖| := neg_le_abs _

/-- `‖z‖ → 0` on the punctured plane. -/
private theorem tendsto_norm_nhdsNE : Tendsto (fun z : ℂ ↦ ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
  simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds

/-- `e⁻¹ < 1`. -/
private theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)

/-- The derivative of the example tends to `0` at the origin: it has size
`2 r / |log r²| + 2 r |log log (1 / r)|`. -/
private theorem tendsto_fderiv_logLogExample :
    Tendsto (fderiv ℝ logLogExample) (𝓝[≠] 0) (𝓝 0) := by
  have hb : Tendsto (fun z : ℂ ↦ 2 * ‖z‖ * |(Real.log (‖z‖ ^ 2))⁻¹| +
      2 * |‖z‖ * Real.log ‖z‖|) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((tendsto_norm_nhdsNE.const_mul 2).mul tendsto_inv_log_norm_sq.abs).add
      ((tendsto_norm_mul_log_norm.mono_left nhdsWithin_le_nhds).abs.const_mul 2)
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_norm_lt _ (Real.exp_pos (-1)))] with z hz0 hz
  obtain ⟨hs0, hs1⟩ := norm_sq_mem hz0 (hz.trans exp_neg_one_lt_one)
  rw [logLogExample_eq]
  refine (norm_fderiv_pow_mul_radial_le 2 (hasDerivAt_profile hs0 hs1)).trans ?_
  have h1 : ‖z‖ ^ 2 * (2 * |profileDeriv (‖z‖ ^ 2)| * ‖z‖) =
      2 * ‖z‖ * |(Real.log (‖z‖ ^ 2))⁻¹| := by
    rw [← norm_sq_mul_abs_profileDeriv]; ring
  have h2 : |profile (‖z‖ ^ 2)| * (((2 : ℕ) : ℝ) * ‖z‖ ^ (2 - 1)) ≤
      2 * |‖z‖ * Real.log ‖z‖| := by
    rw [profile_norm_sq]
    calc |Real.log (Real.log ‖z‖⁻¹)| * (((2 : ℕ) : ℝ) * ‖z‖ ^ (2 - 1))
        ≤ -Real.log ‖z‖ * (2 * ‖z‖) := by
          rw [show (((2 : ℕ) : ℝ) * ‖z‖ ^ (2 - 1)) = 2 * ‖z‖ by norm_num]
          gcongr
          exact abs_log_log_inv_le (norm_nonneg z) hz
      _ = 2 * -(‖z‖ * Real.log ‖z‖) := by ring
      _ ≤ 2 * |‖z‖ * Real.log ‖z‖| := by gcongr; exact neg_le_abs _
  rw [h1]
  exact add_le_add le_rfl h2

/-- `\bar∂f = z³ (‖z‖² log ‖z‖²)⁻¹` on the unit disc. -/
private theorem conjWirtingerDeriv_logLogExample_apply_one_eq {z : ℂ} (hz1 : ‖z‖ < 1) :
    conjWirtingerDeriv logLogExample z 1 = z ^ 3 * (profileDeriv (‖z‖ ^ 2) : ℂ) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [conjWirtingerDeriv_apply, hasFDerivAt_logLogExample_zero.fderiv]
  obtain ⟨hs0, hs1⟩ := norm_sq_mem hz0 hz1
  rw [logLogExample_eq,
    conjWirtingerDeriv_pow_mul_radial_apply_one 2 (hasDerivAt_profile hs0 hs1)]
  ring

/-- `(log ‖z‖²)⁻¹ → 0` at the origin, where it takes the value `0`. -/
private theorem tendsto_inv_log_norm_sq_nhds :
    Tendsto (fun z : ℂ ↦ (Real.log (‖z‖ ^ 2))⁻¹) (𝓝 0) (𝓝 0) := by
  have h : ContinuousWithinAt (fun z : ℂ ↦ (Real.log (‖z‖ ^ 2))⁻¹) {0}ᶜ 0 := by
    simpa [ContinuousWithinAt] using tendsto_inv_log_norm_sq
  simpa using (continuousWithinAt_compl_self.1 h).tendsto

/-- The radial term in the derivative of `\bar∂f`, rewritten in terms of `(log ‖z‖²)⁻¹`. -/
private theorem abs_profileDeriv_deriv_eq {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    ‖z‖ ^ 3 * (2 * |-(Real.log (‖z‖ ^ 2) + 1) / (‖z‖ ^ 2 * Real.log (‖z‖ ^ 2)) ^ 2| * ‖z‖) =
      2 * |(Real.log (‖z‖ ^ 2))⁻¹ + ((Real.log (‖z‖ ^ 2))⁻¹) ^ 2| := by
  obtain ⟨hs0, hs1⟩ := norm_sq_mem hz0 hz1
  set s := ‖z‖ ^ 2 with hs
  have ht : Real.log s ≠ 0 := (Real.log_neg hs0 hs1).ne
  have h : -(Real.log s + 1) / (s * Real.log s) ^ 2 =
      -((Real.log s)⁻¹ + ((Real.log s)⁻¹) ^ 2) / s ^ 2 := by
    field_simp
  rw [h, abs_div, abs_neg, abs_of_pos (pow_pos hs0 2)]
  have h4 : ‖z‖ ^ 3 * ‖z‖ = s ^ 2 := by rw [hs]; ring
  calc ‖z‖ ^ 3 * (2 * (|(Real.log s)⁻¹ + ((Real.log s)⁻¹) ^ 2| / s ^ 2) * ‖z‖)
      = 2 * |(Real.log s)⁻¹ + ((Real.log s)⁻¹) ^ 2| * ((‖z‖ ^ 3 * ‖z‖) / s ^ 2) := by ring
    _ = 2 * |(Real.log s)⁻¹ + ((Real.log s)⁻¹) ^ 2| := by
      rw [h4, div_self (pow_pos hs0 2).ne', mul_one]

/-- `z ↦ z³ (‖z‖² log ‖z‖²)⁻¹` is `C¹` on the unit disc: its derivative has size
`2 |u + u²| + 3 |u|` with `u = (log ‖z‖²)⁻¹ → 0`. -/
private theorem contDiffOn_pow_mul_profileDeriv :
    ContDiffOn ℝ 1 (fun z : ℂ ↦ z ^ 3 * (profileDeriv (‖z‖ ^ 2) : ℂ)) (ball 0 1) := by
  refine contDiffOn_one_ball_of_tendsto_fderiv (fun z hz hz0 ↦ ?_) ?_ ?_
  · obtain ⟨hs0, hs1⟩ := norm_sq_mem hz0 (by simpa using hz)
    exact contDiffAt_pow_mul_radial 3 (contDiffAt_profileDeriv hs0 hs1)
  · refine hasFDerivAt_zero_of_tendsto (k := fun z ↦ z ^ 2 * (profileDeriv (‖z‖ ^ 2) : ℂ))
      (fun z ↦ by ring) ?_
    have h0 := tendsto_inv_log_norm_sq_nhds.abs
    rw [abs_zero] at h0
    refine squeeze_zero_norm (fun z ↦ le_of_eq ?_) h0
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_sq_mul_abs_profileDeriv]
  · have hu := tendsto_inv_log_norm_sq
    have hb : Tendsto (fun z : ℂ ↦
        2 * |(Real.log (‖z‖ ^ 2))⁻¹ + ((Real.log (‖z‖ ^ 2))⁻¹) ^ 2| +
          3 * |(Real.log (‖z‖ ^ 2))⁻¹|) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((hu.add (hu.pow 2)).abs.const_mul 2).add (hu.abs.const_mul 3)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_norm_lt _ one_pos)] with z hz0 hz
    obtain ⟨hs0, hs1⟩ := norm_sq_mem hz0 hz
    refine (norm_fderiv_pow_mul_radial_le 3 (hasDerivAt_profileDeriv hs0 hs1)).trans
      (le_of_eq ?_)
    rw [abs_profileDeriv_deriv_eq hz0 hz, ← norm_sq_mul_abs_profileDeriv]
    push_cast
    ring

/-- **The example is `C¹` on the unit disc**, hence `W^{1,∞}` on every smaller disc. -/
theorem contDiffOn_logLogExample : ContDiffOn ℝ 1 logLogExample (ball 0 1) :=
  contDiffOn_one_ball_of_tendsto_fderiv
    (fun _ hz hz0 ↦ contDiffAt_logLogExample hz0 (by simpa using hz))
    hasFDerivAt_logLogExample_zero tendsto_fderiv_logLogExample

/-- The profile at `x²` for real `x ≥ 0`. -/
private theorem profile_sq {x : ℝ} (hx : 0 ≤ x) : profile (x ^ 2) = Real.log (Real.log x⁻¹) := by
  simpa [abs_of_nonneg hx] using profile_norm_sq (x : ℂ)

/-- Along the positive real axis, `Re (Df(x) 1) = 2 x (log x²)⁻¹ + 2 x log log (1 / x)`, written in
terms of the profiles. -/
private theorem re_fderiv_logLogExample_ofReal_apply_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (fderiv ℝ logLogExample (x : ℂ) 1).re =
      2 * x * (x ^ 2 * profileDeriv (x ^ 2)) + 2 * x * profile (x ^ 2) := by
  have hn : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx0]
  have hs0 : 0 < x ^ 2 := by positivity
  have hs1 : x ^ 2 < 1 := pow_lt_one₀ hx0.le hx1 two_ne_zero
  have h : HasDerivAt profile (profileDeriv (‖(x : ℂ)‖ ^ 2)) (‖(x : ℂ)‖ ^ 2) := by
    rw [hn]; exact hasDerivAt_profile hs0 hs1
  have hp := (hasDerivAt_pow 2 (x : ℂ)).hasFDerivAt.restrictScalars ℝ
  rw [logLogExample_eq,
    fderiv_fun_mul hp.differentiableAt (hasFDerivAt_radial h).differentiableAt]
  simp only [add_apply, smul_apply, fderiv_radial_apply h, hp.fderiv, smul_eq_mul, hn]
  simp only [conj_ofReal, one_mul, ofReal_re, ofReal_mul, ofReal_ofNat, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, add_re, mul_re, re_ofNat, im_ofNat,
    ofReal_im, mul_zero, sub_zero, mul_im, zero_mul, add_zero]
  rw [← ofReal_pow, ofReal_re]
  ring

/-- `log log (1 / x) → ∞` as `x → 0⁺`. -/
private theorem tendsto_log_log_inv :
    Tendsto (fun x : ℝ ↦ Real.log (Real.log x⁻¹)) (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)

/-- **The second derivative of the example is unbounded near the origin.** Along the positive real
axis `Re (Df(x) 1) = 2 x log log (1 / x) + 2 x / log x²`, so a bound `‖D²f‖ ≤ M` on a punctured
disc would give `Re (Df(x) 1) ≤ M x` by the mean value theorem, contradicting
`log log (1 / x) → ∞`. Since `f` is smooth off the origin, this is the failure of `W^{2,∞}`. -/
theorem not_isBoundedUnder_norm_fderiv_fderiv_logLogExample :
    ¬ IsBoundedUnder (· ≤ ·) (𝓝[≠] 0) (fun z ↦ ‖fderiv ℝ (fderiv ℝ logLogExample) z‖) := by
  rintro ⟨M, hM⟩
  rw [eventually_map] at hM
  obtain ⟨δ, hδ, hδM⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hM)
  set ρ := min δ (Real.exp (-1))
  have hρ : 0 < ρ := lt_min hδ (Real.exp_pos _)
  obtain ⟨x, ⟨hx0, hxρ⟩, hxP⟩ :=
    ((show ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 ρ from Ioo_mem_nhdsGT hρ).and
      (tendsto_log_log_inv.eventually_gt_atTop (M / 2 + 1))).exists
  have hxδ : x < δ := hxρ.trans_le (min_le_left _ _)
  have hxe : x < Real.exp (-1) := hxρ.trans_le (min_le_right _ _)
  have hx1 : x < 1 := hxe.trans exp_neg_one_lt_one
  -- the real slice `k t = Re (Df(t) 1)` of the derivative
  set k : ℝ → ℝ := fun t ↦ (fderiv ℝ logLogExample (t : ℂ) 1).re with hk
  have hcontD : ContinuousOn (fderiv ℝ logLogExample) (ball 0 1) :=
    contDiffOn_logLogExample.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hkcont : ContinuousOn k (Icc 0 x) := by
    have hmaps : MapsTo (fun t : ℝ ↦ (t : ℂ)) (Icc 0 x) (ball 0 1) := fun t ht ↦ by
      simpa [abs_of_nonneg ht.1] using ht.2.trans_lt hx1
    exact continuous_re.comp_continuousOn
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn
        (hcontD.comp continuous_ofReal.continuousOn hmaps))
  have hkderiv : ∀ t ∈ Ioo 0 x, HasDerivAt k
      (fderiv ℝ (fderiv ℝ logLogExample) (t : ℂ) 1 1).re t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.1.ne'
    have ht1 : ‖(t : ℂ)‖ < 1 := by simpa [abs_of_pos ht.1] using ht.2.trans hx1
    have hC2 : ContDiffAt ℝ 2 logLogExample (t : ℂ) := contDiffAt_logLogExample ht0 ht1
    have hD : HasFDerivAt (fderiv ℝ logLogExample)
        (fderiv ℝ (fderiv ℝ logLogExample) (t : ℂ)) (t : ℂ) :=
      ((hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
    have hof : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have happ := (hD.comp_hasDerivAt t hof).clm_apply (hasDerivAt_const t (1 : ℂ))
    simpa [Function.comp_def, hk] using reCLM.hasFDerivAt.comp_hasDerivAt t happ
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope k _ hx0 hkcont hkderiv
  have hk0 : k 0 = 0 := by simp [hk, hasFDerivAt_logLogExample_zero.fderiv]
  have hcM : (fderiv ℝ (fderiv ℝ logLogExample) (c : ℂ) 1 1).re ≤ M := by
    have hbound := hδM (y := (c : ℂ)) (by simpa [abs_of_pos hc.1] using hc.2.trans hxδ)
      (by simpa using hc.1.ne')
    calc (fderiv ℝ (fderiv ℝ logLogExample) (c : ℂ) 1 1).re
        ≤ ‖fderiv ℝ (fderiv ℝ logLogExample) (c : ℂ) 1 1‖ := re_le_norm _
      _ ≤ ‖fderiv ℝ (fderiv ℝ logLogExample) (c : ℂ)‖ := by
        refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
        simpa using (ContinuousLinearMap.le_opNorm _ (1 : ℂ))
      _ ≤ M := hbound
  have hkx : k x ≤ M * x := by
    rw [hk0, sub_zero, sub_zero] at hcslope
    have : k x = (fderiv ℝ (fderiv ℝ logLogExample) (c : ℂ) 1 1).re * x := by
      rw [hcslope]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hcM hx0.le
  change (fderiv ℝ logLogExample (x : ℂ) 1).re ≤ M * x at hkx
  rw [re_fderiv_logLogExample_ofReal_apply_one hx0 hx1] at hkx
  have hlog : Real.log (x ^ 2) < -1 := by
    have : Real.log x < -1 := (Real.log_lt_iff_lt_exp hx0).2 hxe
    rw [Real.log_pow]; push_cast; linarith
  have hA : x ^ 2 * profileDeriv (x ^ 2) = (Real.log (x ^ 2))⁻¹ := by
    rw [profileDeriv, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hinv : -1 ≤ (Real.log (x ^ 2))⁻¹ := by
    have hneg : (Real.log (x ^ 2))⁻¹ < 0 := inv_lt_zero.2 (by linarith)
    have hmul : Real.log (x ^ 2) * (Real.log (x ^ 2))⁻¹ = 1 :=
      mul_inv_cancel₀ (by linarith)
    nlinarith
  rw [hA, profile_sq hx0.le] at hkx
  have : 2 * x * (Real.log (Real.log x⁻¹)) ≤ 2 * x * (M / 2 + 1) := by nlinarith
  have := le_of_mul_le_mul_left this (by positivity)
  linarith

/-- **The example is not `C²` at the origin.** -/
theorem not_contDiffAt_two_logLogExample : ¬ ContDiffAt ℝ 2 logLogExample 0 := by
  intro h
  have h2 : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ logLogExample)) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
  obtain ⟨δ, hδ, hδ1⟩ := Metric.continuousAt_iff.1 h2.continuousAt 1 one_pos
  refine not_isBoundedUnder_norm_fderiv_fderiv_logLogExample
    ⟨‖fderiv ℝ (fderiv ℝ logLogExample) 0‖ + 1, ?_⟩
  rw [eventually_map]
  refine nhdsWithin_le_nhds (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun z hz ↦ ?_⟩)
  have h1 := hδ1 hz
  rw [dist_eq_norm] at h1
  have h3 := norm_le_insert' (fderiv ℝ (fderiv ℝ logLogExample) z)
    (fderiv ℝ (fderiv ℝ logLogExample) 0)
  change ‖fderiv ℝ (fderiv ℝ logLogExample) z‖ ≤ ‖fderiv ℝ (fderiv ℝ logLogExample) 0‖ + 1
  linarith

/-- **`\bar∂f = z³ / (2 ‖z‖² log ‖z‖)` on the unit disc**, of size `‖z‖ / (2 |log ‖z‖|)`. At the
origin both sides vanish. -/
theorem conjWirtingerDeriv_logLogExample_apply_one {z : ℂ} (hz : ‖z‖ < 1) :
    conjWirtingerDeriv logLogExample z 1 = z ^ 3 / (2 * ‖z‖ ^ 2 * Real.log ‖z‖) := by
  rw [conjWirtingerDeriv_logLogExample_apply_one_eq hz, profileDeriv, Real.log_pow]
  push_cast
  ring

/-- **`\bar∂f` is `C¹` on the unit disc.** -/
theorem contDiffOn_conjWirtingerDeriv_logLogExample :
    ContDiffOn ℝ 1 (fun z ↦ conjWirtingerDeriv logLogExample z 1) (ball 0 1) :=
  contDiffOn_pow_mul_profileDeriv.congr fun _ hz ↦
    conjWirtingerDeriv_logLogExample_apply_one_eq (by simpa using hz)

end Example

section Graph

/-- **The graph structure of `g`**: the structure
`J_g(z, w)(v, a) = (i v, i a - 2 i \bar∂g(z) conj v)` on `WithLp 2 (ℂ × ℂ)`, Gromov's graph
structure `TauCeti.Floer.graphStructure` for the target structure `i` and the one-form
`\bar∂g(z) = \bar∂g(z)(1) conj`. The graph of `g` is `J_g`-holomorphic. -/
@[expose] noncomputable def conjWirtingerGraphStructure (g : ℂ → ℂ) :
    WithLp 2 (ℂ × ℂ) → WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  Floer.graphStructure (fun _ ↦ ContinuousLinearMap.mul ℝ ℂ I)
    (fun p ↦ conjWirtingerDeriv g p.1 1 • (conjCLE : ℂ →L[ℝ] ℂ))

/-- The formula `J_g(z, w)(v, a) = (i v, i a - 2 i \bar∂g(z) conj v)`. -/
theorem conjWirtingerGraphStructure_apply (g : ℂ → ℂ) (p ζ : WithLp 2 (ℂ × ℂ)) :
    conjWirtingerGraphStructure g p ζ = WithLp.toLp 2 (I * ζ.fst,
      I * ζ.snd - 2 * I * (conjWirtingerDeriv g p.fst 1 * conj ζ.fst)) := by
  simp [conjWirtingerGraphStructure]
  ring

/-- The graph structure squares to `-1`. -/
theorem conjWirtingerGraphStructure_apply_apply (g : ℂ → ℂ) (p ζ : WithLp 2 (ℂ × ℂ)) :
    conjWirtingerGraphStructure g p (conjWirtingerGraphStructure g p ζ) = -ζ :=
  Floer.graphStructure_graphStructure (fun v ↦ by simp [← mul_assoc]) ζ

/-- The graph structure is as regular as `\bar∂g`. -/
theorem contDiffOn_conjWirtingerGraphStructure {g : ℂ → ℂ} {n : WithTop ℕ∞} {s : Set ℂ}
    (hg : ContDiffOn ℝ n (fun z ↦ conjWirtingerDeriv g z 1) s) :
    ContDiffOn ℝ n (conjWirtingerGraphStructure g) (WithLp.ofLp ⁻¹' (s ×ˢ univ)) :=
  Floer.contDiffOn_graphStructure contDiffOn_const
    ((hg.comp contDiffOn_fst fun _ (hp : _ ∈ s ×ˢ univ) ↦ hp.1).smul contDiffOn_const)

/-- **The graph of `g` solves `dG(i) = J_g dG(1)`.** The graph `G(z) = (z, g z)` of a
real-differentiable `g` solves the inhomogeneous equation `\bar∂g = \bar∂g`, which Gromov's
construction turns into this equation for `J_g`. -/
theorem fderiv_graph_I_eq_conjWirtingerGraphStructure {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, g w)) z I =
      conjWirtingerGraphStructure g (WithLp.toLp 2 (z, g z))
        (fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, g w)) z 1) := by
  refine (Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff hg).2 ?_
  rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := g) z I,
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := g) z 1]
  simp only [smul_eq_mul, conj_I, neg_mul, smul_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousAlgEquiv.coeCLE_apply, conjCAE_apply, mul_neg, sub_neg_eq_add, one_mul, map_one,
    wirtingerDeriv_add_conjWirtingerDeriv, mul_one, ContinuousLinearMap.mul_apply']
  rw [← wirtingerDeriv_add_conjWirtingerDeriv g z 1]
  ring

/-- The graph structure of `g` as a point-dependent `TauCeti.AlmostComplexStructure`. -/
@[expose] noncomputable def conjWirtingerGraphAlmostComplex (g : ℂ → ℂ) (p : WithLp 2 (ℂ × ℂ)) :
    AlmostComplexStructure (WithLp 2 (ℂ × ℂ)) where
  toLinearMap := (conjWirtingerGraphStructure g p).toLinearMap
  square_neg := LinearMap.ext fun ζ ↦ by simp [conjWirtingerGraphStructure_apply_apply]

/-- The almost complex structure acts as the graph structure. -/
@[simp]
theorem conjWirtingerGraphAlmostComplex_apply (g : ℂ → ℂ) (p ζ : WithLp 2 (ℂ × ℂ)) :
    conjWirtingerGraphAlmostComplex g p ζ = conjWirtingerGraphStructure g p ζ :=
  rfl

/-- **The graph of `g` is `J_g`-holomorphic** at every point where `g` is real-differentiable, for
the standard structure on the domain `ℂ`. -/
theorem isJHolomorphicAt_graph_conjWirtingerGraphAlmostComplex {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (conjWirtingerGraphAlmostComplex g) (fun w ↦ WithLp.toLp 2 (w, g w)) z := by
  have hd : DifferentiableAt ℝ (fun w ↦ WithLp.toLp 2 (w, g w)) z :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm.differentiableAt.comp z
      (differentiableAt_id.prodMk hg)
  refine isJHolomorphicAt_of_hasFDerivAt hd.hasFDerivAt
    ((isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ ?_)
  have hI := fderiv_graph_I_eq_conjWirtingerGraphStructure hg
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    apply Complex.ext <;> simp
  have hIv : I • v = v.re • I - v.im • (1 : ℂ) := by
    apply Complex.ext <;> simp
  simp only [ContinuousLinearMap.coe_coe, AlmostComplexStructure.ofComplexModule_apply,
    conjWirtingerGraphAlmostComplex_apply]
  rw [hIv]
  conv_rhs => rw [hv]
  simp only [map_add, map_sub, map_smul, hI, conjWirtingerGraphStructure_apply_apply, smul_neg]
  abel

/-- **The graph structure of the example is `C¹`** over the unit disc. -/
theorem contDiffOn_conjWirtingerGraphStructure_logLogExample :
    ContDiffOn ℝ 1 (conjWirtingerGraphStructure logLogExample)
      (WithLp.ofLp ⁻¹' (ball 0 1 ×ˢ univ)) :=
  contDiffOn_conjWirtingerGraphStructure contDiffOn_conjWirtingerDeriv_logLogExample

/-- **The graph of the example is pseudoholomorphic** for its `C¹` graph structure on the unit
disc. Together with `TauCeti.contDiffOn_logLogExample` and
`TauCeti.not_isBoundedUnder_norm_fderiv_fderiv_logLogExample`, it is a `W^{1,∞}` solution for a
`C¹` structure that is not `W^{2,∞}`. -/
theorem isJHolomorphicOn_graph_logLogExample :
    IsJHolomorphicOn (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ)
      (conjWirtingerGraphAlmostComplex logLogExample)
      (fun w ↦ WithLp.toLp 2 (w, logLogExample w)) (ball 0 1) :=
  (isJHolomorphicOn_iff _ _ _ _).2 fun _ hz ↦
    (isJHolomorphicAt_graph_conjWirtingerGraphAlmostComplex
      ((contDiffOn_logLogExample.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt
        one_ne_zero)).isJHolomorphicWithinAt

end Graph

end TauCeti
