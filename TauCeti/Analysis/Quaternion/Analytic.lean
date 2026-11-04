/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.BochnerIntegral
public import TauCeti.Analysis.Analytic.Composition
public import TauCeti.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Quaternion.Kernel
import Mathlib.Analysis.Analytic.CPolynomialDef

/-!
# Power-series expansion and real analyticity of Cauchy–Fueter potentials

For a pole `q₀ + h` displaced from `q₀` relative to an evaluation point `q ≠ q₀`, the Euclidean
law of cosines writes `‖q - (q₀ + h)‖² = ‖q - q₀‖² * (1 - u)` with dimensionless quadratic
perturbation `u = (2 ⟪q - q₀, h⟫ - ‖h‖²) / ‖q - q₀‖²`. Consequently

`cauchyFueterKernel q (q₀ + h) = ((1 - u)²)⁻¹ • ((‖q - q₀‖⁴)⁻¹ • (star (q - q₀) - star h))`.

Whenever `‖q - q₀‖ ≥ δ > 0`, Cauchy–Schwarz bounds `|u| ≤ 2 (‖h‖ / δ) + (‖h‖ / δ)²`, which lies
strictly below `1` for every `‖h‖ < (√2 - 1) δ` since `(t + 1)² < 2` for `0 ≤ t < √2 - 1`.

Expanding `(1 - u)⁻² = ∑ₙ (n + 1) uⁿ` in the Banach algebra `C(K, ℝ)` for a compact boundary
parameterization `φ : C(K, ℍ)` avoiding `q₀` and composing via the quantitative Cauchy-majorant
bound `HasFPowerSeriesOnBall.comp` yields a formal multilinear series
`TauCeti.cauchyFueterKernelSeries φ hφ` in `C(K, ℍ)` — depending only on `(φ, q₀)` and not on `δ` —
that represents `q ↦ cauchyFueterKernel (φ ·) q` on the full ball of radius `(√2 - 1) δ` around
`q₀`. Pairing with any integrable quaternionic boundary density on a single compact piece or a
finite family of compact faces (such as the eight faces of a four-dimensional box) transfers the
same convergence ball, real analyticity, and `C^∞` smoothness to both left and right Cauchy–Fueter
boundary potentials away from the boundary image.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Remark after Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set Topology
open scoped ENNReal NNReal RealInnerProductSpace Ring

namespace TauCeti

/-! ### Perturbation identity and pointwise series of the Cauchy–Fueter kernel -/

/-- Factoring out `‖q - q₀‖²` from the squared distance to a displaced pole `q₀ + h`. -/
theorem norm_sub_add_sq_eq {q q₀ : ℍ} (hq : q ≠ q₀) (h : ℍ) :
    ‖q - (q₀ + h)‖ ^ 2 =
      ‖q - q₀‖ ^ 2 * (1 - (2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2) := by
  have hw : ‖q - q₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hq))
  rw [sub_add_eq_sub_sub, norm_sub_sq_real, mul_sub, mul_one, mul_div_cancel₀ _ hw]
  ring

/-- Exact algebraic factorization of `cauchyFueterKernel q (q₀ + h)` around `q₀` for `q ≠ q₀`.
This holds for every `h : ℍ`, including the displaced pole `h = q - q₀` where both sides vanish. -/
theorem cauchyFueterKernel_add_eq {q q₀ : ℍ} (hq : q ≠ q₀) (h : ℍ) :
    cauchyFueterKernel q (q₀ + h) =
      ((1 - (2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2) ^ 2)⁻¹ •
        ((‖q - q₀‖ ^ 4)⁻¹ • (star (q - q₀) - star h)) := by
  have hsq := norm_sub_add_sq_eq hq h
  have h4 : ‖q - (q₀ + h)‖ ^ 4 =
      (1 - (2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2) ^ 2 * ‖q - q₀‖ ^ 4 := by
    calc ‖q - (q₀ + h)‖ ^ 4
      _ = (‖q - (q₀ + h)‖ ^ 2) ^ 2 := by ring
      _ = (‖q - q₀‖ ^ 2 * (1 - (2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2)) ^ 2 := by rw [hsq]
      _ = (1 - (2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2) ^ 2 * ‖q - q₀‖ ^ 4 := by ring
  rw [cauchyFueterKernel_eq, h4, mul_inv, sub_add_eq_sub_sub, star_sub, smul_smul]

/-- `√2 - 1` is strictly positive. -/
theorem sqrt_two_sub_one_pos : 0 < Real.sqrt 2 - 1 := by
  rw [sub_pos, Real.lt_sqrt zero_le_one]
  norm_num

/-- `√2 - 1` is strictly less than `1`. -/
theorem sqrt_two_sub_one_lt_one : Real.sqrt 2 - 1 < 1 := by
  have h : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' zero_lt_two]
    norm_num
  linarith

/-- Whenever `0 ≤ t < √2 - 1`, the quadratic majorant `2 t + t²` is strictly less than `1`. -/
theorem two_mul_add_sq_lt_one {t : ℝ} (ht₀ : 0 ≤ t) (ht : t < Real.sqrt 2 - 1) :
    2 * t + t ^ 2 < 1 := by
  have hlt : t + 1 < Real.sqrt 2 := by linarith
  have hsq : (t + 1) ^ 2 < Real.sqrt 2 ^ 2 :=
    pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
  rw [Real.sq_sqrt zero_le_two] at hsq
  linarith

/-- Uniform Cauchy–Schwarz bound on the dimensionless perturbation `(2 ⟪w, h⟫ - ‖h‖²) / ‖w‖²`
when `‖w‖ ≥ δ > 0`. -/
theorem abs_two_mul_inner_sub_norm_sq_div_le {w h : ℍ} {δ : ℝ} (hδ : 0 < δ) (hw : δ ≤ ‖w‖) :
    |(2 * ⟪w, h⟫ - ‖h‖ ^ 2) / ‖w‖ ^ 2| ≤ 2 * (‖h‖ / δ) + (‖h‖ / δ) ^ 2 := by
  have hw₀ : 0 < ‖w‖ := hδ.trans_le hw
  have hdiv : ‖h‖ / ‖w‖ ≤ ‖h‖ / δ := div_le_div_of_nonneg_left (norm_nonneg h) hδ hw
  calc |(2 * ⟪w, h⟫ - ‖h‖ ^ 2) / ‖w‖ ^ 2|
    _ = |2 * ⟪w, h⟫ - ‖h‖ ^ 2| / ‖w‖ ^ 2 := by
        rw [abs_div, abs_of_pos (pow_pos hw₀ 2)]
    _ ≤ (2 * (‖w‖ * ‖h‖) + ‖h‖ ^ 2) / ‖w‖ ^ 2 := by
        gcongr
        refine (abs_sub _ _).trans (add_le_add ?_ (le_of_eq (abs_of_nonneg (sq_nonneg ‖h‖))))
        rw [abs_mul, abs_of_pos zero_lt_two]
        gcongr
        exact abs_real_inner_le_norm w h
    _ = 2 * (‖h‖ / ‖w‖) + (‖h‖ / ‖w‖) ^ 2 := by
        field_simp
    _ ≤ 2 * (‖h‖ / δ) + (‖h‖ / δ) ^ 2 := by gcongr

/-- Pointwise expansion of `cauchyFueterKernel q (q₀ + h)` via `(1 - u)⁻² = ∑ₙ (n + 1) uⁿ`
on the ball `‖h‖ < (√2 - 1) ‖q - q₀‖`. -/
theorem hasSum_cauchyFueterKernel_add {q q₀ h : ℍ} (hq : q ≠ q₀)
    (hh : ‖h‖ < (Real.sqrt 2 - 1) * ‖q - q₀‖) :
    HasSum (fun n : ℕ ↦
      (((n + 1 : ℝ) * ((2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2) ^ n) *
        (‖q - q₀‖ ^ 4)⁻¹) • (star (q - q₀) - star h))
      (cauchyFueterKernel q (q₀ + h)) := by
  have hw : 0 < ‖q - q₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hq)
  set u : ℝ := (2 * ⟪q - q₀, h⟫ - ‖h‖ ^ 2) / ‖q - q₀‖ ^ 2
  have hu : ‖u‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact (abs_two_mul_inner_sub_norm_sq_div_le hw le_rfl).trans_lt
      (two_mul_add_sq_lt_one (by positivity) ((div_lt_iff₀ hw).2 hh))
  have hgeom : HasSum (fun n : ℕ ↦ ((n + 1 : ℝ) * u ^ n)) (((1 - u) ^ 2)⁻¹) := by
    convert hasSum_choose_mul_geometric_of_norm_lt_one' 1 hu using 1
    · ext n
      simp [Nat.choose_one_right]
    · rw [Ring.inverse_eq_inv, inv_pow]
  let L : ℝ →L[ℝ] ℍ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    ((‖q - q₀‖ ^ 4)⁻¹ • (star (q - q₀) - star h))
  rw [cauchyFueterKernel_add_eq hq h]
  simpa [L, smul_smul] using hgeom.mapL L

/-! ### Joint and slice real analyticity of the Cauchy–Fueter kernel off the diagonal -/

/-- Quaternion conjugation as a continuous real-linear map `ℍ →L[ℝ] ℍ`. -/
private noncomputable def conjCLM : ℍ →L[ℝ] ℍ :=
  ((Quaternion.starAe : ℍ ≃ₐ[ℝ] ℍᵐᵒᵖ).toLinearEquiv.trans
    (MulOpposite.opLinearEquiv ℝ).symm).toContinuousLinearMap

@[simp]
private theorem conjCLM_apply (x : ℍ) : conjCLM x = star x := rfl

/-- `cauchyFueterKernel` is jointly real analytic at every off-diagonal pair `(q, q₀)`. -/
theorem analyticAt_cauchyFueterKernel_uncurry {p : ℍ × ℍ} (hp : p.1 ≠ p.2) :
    AnalyticAt ℝ (Function.uncurry cauchyFueterKernel) p := by
  have hd : AnalyticAt ℝ (fun x : ℍ × ℍ ↦ x.1 - x.2) p :=
    (ContinuousLinearMap.fst ℝ ℍ ℍ - ContinuousLinearMap.snd ℝ ℍ ℍ).analyticAt p
  have hnsq : AnalyticAt ℝ (fun x : ℍ × ℍ ↦ ‖x.1 - x.2‖ ^ 2) p :=
    (AnalyticAt.comp₂ (f := fun x : ℍ × ℍ ↦ x.1 - x.2) (g := fun x : ℍ × ℍ ↦ x.1 - x.2)
      ((innerSL ℝ (E := ℍ)).analyticAt_bilinear _) hd hd).congr
      (Eventually.of_forall fun x ↦
        (innerSL_apply_apply ℝ (x.1 - x.2) (x.1 - x.2)).trans (real_inner_self_eq_norm_sq _))
  have hn4 : AnalyticAt ℝ (fun x : ℍ × ℍ ↦ ‖x.1 - x.2‖ ^ 4) p := by
    convert hnsq.fun_mul hnsq using 1
    ext x
    ring
  have hne : ‖p.1 - p.2‖ ^ 4 ≠ 0 := pow_ne_zero 4 (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))
  have hinv : AnalyticAt ℝ (fun x : ℍ × ℍ ↦ (‖x.1 - x.2‖ ^ 4)⁻¹) p := hn4.fun_inv hne
  have hstar : AnalyticAt ℝ (fun x : ℍ × ℍ ↦ star (x.1 - x.2)) p := by
    simpa [Function.comp_def] using
      AnalyticAt.comp (f := fun x : ℍ × ℍ ↦ x.1 - x.2) (conjCLM.analyticAt _) hd
  have hfn : Function.uncurry cauchyFueterKernel =
      fun x : ℍ × ℍ ↦ (‖x.1 - x.2‖ ^ 4)⁻¹ • star (x.1 - x.2) := by
    funext ⟨q, q₀⟩
    exact cauchyFueterKernel_eq q q₀
  rw [hfn]
  exact hinv.fun_smul hstar

/-- `cauchyFueterKernel` is jointly real analytic on the off-diagonal open set `{p | p.1 ≠ p.2}`. -/
theorem analyticOnNhd_cauchyFueterKernel_uncurry :
    AnalyticOnNhd ℝ (Function.uncurry cauchyFueterKernel) {p : ℍ × ℍ | p.1 ≠ p.2} :=
  fun _ hp ↦ analyticAt_cauchyFueterKernel_uncurry hp

/-- Away from its pole `q₀`, `q ↦ cauchyFueterKernel q q₀` is real analytic at `q`. -/
theorem analyticAt_cauchyFueterKernel_left {q q₀ : ℍ} (hq : q ≠ q₀) :
    AnalyticAt ℝ (fun x ↦ cauchyFueterKernel x q₀) q :=
  (analyticAt_cauchyFueterKernel_uncurry (p := (q, q₀)) hq).curry_left

/-- Away from `q`, the pole map `q₀ ↦ cauchyFueterKernel q q₀` is real analytic at `q₀`. -/
theorem analyticAt_cauchyFueterKernel_right {q q₀ : ℍ} (hq : q ≠ q₀) :
    AnalyticAt ℝ (fun y ↦ cauchyFueterKernel q y) q₀ :=
  (analyticAt_cauchyFueterKernel_uncurry (p := (q, q₀)) hq).curry_right

/-- `q ↦ cauchyFueterKernel q q₀` is real analytic on `{q₀}ᶜ`. -/
theorem analyticOnNhd_cauchyFueterKernel_left (q₀ : ℍ) :
    AnalyticOnNhd ℝ (fun x ↦ cauchyFueterKernel x q₀) {q₀}ᶜ :=
  fun _ hq ↦ analyticAt_cauchyFueterKernel_left hq

/-- `q₀ ↦ cauchyFueterKernel q q₀` is real analytic on `{q}ᶜ`. -/
theorem analyticOnNhd_cauchyFueterKernel_right (q : ℍ) :
    AnalyticOnNhd ℝ (fun y ↦ cauchyFueterKernel q y) {q}ᶜ :=
  fun _ hq ↦ analyticAt_cauchyFueterKernel_right (Ne.symm hq)

/-! ### Quantitative uniform power series on compact boundary pieces -/

section UniformKernelSeries

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Continuous inverse-square distance `z ↦ (‖φ z - q₀‖²)⁻¹` on a compact space avoiding `q₀`. -/
private noncomputable def invNormSubSqMap (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    C(K, ℝ) :=
  ⟨fun z ↦ (‖φ z - q₀‖ ^ 2)⁻¹,
    Continuous.inv₀ ((φ.continuous.sub continuous_const).norm.pow 2)
      fun z ↦ pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (hφ z)))⟩

/-- Continuous inverse-fourth-power distance `z ↦ (‖φ z - q₀‖⁴)⁻¹` on a compact space. -/
private noncomputable def invNormSubPowFourMap (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    C(K, ℝ) :=
  ⟨fun z ↦ (‖φ z - q₀‖ ^ 4)⁻¹,
    Continuous.inv₀ ((φ.continuous.sub continuous_const).norm.pow 4)
      fun z ↦ pow_ne_zero 4 (norm_ne_zero_iff.2 (sub_ne_zero.2 (hφ z)))⟩

/-- Linear part `h ↦ (z ↦ 2 ⟪φ z - q₀, h⟫ / ‖φ z - q₀‖²)` of the dimensionless perturbation. -/
private noncomputable def kernelPerturbLinear (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    ℍ →L[ℝ] C(K, ℝ) :=
  let d2 := invNormSubSqMap φ hφ
  let disp : C(K, ℍ) := φ - ContinuousMap.const K q₀
  LinearMap.mkContinuous
    { toFun h := ⟨fun z ↦ 2 * ⟪disp z, h⟫ * d2 z,
        ((continuous_const.mul (disp.continuous.inner continuous_const)).mul d2.continuous)⟩
      map_add' h₁ h₂ := by ext z; simp [inner_add_right]; ring
      map_smul' c h := by ext z; simp [inner_smul_right]; ring }
    (2 * ‖disp‖ * ‖d2‖) fun h ↦
      (ContinuousMap.norm_le _ (by positivity)).2 fun z ↦ by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos zero_lt_two]
        calc 2 * |⟪disp z, h⟫| * |d2 z|
          _ ≤ 2 * (‖disp z‖ * ‖h‖) * ‖d2‖ := by
              gcongr
              · exact abs_real_inner_le_norm _ _
              · exact d2.norm_coe_le_norm z
          _ ≤ 2 * (‖disp‖ * ‖h‖) * ‖d2‖ := by
              gcongr
              exact disp.norm_coe_le_norm z
          _ = 2 * ‖disp‖ * ‖d2‖ * ‖h‖ := by ring

private theorem kernelPerturbLinear_apply (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    (h : ℍ) (z : K) :
    kernelPerturbLinear φ hφ h z = 2 * ⟪φ z - q₀, h⟫ / ‖φ z - q₀‖ ^ 2 := by
  simp [kernelPerturbLinear, invNormSubSqMap, div_eq_mul_inv]

private theorem norm_kernelPerturbLinear_le (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) :
    ‖kernelPerturbLinear φ hφ‖ ≤ 2 / δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun z ↦ ?_
  have hw₀ : 0 < ‖φ z - q₀‖ := hδ₀.trans_le (hδ z)
  rw [kernelPerturbLinear_apply, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos zero_lt_two,
    abs_of_pos (pow_pos hw₀ 2)]
  calc 2 * |⟪φ z - q₀, h⟫| / ‖φ z - q₀‖ ^ 2
    _ ≤ 2 * (‖φ z - q₀‖ * ‖h‖) / ‖φ z - q₀‖ ^ 2 := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = (2 / ‖φ z - q₀‖) * ‖h‖ := by
        field_simp
    _ ≤ (2 / δ) * ‖h‖ := by
        gcongr
        exact hδ z

/-- Quadratic part `(h₁, h₂) ↦ (z ↦ -⟪h₁, h₂⟫ / ‖φ z - q₀‖²)` of the perturbation. -/
private noncomputable def kernelPerturbBilin (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    ℍ [×2]→L[ℝ] C(K, ℝ) :=
  let d2 := invNormSubSqMap φ hφ
  MultilinearMap.mkContinuous
    { toFun m := (-⟪m 0, m 1⟫) • d2
      map_update_add' m i x y := by
        fin_cases i <;> ext z <;> simp [inner_add_left, inner_add_right] <;> ring
      map_update_smul' m i c x := by
        fin_cases i <;> ext z <;> simp [inner_smul_left, inner_smul_right] <;> ring }
    ‖d2‖ fun m ↦ by
      rw [MultilinearMap.coe_mk, norm_smul, Real.norm_eq_abs, abs_neg, Fin.prod_univ_two]
      calc |⟪m 0, m 1⟫| * ‖d2‖
        _ ≤ (‖m 0‖ * ‖m 1‖) * ‖d2‖ := by
            gcongr
            exact abs_real_inner_le_norm _ _
        _ = ‖d2‖ * (‖m 0‖ * ‖m 1‖) := mul_comm _ _

private theorem kernelPerturbBilin_apply (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    (m : Fin 2 → ℍ) (z : K) :
    kernelPerturbBilin φ hφ m z = -⟪m 0, m 1⟫ / ‖φ z - q₀‖ ^ 2 := by
  simp [kernelPerturbBilin, invNormSubSqMap, div_eq_mul_inv]

private theorem norm_kernelPerturbBilin_le (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) :
    ‖kernelPerturbBilin φ hφ‖ ≤ 1 / δ ^ 2 := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  rw [Fin.prod_univ_two]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun z ↦ ?_
  have hw₀ : 0 < ‖φ z - q₀‖ := hδ₀.trans_le (hδ z)
  rw [kernelPerturbBilin_apply, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (pow_pos hw₀ 2)]
  calc |⟪m 0, m 1⟫| / ‖φ z - q₀‖ ^ 2
    _ ≤ (‖m 0‖ * ‖m 1‖) / ‖φ z - q₀‖ ^ 2 := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = (1 / ‖φ z - q₀‖ ^ 2) * (‖m 0‖ * ‖m 1‖) := by ring
    _ ≤ (1 / δ ^ 2) * (‖m 0‖ * ‖m 1‖) := by
        gcongr
        exact hδ z

/-- Degree-2 formal multilinear series in `C(K, ℝ)` for the dimensionless perturbation
`h ↦ (2 ⟪φ · - q₀, h⟫ - ‖h‖²) / ‖φ · - q₀‖²`. -/
private noncomputable def kernelPerturbSeries (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    FormalMultilinearSeries ℝ ℍ C(K, ℝ)
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 ℝ ℍ C(K, ℝ)).symm (kernelPerturbLinear φ hφ)
  | 2 => kernelPerturbBilin φ hφ
  | _ + 3 => 0

private theorem kernelPerturbSeries_one (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    kernelPerturbSeries φ hφ 1 =
      (continuousMultilinearCurryFin1 ℝ ℍ C(K, ℝ)).symm (kernelPerturbLinear φ hφ) := rfl

private theorem nnnorm_kernelPerturbSeries_add_three (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    (n : ℕ) : ‖kernelPerturbSeries φ hφ (n + 3)‖₊ = 0 := by
  unfold kernelPerturbSeries
  exact @nnnorm_zero (ℍ [×n + 3]→L[ℝ] C(K, ℝ)) _

/-- Continuous map `h ↦ (z ↦ (2 ⟪φ z - q₀, h⟫ - ‖h‖²) / ‖φ z - q₀‖²)` in `C(K, ℝ)`. -/
private noncomputable def kernelPerturbMap (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) (h : ℍ) :
    C(K, ℝ) :=
  kernelPerturbLinear φ hφ h + kernelPerturbBilin φ hφ fun _ ↦ h

private theorem kernelPerturbMap_apply (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    (h : ℍ) (z : K) :
    kernelPerturbMap φ hφ h z = (2 * ⟪φ z - q₀, h⟫ - ‖h‖ ^ 2) / ‖φ z - q₀‖ ^ 2 := by
  rw [kernelPerturbMap, ContinuousMap.add_apply, kernelPerturbLinear_apply,
    kernelPerturbBilin_apply, real_inner_self_eq_norm_sq]
  ring

private theorem kernelPerturbMap_zero (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    kernelPerturbMap φ hφ 0 = 0 := by
  ext z
  simp [kernelPerturbMap_apply]

private theorem hasFiniteFPowerSeriesOnBall_kernelPerturbMap (φ : C(K, ℍ)) {q₀ : ℍ}
    (hφ : ∀ z, φ z ≠ q₀) :
    HasFiniteFPowerSeriesOnBall (kernelPerturbMap φ hφ) (kernelPerturbSeries φ hφ) 0 3 ⊤ := by
  refine .mk' (fun m hm ↦ ?_) ENNReal.zero_lt_top fun h _ ↦ ?_
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    rfl
  · simp [Finset.sum_range_succ, kernelPerturbSeries, kernelPerturbMap]

private theorem tsum_kernelPerturbSeries_lt_one (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) {r' : ℝ≥0}
    (hr' : (r' : ℝ≥0∞) < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) :
    ((∑' k : ℕ, ‖kernelPerturbSeries φ hφ (k + 1)‖₊ * r' ^ (k + 1) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hr'_real : (r' : ℝ) < (Real.sqrt 2 - 1) * δ := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr'
    exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos sqrt_two_sub_one_pos hδ₀)).1 hr'
  rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, NNReal.coe_one]
  have htsum : (∑' k : ℕ, ‖kernelPerturbSeries φ hφ (k + 1)‖₊ * r' ^ (k + 1)) =
      ‖kernelPerturbSeries φ hφ 1‖₊ * r' + ‖kernelPerturbSeries φ hφ 2‖₊ * r' ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro k hk
      rw [Finset.mem_range, not_lt] at hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
      rw [nnnorm_kernelPerturbSeries_add_three φ hφ j, zero_mul]
  rw [htsum]
  push_cast
  have h1 : ‖kernelPerturbSeries φ hφ 1‖ ≤ 2 / δ := by
    rw [kernelPerturbSeries_one, LinearIsometryEquiv.norm_map]
    exact norm_kernelPerturbLinear_le φ hφ hδ₀ hδ
  have h2 : ‖kernelPerturbSeries φ hφ 2‖ ≤ 1 / δ ^ 2 :=
    norm_kernelPerturbBilin_le φ hφ hδ₀ hδ
  calc ‖kernelPerturbSeries φ hφ 1‖ * (r' : ℝ) + ‖kernelPerturbSeries φ hφ 2‖ * (r' : ℝ) ^ 2
    _ ≤ (2 / δ) * (r' : ℝ) + (1 / δ ^ 2) * (r' : ℝ) ^ 2 := by gcongr
    _ = 2 * ((r' : ℝ) / δ) + ((r' : ℝ) / δ) ^ 2 := by field_simp
    _ < 1 := two_mul_add_sq_lt_one (by positivity) ((div_lt_iff₀ hδ₀).2 hr'_real)

/-- Scalar series in `C(K, ℝ)` for `h ↦ (1 - kernelPerturbMap φ hφ h)⁻¹ʳ ^ 2`. -/
private noncomputable def kernelScalarFactorSeries (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    FormalMultilinearSeries ℝ ℍ C(K, ℝ) :=
  (FormalMultilinearSeries.ofScalars C(K, ℝ) fun n : ℕ ↦ ((n + 1).choose 1 : ℝ)).comp
    (kernelPerturbSeries φ hφ)

private theorem hasFPowerSeriesOnBall_kernelScalarFactor (φ : C(K, ℍ)) {q₀ : ℍ}
    (hφ : ∀ z, φ z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) :
    HasFPowerSeriesOnBall (fun h : ℍ ↦ (1 - kernelPerturbMap φ hφ h)⁻¹ʳ ^ 2)
      (kernelScalarFactorSeries φ hφ) 0 (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hg : HasFPowerSeriesOnBall (fun u : C(K, ℝ) ↦ (1 - u)⁻¹ʳ ^ 2)
      (FormalMultilinearSeries.ofScalars C(K, ℝ) fun n : ℕ ↦ ((n + 1).choose 1 : ℝ))
      (kernelPerturbMap φ hφ 0) 1 := by
    rw [kernelPerturbMap_zero]
    exact hasFPowerSeriesOnBall_inverse_one_sub_pow ℝ C(K, ℝ) 1
  have hr_pos : 0 < ENNReal.ofReal ((Real.sqrt 2 - 1) * δ) :=
    ENNReal.ofReal_pos.2 (mul_pos sqrt_two_sub_one_pos hδ₀)
  exact hg.comp (hasFiniteFPowerSeriesOnBall_kernelPerturbMap φ hφ).toHasFPowerSeriesOnBall
    hr_pos le_top fun _ hr' ↦ tsum_kernelPerturbSeries_lt_one φ hφ hδ₀ hδ hr'

/-- Multiplication by the unperturbed kernel `z ↦ cauchyFueterKernel (φ z) q₀` as a continuous
linear map `C(K, ℝ) →L[ℝ] C(K, ℍ)`. -/
private noncomputable def kernelZeroNumerCLM (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    C(K, ℝ) →L[ℝ] C(K, ℍ) :=
  let w₀ : C(K, ℍ) := ⟨fun z ↦ (‖φ z - q₀‖ ^ 4)⁻¹ • star (φ z - q₀),
    (invNormSubPowFourMap φ hφ).continuous.smul
      (conjCLM.continuous.comp (φ.continuous.sub continuous_const))⟩
  LinearMap.mkContinuous
    { toFun a := ⟨fun z ↦ a z • w₀ z, a.continuous.smul w₀.continuous⟩
      map_add' a₁ a₂ := by ext z : 1; simp [add_smul]
      map_smul' c a := by ext z : 1; simp [mul_smul] }
    ‖w₀‖ fun a ↦ (ContinuousMap.norm_le _ (by positivity)).2 fun z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk]
      rw [norm_smul, mul_comm]
      gcongr
      · exact w₀.norm_coe_le_norm z
      · exact a.norm_coe_le_norm z

private theorem kernelZeroNumerCLM_apply (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    (a : C(K, ℝ)) (z : K) :
    kernelZeroNumerCLM φ hφ a z = a z • ((‖φ z - q₀‖ ^ 4)⁻¹ • star (φ z - q₀)) := rfl

/-- Linear-in-`h` numerator operator `a ↦ (h ↦ (z ↦ -(a z * (‖φ z - q₀‖⁴)⁻¹) • star h))`. -/
private noncomputable def kernelDispNumerCLM (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    C(K, ℝ) →L[ℝ] ℍ →L[ℝ] C(K, ℍ) :=
  let d4 := invNormSubPowFourMap φ hφ
  let innerCLM (a : C(K, ℝ)) : ℍ →L[ℝ] C(K, ℍ) :=
    LinearMap.mkContinuous
      { toFun h := ⟨fun z ↦ -(a z * d4 z) • star h,
          ((a.continuous.mul d4.continuous).neg).smul continuous_const⟩
        map_add' h₁ h₂ := by ext z : 1; simp [smul_add]
        map_smul' c h := by ext z : 1; simp [smul_comm _ c] }
      (‖d4‖ * ‖a‖) fun h ↦ (ContinuousMap.norm_le _ (by positivity)).2 fun z ↦ by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk]
        rw [norm_smul, norm_neg, norm_mul, _root_.norm_star]
        calc ‖a z‖ * ‖d4 z‖ * ‖h‖
          _ ≤ ‖a‖ * ‖d4‖ * ‖h‖ := by
              gcongr
              · exact a.norm_coe_le_norm z
              · exact d4.norm_coe_le_norm z
          _ = ‖d4‖ * ‖a‖ * ‖h‖ := by ring
  LinearMap.mkContinuous
    { toFun := innerCLM
      map_add' a₁ a₂ := by ext h z : 2; simp [innerCLM, add_mul, add_smul]; abel
      map_smul' c a := by ext h z : 2; simp [innerCLM, mul_smul] }
    ‖d4‖ fun a ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, innerCLM]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

private theorem kernelDispNumerCLM_apply (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀)
    (a : C(K, ℝ)) (h : ℍ) (z : K) :
    kernelDispNumerCLM φ hφ a h z = -((a z * (‖φ z - q₀‖ ^ 4)⁻¹) • star h) := by
  simp [kernelDispNumerCLM, invNormSubPowFourMap, neg_smul]

/-- The formal multilinear series in `C(K, ℍ)` of `q ↦ cauchyFueterKernel (φ ·) q` centered at a
point `q₀` avoided by `φ`. It depends only on `(φ, q₀)` and not on any distance bound `δ`. -/
noncomputable def cauchyFueterKernelSeries (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) :
    FormalMultilinearSeries ℝ ℍ C(K, ℍ) :=
  (kernelZeroNumerCLM φ hφ).compFormalMultilinearSeries (kernelScalarFactorSeries φ hφ) +
    ((kernelDispNumerCLM φ hφ).compFormalMultilinearSeries
      (kernelScalarFactorSeries φ hφ)).unshift 0

private theorem inverse_one_sub_sq_apply {a : C(K, ℝ)} (ha : ‖a‖ < 1) (z : K) :
    ((1 - a)⁻¹ʳ ^ 2) z = ((1 - a z) ^ 2)⁻¹ := by
  have hmul : (1 - a) * (1 - a)⁻¹ʳ = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_sub_of_norm_lt_one ha)
  have hz : (1 - a z) * ((1 - a)⁻¹ʳ z) = 1 := by
    simpa using congrArg (fun f : C(K, ℝ) ↦ f z) hmul
  rw [ContinuousMap.pow_apply, eq_inv_of_mul_eq_one_right hz, inv_pow]

/-- Quantitative uniform power-series expansion of `cauchyFueterKernel` along a compact boundary
map `φ : C(K, ℍ)`: if `‖φ z - q₀‖ ≥ δ > 0` for all `z : K`, then `cauchyFueterKernelSeries φ hφ`
represents `q ↦ ContinuousMap.mkD (fun z ↦ cauchyFueterKernel (φ z) q) 0` on the entire open ball
of radius `(√2 - 1) δ` around `q₀`. -/
theorem hasFPowerSeriesOnBall_cauchyFueterKernel_mkD (φ : C(K, ℍ)) {q₀ : ℍ}
    (hφ : ∀ z, φ z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) :
    HasFPowerSeriesOnBall
      (fun q ↦ ContinuousMap.mkD (fun z ↦ cauchyFueterKernel (φ z) q) 0)
      (cauchyFueterKernelSeries φ hφ) q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  have hS := hasFPowerSeriesOnBall_kernelScalarFactor φ hφ hδ₀ hδ
  have hA := (kernelZeroNumerCLM φ hφ).comp_hasFPowerSeriesOnBall hS
  have hB := ((kernelDispNumerCLM φ hφ).comp_hasFPowerSeriesOnBall hS).unshift (z := 0)
  have hsum := (hA.add hB).comp_sub q₀
  rw [zero_add] at hsum
  refine hsum.congr fun q hq ↦ ?_
  set h : ℍ := q - q₀
  have hh_lt : ‖h‖ < (Real.sqrt 2 - 1) * δ := by
    rw [Metric.mem_eball, edist_dist, dist_eq_norm,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos sqrt_two_sub_one_pos hδ₀)] at hq
    exact hq
  have hu_norm : ‖kernelPerturbMap φ hφ h‖ < 1 := by
    refine (ContinuousMap.norm_lt_iff _ zero_lt_one).2 fun z ↦ ?_
    rw [kernelPerturbMap_apply, Real.norm_eq_abs]
    exact (abs_two_mul_inner_sub_norm_sq_div_le hδ₀ (hδ z)).trans_lt
      (two_mul_add_sq_lt_one (by positivity) ((div_lt_iff₀ hδ₀).2 hh_lt))
  set Fq : C(K, ℍ) :=
    ((kernelZeroNumerCLM φ hφ ∘ fun x ↦ (1 - kernelPerturbMap φ hφ x)⁻¹ʳ ^ 2) +
      fun y ↦ 0 + (kernelDispNumerCLM φ hφ ∘ fun x ↦ (1 - kernelPerturbMap φ hφ x)⁻¹ʳ ^ 2)
        y (y - 0)) h
  have hFq_eq : (fun z ↦ cauchyFueterKernel (φ z) q) = ⇑Fq := by
    funext z
    have hq_eq : q = q₀ + h := (add_sub_cancel q₀ q).symm
    rw [hq_eq, cauchyFueterKernel_add_eq (hφ z) h]
    simp only [Fq, Pi.add_apply, Function.comp_apply, zero_add, sub_zero,
      ContinuousMap.add_apply, kernelZeroNumerCLM_apply, kernelDispNumerCLM_apply,
      inverse_one_sub_sq_apply hu_norm z, kernelPerturbMap_apply, smul_smul, smul_sub]
    abel
  rw [hFq_eq]
  exact (ContinuousMap.mkD_of_continuous Fq.continuous).symm

omit [CompactSpace K] in
/-- On every ball `‖q - q₀‖ < (√2 - 1) δ` with `‖φ z - q₀‖ ≥ δ > 0`,
`z ↦ cauchyFueterKernel (φ z) q` is continuous on `K`. -/
private theorem continuous_cauchyFueterKernel_of_mem_eball (φ : C(K, ℍ)) {q₀ q : ℍ}
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ : ∀ z, δ ≤ ‖φ z - q₀‖)
    (hq : q ∈ eball q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ))) :
    Continuous fun z ↦ cauchyFueterKernel (φ z) q := by
  have hlt : ‖q - q₀‖ < δ := by
    have h1 : ‖q - q₀‖ < (Real.sqrt 2 - 1) * δ := by
      rw [Metric.mem_eball, edist_dist, dist_eq_norm,
        ENNReal.ofReal_lt_ofReal_iff (mul_pos sqrt_two_sub_one_pos hδ₀)] at hq
      exact hq
    nlinarith [sqrt_two_sub_one_lt_one]
  have hne : ∀ z, φ z ≠ q := by
    intro z heq
    have hle := hδ z
    rw [heq] at hle
    linarith
  have hcomp : (fun z ↦ cauchyFueterKernel (φ z) q) =
      (fun p : ℍ × ℍ ↦ cauchyFueterKernel p.1 p.2) ∘ fun z ↦ (φ z, q) := rfl
  rw [hcomp]
  refine ContinuousOn.comp_continuous (s := {p : ℍ × ℍ | p.1 ≠ p.2}) ?_
    (φ.continuous.prodMk continuous_const) fun z ↦ hne z
  exact analyticOnNhd_cauchyFueterKernel_uncurry.continuousOn

private theorem exists_pos_le_norm_sub_of_notMem_range {φ : C(K, ℍ)} {q₀ : ℍ}
    (hq₀ : q₀ ∉ range φ) : ∃ δ > 0, ∀ z, δ ≤ ‖φ z - q₀‖ := by
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨1, zero_lt_one, isEmptyElim⟩
  · obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      ((φ.continuous.sub continuous_const).norm.continuousOn)
    refine ⟨‖φ z₀ - q₀‖, norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ hq₀ ⟨z₀, h⟩), fun z ↦ hz₀ trivial⟩

/-- Uniform `C(K, ℍ)` analyticity of `q ↦ cauchyFueterKernel (φ ·) q` at every point
`q₀ ∉ range φ`. -/
theorem analyticAt_cauchyFueterKernel_mkD (φ : C(K, ℍ)) {q₀ : ℍ} (hq₀ : q₀ ∉ range φ) :
    AnalyticAt ℝ (fun q ↦ ContinuousMap.mkD (fun z ↦ cauchyFueterKernel (φ z) q) 0) q₀ := by
  obtain ⟨δ, hδ₀, hδ⟩ := exists_pos_le_norm_sub_of_notMem_range hq₀
  exact (hasFPowerSeriesOnBall_cauchyFueterKernel_mkD φ (fun z hz ↦ hq₀ ⟨z, hz⟩)
    hδ₀ hδ).analyticAt

end UniformKernelSeries

/-! ### Left and right Cauchy–Fueter boundary potential integrals -/

section BoundaryPotentials

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K] {μ : Measure K}

/-- Quantitative power-series expansion on `eball q₀ ((√2 - 1) δ)` of a left Cauchy–Fueter
boundary integral `q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ`. -/
theorem hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul
    (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) {g : K → ℍ} (hg : Integrable g μ) :
    HasFPowerSeriesOnBall (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ)
      (((ContinuousLinearMap.mul ℝ ℍ).continuousMapIntegralCLM
        hg).compFormalMultilinearSeries (cauchyFueterKernelSeries φ hφ))
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  refine ((hasFPowerSeriesOnBall_cauchyFueterKernel_mkD φ hφ hδ₀
    hδ).integral_mul_of_integrable_right hg).congr fun q hq ↦ ?_
  have hcont := continuous_cauchyFueterKernel_of_mem_eball φ hδ₀ hδ hq
  simp_rw [ContinuousMap.mkD_apply_of_continuous hcont]

/-- Quantitative power-series expansion on `eball q₀ ((√2 - 1) δ)` of a right Cauchy–Fueter
boundary integral `q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ`. -/
theorem hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel
    (φ : C(K, ℍ)) {q₀ : ℍ} (hφ : ∀ z, φ z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ z, δ ≤ ‖φ z - q₀‖) {g : K → ℍ} (hg : Integrable g μ) :
    HasFPowerSeriesOnBall (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ)
      (((ContinuousLinearMap.mul ℝ ℍ).flip.continuousMapIntegralCLM
        hg).compFormalMultilinearSeries (cauchyFueterKernelSeries φ hφ))
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) := by
  refine ((hasFPowerSeriesOnBall_cauchyFueterKernel_mkD φ hφ hδ₀
    hδ).integral_mul_of_integrable_left hg).congr fun q hq ↦ ?_
  have hcont := continuous_cauchyFueterKernel_of_mem_eball φ hδ₀ hδ hq
  simp_rw [ContinuousMap.mkD_apply_of_continuous hcont]

/-- A left Cauchy–Fueter boundary integral is real analytic at every point outside `range φ`. -/
theorem analyticAt_integral_cauchyFueterKernel_mul
    (φ : C(K, ℍ)) {q₀ : ℍ} (hq₀ : q₀ ∉ range φ) {g : K → ℍ} (hg : Integrable g μ) :
    AnalyticAt ℝ (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀ := by
  obtain ⟨δ, hδ₀, hδ⟩ := exists_pos_le_norm_sub_of_notMem_range hq₀
  exact (hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul φ
    (fun z hz ↦ hq₀ ⟨z, hz⟩) hδ₀ hδ hg).analyticAt

/-- A right Cauchy–Fueter boundary integral is real analytic at every point outside `range φ`. -/
theorem analyticAt_integral_mul_cauchyFueterKernel
    (φ : C(K, ℍ)) {q₀ : ℍ} (hq₀ : q₀ ∉ range φ) {g : K → ℍ} (hg : Integrable g μ) :
    AnalyticAt ℝ (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀ := by
  obtain ⟨δ, hδ₀, hδ⟩ := exists_pos_le_norm_sub_of_notMem_range hq₀
  exact (hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel φ
    (fun z hz ↦ hq₀ ⟨z, hz⟩) hδ₀ hδ hg).analyticAt

/-- A left Cauchy–Fueter boundary integral is real analytic on `(range φ)ᶜ`. -/
theorem analyticOnNhd_integral_cauchyFueterKernel_mul
    (φ : C(K, ℍ)) {g : K → ℍ} (hg : Integrable g μ) :
    AnalyticOnNhd ℝ (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) (range φ)ᶜ :=
  fun _ hq₀ ↦ analyticAt_integral_cauchyFueterKernel_mul φ hq₀ hg

/-- A right Cauchy–Fueter boundary integral is real analytic on `(range φ)ᶜ`. -/
theorem analyticOnNhd_integral_mul_cauchyFueterKernel
    (φ : C(K, ℍ)) {g : K → ℍ} (hg : Integrable g μ) :
    AnalyticOnNhd ℝ (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) (range φ)ᶜ :=
  fun _ hq₀ ↦ analyticAt_integral_mul_cauchyFueterKernel φ hq₀ hg

/-- A left Cauchy–Fueter boundary integral is `C^n` (in particular `C^∞`) on `(range φ)ᶜ`. -/
theorem contDiffOn_integral_cauchyFueterKernel_mul
    (φ : C(K, ℍ)) {g : K → ℍ} (hg : Integrable g μ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) (range φ)ᶜ :=
  (analyticOnNhd_integral_cauchyFueterKernel_mul φ hg).contDiffOn_of_completeSpace

/-- A right Cauchy–Fueter boundary integral is `C^n` (in particular `C^∞`) on `(range φ)ᶜ`. -/
theorem contDiffOn_integral_mul_cauchyFueterKernel
    (φ : C(K, ℍ)) {g : K → ℍ} (hg : Integrable g μ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) (range φ)ᶜ :=
  (analyticOnNhd_integral_mul_cauchyFueterKernel φ hg).contDiffOn_of_completeSpace

end BoundaryPotentials

/-! ### Finite sums of compact face potentials -/

section FiniteFaceSums

variable {ι : Type*} {K : ι → Type*}
  [∀ i, TopologicalSpace (K i)] [∀ i, CompactSpace (K i)]
  [∀ i, MeasurableSpace (K i)] [∀ i, OpensMeasurableSpace (K i)]

/-- Quantitative power-series expansion on `eball q₀ ((√2 - 1) δ)` of a finite sum of left
Cauchy–Fueter face integrals whose faces all lie at distance at least `δ > 0` from `q₀`. -/
theorem hasFPowerSeriesOnBall_sum_integral_cauchyFueterKernel_mul
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {q₀ : ℍ} (hφ : ∀ i ∈ I, ∀ z, φ i z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ i ∈ I, ∀ z, δ ≤ ‖φ i z - q₀‖)
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) :
    HasFPowerSeriesOnBall
      (fun q ↦ ∑ i ∈ I, ∫ z, cauchyFueterKernel (φ i z) q * g i z ∂μ i)
      (∑ i ∈ I.attach, ((ContinuousLinearMap.mul ℝ ℍ).continuousMapIntegralCLM
        (hg i.1 i.2)).compFormalMultilinearSeries
          (cauchyFueterKernelSeries (φ i.1) (hφ i.1 i.2)))
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) :=
  (I.attach.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos sqrt_two_sub_one_pos hδ₀))
    fun i _ ↦ hasFPowerSeriesOnBall_integral_cauchyFueterKernel_mul
      (φ i.1) (hφ i.1 i.2) hδ₀ (hδ i.1 i.2) (hg i.1 i.2)).congr fun q _ ↦
    I.sum_attach fun i ↦ ∫ z, cauchyFueterKernel (φ i z) q * g i z ∂μ i

/-- Quantitative power-series expansion on `eball q₀ ((√2 - 1) δ)` of a finite sum of right
Cauchy–Fueter face integrals whose faces all lie at distance at least `δ > 0` from `q₀`. -/
theorem hasFPowerSeriesOnBall_sum_integral_mul_cauchyFueterKernel
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {q₀ : ℍ} (hφ : ∀ i ∈ I, ∀ z, φ i z ≠ q₀) {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ i ∈ I, ∀ z, δ ≤ ‖φ i z - q₀‖)
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) :
    HasFPowerSeriesOnBall
      (fun q ↦ ∑ i ∈ I, ∫ z, g i z * cauchyFueterKernel (φ i z) q ∂μ i)
      (∑ i ∈ I.attach, ((ContinuousLinearMap.mul ℝ ℍ).flip.continuousMapIntegralCLM
        (hg i.1 i.2)).compFormalMultilinearSeries
          (cauchyFueterKernelSeries (φ i.1) (hφ i.1 i.2)))
      q₀ (ENNReal.ofReal ((Real.sqrt 2 - 1) * δ)) :=
  (I.attach.hasFPowerSeriesOnBall_fun_sum
    (ENNReal.ofReal_pos.2 (mul_pos sqrt_two_sub_one_pos hδ₀))
    fun i _ ↦ hasFPowerSeriesOnBall_integral_mul_cauchyFueterKernel
      (φ i.1) (hφ i.1 i.2) hδ₀ (hδ i.1 i.2) (hg i.1 i.2)).congr fun q _ ↦
    I.sum_attach fun i ↦ ∫ z, g i z * cauchyFueterKernel (φ i z) q ∂μ i

/-- A finite sum of left Cauchy–Fueter face potentials is real analytic at every point outside
the union of the face images. -/
theorem analyticAt_sum_integral_cauchyFueterKernel_mul
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {q₀ : ℍ} (hq₀ : q₀ ∉ ⋃ i ∈ I, range (φ i))
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) :
    AnalyticAt ℝ (fun q ↦ ∑ i ∈ I, ∫ z, cauchyFueterKernel (φ i z) q * g i z ∂μ i) q₀ :=
  I.analyticAt_fun_sum fun i hi ↦
    analyticAt_integral_cauchyFueterKernel_mul (φ i) (fun h ↦ hq₀ (mem_biUnion hi h)) (hg i hi)

/-- A finite sum of right Cauchy–Fueter face potentials is real analytic at every point outside
the union of the face images. -/
theorem analyticAt_sum_integral_mul_cauchyFueterKernel
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {q₀ : ℍ} (hq₀ : q₀ ∉ ⋃ i ∈ I, range (φ i))
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) :
    AnalyticAt ℝ (fun q ↦ ∑ i ∈ I, ∫ z, g i z * cauchyFueterKernel (φ i z) q ∂μ i) q₀ :=
  I.analyticAt_fun_sum fun i hi ↦
    analyticAt_integral_mul_cauchyFueterKernel (φ i) (fun h ↦ hq₀ (mem_biUnion hi h)) (hg i hi)

/-- A finite sum of left Cauchy–Fueter face potentials is real analytic away from the union of
the face images. -/
theorem analyticOnNhd_sum_integral_cauchyFueterKernel_mul
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) :
    AnalyticOnNhd ℝ (fun q ↦ ∑ i ∈ I, ∫ z, cauchyFueterKernel (φ i z) q * g i z ∂μ i)
      (⋃ i ∈ I, range (φ i))ᶜ :=
  fun _ hq₀ ↦ analyticAt_sum_integral_cauchyFueterKernel_mul I φ μ hq₀ hg

/-- A finite sum of right Cauchy–Fueter face potentials is real analytic away from the union of
the face images. -/
theorem analyticOnNhd_sum_integral_mul_cauchyFueterKernel
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) :
    AnalyticOnNhd ℝ (fun q ↦ ∑ i ∈ I, ∫ z, g i z * cauchyFueterKernel (φ i z) q ∂μ i)
      (⋃ i ∈ I, range (φ i))ᶜ :=
  fun _ hq₀ ↦ analyticAt_sum_integral_mul_cauchyFueterKernel I φ μ hq₀ hg

/-- A finite sum of left Cauchy–Fueter face potentials is `C^n` (in particular `C^∞`) away from
the union of the face images. -/
theorem contDiffOn_sum_integral_cauchyFueterKernel_mul
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun q ↦ ∑ i ∈ I, ∫ z, cauchyFueterKernel (φ i z) q * g i z ∂μ i)
      (⋃ i ∈ I, range (φ i))ᶜ :=
  (analyticOnNhd_sum_integral_cauchyFueterKernel_mul I φ μ hg).contDiffOn_of_completeSpace

/-- A finite sum of right Cauchy–Fueter face potentials is `C^n` (in particular `C^∞`) away from
the union of the face images. -/
theorem contDiffOn_sum_integral_mul_cauchyFueterKernel
    (I : Finset ι) (φ : ∀ i, C(K i, ℍ)) (μ : ∀ i, Measure (K i))
    {g : ∀ i, K i → ℍ} (hg : ∀ i ∈ I, Integrable (g i) (μ i)) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun q ↦ ∑ i ∈ I, ∫ z, g i z * cauchyFueterKernel (φ i z) q ∂μ i)
      (⋃ i ∈ I, range (φ i))ᶜ :=
  (analyticOnNhd_sum_integral_mul_cauchyFueterKernel I φ μ hg).contDiffOn_of_completeSpace

end FiniteFaceSums

end TauCeti
