/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.PlaneShear
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Shears of the plane and the Sobolev space `H¹`

For `g : ℝ → ℝ` of temperate growth, precomposition with the shear `φ(x, y) = (x, y + g x)` of the
plane maps Schwartz functions to Schwartz functions (`TauCeti.compPlaneShearCLM`). Since the shear
preserves Lebesgue measure, precomposition with it preserves the `H^{0,p} = Lᵖ` norm of Schwartz
functions (`TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`).

It nevertheless admits no bound for the `H¹` norm on Schwartz functions as soon as
`|g'(x)| → ∞` as `x → ∞`
(`TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le`), for instance for
the cubic shear `(x, y) ↦ (x, y + x³)`
(`TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_cube_le`). Indeed
`∂ₓ (f ∘ φ) = (∂ₓ f) ∘ φ + g'(x) (∂_y f) ∘ φ`, and translating a fixed bump function `f` far out
in the `x` direction does not change its `H¹` norm, while the second term grows like `g'(x)` on
its support. So a bound on the Jacobian determinant alone does not control Sobolev norms of order
one: changes of variables of `H^s` require bounds on the derivatives of the map, as in
`TemperedDistribution.comp_mem_realSobolevFunctions_natCast`.

## Main declarations

* `TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`: precomposition with the shear
  preserves the `H^{0,p}` norm of Schwartz functions.
* `TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le`: on Schwartz
  functions, precomposition with the shear admits no `H¹` norm bound when `|g'| → ∞` at `+∞`, in
  particular for the cubic shear
  (`TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_cube_le`).

The `H¹` norm is computed from first derivatives by
`SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap LineDeriv Real ContDiff

namespace TauCeti

variable {g : ℝ → ℝ}

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The shear term of the derivative.** For a Schwartz function `u`, the squared `L²` norm
`∫ ‖∂ₓ (u ∘ φ)‖²` is at least `(1 / 2) ∫ g'(x)² ‖∂_y u‖² - ∫ ‖∂ₓ u‖²`. -/
private theorem half_integral_sub_le_integral_norm_lineDerivOp_compPlaneShearCLM_sq
    (hg : g.HasTemperateGrowth) (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) :
    (1 / 2) * (∫ q, deriv g (q 0) ^ 2 * ‖∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q‖ ^ 2) -
        ∫ q, ‖∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} u q‖ ^ 2 ≤
      ∫ p, ‖∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} (compPlaneShearCLM ℂ g hg u) p‖ ^ 2 := by
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hφ := measurePreserving_planeShear hg.1.continuous.measurable
  have hemb := measurableEmbedding_planeShear hg.1.continuous.measurable
  have hint (w : 𝓢(EuclideanSpace ℝ (Fin 2), F)) : Integrable (fun q ↦ ‖w q‖ ^ 2) :=
    (w.memLp 2).integrable_norm_pow two_ne_zero
  -- Transport `∫ ‖(∂ₓ u) ∘ φ‖²` and the weighted integral back along `φ`.
  have ha : ∫ p, ‖∂_{e₀} u (planeShear g p)‖ ^ 2 = ∫ q, ‖∂_{e₀} u q‖ ^ 2 :=
    hφ.integral_comp hemb fun q ↦ ‖∂_{e₀} u q‖ ^ 2
  have hb : ∫ p, ‖deriv g (p 0) • ∂_{e₁} u (planeShear g p)‖ ^ 2 =
      ∫ q, deriv g (q 0) ^ 2 * ‖∂_{e₁} u q‖ ^ 2 := by
    rw [← hφ.integral_comp hemb fun q ↦ deriv g (q 0) ^ 2 * ‖∂_{e₁} u q‖ ^ 2]
    simp [norm_smul, mul_pow]
  have hia : Integrable (fun p ↦ ‖∂_{e₀} u (planeShear g p)‖ ^ 2) :=
    (hφ.integrable_comp_emb hemb).2 (hint _)
  -- Pointwise, `‖b‖² ≤ 2 ‖a + b‖² + 2 ‖a‖²`.
  have hle : ∫ p, ‖deriv g (p 0) • ∂_{e₁} u (planeShear g p)‖ ^ 2 ≤
      ∫ p, (2 * ‖∂_{e₀} (compPlaneShearCLM ℂ g hg u) p‖ ^ 2 +
        2 * ‖∂_{e₀} u (planeShear g p)‖ ^ 2) := by
    refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
      (((hint _).const_mul 2).add (hia.const_mul 2)) (.of_forall fun p ↦ ?_)
    have hd : ∂_{e₀} (compPlaneShearCLM ℂ g hg u) p =
        ∂_{e₀} u (planeShear g p) + deriv g (p 0) • ∂_{e₁} u (planeShear g p) := by
      simpa [e₀] using lineDerivOp_compPlaneShearCLM_apply hg u e₀ p
    dsimp only
    rw [hd]
    set a := ∂_{e₀} u (planeShear g p)
    set b := deriv g (p 0) • ∂_{e₁} u (planeShear g p)
    have htri : ‖b‖ ≤ ‖a + b‖ + ‖a‖ := by simpa using norm_sub_le (a + b) a
    have hsq := pow_le_pow_left₀ (norm_nonneg b) htri 2
    nlinarith [sq_nonneg (‖a + b‖ - ‖a‖)]
  rw [integral_add ((hint _).const_mul 2) (hia.const_mul 2), integral_const_mul,
    integral_const_mul, hb, ha] at hle
  linarith

/-- **The shear term for a translate.** Let `u` be a Schwartz function such that `∂_y u` is
compactly supported in the strip `|x| ≤ 1`, and let `M ≤ |g'|` on `[t - 1, ∞)`. Then for the
translate `u_t = u (· - t e₀)`, `∫ ‖∂ₓ (u_t ∘ φ)‖² ≥ (1 / 2) M² ∫ ‖∂_y u‖² - ∫ ‖∂ₓ u‖²`. -/
private theorem half_mul_sub_le_integral_norm_lineDerivOp_compPlaneShearCLM_compSubConstCLM_sq
    (hg : g.HasTemperateGrowth) {u : 𝓢(EuclideanSpace ℝ (Fin 2), F)}
    (hcs : HasCompactSupport (fun q ↦ ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q))
    (hsupp : ∀ q, ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q ≠ 0 → |q 0| ≤ 1)
    {M t : ℝ} (hM : 0 ≤ M) (ht : ∀ s, t - 1 ≤ s → M ≤ |deriv g s|) :
    (1 / 2) * (M ^ 2 * ∫ q, ‖∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q‖ ^ 2) -
        ∫ q, ‖∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} u q‖ ^ 2 ≤
      ∫ p, ‖∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} (compPlaneShearCLM ℂ g hg
        (u.compSubConstCLM ℂ (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))) p‖ ^ 2 := by
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have key := half_integral_sub_le_integral_norm_lineDerivOp_compPlaneShearCLM_sq hg
    (u.compSubConstCLM ℂ (t • e₀))
  -- Translating back, the weight `g'(x)²` is shifted by `t`, and `∫ ‖∂ₓ u_t‖² = ∫ ‖∂ₓ u‖²`.
  have hweight : ∫ q, deriv g (q 0) ^ 2 * ‖∂_{e₁} (u.compSubConstCLM ℂ (t • e₀)) q‖ ^ 2 =
      ∫ q, deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u q‖ ^ 2 := by
    simp only [SchwartzMap.lineDerivOp_compSubConstCLM, SchwartzMap.compSubConstCLM_apply]
    rw [← integral_sub_right_eq_self (fun q ↦ deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u q‖ ^ 2) (t • e₀)]
    simp [e₀]
  have hB : ∫ q, ‖∂_{e₀} (u.compSubConstCLM ℂ (t • e₀)) q‖ ^ 2 = ∫ q, ‖∂_{e₀} u q‖ ^ 2 := by
    simp only [SchwartzMap.lineDerivOp_compSubConstCLM, SchwartzMap.compSubConstCLM_apply,
      integral_sub_right_eq_self (fun q ↦ ‖∂_{e₀} u q‖ ^ 2) (t • e₀)]
  rw [hweight, hB] at key
  -- Far out, `|g'| ≥ M` on the support of `∂_y u`.
  have hw : M ^ 2 * ∫ q, ‖∂_{e₁} u q‖ ^ 2 ≤ ∫ q, deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u q‖ ^ 2 := by
    rw [← integral_const_mul]
    have hcont : Continuous fun q : EuclideanSpace ℝ (Fin 2) ↦
        deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u q‖ ^ 2 :=
      (((hg.1.continuous_deriv (by simp)).comp
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.add_const t)).pow 2).mul
        ((∂_{e₁} u).continuous.norm.pow 2)
    refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
      (hcont.integrable_of_hasCompactSupport
        (hcs.comp_left (g := fun z : F ↦ ‖z‖ ^ 2) (by simp)).mul_left) (.of_forall fun q ↦ ?_)
    by_cases hq : ∂_{e₁} u q = 0
    · simp [hq]
    · have h1 := ht (q 0 + t) (by linarith [(abs_le.1 (hsupp q hq)).1])
      have h2 : M ^ 2 ≤ deriv g (q 0 + t) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ hM h1 2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

end NormedSpace

/-- **The shear preserves the `H^{0,p} = Lᵖ` norm** of Schwartz functions. -/
@[simp]
theorem norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (hg : g.HasTemperateGrowth) {p : ENNReal} [Fact (1 ≤ p)]
    (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM 0 p (compPlaneShearCLM ℂ g hg u)‖ =
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 p u‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.norm_toLp_eq,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero, SchwartzMap.norm_toLp,
    SchwartzMap.norm_toLp, coe_compPlaneShearCLM, eLpNorm_comp_measurePreserving
      u.continuous.aestronglyMeasurable (measurePreserving_planeShear hg.1.continuous.measurable)]

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A Schwartz function whose derivative in the `y` direction is compactly supported in the strip
`|x| ≤ 1` and does not vanish identically. -/
private theorem exists_lineDerivOp_single_one_ne_zero [Nontrivial F] :
    ∃ u : 𝓢(EuclideanSpace ℝ (Fin 2), F),
      HasCompactSupport (fun q ↦ ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q) ∧
      (∀ q, ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q ≠ 0 → |q 0| ≤ 1) ∧
      ∃ q, ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q ≠ 0 := by
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  -- A smooth bump function on the unit disc, times `v`.
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hc : HasCompactSupport (fun x ↦ f x • v) := f.hasCompactSupport.smul_right
  have hs : ContDiff ℝ ∞ (fun x ↦ f x • v) := f.contDiff.smul contDiff_const
  let u := hc.toSchwartzMap hs
  have hfun : ⇑u = fun x ↦ f x • v := funext (HasCompactSupport.toSchwartzMap_toFun hc hs)
  have hder (q) : ∂_{e₁} u q = fderiv ℝ (fun x ↦ f x • v) q e₁ := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun]
  refine ⟨u, ?_, fun q hq ↦ ?_, ?_⟩
  · simp only [hder]
    exact (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ L e₁) rfl
  · rw [hder] at hq
    have hq' : q ∈ Function.support (fderiv ℝ (fun x ↦ f x • v)) := fun h ↦ hq (by simp [h])
    have hts := tsupport_smul_subset_left (fun x ↦ f x) (fun _ ↦ v) (support_fderiv_subset ℝ hq')
    rw [f.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hts
    exact (PiLp.norm_apply_le q 0).trans hts
  · -- Otherwise `s ↦ u (s • e₁)` would be constant, but it is `v` at `0` and `0` at `2 e₁`.
    by_contra! h
    have hderiv (s : ℝ) : HasDerivAt (fun s : ℝ ↦ u (s • e₁)) (∂_{e₁} u (s • e₁)) s := by
      convert (u.differentiableAt (x := s • e₁)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).smul_const e₁) using 1
      · exact (Function.comp_def _ _).symm
      · rw [one_smul, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hderiv s).differentiableAt)
      (fun s ↦ (hderiv s).deriv.trans (h _)) 0 2
    have h0 : f 0 = 1 := f.one_of_mem_closedBall (by simp [f])
    have h2 : f ((2 : ℝ) • e₁) = 0 := f.zero_of_le_dist (by simp [f, e₁, norm_smul])
    exact hv (by simpa [hfun, h0, h2] using hconst)

variable [CompleteSpace F] [Nontrivial F]

/-- **The shear admits no `H¹` norm bound** when `|g'(x)| → ∞` as `x → ∞`: no constant `C`
satisfies `‖u ∘ φ‖_{H¹} ≤ C ‖u‖_{H¹}` for all Schwartz functions `u`, although precomposition with
the shear preserves the `L²` norm of Schwartz functions
(`TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`). -/
theorem not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le
    (hg : g.HasTemperateGrowth) (hg' : Tendsto (fun x ↦ |deriv g x|) atTop atTop) :
    ¬ ∃ C, ∀ u : 𝓢(EuclideanSpace ℝ (Fin 2), F),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 (compPlaneShearCLM ℂ g hg u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 u‖ := by
  -- Test the bound on the translates `u_t = u₀(· - t e₀)` of a bump function: their `H¹` norm is
  -- constant, while `‖u_t ∘ φ‖_{H¹}² ≥ (2π)⁻² ‖∂ₓ (u_t ∘ φ)‖²_{L²} ≥ (2π)⁻² (M² A / 2 - B)`
  -- whenever `|g'| ≥ M` on `[t - 1, ∞)`, with `A = ‖∂_y u₀‖²_{L²} > 0` and `B = ‖∂ₓ u₀‖²_{L²}`.
  rintro ⟨C, hC⟩
  obtain ⟨u₀, hcs, hsupp, q₀, hq₀⟩ := exists_lineDerivOp_single_one_ne_zero (F := F)
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  set A := ∫ q, ‖∂_{e₁} u₀ q‖ ^ 2
  set B := ∫ q, ‖∂_{e₀} u₀ q‖ ^ 2
  set N := ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 u₀‖
  set c : ℝ := (2 * π)⁻¹ ^ 2
  have hc : 0 < c := by positivity
  have hA : 0 < A := by
    have hcont : Continuous fun q ↦ ‖∂_{e₁} u₀ q‖ ^ 2 := by fun_prop
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (hcs.comp_left (g := fun z : F ↦ ‖z‖ ^ 2) (by simp)) (fun _ ↦ sq_nonneg _)
      (by simpa using hq₀)
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ by positivity
  -- The `H¹` norm of `u_t ∘ φ` bounds the `L²` norm of its `x`-derivative, uniformly in `t`.
  have hlow (t : ℝ) :
      c * ∫ p, ‖∂_{e₀} (compPlaneShearCLM ℂ g hg (u₀.compSubConstCLM ℂ (t • e₀))) p‖ ^ 2 ≤
        (C * N) ^ 2 := by
    have h := SchwartzMap.inv_two_pi_sq_mul_integral_norm_lineDerivOp_sq_le
      (EuclideanSpace.basisFun (Fin 2) ℝ)
      (compPlaneShearCLM ℂ g hg (u₀.compSubConstCLM ℂ (t • e₀))) 0
    rw [EuclideanSpace.basisFun_apply] at h
    refine h.trans (pow_le_pow_left₀ (norm_nonneg _) ((hC _).trans_eq ?_) 2)
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_compSubConstCLM]
  -- Choose `M` with `c (M² A / 2 - B) > (C N)²`, and `t` far enough out.
  set M : ℝ := 2 * ((C * N) ^ 2 / c + B) / A + 1
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 2 * ((C * N) ^ 2 / c + B) / A := by positivity
    linarith
  obtain ⟨S, hS⟩ := eventually_atTop.1 (hg'.eventually_ge_atTop M)
  have key := half_mul_sub_le_integral_norm_lineDerivOp_compPlaneShearCLM_compSubConstCLM_sq hg
    hcs hsupp (t := S + 1) (by linarith) fun s hs ↦ hS s (by linarith)
  have hlt := hlow (S + 1)
  have hMA : M * A = 2 * ((C * N) ^ 2 / c + B) + A := by
    simp only [M]; field_simp
  have hM2 : M * A ≤ M ^ 2 * A := mul_le_mul_of_nonneg_right (by nlinarith) hA.le
  have hcCN : c * ((C * N) ^ 2 / c) = (C * N) ^ 2 := by field_simp
  nlinarith

/-- **The cubic shear `(x, y) ↦ (x, y + x³)` admits no `H¹` norm bound** on Schwartz functions,
although precomposition with it preserves their `L²` norm
(`TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`): its derivative `3x²` is
unbounded. -/
theorem not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_cube_le :
    ¬ ∃ C, ∀ u : 𝓢(EuclideanSpace ℝ (Fin 2), F),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 (compPlaneShearCLM ℂ (· ^ 3) (by fun_prop) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 u‖ := by
  refine not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le _ ?_
  have h : (fun x : ℝ ↦ |deriv (· ^ 3) x|) = fun x ↦ 3 * x ^ 2 := by
    ext x
    simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * x ^ 2)]
  rw [h]
  exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by norm_num)

end InnerProductSpace

end TauCeti
