/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Shears of the plane and the Sobolev space `H¹`

For a function `g : ℝ → ℝ` the **shear** `(x, y) ↦ (x, y + g x)` of the plane `ℝ²`
(`TauCeti.planeShear`) has inverse the shear along `-g`, and is a homeomorphism when `g` is
continuous (`TauCeti.planeShearHomeomorph`). Where `g` is differentiable its Jacobian determinant is
`1`, and for measurable `g` it preserves Lebesgue measure (`TauCeti.measurePreserving_planeShear`),
so precomposition with it is an isometry of every `Lᵖ`. When `g` has temperate growth,
precomposition maps Schwartz functions to Schwartz functions (`TauCeti.compPlaneShearCLM`), and on
Schwartz functions it is an isometry of `H⁰ = Lᵖ`
(`TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`).

It is nevertheless unbounded for the `H¹` norm as soon as `|g'(x)| → ∞` as `x → ∞`
(`TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le`), for instance for the
cubic shear `(x, y) ↦ (x, y + x³)`
(`TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_cube_le`). Indeed
`∂ₓ (f ∘ φ) = (∂ₓ f) ∘ φ + g'(x) (∂_y f) ∘ φ`, and translating a fixed bump function `f` far out
in the `x` direction does not change its `H¹` norm, while the second term grows like `g'(x)` on
its support. So a bound on the Jacobian determinant alone does not control Sobolev norms of order
one: changes of variables of `H^s` require bounds on the derivatives of the map, as in
`TemperedDistribution.comp_mem_realSobolevFunctions_natCast`.

## Main declarations

* `TauCeti.planeShear g`: the shear `(x, y) ↦ (x, y + g x)`, with inverse `planeShear (-g)`.
* `TauCeti.measurePreserving_planeShear`: the shear preserves Lebesgue measure.
* `TauCeti.compPlaneShearCLM`: precomposition with the shear on Schwartz functions, with the chain
  rule `TauCeti.lineDerivOp_compPlaneShearCLM_apply`.
* `TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`: it is an isometry of `H^{0,p}`.
* `TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le`: it is unbounded for
  the `H¹` norm when `|g'| → ∞` at `+∞`, in particular for the cubic shear
  (`TauCeti.not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_cube_le`).

The `H¹` norm is computed from first derivatives by
`SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap LineDeriv Real ContDiff

namespace TauCeti

/-- The **shear** `(x, y) ↦ (x, y + g x)` of the plane along a function `g : ℝ → ℝ`. -/
def planeShear (g : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  p + g (p 0) • EuclideanSpace.single 1 1

variable {g : ℝ → ℝ}

@[simp]
theorem planeShear_apply_zero (p : EuclideanSpace ℝ (Fin 2)) : planeShear g p 0 = p 0 := by
  simp [planeShear]

@[simp]
theorem planeShear_apply_one (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear g p 1 = p 1 + g (p 0) := by
  simp [planeShear]

@[simp]
theorem planeShear_neg_planeShear (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear (-g) (planeShear g p) = p := by
  ext i; fin_cases i <;> simp

@[simp]
theorem planeShear_planeShear_neg (p : EuclideanSpace ℝ (Fin 2)) :
    planeShear g (planeShear (-g) p) = p := by
  simpa using planeShear_neg_planeShear (g := -g) p

/-- The derivative of the shear: `D φ(p) v = v + g'(p₀) v₀ e₁`. -/
theorem hasFDerivAt_planeShear {p : EuclideanSpace ℝ (Fin 2)} (hg : DifferentiableAt ℝ g (p 0)) :
    HasFDerivAt (planeShear g)
      (ContinuousLinearMap.id ℝ _ +
        (deriv g (p 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight
          (EuclideanSpace.single 1 1)) p :=
  (hasFDerivAt_id p).add ((hg.hasDerivAt.comp_hasFDerivAt p
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt).smul_const _)

theorem continuous_planeShear (hg : Continuous g) : Continuous (planeShear g) := by
  unfold planeShear; fun_prop

/-- The shear along a continuous function, as a homeomorphism of the plane. -/
def planeShearHomeomorph (hg : Continuous g) :
    EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) where
  toFun := planeShear g
  invFun := planeShear (-g)
  left_inv := planeShear_neg_planeShear
  right_inv := planeShear_planeShear_neg
  continuous_toFun := continuous_planeShear hg
  continuous_invFun := continuous_planeShear hg.neg

@[simp]
theorem coe_planeShearHomeomorph (hg : Continuous g) : ⇑(planeShearHomeomorph hg) = planeShear g :=
  (rfl)

@[simp]
theorem coe_planeShearHomeomorph_symm (hg : Continuous g) :
    ⇑(planeShearHomeomorph hg).symm = planeShear (-g) :=
  (rfl)

/-- **The shear preserves Lebesgue measure.** In coordinates `(x, y)` it is the skew product of the
identity with the translations `y ↦ y + g x`. -/
theorem measurePreserving_planeShear (hg : Measurable g) :
    MeasurePreserving (planeShear g) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e := (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  have hσ : MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1, q.2 + g q.1)) :=
    (MeasurePreserving.id volume).skew_product (g := fun x y ↦ y + g x)
      (measurable_snd.add (hg.comp measurable_fst))
      (ae_of_all _ fun x ↦ map_add_right_eq_self volume (g x))
  have h : planeShear g = e.symm ∘ (fun q : ℝ × ℝ ↦ (q.1, q.2 + g q.1)) ∘ e := by
    ext p i
    fin_cases i <;> simp [e, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]
  rw [h]
  exact he.symm.comp (hσ.comp he)

theorem measurableEmbedding_planeShear (hg : Continuous g) : MeasurableEmbedding (planeShear g) :=
  coe_planeShearHomeomorph hg ▸ (planeShearHomeomorph hg).measurableEmbedding

/-! ### Schwartz functions -/

/-- For `g` of temperate growth, the shear grows at most polynomially, and so does its inverse. -/
theorem norm_le_mul_one_add_norm_planeShear_pow (hg : g.HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖planeShear g p‖) ^ k := by
  obtain ⟨k, C, hC⟩ := hg.2 0
  refine ⟨k + 1, 1 + |C|, fun p ↦ ?_⟩
  set q := planeShear g p
  have hq : 1 ≤ 1 + ‖q‖ := by simp
  have hg0 : |g (q 0)| ≤ |C| * (1 + ‖q‖) ^ k := by
    have := hC (q 0)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
    refine this.trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ?_ k)
      (by positivity) (abs_nonneg C))
    simpa using PiLp.norm_apply_le q 0
  calc ‖p‖ = ‖q - g (q 0) • EuclideanSpace.single 1 1‖ := by
        rw [← planeShear_neg_planeShear (g := g) p]
        simp [q, planeShear, sub_eq_add_neg]
    _ ≤ ‖q‖ + |g (q 0)| := by
        refine (norm_sub_le _ _).trans ?_
        simp [norm_smul]
    _ ≤ (1 + ‖q‖) ^ (k + 1) + |C| * (1 + ‖q‖) ^ (k + 1) := by
        gcongr
        · exact (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hq (by omega))
        · exact hg0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (by omega))
            (abs_nonneg C))
    _ = (1 + |C|) * (1 + ‖q‖) ^ (k + 1) := by ring

theorem hasTemperateGrowth_planeShear (hg : g.HasTemperateGrowth) :
    (planeShear g).HasTemperateGrowth := by
  have h0 : (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0).HasTemperateGrowth :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasTemperateGrowth
  unfold planeShear
  fun_prop

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Precomposition with the shear** `(x, y) ↦ (x, y + g x)` on Schwartz functions, for `g` of
temperate growth. -/
def compPlaneShearCLM (g : ℝ → ℝ) (hg : g.HasTemperateGrowth) :
    𝓢(EuclideanSpace ℝ (Fin 2), F) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin 2), F) :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_planeShear hg)
    (norm_le_mul_one_add_norm_planeShear_pow hg)

@[simp]
theorem compPlaneShearCLM_apply (hg : g.HasTemperateGrowth) (u : 𝓢(EuclideanSpace ℝ (Fin 2), F))
    (p : EuclideanSpace ℝ (Fin 2)) : compPlaneShearCLM g hg u p = u (planeShear g p) := by
  simp [compPlaneShearCLM]

theorem coe_compPlaneShearCLM (hg : g.HasTemperateGrowth) (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) :
    ⇑(compPlaneShearCLM g hg u) = u ∘ planeShear g :=
  funext <| compPlaneShearCLM_apply hg u

/-- **The chain rule for the shear**: `∂_v (u ∘ φ) = (∂_v u) ∘ φ + g'(x) v₀ (∂_y u) ∘ φ`. -/
theorem lineDerivOp_compPlaneShearCLM_apply (hg : g.HasTemperateGrowth)
    (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) (v p : EuclideanSpace ℝ (Fin 2)) :
    ∂_{v} (compPlaneShearCLM g hg u) p =
      ∂_{v} u (planeShear g p) + (deriv g (p 0) * v 0) •
        ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u (planeShear g p) := by
  have hφ := hasFDerivAt_planeShear (hg.1.differentiable (by simp) (p 0))
  have h := (u.differentiableAt (x := planeShear g p)).hasFDerivAt.comp p hφ
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, coe_compPlaneShearCLM, h.fderiv]
  simp [mul_comm, mul_smul]

/-! ### Unboundedness for the `H¹` norm -/

/-- **The shear term of the derivative.** By the chain rule
`∂ₓ (u ∘ φ) = (∂ₓ u) ∘ φ + g'(x) (∂_y u) ∘ φ`, so the `L²` norm of `∂ₓ (u ∘ φ)` is at least half
the weighted integral `∫ g'(x)² |∂_y u|²` minus `∫ |∂ₓ u|²`; both integrals are transported back
from `u ∘ φ` to `u` by the measure-preserving shear. -/
private theorem half_integral_sub_le_integral_norm_lineDerivOp_compPlaneShearCLM_sq
    (hg : g.HasTemperateGrowth) (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) :
    (1 / 2) * (∫ q, deriv g (q 0) ^ 2 * ‖∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q‖ ^ 2) -
        ∫ q, ‖∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} u q‖ ^ 2 ≤
      ∫ p, ‖∂_{EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} (compPlaneShearCLM g hg u) p‖ ^ 2 := by
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hφ := measurePreserving_planeShear hg.1.continuous.measurable
  have hemb := measurableEmbedding_planeShear hg.1.continuous
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
      ∫ p, (2 * ‖∂_{e₀} (compPlaneShearCLM g hg u) p‖ ^ 2 +
        2 * ‖∂_{e₀} u (planeShear g p)‖ ^ 2) := by
    refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
      (((hint _).const_mul 2).add (hia.const_mul 2)) (.of_forall fun p ↦ ?_)
    have hd : ∂_{e₀} (compPlaneShearCLM g hg u) p =
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

variable [CompleteSpace F]

/-- **The shear is an isometry of `H^{0,p} = Lᵖ`**, since it preserves Lebesgue measure. -/
theorem norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM (hg : g.HasTemperateGrowth)
    {p : ENNReal} [Fact (1 ≤ p)] (u : 𝓢(EuclideanSpace ℝ (Fin 2), F)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM 0 p (compPlaneShearCLM g hg u)‖ =
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 p u‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.norm_toLp_eq,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero, SchwartzMap.norm_toLp,
    SchwartzMap.norm_toLp, coe_compPlaneShearCLM, eLpNorm_comp_measurePreserving
      u.continuous.aestronglyMeasurable (measurePreserving_planeShear hg.1.continuous.measurable)]

/-- A Schwartz function whose derivative in the `y` direction is compactly supported in the strip
`|x| ≤ 1` and does not vanish identically: a smooth bump function on the unit disc. -/
private theorem exists_lineDerivOp_single_one_ne_zero :
    ∃ u : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ),
      HasCompactSupport (fun q ↦ ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q) ∧
      (∀ q, ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q ≠ 0 → |q 0| ≤ 1) ∧
      ∃ q, ∂_{EuclideanSpace.single (1 : Fin 2) (1 : ℝ)} u q ≠ 0 := by
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hc : HasCompactSupport (fun x ↦ (f x : ℂ)) :=
    f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun x ↦ (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp f.contDiff
  let u := hc.toSchwartzMap hs
  have hfun : ⇑u = fun x ↦ (f x : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun hc hs)
  have hder (q) : ∂_{e₁} u q = fderiv ℝ (fun x ↦ (f x : ℂ)) q e₁ := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun]
  refine ⟨u, ?_, fun q hq ↦ ?_, ?_⟩
  · simp only [hder]
    exact (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L ↦ L e₁) rfl
  · rw [hder] at hq
    have hq' : q ∈ Function.support (fderiv ℝ (fun x ↦ (f x : ℂ))) := fun h ↦ hq (by simp [h])
    have hts := (tsupport_comp_subset Complex.ofReal_zero f) (support_fderiv_subset ℝ hq')
    rw [f.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hts
    exact (PiLp.norm_apply_le q 0).trans hts
  · -- Otherwise `s ↦ u (s • e₁)` would be constant, but it is `1` at `0` and `0` at `2 e₁`.
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
    simp [hfun, h0, h2] at hconst

/-- **The shear is unbounded for the `H¹` norm** when `|g'(x)| → ∞` as `x → ∞`: no constant `C`
satisfies `‖u ∘ φ‖_{H¹} ≤ C ‖u‖_{H¹}` for all Schwartz functions `u`, although the shear is an
isometry of `L²` (`TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`). -/
theorem not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le
    (hg : g.HasTemperateGrowth) (hg' : Tendsto (fun x ↦ |deriv g x|) atTop atTop) :
    ¬ ∃ C, ∀ u : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 (compPlaneShearCLM g hg u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 u‖ := by
  -- Test the bound on the translates `u_t = u₀(· - t e₀)` of a bump function: their `H¹` norm is
  -- constant, while `‖u_t ∘ φ‖_{H¹}² ≥ (2π)⁻² ‖∂ₓ (u_t ∘ φ)‖²_{L²} ≥ (2π)⁻² (M² A / 2 - B)`
  -- whenever `|g'| ≥ M` on `[t - 1, ∞)`, with `A = ‖∂_y u₀‖²_{L²} > 0` and `B = ‖∂ₓ u₀‖²_{L²}`.
  rintro ⟨C, hC⟩
  obtain ⟨u₀, hcs, hsupp, q₀, hq₀⟩ := exists_lineDerivOp_single_one_ne_zero
  set e₀ := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  set e₁ := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  set b := EuclideanSpace.basisFun (Fin 2) ℝ
  set A := ∫ q, ‖∂_{e₁} u₀ q‖ ^ 2
  set B := ∫ q, ‖∂_{e₀} u₀ q‖ ^ 2
  set N := ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 u₀‖
  set c : ℝ := (2 * π)⁻¹ ^ 2
  have hc : 0 < c := by positivity
  have hA : 0 < A := by
    have hcont : Continuous fun q ↦ ‖∂_{e₁} u₀ q‖ ^ 2 := by fun_prop
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (hcs.comp_left (g := fun z : ℂ ↦ ‖z‖ ^ 2) (by simp)) (fun _ ↦ sq_nonneg _)
      (by simpa using hq₀)
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ by positivity
  -- The translate `u_t(q) = u₀(q - t e₀)` and its derivatives.
  have hder (t : ℝ) (v q : EuclideanSpace ℝ (Fin 2)) :
      ∂_{v} (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀) q = ∂_{v} u₀ (q - t • e₀) := by
    have hfun : ⇑(SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀) = fun x ↦ u₀ (x - t • e₀) :=
      funext fun x ↦ SchwartzMap.compSubConstCLM_apply u₀ (t • e₀) x
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun, fderiv_comp_sub]
  -- Translation does not change the `H¹` norm.
  have hnorm (t : ℝ) :
      ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀)‖ =
        N := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    simp only [SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq b, hder,
      SchwartzMap.compSubConstCLM_apply,
      integral_sub_right_eq_self (fun q ↦ ‖u₀ q‖ ^ 2) (t • e₀)]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦
      integral_sub_right_eq_self (fun q ↦ ‖∂_{b i} u₀ q‖ ^ 2) (t • e₀)
  -- The `H¹` norm of `u_t ∘ φ` bounds the `L²` norm of its `x`-derivative.
  have hlow (t : ℝ) :
      c * ∫ p, ‖∂_{e₀} (compPlaneShearCLM g hg (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀)) p‖ ^ 2
        ≤ (C * N) ^ 2 := by
    set w := compPlaneShearCLM g hg (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀)
    have hCw := (hC (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀)).trans_eq (by rw [hnorm])
    refine le_trans ?_ (pow_le_pow_left₀ (norm_nonneg _) hCw 2)
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq b]
    have hb0 : b 0 = e₀ := by simp [b, e₀]
    have hterm : ∫ p, ‖∂_{e₀} w p‖ ^ 2 ≤ ∑ i, ∫ p, ‖∂_{b i} w p‖ ^ 2 := by
      rw [← hb0]
      exact Finset.single_le_sum (f := fun i ↦ ∫ p, ‖∂_{b i} w p‖ ^ 2)
        (fun i _ ↦ integral_nonneg fun _ ↦ by positivity) (Finset.mem_univ 0)
    have h0 : 0 ≤ ∫ p, ‖w p‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
    nlinarith
  -- The weighted integral of `u_t` is the integral of `u₀` with the weight shifted by `t`.
  have hweight (t : ℝ) :
      ∫ q, deriv g (q 0) ^ 2 * ‖∂_{e₁} (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀) q‖ ^ 2 =
        ∫ q, deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u₀ q‖ ^ 2 := by
    simp only [hder]
    rw [← integral_sub_right_eq_self (fun q ↦ deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u₀ q‖ ^ 2) (t • e₀)]
    simp [e₀]
  have hB' (t : ℝ) :
      ∫ q, ‖∂_{e₀} (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀) q‖ ^ 2 = B := by
    simp only [hder, B, integral_sub_right_eq_self (fun q ↦ ‖∂_{e₀} u₀ q‖ ^ 2) (t • e₀)]
  -- Far out, `|g'| ≥ M` on the support of `∂_y u₀`, so the weighted integral is at least `M² A`.
  have hM (M t : ℝ) (hM0 : 0 ≤ M) (ht : ∀ s, t - 1 ≤ s → M ≤ |deriv g s|) :
      M ^ 2 * A ≤ ∫ q, deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u₀ q‖ ^ 2 := by
    rw [← integral_const_mul]
    have hcont : Continuous fun q : EuclideanSpace ℝ (Fin 2) ↦
        deriv g (q 0 + t) ^ 2 * ‖∂_{e₁} u₀ q‖ ^ 2 :=
      (((hg.1.continuous_deriv (by simp)).comp
        ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.add_const t)).pow 2).mul
        ((∂_{e₁} u₀).continuous.norm.pow 2)
    refine integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
      (hcont.integrable_of_hasCompactSupport
        (hcs.comp_left (g := fun z : ℂ ↦ ‖z‖ ^ 2) (by simp)).mul_left) (.of_forall fun q ↦ ?_)
    by_cases hq : ∂_{e₁} u₀ q = 0
    · simp [hq]
    · have h1 := ht (q 0 + t) (by linarith [(abs_le.1 (hsupp q hq)).1])
      have h2 : M ^ 2 ≤ deriv g (q 0 + t) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ hM0 h1 2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
  -- Choose `M` with `c (M² A / 2 - B) > (C N)²`, and `t` far enough out.
  set M : ℝ := 2 * ((C * N) ^ 2 / c + B) / A + 1
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 2 * ((C * N) ^ 2 / c + B) / A := by positivity
    linarith
  obtain ⟨S, hS⟩ := eventually_atTop.1 (hg'.eventually_ge_atTop M)
  set t := S + 1
  have key := half_integral_sub_le_integral_norm_lineDerivOp_compPlaneShearCLM_sq hg
    (SchwartzMap.compSubConstCLM ℂ (t • e₀) u₀)
  rw [hweight, hB'] at key
  have hMt := hM M t (by linarith) fun s hs ↦ hS s (by linarith)
  have hlt := hlow t
  have hMA : M * A = 2 * ((C * N) ^ 2 / c + B) + A := by
    simp only [M]; field_simp
  have hM2 : M * A ≤ M ^ 2 * A := mul_le_mul_of_nonneg_right (by nlinarith) hA.le
  have hcCN : c * ((C * N) ^ 2 / c) = (C * N) ^ 2 := by field_simp
  nlinarith

/-- **The cubic shear `(x, y) ↦ (x, y + x³)` is unbounded for the `H¹` norm**, although it is an
isometry of `L²` (`TauCeti.norm_toBesselPotentialSpaceCLM_zero_compPlaneShearCLM`): its derivative
`3x²` is unbounded. -/
theorem not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_cube_le :
    ¬ ∃ C, ∀ u : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 (compPlaneShearCLM (· ^ 3) (by fun_prop) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 1 2 u‖ := by
  refine not_exists_norm_toBesselPotentialSpaceCLM_one_compPlaneShearCLM_le _ ?_
  have h : (fun x : ℝ ↦ |deriv (· ^ 3) x|) = fun x ↦ 3 * x ^ 2 := by
    ext x
    simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * x ^ 2)]
  rw [h]
  exact (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by norm_num)

end TauCeti
