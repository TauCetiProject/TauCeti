/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Sobolev.Mollification.Lipschitz

/-!
# Lipschitz shears

For a function `γ : E → ℝ`, the **shear** `(t, x) ↦ (t - γ x, x)` of `WithLp 2 (ℝ × E)`
(`TauCeti.normalShear γ`) moves the region `{γ x < t}` above the graph of `γ`, the domain of a
Lipschitz boundary chart, onto the half-space `{0 < t}`, and the graph onto the hyperplane
`{t = 0}`. Its inverse is the shear along `-γ`. The normal coordinate comes first, as in
`Set.IsLipschitzChart`; in the coordinates `(x, t)` this is `Φ(x, t) = (x, t - γ(x))`.

For a `K`-Lipschitz `γ`, the shear and its inverse are `(1 + K)`-Lipschitz
(`TauCeti.lipschitzWith_normalShear`). Where `γ` has derivative `γ'`, the shear has derivative
`v ↦ v - (γ' v.2, 0)` (`TauCeti.hasFDerivAt_normalShear`), a transvection, of determinant `1`
(`TauCeti.det_normalShearCLM`) and norm at most `1 + ‖γ'‖`. Two shears differ pointwise by the
difference of their functions.

Mollifying `γ` with a normalized bump `ρ` gives the smooth shears `Φ_ρ` along `ρ ⋆ γ`
(`TauCeti.contDiff_normalShear_normed_convolution`), of determinant `1`, with
`‖DΦ_ρ‖ ≤ 1 + K` (`TauCeti.norm_fderiv_normalShear_normed_convolution_le`), uniformly within
`K · ρ.rOut` of the shear along `γ` (`TauCeti.dist_normalShear_normed_convolution_le`). These are
the inputs for the composition `u ↦ u ∘ Φ` on `W^{1,p}` through smooth approximations.

## Main declarations

* `TauCeti.normalShear γ`: the shear `(t, x) ↦ (t - γ x, x)`, with inverse `normalShear (-γ)`.
* `TauCeti.normalShear_image_setOf_lt_fst`: it maps the region above the graph onto `{0 < t}`.
* `TauCeti.lipschitzWith_normalShear`: a `K`-Lipschitz `γ` gives a `(1 + K)`-Lipschitz shear.
* `TauCeti.normalShearCLM`, `TauCeti.hasFDerivAt_normalShear`, `TauCeti.det_normalShearCLM`,
  `TauCeti.norm_normalShearCLM_le`: the derivative of the shear, of determinant `1`.
* `TauCeti.contDiff_normalShear_normed_convolution`,
  `TauCeti.norm_fderiv_normalShear_normed_convolution_le`,
  `TauCeti.dist_normalShear_normed_convolution_le`: the mollified shears.
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory Metric Set
open scoped NNReal Convolution ContDiff

namespace TauCeti

/-! ### The shear -/

section Shear

variable {E : Type*}

/-- The **shear** `(t, x) ↦ (t - γ x, x)` of `WithLp 2 (ℝ × E)` along `γ : E → ℝ`, with inverse
the shear `(t, x) ↦ (t + γ x, x)`. -/
@[expose] def normalShear (γ : E → ℝ) : WithLp 2 (ℝ × E) ≃ WithLp 2 (ℝ × E) where
  toFun z := WithLp.toLp 2 (z.fst - γ z.snd, z.snd)
  invFun z := WithLp.toLp 2 (z.fst + γ z.snd, z.snd)
  left_inv z := by
    change WithLp.toLp 2 (z.fst - γ z.snd + γ z.snd, z.snd) = z
    rw [sub_add_cancel]
    rfl
  right_inv z := by
    change WithLp.toLp 2 (z.fst + γ z.snd - γ z.snd, z.snd) = z
    rw [add_sub_cancel_right]
    rfl

variable {γ : E → ℝ}

/-- The normal coordinate of the shear. -/
@[simp]
theorem normalShear_apply_fst (z : WithLp 2 (ℝ × E)) :
    (normalShear γ z).fst = z.fst - γ z.snd :=
  rfl

/-- The base coordinate of the shear. -/
@[simp]
theorem normalShear_apply_snd (z : WithLp 2 (ℝ × E)) : (normalShear γ z).snd = z.snd :=
  rfl

/-- The inverse of the shear along `γ` is the shear along `-γ`. -/
theorem normalShear_symm (γ : E → ℝ) : (normalShear γ).symm = normalShear (-γ) := by
  ext z
  change WithLp.toLp 2 (z.fst + γ z.snd, z.snd) = WithLp.toLp 2 (z.fst - -γ z.snd, z.snd)
  rw [sub_neg_eq_add]

/-- The shear along `0` is the identity. -/
@[simp]
theorem normalShear_zero : normalShear (0 : E → ℝ) = Equiv.refl _ := by
  ext z
  change WithLp.toLp 2 (z.fst - 0, z.snd) = z
  rw [sub_zero]
  rfl

/-- **The shear flattens the graph**: it maps the region strictly above the graph of `γ` onto the
half-space `{0 < t}`. -/
theorem normalShear_image_setOf_lt_fst :
    normalShear γ '' {z | γ z.snd < z.fst} = {z | 0 < z.fst} := by
  rw [Equiv.image_eq_preimage_symm, normalShear_symm]
  ext z
  simp

/-- The shear maps the graph of `γ` onto the hyperplane `{t = 0}`. -/
theorem normalShear_image_setOf_fst_eq :
    normalShear γ '' {z | z.fst = γ z.snd} = {z | z.fst = 0} := by
  rw [Equiv.image_eq_preimage_symm, normalShear_symm]
  ext z
  simp

end Shear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ γ₁ γ₂ : E → ℝ}

omit [NormedSpace ℝ E] in
/-- Two shears differ pointwise by the difference of their functions. -/
theorem dist_normalShear_normalShear (z : WithLp 2 (ℝ × E)) :
    dist (normalShear γ₁ z) (normalShear γ₂ z) = dist (γ₁ z.snd) (γ₂ z.snd) := by
  rw [WithLp.prod_dist_eq_of_L2]
  simp only [normalShear_apply_fst, normalShear_apply_snd, dist_self, Real.dist_eq]
  rw [show z.fst - γ₁ z.snd - (z.fst - γ₂ z.snd) = -(γ₁ z.snd - γ₂ z.snd) by ring, abs_neg,
    sq_abs, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]

omit [NormedSpace ℝ E] in
/-- **A Lipschitz shear is Lipschitz**: for a `K`-Lipschitz `γ`, the shear along `γ` is
`(1 + K)`-Lipschitz; so is its inverse, the shear along `-γ`. -/
theorem lipschitzWith_normalShear {K : ℝ≥0} (hγ : LipschitzWith K γ) :
    LipschitzWith (1 + K) (normalShear γ) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  have hz (y : WithLp 2 (ℝ × E)) : normalShear γ y = y - WithLp.toLp 2 (γ y.snd, 0) :=
    (WithLp.ext_iff 2).2 (Prod.ext (by simp) (by simp))
  have hγzw : dist (WithLp.toLp 2 (γ z.snd, (0 : E))) (WithLp.toLp 2 (γ w.snd, 0)) ≤
      K * dist z w := by
    rw [WithLp.prod_dist_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, zero_pow two_ne_zero, add_zero,
      Real.sqrt_sq dist_nonneg]
    exact (hγ.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (WithLp.dist_snd_le z w) K.coe_nonneg)
  rw [hz, hz, NNReal.coe_add, NNReal.coe_one, add_mul, one_mul]
  exact (dist_sub_sub_le _ _ _ _).trans (add_le_add le_rfl hγzw)

omit [NormedSpace ℝ E] in
/-- The inverse of a shear along a `K`-Lipschitz `γ` is `(1 + K)`-Lipschitz. -/
theorem lipschitzWith_normalShear_symm {K : ℝ≥0} (hγ : LipschitzWith K γ) :
    LipschitzWith (1 + K) (normalShear γ).symm := by
  rw [normalShear_symm]
  exact lipschitzWith_normalShear (by simpa using hγ.neg)

/-! ### The derivative -/

/-- The derivative of a shear: `v ↦ v - (γ' v.2, 0)` for the derivative `γ'` of `γ`. -/
def normalShearCLM (γ' : E →L[ℝ] ℝ) : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) :=
  ContinuousLinearMap.id ℝ _ -
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.inl ℝ ℝ E ∘L γ' ∘L WithLp.sndL 2 ℝ ℝ E

/-- The derivative of a shear applied to a vector. -/
theorem normalShearCLM_apply (γ' : E →L[ℝ] ℝ) (v : WithLp 2 (ℝ × E)) :
    normalShearCLM γ' v = WithLp.toLp 2 (v.fst - γ' v.snd, v.snd) :=
  (WithLp.ext_iff 2).2 (Prod.ext (by simp [normalShearCLM]) (by simp [normalShearCLM]))

/-- The derivative of a shear has norm at most `1 + ‖γ'‖`. -/
theorem norm_normalShearCLM_le (γ' : E →L[ℝ] ℝ) : ‖normalShearCLM γ'‖ ≤ 1 + ‖γ'‖ := by
  refine (norm_sub_le _ _).trans (add_le_add norm_id_le (opNorm_le_bound _ (norm_nonneg _)
    fun v => ?_))
  simp only [coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply, inl_apply]
  rw [WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    norm_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]
  exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le (x := v))
    (norm_nonneg _))

/-- **The derivative of a shear has determinant `1`**: it is the transvection
`v ↦ v + f v • (1, 0)` for the linear form `f = -γ' ∘ snd`, which vanishes on `(1, 0)`. (In
infinite dimension the determinant is `1` by convention.) -/
theorem det_normalShearCLM (γ' : E →L[ℝ] ℝ) :
    (normalShearCLM γ').det = 1 := by
  have h : (normalShearCLM γ' : WithLp 2 (ℝ × E) →ₗ[ℝ] WithLp 2 (ℝ × E)) =
      LinearMap.transvection (-(γ' ∘L WithLp.sndL 2 ℝ ℝ E : WithLp 2 (ℝ × E) →L[ℝ] ℝ).toLinearMap)
        (WithLp.toLp 2 (1, 0)) := by
    refine LinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.coe_coe, normalShearCLM_apply, LinearMap.transvection.apply]
    refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;> simp [sub_eq_add_neg]
  rw [ContinuousLinearMap.det, h]
  by_cases hfin : Module.Finite ℝ (WithLp 2 (ℝ × E))
  · rw [LinearMap.transvection.det]
    simp
  · exact LinearMap.det_eq_one_of_not_module_finite hfin _

/-- **The derivative of a shear**: where `γ` has derivative `γ'` at the base point `z.2`, the
shear along `γ` has derivative `v ↦ v - (γ' v.2, 0)` at `z`. -/
theorem hasFDerivAt_normalShear {γ' : E →L[ℝ] ℝ} {z : WithLp 2 (ℝ × E)}
    (h : HasFDerivAt γ γ' z.snd) : HasFDerivAt (normalShear γ) (normalShearCLM γ') z := by
  have h1 : HasFDerivAt (fun y : WithLp 2 (ℝ × E) => y.fst - γ y.snd)
      (WithLp.fstL 2 ℝ ℝ E - γ' ∘L WithLp.sndL 2 ℝ ℝ E) z :=
    (WithLp.fstL 2 ℝ ℝ E).hasFDerivAt.sub
      ((h : HasFDerivAt γ γ' (WithLp.sndL 2 ℝ ℝ E z)).comp z (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt)
  have h3 := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt.comp z
    (h1.prodMk (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt)
  convert h3 using 1
  · funext v
    rfl
  ext1 v
  rw [normalShearCLM_apply]
  refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;> simp

/-- The shear along a `C^n` function is `C^n`. -/
theorem contDiff_normalShear {n : WithTop ℕ∞} (hγ : ContDiff ℝ n γ) :
    ContDiff ℝ n (normalShear γ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff.comp
    (((WithLp.fstL 2 ℝ ℝ E).contDiff.sub (hγ.comp (WithLp.sndL 2 ℝ ℝ E).contDiff)).prodMk
      (WithLp.sndL 2 ℝ ℝ E).contDiff)

/-- Where `γ` is differentiable, the derivative of the shear along `γ` is `normalShearCLM`. -/
theorem fderiv_normalShear {z : WithLp 2 (ℝ × E)} (hγ : DifferentiableAt ℝ γ z.snd) :
    fderiv ℝ (normalShear γ) z = normalShearCLM (fderiv ℝ γ z.snd) :=
  (hasFDerivAt_normalShear hγ.hasFDerivAt).fderiv

/-- **Jacobian `1`**: where `γ` is differentiable, the derivative of the shear along `γ` has
determinant `1`. -/
theorem det_fderiv_normalShear {z : WithLp 2 (ℝ × E)}
    (hγ : DifferentiableAt ℝ γ z.snd) : (fderiv ℝ (normalShear γ) z).det = 1 := by
  rw [fderiv_normalShear hγ, det_normalShearCLM]

/-! ### Mollified shears -/

section Mollified

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {K : ℝ≥0}

/-- **Mollified shears are smooth**, for every locally integrable `γ`. -/
theorem contDiff_normalShear_normed_convolution (hγ : LocallyIntegrable γ μ)
    (ρ : ContDiffBump (0 : E)) :
    ContDiff ℝ ∞ (normalShear (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ)) :=
  contDiff_normalShear
    (ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed hγ)

/-- **Mollified shears have Jacobian `1`**, for every locally integrable `γ`. -/
theorem det_fderiv_normalShear_normed_convolution (hγ : LocallyIntegrable γ μ)
    (ρ : ContDiffBump (0 : E)) (z : WithLp 2 (ℝ × E)) :
    (fderiv ℝ (normalShear (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ)) z).det = 1 :=
  det_fderiv_normalShear ((ρ.hasCompactSupport_normed.contDiff_convolution_left (n := 1)
    (lsmul ℝ ℝ) ρ.contDiff_normed hγ).differentiable one_ne_zero _)

/-- **Mollified shears have derivatives of norm at most `1 + K`** for a `K`-Lipschitz `γ`. -/
theorem norm_fderiv_normalShear_normed_convolution_le (hγ : LipschitzWith K γ)
    (ρ : ContDiffBump (0 : E)) (z : WithLp 2 (ℝ × E)) :
    ‖fderiv ℝ (normalShear (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ)) z‖ ≤ 1 + K := by
  rw [fderiv_normalShear ((ρ.hasCompactSupport_normed.contDiff_convolution_left (n := 1)
    (lsmul ℝ ℝ) ρ.contDiff_normed hγ.continuous.locallyIntegrable).differentiable one_ne_zero _)]
  refine (norm_normalShearCLM_le _).trans (add_le_add le_rfl ?_)
  exact opNorm_le_bound _ K.coe_nonneg fun v => hγ.norm_fderiv_normed_convolution_apply_le ρ _ v

/-- **Mollified shears converge uniformly**: the shear along `ρ ⋆ γ` is within `K · ρ.rOut` of
the shear along a `K`-Lipschitz `γ`, at every point. -/
theorem dist_normalShear_normed_convolution_le (hγ : LipschitzWith K γ)
    (ρ : ContDiffBump (0 : E)) (z : WithLp 2 (ℝ × E)) :
    dist (normalShear (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ) z) (normalShear γ z) ≤ K * ρ.rOut := by
  rw [dist_normalShear_normalShear]
  exact ContDiffBump.dist_normed_convolution_le hγ.continuous.aestronglyMeasurable
    fun x hx => (hγ.dist_le_mul x z.snd).trans
      (mul_le_mul_of_nonneg_left (mem_ball.1 hx).le K.coe_nonneg)

end Mollified

end TauCeti
