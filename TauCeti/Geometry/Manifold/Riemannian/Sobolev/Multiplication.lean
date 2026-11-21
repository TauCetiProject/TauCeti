/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Geometry.Manifold.Riemannian.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
import TauCeti.MeasureTheory.Function.Lp.Precomposition
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Smooth multiplication and conformal metric change on `H¹`

Let `M` be a compact `C¹` manifold with a continuous Riemannian metric and Sobolev space `H¹(M)`
(`TauCeti.Manifold.SobolevH1`). On compact `M`, the product rule `∇(u v) = u ∇v + v ∇u` and uniform
bounds on `|u|` and `‖∇u‖` bound `‖u v‖_{H¹}` by a multiple of `‖v‖_{H¹}`, so `v ↦ u v` extends from
smooth functions to `TauCeti.Manifold.SobolevH1.mulLeft u : H¹(M) →L[ℝ] H¹(M)` with `L²` value
`x ↦ u x * toLp w x` (`TauCeti.Manifold.SobolevH1.toLp_mulLeft_ae_eq`), giving a continuous linear
equivalence `TauCeti.Manifold.SobolevH1.mulLeftEquiv` when `u` is nowhere vanishing.

For a conformally rescaled `C^n` metric `ĝ = f g` with `f > 0`, the volume density `f ^ (N / 2)` and
Dirichlet weight `f⁻¹` are bounded above and away from zero on compact `M`, inducing an equivalence
`TauCeti.Manifold.SobolevH1.congrRescale : H¹(WithMetric ĝ) ≃L[ℝ] H¹(WithMetric g)` compatible with
`L²` (`TauCeti.Manifold.SobolevH1.toLp_congrRescale_ae_eq`).

## Main definitions

* `TauCeti.Manifold.SobolevH1.mulLeft`: multiplication by `u : C^∞⟮I, M; ℝ⟯` on `H¹(M)`.
* `TauCeti.Manifold.SobolevH1.mulLeftEquiv`: equivalence `H¹(M) ≃L[ℝ] H¹(M)` when `∀ x, u x ≠ 0`.
* `TauCeti.Manifold.SobolevH1.congrRescale`: equivalence
  `H¹(WithMetric (g.rescale f hf hf_pos)) ≃L[ℝ] H¹(WithMetric g)` on a compact manifold.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), §2.2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), §2.1.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2.
-/

public section

open Bundle MeasureTheory Module Set
open scoped ContDiff ENNReal InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold.SobolevH1

section MulLeft

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- Pointwise squared-gradient bound for a product of `C¹` functions. -/
private theorem norm_mgradient_mul_sq_le {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) {M₀ G₀ : ℝ} {x : M} (hux : |u x| ≤ M₀)
    (hgx : ‖mgradient I u x‖ ≤ G₀) :
    ‖mgradient I (u * v) x‖ ^ 2 ≤
      2 * M₀ ^ 2 * ‖mgradient I v x‖ ^ 2 + 2 * G₀ ^ 2 * v x ^ 2 := by
  have hle : ‖mgradient I (u * v) x‖ ≤ M₀ * ‖mgradient I v x‖ + G₀ * |v x| := by
    rw [mgradient_mul (hu.mdifferentiable one_ne_zero) (hv.mdifferentiable one_ne_zero)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_right hux (norm_nonneg _))
      (mul_comm |v x| ‖mgradient I u x‖ ▸ mul_le_mul_of_nonneg_right hgx (abs_nonneg _))
  refine (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans ?_
  rw [← sq_abs (v x)]
  nlinarith [sq_nonneg (M₀ * ‖mgradient I v x‖ - G₀ * |v x|)]

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Multiplication by a smooth function `u` is bounded on smooth functions in the `H¹` norm. -/
private theorem exists_norm_ofSmooth_mul_le (u : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, ∀ v : C^∞⟮I, M; ℝ⟯, ‖ofSmooth (u * v)‖ ≤ C * ‖ofSmooth v‖ := by
  have hu1 : ContMDiff I 𝓘(ℝ) 1 u := u.contMDiff.of_le (by simp)
  let uC : C(M, ℝ) := u
  let gC : C(M, ℝ) := ⟨fun x ↦ ‖mgradient I u x‖, continuous_norm_mgradient hu1⟩
  set M₀ := ‖uC‖
  set G₀ := ‖gC‖
  have hM (x : M) : |u x| ≤ M₀ := by
    simpa only [uC, ContinuousMap.coe_ofClass, Real.norm_eq_abs] using uC.norm_coe_le_norm x
  have hG (x : M) : ‖mgradient I u x‖ ≤ G₀ := gC.apply_le_norm x
  refine ⟨Real.sqrt (3 * M₀ ^ 2 + 2 * G₀ ^ 2), fun v ↦ ?_⟩
  have hv1 : ContMDiff I 𝓘(ℝ) 1 v := v.contMDiff.of_le (by simp)
  set dV := riemannianVolume I M
  have hval : ∫ x, (u * v) x ^ 2 ∂dV ≤ M₀ ^ 2 * ∫ x, v x ^ 2 ∂dV := by
    rw [← integral_const_mul]
    refine integral_mono ((map_continuous (u * v)).pow 2).integrable_of_compactSpace
      (continuous_const.mul ((map_continuous v).pow 2)).integrable_of_compactSpace fun x ↦ ?_
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, mul_pow, ← sq_abs (u x)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM x) 2) (sq_nonneg _)
  have hgrad : ∫ x, ‖mgradient I (u * v) x‖ ^ 2 ∂dV ≤
      2 * M₀ ^ 2 * (∫ x, ‖mgradient I v x‖ ^ 2 ∂dV) + 2 * G₀ ^ 2 * ∫ x, v x ^ 2 ∂dV := by
    have hi₁ : Integrable (fun x ↦ 2 * M₀ ^ 2 * ‖mgradient I v x‖ ^ 2) dV :=
      (continuous_const.mul (continuous_norm_sq_mgradient hv1)).integrable_of_compactSpace
    have hi₂ : Integrable (fun x ↦ 2 * G₀ ^ 2 * v x ^ 2) dV :=
      (continuous_const.mul ((map_continuous v).pow 2)).integrable_of_compactSpace
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi₁ hi₂]
    exact integral_mono (continuous_norm_sq_mgradient (hu1.mul hv1)).integrable_of_compactSpace
      (hi₁.add hi₂) fun x ↦
        ContMDiffMap.coe_mul u v ▸ norm_mgradient_mul_sq_le hu1 hv1 (hM x) (hG x)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), norm_ofSmooth_sq, norm_ofSmooth_sq]
  nlinarith [integral_nonneg (μ := dV) fun x ↦ sq_nonneg (v x),
    integral_nonneg (μ := dV) fun x ↦ sq_nonneg ‖mgradient I v x‖, sq_nonneg M₀, sq_nonneg G₀]

/-- **Multiplication by a smooth function on `H¹(M)`.** On a compact Riemannian manifold, pointwise
multiplication `v ↦ u * v` by `u : C^∞⟮I, M; ℝ⟯` extends from smooth functions to a continuous
linear operator `H¹(M) →L[ℝ] H¹(M)`. -/
def mulLeft (u : C^∞⟮I, M; ℝ⟯) : SobolevH1 I M →L[ℝ] SobolevH1 I M :=
  liftSmooth (ofSmooth.comp (LinearMap.mulLeft ℝ u)) (exists_norm_ofSmooth_mul_le u)

/-- On a smooth function `v`, `mulLeft u` gives the class of `u * v`. -/
@[simp]
theorem mulLeft_ofSmooth (u v : C^∞⟮I, M; ℝ⟯) :
    mulLeft u (ofSmooth v) = ofSmooth (u * v) :=
  liftSmooth_ofSmooth _ _ v

/-- The value in `L²(M)` of `mulLeft u w` is the Hölder product of `u ∈ L^∞(M)` and `toLp w`. -/
theorem toLp_mulLeft (u : C^∞⟮I, M; ℝ⟯) (w : SobolevH1 I M) :
    toLp (mulLeft u w) =
      (ContinuousLinearMap.mul ℝ ℝ).holder 2
        (ContinuousMap.toLp (⊤ : ℝ≥0∞) (riemannianVolume I M) ℝ (u : C(M, ℝ))) (toLp w) := by
  refine induction_on w (isClosed_eq (toLp.continuous.comp (mulLeft u).continuous)
    ((((ContinuousLinearMap.mul ℝ ℝ).holderL (riemannianVolume I M) (⊤ : ℝ≥0∞) 2 2
      (ContinuousMap.toLp (⊤ : ℝ≥0∞) (riemannianVolume I M) ℝ (u : C(M, ℝ)))).continuous).comp
      toLp.continuous)) fun v ↦ ?_
  rw [mulLeft_ofSmooth, toLp_ofSmooth, toLp_ofSmooth]
  refine Lp.ext ?_
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I M)
      ((u * v : C^∞⟮I, M; ℝ⟯) : C(M, ℝ)),
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
      (ContinuousMap.toLp (⊤ : ℝ≥0∞) (riemannianVolume I M) ℝ (u : C(M, ℝ)))
      (ContinuousMap.toLp 2 (riemannianVolume I M) ℝ (v : C(M, ℝ))),
    ContinuousMap.coeFn_toLp (p := (⊤ : ℝ≥0∞)) (𝕜 := ℝ) (riemannianVolume I M) (u : C(M, ℝ)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I M) (v : C(M, ℝ))]
    with x huv hmul hu hv
  rw [huv, hmul, ContinuousLinearMap.mul_apply', hu, hv]; rfl

/-- **Compatibility of `mulLeft` with `L²`.** The value of `mulLeft u w` is almost everywhere equal
to `x ↦ u x * toLp w x`. -/
theorem toLp_mulLeft_ae_eq (u : C^∞⟮I, M; ℝ⟯) (w : SobolevH1 I M) :
    toLp (mulLeft u w) =ᵐ[riemannianVolume I M] fun x ↦ u x * toLp w x := by
  rw [toLp_mulLeft]
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
      (ContinuousMap.toLp (⊤ : ℝ≥0∞) (riemannianVolume I M) ℝ (u : C(M, ℝ))) (toLp w),
    ContinuousMap.coeFn_toLp (p := (⊤ : ℝ≥0∞)) (𝕜 := ℝ) (riemannianVolume I M) (u : C(M, ℝ))]
    with x hmul hu
  rw [hmul, ContinuousLinearMap.mul_apply', hu]; rfl

@[simp]
theorem mulLeft_one : mulLeft (1 : C^∞⟮I, M; ℝ⟯) = ContinuousLinearMap.id ℝ (SobolevH1 I M) := by
  ext1 w; exact induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ by simp

@[simp]
theorem mulLeft_zero : mulLeft (0 : C^∞⟮I, M; ℝ⟯) = 0 := by
  ext1 w; exact induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ by simp

theorem mulLeft_add (u₁ u₂ : C^∞⟮I, M; ℝ⟯) : mulLeft (u₁ + u₂) = mulLeft u₁ + mulLeft u₂ := by
  ext1 w; exact induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ by simp [add_mul]

theorem mulLeft_smul (c : ℝ) (u : C^∞⟮I, M; ℝ⟯) : mulLeft (c • u) = c • mulLeft u := by
  ext1 w; exact induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ by simp

theorem mulLeft_mul (u₁ u₂ : C^∞⟮I, M; ℝ⟯) :
    mulLeft (u₁ * u₂) = (mulLeft u₁).comp (mulLeft u₂) := by
  ext1 w; exact induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ by simp [mul_assoc]

/-- **Multiplication by a nowhere-vanishing smooth function on `H¹(M)`.** When `u x ≠ 0` for all
`x`, multiplication by `u` is a continuous linear equivalence `H¹(M) ≃L[ℝ] H¹(M)` with inverse
multiplication by `u⁻¹`. -/
def mulLeftEquiv (u : C^∞⟮I, M; ℝ⟯) (hu : ∀ x, u x ≠ 0) : SobolevH1 I M ≃L[ℝ] SobolevH1 I M :=
  let uInv : C^∞⟮I, M; ℝ⟯ := ⟨fun x ↦ (u x)⁻¹, u.contMDiff.inv₀ hu⟩
  ContinuousLinearEquiv.ofContinuousLinearMap (mulLeft u) (mulLeft uInv)
    (ContinuousLinearMap.ext fun w ↦ by
      have hmul : u * uInv = 1 := ContMDiffMap.ext fun x ↦ mul_inv_cancel₀ (hu x)
      simp [← mulLeft_mul, hmul])
    (ContinuousLinearMap.ext fun w ↦ by
      have hmul : uInv * u = 1 := ContMDiffMap.ext fun x ↦ inv_mul_cancel₀ (hu x)
      simp [← mulLeft_mul, hmul])

@[simp]
theorem mulLeftEquiv_apply (u : C^∞⟮I, M; ℝ⟯) (hu : ∀ x, u x ≠ 0) (w : SobolevH1 I M) :
    mulLeftEquiv u hu w = mulLeft u w := (rfl)

@[simp]
theorem coe_mulLeftEquiv (u : C^∞⟮I, M; ℝ⟯) (hu : ∀ x, u x ≠ 0) :
    (mulLeftEquiv u hu : SobolevH1 I M →L[ℝ] SobolevH1 I M) = mulLeft u := (rfl)

@[simp]
theorem mulLeftEquiv_symm_apply (u : C^∞⟮I, M; ℝ⟯) (hu : ∀ x, u x ≠ 0) (w : SobolevH1 I M) :
    (mulLeftEquiv u hu).symm w = mulLeft ⟨fun x ↦ (u x)⁻¹, u.contMDiff.inv₀ hu⟩ w := (rfl)

end MulLeft

/-! ### Conformal rescaling of the metric on `H¹` -/

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- Precomposition of smooth functions with `WithMetric.diffeomorphWithMetric g g' ∞`. -/
private def compDiffeomorphWithMetricLinear
    (g g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) :
    C^∞⟮I, WithMetric g'; ℝ⟯ →ₗ[ℝ] C^∞⟮I, WithMetric g; ℝ⟯ where
  toFun u := u.comp (WithMetric.diffeomorphWithMetric g g' ∞).toContMDiffMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem compDiffeomorphWithMetricLinear_apply
    (g g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (u : C^∞⟮I, WithMetric g'; ℝ⟯) :
    compDiffeomorphWithMetricLinear g g' u =
      u.comp (WithMetric.diffeomorphWithMetric g g' ∞).toContMDiffMap := rfl

variable [FiniteDimensional ℝ E] [CompactSpace M]

/-- Squared `H¹` norm of a smooth function on `WithMetric (g.rescale f hf hf_pos)`, written as a
weighted integral against the Riemannian volume of `WithMetric g`. -/
private theorem norm_ofSmooth_rescale_sq
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    (u : C^∞⟮I, WithMetric (g.rescale f hf hf_pos); ℝ⟯) :
    ‖ofSmooth u‖ ^ 2 =
      (∫ x, f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) *
          u (WithMetric.toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric) ^ 2
        ∂riemannianVolume I (WithMetric g)) +
      ∫ x, (f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) * (f x.ofWithMetric)⁻¹) *
          ‖mgradient I
              (u.comp (WithMetric.diffeomorphWithMetric g (g.rescale f hf hf_pos) ∞).toContMDiffMap)
              x‖ ^ 2
        ∂riemannianVolume I (WithMetric g) := by
  let ĝ := g.rescale f hf hf_pos
  let v : M → ℝ := fun y ↦ u (WithMetric.toWithMetric ĝ y)
  have hu_eq : (u : WithMetric ĝ → ℝ) = v ∘ WithMetric.ofWithMetric :=
    funext fun x ↦ congrArg u (WithMetric.toWithMetric_ofWithMetric ĝ x).symm
  have hug_eq : (u.comp (WithMetric.diffeomorphWithMetric g ĝ ∞).toContMDiffMap :
      WithMetric g → ℝ) = v ∘ WithMetric.ofWithMetric := funext fun x ↦ by dsimp [v]; simp
  rw [norm_ofSmooth_sq]; congr 1
  · rw [hu_eq]
    simpa only [Function.comp_apply, smul_eq_mul] using
      WithMetric.integral_riemannianVolume_rescale (g := g) (hf := hf) (hf_pos := hf_pos)
        fun y ↦ v y ^ 2
  · have h2 := WithMetric.integral_riemannianVolume_rescale (g := g) (hf := hf) (hf_pos := hf_pos)
      fun y ↦ ‖mgradient I (v ∘ WithMetric.ofWithMetric) (WithMetric.toWithMetric ĝ y)‖ ^ 2
    have h2' : ∫ x, ‖mgradient I u x‖ ^ 2 ∂riemannianVolume I (WithMetric ĝ) =
        ∫ x, f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) *
          ‖mgradient I u (WithMetric.toWithMetric ĝ x.ofWithMetric)‖ ^ 2
          ∂riemannianVolume I (WithMetric g) := by
      rw [hu_eq]
      exact (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
          rw [WithMetric.toWithMetric_ofWithMetric])).trans
        (h2.trans (integral_congr_ae
          (Filter.Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; rfl)))
    rw [h2']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    have hg := WithMetric.inner_mgradient_rescale (g := g) (hf := hf) (hf_pos := hf_pos)
      v v x.ofWithMetric
    simp only [real_inner_self_eq_norm_sq, ← hu_eq, ← hug_eq] at hg
    rw [WithMetric.toWithMetric_ofWithMetric g x] at hg
    dsimp only; rw [hg]; ring

/-- Forward `H¹` norm bound from `WithMetric (g.rescale f hf hf_pos)` to `WithMetric g`. -/
private theorem exists_norm_ofSmooth_comp_diffeomorphWithMetric_le
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x) :
    ∃ C : ℝ, ∀ u : C^∞⟮I, WithMetric (g.rescale f hf hf_pos); ℝ⟯,
      ‖ofSmooth (compDiffeomorphWithMetricLinear g (g.rescale f hf hf_pos) u)‖ ≤
        C * ‖ofSmooth u‖ := by
  let ĝ := g.rescale f hf hf_pos
  have hc₀ : Continuous fun y : M ↦ f y ^ ((finrank ℝ E : ℝ) / 2) :=
    hf.continuous.rpow_const fun _ ↦ Or.inr (by positivity)
  have hc₁ : Continuous fun y : M ↦ f y ^ ((finrank ℝ E : ℝ) / 2) * (f y)⁻¹ :=
    hc₀.mul (hf.continuous.inv₀ fun y ↦ (hf_pos y).ne')
  have h0_pos (y : M) : 0 < f y ^ ((finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos (hf_pos y) _
  have h1_pos (y : M) : 0 < f y ^ ((finrank ℝ E : ℝ) / 2) * (f y)⁻¹ :=
    mul_pos (h0_pos y) (inv_pos.2 (hf_pos y))
  let kC : C(M, ℝ) :=
    ⟨_, (hc₀.inv₀ fun y ↦ (h0_pos y).ne').max (hc₁.inv₀ fun y ↦ (h1_pos y).ne')⟩
  set K := ‖kC‖
  have hK0 : 0 ≤ K := norm_nonneg kC
  refine ⟨Real.sqrt K, fun u ↦ ?_⟩
  let ug := compDiffeomorphWithMetricLinear g ĝ u
  let dVg := riemannianVolume I (WithMetric g)
  have hug_apply (x : WithMetric g) : u (WithMetric.toWithMetric ĝ x.ofWithMetric) = ug x := by
    simp [ug]
  have hval : ∫ x, ug x ^ 2 ∂dVg ≤ K * ∫ x, f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) *
      u (WithMetric.toWithMetric ĝ x.ofWithMetric) ^ 2 ∂dVg := by
    simp_rw [hug_apply, ← integral_const_mul]
    refine integral_mono ((map_continuous ug).pow 2).integrable_of_compactSpace
      (continuous_const.mul ((hc₀.comp WithMetric.continuous_ofWithMetric).mul
        ((map_continuous ug).pow 2))).integrable_of_compactSpace fun x ↦ ?_
    have hK₁ : 1 ≤ K * f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) :=
      (inv_mul_cancel₀ (h0_pos _).ne').symm.trans_le
        (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (kC.apply_le_norm _)) (h0_pos _).le)
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hK₁ (sq_nonneg _)
  have hgrad : ∫ x, ‖mgradient I ug x‖ ^ 2 ∂dVg ≤
      K * ∫ x, (f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) * (f x.ofWithMetric)⁻¹) *
        ‖mgradient I ug x‖ ^ 2 ∂dVg := by
    have hug1 : ContMDiff I 𝓘(ℝ) 1 ug := ug.contMDiff.of_le (by simp)
    rw [← integral_const_mul]
    refine integral_mono (continuous_norm_sq_mgradient hug1).integrable_of_compactSpace
      (continuous_const.mul ((hc₁.comp WithMetric.continuous_ofWithMetric).mul
        (continuous_norm_sq_mgradient hug1))).integrable_of_compactSpace fun x ↦ ?_
    have hK₂ : 1 ≤ K * (f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) * (f x.ofWithMetric)⁻¹) :=
      (inv_mul_cancel₀ (h1_pos _).ne').symm.trans_le
        (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (kC.apply_le_norm _)) (h1_pos _).le)
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hK₂ (sq_nonneg _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hK0, norm_ofSmooth_sq, norm_ofSmooth_rescale_sq g hf hf_pos u, mul_add]
  exact add_le_add hval hgrad

/-- Inverse `H¹` norm bound from `WithMetric g` to `WithMetric (g.rescale f hf hf_pos)`. -/
private theorem exists_norm_ofSmooth_comp_diffeomorphWithMetric_symm_le
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x) :
    ∃ C : ℝ, ∀ v : C^∞⟮I, WithMetric g; ℝ⟯,
      ‖ofSmooth (compDiffeomorphWithMetricLinear (g.rescale f hf hf_pos) g v)‖ ≤
        C * ‖ofSmooth v‖ := by
  let ĝ := g.rescale f hf hf_pos
  have hc₀ : Continuous fun y : M ↦ f y ^ ((finrank ℝ E : ℝ) / 2) :=
    hf.continuous.rpow_const fun _ ↦ Or.inr (by positivity)
  have hc₁ : Continuous fun y : M ↦ f y ^ ((finrank ℝ E : ℝ) / 2) * (f y)⁻¹ :=
    hc₀.mul (hf.continuous.inv₀ fun y ↦ (hf_pos y).ne')
  let kC : C(M, ℝ) := ⟨_, hc₀.max hc₁⟩
  set K := ‖kC‖
  have hK0 : 0 ≤ K := norm_nonneg kC
  refine ⟨Real.sqrt K, fun v ↦ ?_⟩
  let u := compDiffeomorphWithMetricLinear ĝ g v
  have huv : u.comp (WithMetric.diffeomorphWithMetric g ĝ ∞).toContMDiffMap = v :=
    ContMDiffMap.ext fun x ↦ by simp [u]
  let dVg := riemannianVolume I (WithMetric g)
  have hv1 : ContMDiff I 𝓘(ℝ) 1 v := v.contMDiff.of_le (by simp)
  have hu_apply (x : WithMetric g) : u (WithMetric.toWithMetric ĝ x.ofWithMetric) = v x := by
    simp [u]
  have hval : ∫ x, f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) *
      u (WithMetric.toWithMetric ĝ x.ofWithMetric) ^ 2 ∂dVg ≤ K * ∫ x, v x ^ 2 ∂dVg := by
    simp_rw [hu_apply, ← integral_const_mul]
    exact integral_mono
      ((hc₀.comp WithMetric.continuous_ofWithMetric).mul
        ((map_continuous v).pow 2)).integrable_of_compactSpace
      (continuous_const.mul ((map_continuous v).pow 2)).integrable_of_compactSpace fun x ↦
        mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (kC.apply_le_norm _)) (sq_nonneg _)
  have hgrad : ∫ x, (f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2) * (f x.ofWithMetric)⁻¹) *
      ‖mgradient I v x‖ ^ 2 ∂dVg ≤ K * ∫ x, ‖mgradient I v x‖ ^ 2 ∂dVg := by
    rw [← integral_const_mul]
    exact integral_mono
      ((hc₁.comp WithMetric.continuous_ofWithMetric).mul
        (continuous_norm_sq_mgradient hv1)).integrable_of_compactSpace
      (continuous_const.mul (continuous_norm_sq_mgradient hv1)).integrable_of_compactSpace fun x ↦
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (kC.apply_le_norm _)) (sq_nonneg _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt hK0, norm_ofSmooth_rescale_sq g hf hf_pos u, huv, norm_ofSmooth_sq,
    mul_add]
  exact add_le_add hval hgrad

/-- **Equivalence of `H¹` under conformal rescaling.** On a compact manifold, the identity map
induces a continuous linear equivalence between `H¹(WithMetric (g.rescale f hf hf_pos))` and
`H¹(WithMetric g)`. -/
def congrRescale
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x) :
    SobolevH1 I (WithMetric (g.rescale f hf hf_pos)) ≃L[ℝ] SobolevH1 I (WithMetric g) :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (liftSmooth (ofSmooth.comp (compDiffeomorphWithMetricLinear g (g.rescale f hf hf_pos)))
      (exists_norm_ofSmooth_comp_diffeomorphWithMetric_le g hf hf_pos))
    (liftSmooth (ofSmooth.comp (compDiffeomorphWithMetricLinear (g.rescale f hf hf_pos) g))
      (exists_norm_ofSmooth_comp_diffeomorphWithMetric_symm_le g hf hf_pos))
    (ContinuousLinearMap.ext fun w ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      refine induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun v ↦ ?_
      rw [liftSmooth_ofSmooth, LinearMap.comp_apply, liftSmooth_ofSmooth, LinearMap.comp_apply]
      exact congrArg ofSmooth (ContMDiffMap.ext fun x ↦ by simp))
    (ContinuousLinearMap.ext fun w ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      refine induction_on w (isClosed_eq (by fun_prop) (by fun_prop)) fun u ↦ ?_
      rw [liftSmooth_ofSmooth, LinearMap.comp_apply, liftSmooth_ofSmooth, LinearMap.comp_apply]
      exact congrArg ofSmooth (ContMDiffMap.ext fun x ↦ by simp))

@[simp]
theorem congrRescale_ofSmooth
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    (u : C^∞⟮I, WithMetric (g.rescale f hf hf_pos); ℝ⟯) :
    congrRescale g hf hf_pos (ofSmooth u) =
      ofSmooth
        (u.comp (WithMetric.diffeomorphWithMetric g (g.rescale f hf hf_pos) ∞).toContMDiffMap) :=
  liftSmooth_ofSmooth _ _ u

@[simp]
theorem congrRescale_symm_ofSmooth
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    (v : C^∞⟮I, WithMetric g; ℝ⟯) :
    (congrRescale g hf hf_pos).symm (ofSmooth v) =
      ofSmooth
        (v.comp (WithMetric.diffeomorphWithMetric (g.rescale f hf hf_pos) g ∞).toContMDiffMap) :=
  liftSmooth_ofSmooth _ _ v

/-- Pushforward of `riemannianVolume I (WithMetric g)` to `WithMetric (g.rescale f hf hf_pos)` is
dominated by a finite multiple of the rescaled volume. -/
private theorem exists_map_riemannianVolume_le_smul_rescale
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (riemannianVolume I (WithMetric g)).map
          (fun x ↦ WithMetric.toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric) ≤
        C • riemannianVolume I (WithMetric (g.rescale f hf hf_pos)) := by
  let ĝ := g.rescale f hf hf_pos
  let ι : WithMetric g → WithMetric ĝ := fun x ↦ WithMetric.toWithMetric ĝ x.ofWithMetric
  have hι : Measurable ι :=
    (WithMetric.continuous_toWithMetric.comp WithMetric.continuous_ofWithMetric).measurable
  have hfN_pos (y : M) : 0 < f y ^ ((finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos (hf_pos y) _
  let kC : C(M, ℝ) :=
    ⟨_, (hf.continuous.rpow_const fun _ ↦ Or.inr (by positivity)).inv₀ fun y ↦ (hfN_pos y).ne'⟩
  refine ⟨ENNReal.ofReal ‖kC‖, ENNReal.ofReal_ne_top, Measure.le_iff.2 fun s hs ↦ ?_⟩
  rw [Measure.map_apply hι hs, smul_apply, smul_eq_mul, WithMetric.riemannianVolume_rescale,
    Measure.map_apply hι hs, withDensity_apply _ (hι hs)]
  have hm : Measurable fun x : WithMetric g ↦
      ENNReal.ofReal (f x.ofWithMetric ^ ((finrank ℝ E : ℝ) / 2)) :=
    ((hf.continuous.comp WithMetric.continuous_ofWithMetric).measurable.pow_const _).ennreal_ofReal
  rw [← setLIntegral_one, ← lintegral_const_mul _ hm]
  refine setLIntegral_mono (hm.const_mul _) fun x _ ↦ ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg kC), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((inv_mul_cancel₀ (hfN_pos _).ne').symm.trans_le
    (mul_le_mul_of_nonneg_right (kC.apply_le_norm _) (hfN_pos _).le))

/-- **Compatibility of `congrRescale` with `L²`.** Under `congrRescale`, the value in
`L²(WithMetric g)` is almost everywhere the value in `L²(WithMetric (g.rescale f hf hf_pos))`
transported along the identity between the two copies. -/
theorem toLp_congrRescale_ae_eq
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    (w : SobolevH1 I (WithMetric (g.rescale f hf hf_pos))) :
    toLp (congrRescale g hf hf_pos w) =ᵐ[riemannianVolume I (WithMetric g)]
      fun x ↦ toLp w (WithMetric.toWithMetric (g.rescale f hf hf_pos) x.ofWithMetric) := by
  let ĝ := g.rescale f hf hf_pos
  let ι : WithMetric g → WithMetric ĝ := fun x ↦ WithMetric.toWithMetric ĝ x.ofWithMetric
  have hι : Measurable ι :=
    (WithMetric.continuous_toWithMetric.comp WithMetric.continuous_ofWithMetric).measurable
  obtain ⟨C, hC, hmap⟩ := exists_map_riemannianVolume_le_smul_rescale g hf hf_pos
  let L := Lp.compOfMapLeSmul (E := ℝ) (p := 2) ℝ hι.aemeasurable hC hmap
  have heq : toLp (congrRescale g hf hf_pos w) = L (toLp w) := by
    refine induction_on w (isClosed_eq (toLp.continuous.comp (congrRescale g hf hf_pos).continuous)
      (L.continuous.comp toLp.continuous)) fun u ↦ ?_
    rw [congrRescale_ofSmooth, toLp_ofSmooth, toLp_ofSmooth]
    refine Lp.ext ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I (WithMetric g))
        ((u.comp (WithMetric.diffeomorphWithMetric g ĝ ∞).toContMDiffMap :
          C^∞⟮I, WithMetric g; ℝ⟯) : C(WithMetric g, ℝ)),
      Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) hι.aemeasurable hC hmap
        (ContinuousMap.toLp 2 (riemannianVolume I (WithMetric ĝ)) ℝ (u : C(WithMetric ĝ, ℝ))),
      (QuasiMeasurePreserving.of_map_le_smul hι.aemeasurable hmap).ae_eq_comp
        (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I (WithMetric ĝ))
          (u : C(WithMetric ĝ, ℝ)))] with x h1 h2 h3
    rw [h1, h2, h3]; simp [ι]
  exact heq ▸ Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) hι.aemeasurable hC hmap (toLp w)

end Rescale

end TauCeti.Manifold.SobolevH1
