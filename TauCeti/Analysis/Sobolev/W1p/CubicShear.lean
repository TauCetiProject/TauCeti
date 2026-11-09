/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The cubic shear: an `Lᵖ` isometry that is unbounded on `W^{1,p}`

The cubic shear `φ(x, y) = (x, y + x³)` of the plane `ℝ²` is a smooth diffeomorphism with
Jacobian determinant `1`, so it preserves Lebesgue measure (`TauCeti.measurePreserving_cubicShear`)
and pullback `f ↦ f ∘ φ` is a linear isometry of every `Lᵖ(ℝ²)`, `1 ≤ p ≤ ∞`
(Mathlib's `MeasureTheory.Lp.compMeasurePreservingₗᵢ`).

Its derivative is not bounded, and pullback is not bounded on the first-order Sobolev space
`W^{1,p}(ℝ²)` for any `1 ≤ p ≤ ∞` (`TauCeti.W1p.not_exists_bound_comp_cubicShear`); in particular
no bounded operator on `W^{1,p}(ℝ²)` acts by `u ↦ u ∘ φ`
(`TauCeti.W1p.not_exists_continuousLinearMap_comp_cubicShear`). The reason is the chain rule
`∂ₓ(f ∘ φ) = (∂ₓf) ∘ φ + 3x² (∂_y f) ∘ φ` (`TauCeti.fderiv_comp_cubicShear_apply_single_zero`):
translating a fixed smooth compactly supported `f` with `∂_y f ≠ 0` to `x ≈ k` leaves its
`W^{1,p}` norm unchanged, while the `Lᵖ` norm of `∂ₓ(f ∘ φ)` grows like `3k²`.

So a bound on the Jacobian determinant alone controls `Lᵖ` norms but not Sobolev norms: the
coordinate-change estimates for Sobolev, Bessel-potential and Besov spaces on `ℝⁿ` need
uniform bounds on the derivatives of the diffeomorphism. The derivative of `φ` is bounded on
bounded sets, so for a bounded open `V` pullback is bounded from `W^{1,p}(V)` to `W^{1,p}(φ⁻¹V)`
(`TauCeti.W1p.compMeasurePreservingL`); the failure is a phenomenon at infinity.

## Main declarations

* `TauCeti.cubicShear`: the homeomorphism `(x, y) ↦ (x, y + x³)` of `EuclideanSpace ℝ (Fin 2)`.
* `TauCeti.measurePreserving_cubicShear`: it preserves Lebesgue measure.
* `TauCeti.fderiv_cubicShear_apply`: its derivative `h ↦ h + 3x² h₀ e₁`.
* `TauCeti.fderiv_comp_cubicShear_apply_single_zero`: the chain rule for `∂ₓ(f ∘ φ)`.
* `TauCeti.W1p.not_exists_bound_comp_cubicShear`: no inequality `‖u ∘ φ‖ ≤ C ‖u‖` holds on
  `W^{1,p}(ℝ²)`.
* `TauCeti.W1p.not_exists_continuousLinearMap_comp_cubicShear`: pullback by `φ` is not a bounded
  operator on `W^{1,p}(ℝ²)`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Gradient ContDiff Topology

/-- The cubic shear `(x, y) ↦ (x, y + x³)` of the Euclidean plane, a homeomorphism with inverse
`(x, y) ↦ (x, y - x³)`. -/
def cubicShear : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) where
  toFun v := v + (v 0 ^ 3) • EuclideanSpace.single 1 1
  invFun v := v - (v 0 ^ 3) • EuclideanSpace.single 1 1
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem cubicShear_apply (v : EuclideanSpace ℝ (Fin 2)) :
    cubicShear v = v + (v 0 ^ 3) • EuclideanSpace.single 1 1 :=
  (rfl)

theorem cubicShear_symm_apply (v : EuclideanSpace ℝ (Fin 2)) :
    cubicShear.symm v = v - (v 0 ^ 3) • EuclideanSpace.single 1 1 :=
  (rfl)

@[simp]
theorem cubicShear_apply_zero (v : EuclideanSpace ℝ (Fin 2)) : cubicShear v 0 = v 0 := by
  simp [cubicShear_apply]

@[simp]
theorem cubicShear_apply_one (v : EuclideanSpace ℝ (Fin 2)) :
    cubicShear v 1 = v 1 + v 0 ^ 3 := by
  simp [cubicShear_apply]

@[simp]
theorem cubicShear_symm_apply_zero (v : EuclideanSpace ℝ (Fin 2)) : cubicShear.symm v 0 = v 0 := by
  simp [cubicShear_symm_apply]

@[simp]
theorem cubicShear_symm_apply_one (v : EuclideanSpace ℝ (Fin 2)) :
    cubicShear.symm v 1 = v 1 - v 0 ^ 3 := by
  simp [cubicShear_symm_apply]

/-- The derivative of the cubic shear at `v` is `h ↦ h + 3 x² h₀ e₁`, where `x = v₀`. -/
theorem hasFDerivAt_cubicShear (v : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt cubicShear
      (ContinuousLinearMap.id ℝ _ + ((3 * v 0 ^ 2) • EuclideanSpace.proj 0).smulRight
        (EuclideanSpace.single 1 1)) v := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := v)).pow 3
  have hφ : (cubicShear : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) =
      fun w => w + EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) w ^ 3 • EuclideanSpace.single 1 1 :=
    funext fun w => by simp [cubicShear_apply]
  rw [hφ]
  refine ((hasFDerivAt_id v).add
    (h.smul_const (EuclideanSpace.single 1 (1 : ℝ)))).congr_fderiv ?_
  ext w : 1
  simp [nsmul_eq_mul]

theorem fderiv_cubicShear_apply (v h : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ cubicShear v h = h + (3 * v 0 ^ 2 * h 0) • EuclideanSpace.single 1 1 := by
  simp [(hasFDerivAt_cubicShear v).fderiv, mul_assoc]

theorem contDiff_cubicShear {n : WithTop ℕ∞} : ContDiff ℝ n cubicShear :=
  contDiff_id.add (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.pow 3).smul contDiff_const)

/-- The cubic shear preserves Lebesgue measure: in coordinates it is the skew product of the
identity with the translations `y ↦ y + x³`. -/
theorem measurePreserving_cubicShear : MeasurePreserving cubicShear := by
  have hS : MeasurePreserving (fun q : ℝ × ℝ => (q.1, q.2 + q.1 ^ 3)) := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).skew_product (g := fun x y => y + x ^ 3) (by fun_prop)
      (ae_of_all _ fun x => (measurePreserving_add_right volume (x ^ 3)).map_eq)
  have h := (PiLp.volume_preserving_toLp (Fin 2)).comp <|
    (volume_preserving_finTwoArrow ℝ).symm.comp <| hS.comp <|
      (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  convert h using 1
  funext v
  ext i
  fin_cases i <;> simp [MeasurableEquiv.finTwoArrow, cubicShear_apply]

/-- **Chain rule for the cubic shear.** The derivative of `f ∘ φ` in the first coordinate direction
is `∂ₓ(f ∘ φ) = (∂ₓf) ∘ φ + 3x² (∂_y f) ∘ φ`: the factor `3x²` is unbounded. -/
theorem fderiv_comp_cubicShear_apply_single_zero {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {v : EuclideanSpace ℝ (Fin 2)} (hf : DifferentiableAt ℝ f (cubicShear v)) :
    fderiv ℝ (f ∘ cubicShear) v (EuclideanSpace.single 0 1) =
      fderiv ℝ f (cubicShear v) (EuclideanSpace.single 0 1) +
        3 * v 0 ^ 2 * fderiv ℝ f (cubicShear v) (EuclideanSpace.single 1 1) := by
  rw [fderiv_comp v hf (hasFDerivAt_cubicShear v).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_cubicShear_apply]
  simp

/-! ### Unboundedness on `W^{1,p}` -/

/-- The pointwise form of the growth estimate: for `f` supported in the ball of radius `R` and
`R ≤ k`, translating by `k` in the first coordinate and pulling back by the cubic shear gives
`3 (k - R)² |∂_y f| ≤ ‖∇g‖ + ‖∇f‖` at the shifted point, where `g = f ∘ (cubicShear - k e₀)`.
Only differentiability of `f` at the shifted point is needed. -/
private theorem norm_smul_fderiv_single_le {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    {R k : ℝ} (hR : tsupport f ⊆ Metric.closedBall 0 R) (hk : R ≤ k)
    (w : EuclideanSpace ℝ (Fin 2))
    (hf : DifferentiableAt ℝ f (cubicShear w - k • EuclideanSpace.single 0 1)) :
    ‖(3 * (k - R) ^ 2) • fderiv ℝ f (cubicShear w - k • EuclideanSpace.single 0 1)
        (EuclideanSpace.single 1 1)‖ ≤
      ‖∇ (fun w => f (cubicShear w - k • EuclideanSpace.single 0 1)) w‖ +
        ‖∇ f (cubicShear w - k • EuclideanSpace.single 0 1)‖ := by
  set c : EuclideanSpace ℝ (Fin 2) := k • EuclideanSpace.single 0 1
  set T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w => cubicShear w - c
  set D := fderiv ℝ f (T w) (EuclideanSpace.single 1 1)
  have hchain : fderiv ℝ (fun w => f (T w)) w (EuclideanSpace.single 0 1) =
      fderiv ℝ f (T w) (EuclideanSpace.single 0 1) + 3 * w 0 ^ 2 * D := by
    have h := fderiv_comp_cubicShear_apply_single_zero (f := fun z => f (z - c)) (v := w)
      ((differentiableAt_comp_sub c).2 hf)
    simp only [fderiv_comp_sub] at h
    exact h
  have hle : ∀ L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ, ∀ i : Fin 2,
      |L (EuclideanSpace.single i 1)| ≤ ‖L‖ := fun L i => by
    simpa [PiLp.norm_single] using L.le_opNorm (EuclideanSpace.single i 1)
  have hgrowth : (3 * (k - R) ^ 2) * |D| ≤ 3 * w 0 ^ 2 * |D| := by
    rcases eq_or_ne D 0 with hD0 | hD0
    · simp [hD0]
    have hmem : T w ∈ tsupport f :=
      support_fderiv_subset ℝ fun h => hD0 (by simp [D, h])
    have hTw : |w 0 - k| ≤ R := by
      have := (PiLp.norm_apply_le (T w) 0).trans (mem_closedBall_zero_iff.1 (hR hmem))
      simpa [T, c] using this
    have hw : k - R ≤ w 0 := by linarith [neg_abs_le (w 0 - k)]
    gcongr
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_gradient_eq_norm_fderiv,
    norm_gradient_eq_norm_fderiv]
  refine hgrowth.trans ?_
  calc 3 * w 0 ^ 2 * |D| = |fderiv ℝ (fun w => f (T w)) w (EuclideanSpace.single 0 1) -
        fderiv ℝ f (T w) (EuclideanSpace.single 0 1)| := by
        rw [hchain, add_sub_cancel_left, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * w 0 ^ 2)]
    _ ≤ _ := (abs_sub _ _).trans (add_le_add (hle _ 0) (hle _ 0))

section Sobolev

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The growth estimate.** Translate a `C¹` function `f` supported in the ball of radius `R` by
`k ≥ R` in the first coordinate and pull it back by the cubic shear. The `Lᵖ` norm of the gradient
of the result, plus that of `∇f`, is at least `3 (k - R)²` times the `Lᵖ` norm of `∂_y f`. -/
private theorem ofReal_mul_eLpNorm_fderiv_le {f : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ContDiff ℝ 1 f) {R k : ℝ} (hR : tsupport f ⊆ Metric.closedBall 0 R) (hk : R ≤ k) :
    ENNReal.ofReal (3 * (k - R) ^ 2) *
        eLpNorm (fun z => fderiv ℝ f z (EuclideanSpace.single 1 1)) p volume ≤
      eLpNorm (∇ fun w => f (cubicShear w - k • EuclideanSpace.single 0 1)) p volume +
        eLpNorm (∇ f) p volume := by
  set c : EuclideanSpace ℝ (Fin 2) := k • EuclideanSpace.single 0 1
  set T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun w => cubicShear w - c
  have hT : MeasurePreserving T := (measurePreserving_sub_right volume c).comp
    measurePreserving_cubicShear
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hD : Continuous fun z => fderiv ℝ f z (EuclideanSpace.single 1 1) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpt : ∀ w, ‖(3 * (k - R) ^ 2) • fderiv ℝ f (T w) (EuclideanSpace.single 1 1)‖ ≤
      ‖∇ (fun w => f (T w)) w‖ + ‖∇ f (T w)‖ := fun w => norm_smul_fderiv_single_le hR hk w (hfd _)
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => fderiv ℝ f z (EuclideanSpace.single 1 1)
  calc ENNReal.ofReal (3 * (k - R) ^ 2) * eLpNorm G p volume
      = ‖3 * (k - R) ^ 2‖ₑ * eLpNorm (G ∘ T) p volume := by
        rw [Real.enorm_eq_ofReal (by positivity),
          eLpNorm_comp_measurePreserving hD.aestronglyMeasurable hT]
    _ = eLpNorm ((3 * (k - R) ^ 2) • (G ∘ T)) p volume := (eLpNorm_const_smul _ _ _ _).symm
    _ ≤ eLpNorm (fun w => ‖∇ (fun w => f (T w)) w‖ + ‖∇ f (T w)‖) p volume :=
        eLpNorm_mono_real (((hD.comp (continuous_sub_right c |>.comp
          cubicShear.continuous)).aestronglyMeasurable).const_smul _) hpt
    _ ≤ eLpNorm (fun w => ‖∇ (fun w => f (T w)) w‖) p volume +
          eLpNorm (fun w => ‖∇ f (T w)‖) p volume :=
        eLpNorm_add_le (f := fun w => ‖∇ (fun w => f (T w)) w‖)
          (g := fun w => ‖∇ f (T w)‖) Fact.out
    _ = _ := by
        -- `eLpNorm_comp_measurePreserving` rewrites `eLpNorm (g ∘ T)` syntactically, so the
        -- integrand `fun w => ‖∇ f (T w)‖` is first exhibited as `(fun z => ‖∇ f z‖) ∘ T`.
        rw [eLpNorm_norm _ (measurable_gradient _).aestronglyMeasurable,
          show (fun w => ‖∇ f (T w)‖) = (fun z => ‖∇ f z‖) ∘ T from rfl,
          eLpNorm_comp_measurePreserving (measurable_gradient f).norm.aestronglyMeasurable hT,
          eLpNorm_norm _ (measurable_gradient f).aestronglyMeasurable]

/-- A smooth compactly supported function on the plane, supported in the closed ball of radius
`2`, whose derivative in the second coordinate direction is `1` at the origin. -/
private theorem exists_testFunction : ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ f ∧
    HasCompactSupport f ∧ tsupport f ⊆ Metric.closedBall 0 2 ∧
    fderiv ℝ f 0 (EuclideanSpace.single 1 1) = 1 := by
  let β : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) := ⟨1, 2, one_pos, one_lt_two⟩
  let y : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1
  refine ⟨fun w => y w * β w, y.contDiff.mul β.contDiff, β.hasCompactSupport.mul_left,
    (tsupport_mul_subset_right).trans β.tsupport_eq.subset, ?_⟩
  have hev : (fun w => y w * β w) =ᶠ[𝓝 0] y :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds 0 one_pos) fun w hw => by
      simp [β.one_of_mem_closedBall hw]
  rw [hev.fderiv_eq, y.fderiv]
  simp [y]

/-- **The lower bound from a putative pullback estimate.** If `‖u ∘ φ‖ ≤ C ‖u‖` on `W^{1,p}(ℝ²)`,
then testing it on the translate by `k e₀` of a smooth function `f` supported in the ball of
radius `R ≤ k` bounds `3 (k - R)²` times the `Lᵖ` norm of `∂_y f` independently of `k`. -/
private theorem mul_toReal_eLpNorm_fderiv_le_of_bound {C : ℝ}
    (hC : ∀ u v : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ p,
      W1p.value v =ᵐ[volume] W1p.value u ∘ cubicShear → ‖v‖ ≤ C * ‖u‖)
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) {R k : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) (hk : R ≤ k) :
    3 * (k - R) ^ 2 *
        (eLpNorm (fun z => fderiv ℝ f z (EuclideanSpace.single 1 1)) p volume).toReal ≤
      |C| * ((eLpNorm f p volume).toReal + (eLpNorm (∇ f) p volume).toReal) +
        (eLpNorm (∇ f) p volume).toReal := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  set c : EuclideanSpace ℝ (Fin 2) := k • EuclideanSpace.single 0 1
  have hτ : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin 2) => w - c) :=
    measurePreserving_sub_right volume c
  -- The translate `fk` of `f` and its pullback `gk` by the shear.
  let fk : EuclideanSpace ℝ (Fin 2) → ℝ := fun w => f (w - c)
  have hfk : ContDiff ℝ ∞ fk := hf.comp (contDiff_id.sub contDiff_const)
  have hfks : HasCompactSupport fk := hfs.comp_homeomorph (Homeomorph.subRight c)
  let gk : EuclideanSpace ℝ (Fin 2) → ℝ := fun w => f (cubicShear w - c)
  have hgk : ContDiff ℝ 1 gk := (hfk.comp contDiff_cubicShear).of_le (by simp)
  have hgks : HasCompactSupport gk := hfks.comp_homeomorph cubicShear
  obtain ⟨u, hu, -, hu0, hu1⟩ :=
    W1p.exists_value_gradient_ae_eq_of_hasCompactSupport (mu := volume) (p := p)
      (hfk.of_le (by simp)) hfks
  obtain ⟨v, hv, -, -, hv1⟩ :=
    W1p.exists_value_gradient_ae_eq_of_hasCompactSupport (mu := volume) (p := p) hgk hgks
  -- Translation does not change the norms of `u`.
  have hu0' : ‖W1p.value u‖ = (eLpNorm f p volume).toReal := by
    -- `eLpNorm_comp_measurePreserving` rewrites `eLpNorm (g ∘ τ)` syntactically, so the
    -- translate `fk` is first unfolded to the composition `f ∘ fun w => w - c`.
    rw [hu0, show fk = f ∘ fun w => w - c from rfl,
      eLpNorm_comp_measurePreserving hf.continuous.aestronglyMeasurable hτ]
  have hu1' : ‖W1p.gradient u‖ = (eLpNorm (∇ f) p volume).toReal := by
    have : ∇ fk = ∇ f ∘ fun w => w - c := funext fun w => by
      apply (InnerProductSpace.toDual ℝ _).injective
      rw [Function.comp_apply, toDual_gradient, toDual_gradient]
      exact fderiv_comp_sub _
    rw [hu1, this, eLpNorm_comp_measurePreserving
      (measurable_gradient f).aestronglyMeasurable hτ]
  -- The hypothesis bounds the gradient of `v = u ∘ φ`.
  have hvnorm : ‖W1p.gradient v‖ ≤
      |C| * ((eLpNorm f p volume).toReal + (eLpNorm (∇ f) p volume).toReal) :=
    calc ‖W1p.gradient v‖ ≤ ‖v‖ := W1p.norm_gradient_le v
      _ ≤ C * ‖u‖ := hC u v
        (hv.trans (measurePreserving_cubicShear.quasiMeasurePreserving.ae_eq_comp hu).symm)
      _ ≤ |C| * ‖u‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg u)
      _ ≤ _ := by
        gcongr
        rw [← hu0', ← hu1']
        exact W1p.norm_le_norm_value_add_norm_gradient u
  -- The growth estimate bounds it from below.
  have hgtop : eLpNorm (∇ gk) p volume ≠ ⊤ := (hgks.memLp_gradient hgk).eLpNorm_ne_top
  have hF₁top : eLpNorm (∇ f) p volume ≠ ⊤ := (hfs.memLp_gradient hf1).eLpNorm_ne_top
  have hkey := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hgtop, hF₁top⟩)
    (ofReal_mul_eLpNorm_fderiv_le (p := p) hf1 hR hk)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_add hgtop hF₁top, ← hv1] at hkey
  linarith

/-- **Pullback by the cubic shear is unbounded on `W^{1,p}(ℝ²)`.** For every `1 ≤ p ≤ ∞` there is
no constant `C` with `‖u ∘ φ‖ ≤ C ‖u‖` for all `u` in `W^{1,p}(ℝ²)` such that `u ∘ φ` is again in
`W^{1,p}(ℝ²)`, although `φ` preserves Lebesgue measure. -/
theorem W1p.not_exists_bound_comp_cubicShear :
    ¬ ∃ C : ℝ, ∀ u v : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ p,
      W1p.value v =ᵐ[volume] W1p.value u ∘ cubicShear → ‖v‖ ≤ C * ‖u‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨f, hf, hfs, hR, hf0⟩ := exists_testFunction
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => fderiv ℝ f z (EuclideanSpace.single 1 1)
  have hG : Continuous G := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  -- The `Lᵖ` norm `a` of `∂_y f` is positive and finite.
  have hAtop : eLpNorm G p volume ≠ ⊤ :=
    (hG.memLp_of_hasCompactSupport (hfs.fderiv_apply (𝕜 := ℝ) _)).eLpNorm_ne_top
  have hA0 : eLpNorm G p volume ≠ 0 := by
    rw [Ne, eLpNorm_eq_zero_iff (zero_lt_one.trans_le Fact.out).ne',
      Continuous.ae_eq_iff_eq volume hG continuous_zero]
    intro h
    simpa [G, hf0] using congrFun h 0
  set a := (eLpNorm G p volume).toReal
  have ha : 0 < a := ENNReal.toReal_pos hA0 hAtop
  set b := |C| * ((eLpNorm f p volume).toReal + (eLpNorm (∇ f) p volume).toReal) +
    (eLpNorm (∇ f) p volume).toReal
  have hb : 0 ≤ b := by positivity
  -- The lower bound `3 (k - 2)² a ≤ b` for every `k ≥ 2` fails for `k = 2 + M` with `M` large.
  set M := b / (3 * a) + 1
  have hM : 1 ≤ M := by
    have : 0 ≤ b / (3 * a) := by positivity
    linarith
  have h := mul_toReal_eLpNorm_fderiv_le_of_bound hC hf hfs hR (k := 2 + M) (by linarith)
  rw [add_sub_cancel_left] at h
  have h3 : 3 * a * M = b + 3 * a := by
    simp only [M, mul_add, mul_one]
    field_simp
  have h4 : 3 * a * M ≤ 3 * a * M ^ 2 :=
    mul_le_mul_of_nonneg_left (le_self_pow₀ hM two_ne_zero) (by positivity)
  linarith

/-- **Pullback by the cubic shear is not a bounded operator on `W^{1,p}(ℝ²)`**, for any
`1 ≤ p ≤ ∞`: no continuous linear map `T` on `W^{1,p}(ℝ²)` satisfies `T u = u ∘ φ`. -/
theorem W1p.not_exists_continuousLinearMap_comp_cubicShear :
    ¬ ∃ T : W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ p →L[ℝ]
        W1p (volume : Measure (EuclideanSpace ℝ (Fin 2))) ⊤ p,
      ∀ u, W1p.value (T u) =ᵐ[volume] W1p.value u ∘ cubicShear := by
  rintro ⟨T, hT⟩
  refine W1p.not_exists_bound_comp_cubicShear (p := p) ⟨‖T‖, fun u v huv => ?_⟩
  have : v = T u := W1p.ext_value (Lp.ext (ae_restrict_of_ae (huv.trans (hT u).symm)))
  rw [this]
  exact T.le_opNorm u

end Sobolev

end TauCeti
