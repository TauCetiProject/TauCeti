/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# Derivatives and norms

At a local extremum of the norm of a map, its derivative is orthogonal to its value. In
particular, the derivative of a map into a sphere is tangent to the sphere. Away from the origin,
a vanishing derivative of a norm-composition forces the one-dimensional profile derivative to
vanish, and a radial function on a real inner product space has Fréchet derivatives of equal
operator norm at points of equal norm (`TauCeti.norm_fderiv_eq_of_norm_eq`). Moreover, along any
unit ray a radial function's one-dimensional derivative is bounded in norm by the operator norm of
its Fréchet derivative (`TauCeti.norm_deriv_comp_smul_le`, `TauCeti.deriv_radial_sq_le`), and a
function that is nonincreasing in the norm has derivatives of equal norm at any two points of one
level where they do not vanish (`TauCeti.norm_fderiv_eq_of_antitone_norm`). Likewise, the
`0`-homogeneous radial extension `TauCeti.sphereExtend f` has vanishing radial derivative everywhere
(`TauCeti.fderiv_sphereExtend_self`). The norm itself, being `1`-Lipschitz, has derivative of norm
at most `1` everywhere (`TauCeti.norm_fderiv_norm_le`). In any real normed space, a curve whose
derivative is a multiple `c • f a` of its value has norm with derivative
`c * ‖f a‖` (`HasDerivAt.norm_of_smul_self`).

The squared norm of the derivative of a map from `ℂ` to a Euclidean space is at most twice the
sum of the squared partial derivatives of its components along `1` and `I`
(`TauCeti.norm_fderiv_sq_le_two_mul_sum_sq`). The squared gradient of a real function on `ℂ` is
the sum of its squared partial derivatives along `1` and `I`
(`TauCeti.norm_gradient_sq_eq_fderiv_one_sq_add_fderiv_I_sq`).

The function `y ↦ √(a - ‖y‖²)`, whose graph over the ball of radius `√a` is a hemisphere, has
derivative `-(√(a - ‖x‖²))⁻¹ ⟪x, ·⟫` wherever `a - ‖x‖² ≠ 0`; in particular it is flat at the
origin. Over the open unit ball the height `√(1 - ‖x‖²)` of the unit hemisphere is positive
(`TauCeti.sqrt_one_sub_norm_sq_pos`).
-/

public section

open scoped Gradient RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Away from the origin, a vanishing totalized derivative of a radial function forces its
one-dimensional profile derivative to vanish. The profile need not be differentiable. -/
theorem deriv_eq_zero_of_fderiv_comp_norm_eq_zero {v : ℝ → E} {x : F} (hx : x ≠ 0)
    (hcrit : fderiv ℝ (fun y : F ↦ v ‖y‖) x = 0) : deriv v ‖x‖ = 0 := by
  by_contra hv
  have hn : DifferentiableAt ℝ (‖·‖) x := differentiableAt_id.norm ℝ hx
  -- The chain rule, evaluated at `x`: `‖x‖ • deriv v ‖x‖ = 0` since `fderiv ℝ (‖·‖) x x = ‖x‖`.
  have h := congr($(((differentiableAt_of_deriv_ne_zero hv).hasDerivAt.hasFDerivAt.comp x
    hn.hasFDerivAt).fderiv.symm.trans hcrit) x)
  exact hv (by simpa [hn.fderiv_norm_self, hx] using h)

/-- A radial function `v : F → E` on a real inner product space has Fréchet derivatives of equal
operator norm at points of equal norm, without any differentiability hypothesis on `v`. -/
theorem norm_fderiv_eq_of_norm_eq {v : F → E} (hrad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {x y : F} (hxy : ‖x‖ = ‖y‖) : ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖ := by
  let R := (ℝ ∙ (x - y))ᗮ.reflection
  have hcomp : v ∘ R = v := funext fun z ↦ hrad (R z) z (R.norm_map z)
  have h := R.toContinuousLinearEquiv.comp_right_fderiv (f := v) (x := x)
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, hcomp, Submodule.reflection_sub hxy] at h
  have hnorm := congrArg norm h
  simpa only [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] using hnorm

/-- Along a unit ray `s ↦ s • e₀` at `r > 0`, the derivative of a radial function `v : F → E`
on a real inner product space has norm bounded by `‖fderiv ℝ v (r • e₀)‖`. -/
theorem norm_deriv_comp_smul_le {v : F → E} (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {e₀ : F} (he₀ : ‖e₀‖ = 1) {r : ℝ} (hr : 0 < r) :
    ‖deriv (fun s : ℝ ↦ v (s • e₀)) r‖ ≤ ‖fderiv ℝ v (r • e₀)‖ := by
  set g : ℝ → E := fun s ↦ v (s • e₀)
  by_cases hg : DifferentiableAt ℝ g r
  · have hre₀_ne : r • e₀ ≠ 0 := fun h0 ↦ by
      have := congrArg norm h0
      simp [norm_smul, abs_of_pos hr, he₀, hr.ne'] at this
    have hv_eq : v = g ∘ norm := funext fun x ↦ hv_rad x (‖x‖ • e₀) (by simp [norm_smul, he₀])
    have hnorm_r : ‖r • e₀‖ = r := by simp [norm_smul, abs_of_pos hr, he₀]
    have hv_diff : DifferentiableAt ℝ v (r • e₀) :=
      hv_eq ▸ (hnorm_r ▸ hg).comp (r • e₀) (differentiableAt_id.norm ℝ hre₀_ne)
    have hray : HasDerivAt (fun s : ℝ ↦ s • e₀) e₀ r := by
      simpa only [id_eq, one_smul, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] using
        ((hasDerivAt_id r).hasFDerivAt.smul_const e₀).hasDerivAt
    have hg_deriv : HasDerivAt g (fderiv ℝ v (r • e₀) e₀) r :=
      hv_diff.hasFDerivAt.comp_hasDerivAt r hray
    rw [hg_deriv.deriv]
    simpa only [he₀, mul_one] using (fderiv ℝ v (r • e₀)).le_opNorm e₀
  · rw [deriv_zero_of_not_differentiableAt hg, norm_zero]
    exact norm_nonneg _

/-- Along a unit ray `s ↦ s • e₀` at `r > 0`, the squared derivative of a real radial function
`v : F → ℝ` on a real inner product space is at most `‖fderiv ℝ v (r • e₀)‖ ^ 2`. -/
theorem deriv_radial_sq_le {v : F → ℝ} (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {e₀ : F} (he₀ : ‖e₀‖ = 1) {r : ℝ} (hr : 0 < r) :
    (deriv (fun s : ℝ ↦ v (s • e₀)) r) ^ 2 ≤ ‖fderiv ℝ v (r • e₀)‖ ^ 2 :=
  calc (deriv (fun s : ℝ ↦ v (s • e₀)) r) ^ 2
      = ‖deriv (fun s : ℝ ↦ v (s • e₀)) r‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    _ ≤ ‖fderiv ℝ v (r • e₀)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_deriv_comp_smul_le hv_rad he₀ hr) 2

/-- **Gradients of radially nonincreasing functions.** If `v` is nonincreasing in the norm, then
its totalized derivatives have the same norm at any two points of the same level of `v` at which
they do not vanish. -/
theorem norm_fderiv_eq_of_antitone_norm {v : F → ℝ} (hv : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x)
    {x y : F} (hx : fderiv ℝ v x ≠ 0) (hy : fderiv ℝ v y ≠ 0) (hxy : v x = v y) :
    ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖ := by
  -- A point strictly inside the sphere through a point of the same level is a local minimum.
  have hmin {a b : F} (hab : ‖a‖ < ‖b‖) (heq : v a = v b) : fderiv ℝ v a = 0 := by
    refine IsLocalMin.fderiv_eq_zero ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hab)] with z hz
    rw [heq]
    exact hv z b (mem_ball_zero_iff.1 hz).le
  have hnorm : ‖x‖ = ‖y‖ := by
    rcases lt_trichotomy ‖x‖ ‖y‖ with h | h | h
    · exact absurd (hmin h hxy) hx
    · exact h
    · exact absurd (hmin h hxy.symm) hy
  exact norm_fderiv_eq_of_norm_eq (fun a b h ↦ le_antisymm (hv b a h.ge) (hv a b h.le)) hnorm

/-- The derivative of the norm has norm at most `1` at every point, including the points where the
norm is not differentiable and its derivative is `0` by definition. -/
theorem norm_fderiv_norm_le (x : E) : ‖fderiv ℝ (‖·‖ : E → ℝ) x‖ ≤ 1 := by
  simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := E))

/-- At a local extremum `w` of `‖ψ‖`, the Fréchet derivative of `ψ` is orthogonal to `ψ w`. This
covers a map whose norm is constant near `w`: the derivative of a map into a sphere is tangent to
the sphere. At nondifferentiable points, the Fréchet derivative is zero by definition. -/
theorem _root_.IsLocalExtr.inner_fderiv_eq_zero {ψ : E → F} {w : E}
    (hψ : IsLocalExtr (fun y ↦ ‖ψ y‖) w) (u : E) :
    ⟪ψ w, fderiv ℝ ψ w u⟫ = 0 := by
  by_cases hd : DifferentiableAt ℝ ψ w
  · -- Squaring is monotone on `[0, ∞)`, so `‖ψ‖ ^ 2` also has a local extremum at `w`.
    have hsq : IsLocalExtr (fun y ↦ ‖ψ y‖ ^ 2) w := hψ.elim
      (fun h ↦ IsMinFilter.isExtrFilter <| h.mono fun _ hy ↦ pow_le_pow_left₀ (norm_nonneg _) hy 2)
      (fun h ↦ IsMaxFilter.isExtrFilter <| h.mono fun _ hy ↦ pow_le_pow_left₀ (norm_nonneg _) hy 2)
    -- Fermat's theorem: the derivative `2 ⟪ψ w, fderiv ℝ ψ w ·⟫` of `‖ψ‖ ^ 2` vanishes at `w`.
    simpa using congr($(IsLocalExtr.hasFDerivAt_eq_zero hsq hd.hasFDerivAt.norm_sq) u)
  · simp [fderiv_zero_of_not_differentiableAt hd]

/-- If a curve `f` has derivative `c • f a` at `a`, so that it moves radially to first order, then
its norm has derivative `c * ‖f a‖` at `a`. The norm need not come from an inner product. -/
theorem _root_.HasDerivAt.norm_of_smul_self {f : ℝ → E} {a c : ℝ} (hf : HasDerivAt f (c • f a) a) :
    HasDerivAt (fun t ↦ ‖f t‖) (c * ‖f a‖) a := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  refine (Asymptotics.IsBigO.of_bound' ?_).trans_isLittleO hf
  -- Near `0`, `1 + t * c > 0`, so `‖(1 + t * c) • f a‖ = (1 + t * c) * ‖f a‖`.
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t * c :=
    continuousAt_const.eventually_lt (by fun_prop) (by simp)
  filter_upwards [hpos] with t ht
  calc ‖‖f (a + t)‖ - ‖f a‖ - t • (c * ‖f a‖)‖ = |‖f (a + t)‖ - ‖(1 + t * c) • f a‖| := by
        rw [norm_smul, Real.norm_of_nonneg ht.le, Real.norm_eq_abs]
        ring_nf
    _ ≤ ‖f (a + t) - (1 + t * c) • f a‖ := abs_norm_sub_norm_le _ _
    _ = ‖f (a + t) - f a - t • c • f a‖ := by congr 1; module

/-- The squared operator norm of the derivative of a map from `ℂ` to a Euclidean space is at most
twice the sum, over the components, of the squared partial derivatives along `1` and `I`. -/
theorem norm_fderiv_sq_le_two_mul_sum_sq {ι : Type*} [Fintype ι] (u : ℂ → EuclideanSpace ℝ ι)
    (z : ℂ) :
    ‖fderiv ℝ u z‖ ^ 2 ≤
      2 * ∑ i, (fderiv ℝ (fun w ↦ u w i) z 1 ^ 2 + fderiv ℝ (fun w ↦ u w i) z Complex.I ^ 2) := by
  by_cases hu : DifferentiableAt ℝ u z
  swap
  · rw [fderiv_zero_of_not_differentiableAt hu, norm_zero, zero_pow two_ne_zero]
    positivity
  have hD := (fderiv ℝ u z).opNorm_sq_le_card_mul_sum_norm_apply_sq_orthonormalBasis
    Complex.orthonormalBasisOneI
  simp only [Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hD
  -- The squared norm of a directional derivative is the sum over the components.
  have hcomp (v : ℂ) : ‖fderiv ℝ u z v‖ ^ 2 = ∑ i, fderiv ℝ (fun w ↦ u w i) z v ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h : HasFDerivAt (fun w ↦ u w i) ((EuclideanSpace.proj i).comp (fderiv ℝ u z)) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hu.hasFDerivAt
    rw [h.fderiv]
    rfl
  rwa [hcomp, hcomp, ← Finset.sum_add_distrib] at hD

/-- The squared gradient of a function on `ℂ` is the sum of its squared partial derivatives along
`1` and `I`. -/
theorem norm_gradient_sq_eq_fderiv_one_sq_add_fderiv_I_sq (f : ℂ → ℝ) (z : ℂ) :
    ‖∇ f z‖ ^ 2 = fderiv ℝ f z 1 ^ 2 + fderiv ℝ f z Complex.I ^ 2 := by
  rw [← Complex.orthonormalBasisOneI.sum_sq_inner_left]
  simp [Fin.sum_univ_two, inner_gradient_left]

/-- The hemisphere function `y ↦ √(a - ‖y‖²)` has derivative `-(√(a - ‖x‖²))⁻¹ ⟪x, ·⟫` at every
point `x` with `a - ‖x‖² ≠ 0`. -/
theorem hasFDerivAt_sqrt_sub_norm_sq {a : ℝ} {x : F} (hx : a - ‖x‖ ^ 2 ≠ 0) :
    HasFDerivAt (fun y : F ↦ √(a - ‖y‖ ^ 2)) (-(√(a - ‖x‖ ^ 2))⁻¹ • innerSL ℝ x) x := by
  refine ((((hasFDerivAt_id x).norm_sq).const_sub a).sqrt hx).congr_fderiv ?_
  ext y
  simp only [id_eq, one_div, mul_inv_rev, ContinuousLinearMap.comp_id, smul_neg, neg_apply,
    smul_apply, coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, neg_smul, neg_inj]
  ring

/-- Over the open unit ball the height `√(1 - ‖x‖²)` of the unit hemisphere is positive. -/
theorem sqrt_one_sub_norm_sq_pos {G : Type*} [SeminormedAddCommGroup G] {x : G} (hx : ‖x‖ < 1) :
    0 < √(1 - ‖x‖ ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith [norm_nonneg x])

/-- The Fréchet derivative of `y ↦ ‖y - x₀‖ ^ 2` at `x` is `2 • innerSL ℝ (x - x₀)`. -/
theorem hasFDerivAt_norm_sq_sub (x₀ x : F) :
    HasFDerivAt (fun y => ‖y - x₀‖ ^ 2) (2 • innerSL ℝ (x - x₀)) x := by
  simpa using ((hasFDerivAt_id x).sub_const x₀).norm_sq

/-- The radial directional derivative of `sphereExtend f` at `x` along `x` vanishes unconditionally,
as `sphereExtend f` is constant on positive rays. -/
@[simp]
theorem fderiv_sphereExtend_self {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Metric.sphere (0 : E) 1 → G) (x : E) :
    fderiv ℝ (sphereExtend f) x x = 0 := by
  by_cases hd : DifferentiableAt ℝ (sphereExtend f) x
  · simpa using hd.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
      (w := fun _ ↦ (1 : ℝ)) (hasDerivAt_const (1 : ℝ) (1 : ℝ))
      (Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht ↦ by
        simp [sphereExtend_smul_of_pos f ht])
  · rw [fderiv_zero_of_not_differentiableAt hd, zero_apply]

end TauCeti
