/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Geometry.Manifold.DeRham.PathIntegral
-- Private: the endpoint-ratio identity of winding numbers and the square-zero property of the
-- exterior derivative are used only inside proofs.
import TauCeti.Analysis.Contour.Winding.EndpointRatio
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# Logarithmic derivatives of nonvanishing complex functions

The logarithmic derivative of a complex function `u` on a manifold is the complex-valued `1`-form
`dlog u = u⁻¹ du` (`TauCeti.mlogDeriv`). Where `u` does not vanish it is locally the differential
of a branch of `log u`, so it is closed (`TauCeti.mextDeriv_mlogDeriv`) and as regular as `du`
(`TauCeti.isSmoothForm_mlogDeriv`). Along a `C¹` curve avoiding the zeros of `u` its integral
exponentiates to the ratio of the endpoint values,

`exp (∫_γ dlog u) = u (γ b) / u (γ a)`

(`TauCeti.exp_pathIntegral_mlogDeriv`). This is the endpoint-ratio identity for the winding number
of the plane curve `u ∘ γ` about the origin. Hence the periods of `dlog u` lie in `2πiℤ`
(`TauCeti.exists_pathIntegral_mlogDeriv_eq_int_mul`).

Conversely, on a connected manifold a closed `1`-form `φ` whose integrals along smooth loops at a
base point `x₀` lie in `2πiℤ` is the logarithmic derivative of a nowhere-vanishing function `u`
with `u x₀ = 1` (`TauCeti.exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul`). The function is
`u y = exp (∫_γ φ)` along any smooth curve `γ` from `x₀` to `y`. Two such curves give integrals
that differ by a period, so `u` is well defined. Near each point `u` is a constant multiple of
`exp g` for a local primitive `g` of `φ`, so `u` is smooth with `dlog u = φ`. The construction is
the multiplicative form of the line-integral primitive of
`TauCeti.exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero`.

A function of modulus one, a `U(1)` gauge transformation, has an imaginary logarithmic derivative
(`TauCeti.re_mlogDeriv_apply_eq_zero`). Conversely, on a connected manifold, a nowhere-vanishing
function whose logarithmic derivative is imaginary has constant modulus
(`TauCeti.norm_eq_of_re_mlogDeriv_apply_eq_zero`). Thus imaginary closed `1`-forms with periods in
`2πiℤ` are exactly the logarithmic derivatives of circle-valued functions. The logarithmic
derivative turns products into sums (`TauCeti.mlogDeriv_mul`) and is the differential of the
exponent on exponentials (`TauCeti.mlogDeriv_exp`).

## Main declarations

* `TauCeti.mlogDeriv I u`: the logarithmic derivative `dlog u = u⁻¹ du`, with
  `TauCeti.mlogDeriv_def` and `TauCeti.mlogDeriv_apply`.
* `TauCeti.mlogDeriv_eq_of_eventuallyEq_mul_exp`: near a point, if `u = c exp g` then
  `dlog u = dg` there.
* `TauCeti.isSmoothForm_mlogDeriv`: `dlog u` is a `C^n` form for a nowhere-vanishing `C^(n+1)`
  function `u`.
* `TauCeti.mextDeriv_mlogDeriv`: `dlog u` is closed for a nowhere-vanishing `C²` function `u`.
* `TauCeti.exp_pathIntegral_mlogDeriv`, `TauCeti.exists_pathIntegral_mlogDeriv_eq_int_mul`: the
  periods of `dlog u` lie in `2πiℤ`.
* `TauCeti.exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul`: a closed `1`-form with periods
  in `2πiℤ` is the logarithmic derivative of a nowhere-vanishing function.
* `TauCeti.re_mlogDeriv_apply_eq_zero`, `TauCeti.norm_eq_of_re_mlogDeriv_apply_eq_zero`: modulus one
  and imaginary logarithmic derivatives.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the gauge group of
  circle-valued maps and its logarithmic derivatives).
-/

public section

noncomputable section

open Set Filter Complex MeasureTheory
open scoped Manifold ContDiff Topology Real

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The logarithmic derivative -/

variable (I) in
/-- The **logarithmic derivative** `dlog u = u⁻¹ du` of a complex function `u` on a manifold, a
complex-valued `1`-form. It is meaningful where `u` does not vanish. -/
def mlogDeriv (u : M → ℂ) : RoughForm I M ℂ 1 :=
  fun x ↦ (u x)⁻¹ • mextDeriv (RoughForm.ofFunction I u) x

/-- The logarithmic derivative is `u⁻¹` times the differential of `u`. -/
theorem mlogDeriv_def (u : M → ℂ) (x : M) :
    mlogDeriv I u x = (u x)⁻¹ • mextDeriv (RoughForm.ofFunction I u) x :=
  (rfl)

/-- The logarithmic derivative on a tangent vector `v` is `u⁻¹ du(v)`. -/
@[simp]
theorem mlogDeriv_apply (u : M → ℂ) (x : M) (v : Fin 1 → TangentSpace I x) :
    mlogDeriv I u x v = (u x)⁻¹ * mvfderiv I u x (v 0) := by
  simp only [mlogDeriv, ContinuousAlternatingMap.smul_apply, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, smul_eq_mul]

/-- Near `x`, if `u = c exp g` with `c ≠ 0` and `g` differentiable at `x`, then `dlog u = dg`
at `x`. -/
theorem mlogDeriv_eq_of_eventuallyEq_mul_exp {u g : M → ℂ} {x : M} {c : ℂ} (hc : c ≠ 0)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℂ) g x) (hug : ∀ᶠ y in 𝓝 x, u y = c * exp (g y)) :
    mlogDeriv I u x = mextDeriv (RoughForm.ofFunction I g) x := by
  have hux : u x = c * exp (g x) := hug.self_of_nhds
  have hφ := ((hasDerivAt_exp (g x)).const_mul c).hasFDerivAt.restrictScalars ℝ
  have hu : mvfderiv I u x = mvfderiv I ((fun z ↦ c * exp z) ∘ g) x :=
    Filter.EventuallyEq.mvfderiv_eq hug
  ext v
  rw [mlogDeriv_apply, hu,
    mvfderiv_comp_apply_of_differentiableAt hφ.differentiableAt hg, hφ.fderiv, hux,
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  have hce : c * exp (g x) ≠ 0 := mul_ne_zero hc (exp_ne_zero _)
  rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  field_simp

/-- The logarithmic derivative of `exp g` is the differential of `g`. -/
theorem mlogDeriv_exp {g : M → ℂ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ, ℂ) g x) :
    mlogDeriv I (fun y ↦ exp (g y)) x = mextDeriv (RoughForm.ofFunction I g) x :=
  mlogDeriv_eq_of_eventuallyEq_mul_exp one_ne_zero hg
    (Eventually.of_forall fun _ ↦ (one_mul _).symm)

/-- **The logarithmic derivative turns products into sums.** -/
theorem mlogDeriv_mul {u v : M → ℂ} {x : M} (hu : MDifferentiableAt I 𝓘(ℝ, ℂ) u x)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℂ) v x) (hux : u x ≠ 0) (hvx : v x ≠ 0) :
    mlogDeriv I (u * v) x = mlogDeriv I u x + mlogDeriv I v x := by
  ext w
  -- The product rule `d(uv) = u dv + v du`, evaluated on the tangent vector.
  have hd : mvfderiv I (u * v) x (w 0) =
      u x * mvfderiv I v x (w 0) + v x * mvfderiv I u x (w 0) := by
    simp only [mvfderiv_apply_eq_mfderiv_apply, (hu.hasMFDerivAt.mul hv.hasMFDerivAt).mfderiv]
    -- The sum of scalar multiples of linear maps is evaluated pointwise; the evaluation lemmas do
    -- not fire because the maps are typed into the tangent space of `ℂ`, which is `ℂ` itself.
    rfl
  rw [ContinuousAlternatingMap.add_apply, mlogDeriv_apply, mlogDeriv_apply, mlogDeriv_apply, hd,
    Pi.mul_apply]
  field_simp
  ring

/-- Near a point `x` where it does not vanish, a `C^n` complex function `u` is `u x` times the
exponential of a `C^n` function `g`, the branch `log (u / u x)` on the open set where `u / u x`
lies in the slit plane. There `dlog u` is the exterior derivative of `g` within that set. -/
private theorem exists_mlogDeriv_eq_mextDerivWithin {n : WithTop ℕ∞} (hn : n ≠ 0) {u : M → ℂ}
    (hu : ContMDiff I 𝓘(ℝ, ℂ) n u) {x : M} (hx : u x ≠ 0) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∃ g : M → ℂ, (∀ y ∈ V, ContMDiffAt I 𝓘(ℝ, ℂ) n g y) ∧
      (∀ y ∈ V, u y = u x * exp (g y)) ∧
      ∀ y ∈ V, mlogDeriv I u y = mextDerivWithin (RoughForm.ofFunction I g) V y := by
  set V := (fun y ↦ u y / u x) ⁻¹' slitPlane with hV_def
  have hV : IsOpen V := isOpen_slitPlane.preimage (hu.continuous.div_const _)
  have hg (y : M) (hy : y ∈ V) : ContMDiffAt I 𝓘(ℝ, ℂ) n (fun z ↦ log (u z / u x)) y :=
    (((contDiffAt_log hy).comp (u y) (contDiffAt_id.div_const (u x))).restrict_scalars ℝ)
      |>.comp_contMDiffAt (hu y)
  have hug (y : M) (hy : y ∈ V) : u y = u x * exp (log (u y / u x)) := by
    rw [exp_log (slitPlane_ne_zero hy), mul_div_cancel₀ _ hx]
  refine ⟨V, hV, by simp [hV_def, div_self hx], _, hg, hug, fun y hy ↦ ?_⟩
  rw [mextDerivWithin_of_isOpen hV hy]
  exact mlogDeriv_eq_of_eventuallyEq_mul_exp hx ((hg y hy).mdifferentiableAt hn)
    (eventually_of_mem (hV.mem_nhds hy) hug)

section Regularity

variable [IsManifold I 2 M]

/-- The logarithmic derivative of a nowhere-vanishing `C^(n+1)` function is a `C^n` form. -/
theorem isSmoothForm_mlogDeriv {n : WithTop ℕ∞} {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) (n + 1) u)
    (hu₀ : ∀ x, u x ≠ 0) : IsSmoothForm I n (mlogDeriv I u) := by
  rw [isSmoothForm_def]
  intro x
  obtain ⟨V, hV, hxV, g, hg, -, hdg⟩ := exists_mlogDeriv_eq_mextDerivWithin (by simp) hu (hu₀ x)
  have hd := contMDiffOn_mextDerivWithin (RoughForm.ofFunction I g)
    (fun y hy ↦ (contMDiffAt_ofFunction_iff.mpr (hg y hy)).contMDiffWithinAt) hV.uniqueMDiffOn
    (hV.interior_eq.symm ▸ subset_closure)
  exact (hd.contMDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
    (eventually_of_mem (hV.mem_nhds hxV) fun y hy ↦ by simp only [hdg y hy])

/-- **The logarithmic derivative is closed**: `d (dlog u) = 0` for a nowhere-vanishing `C²`
function `u`. -/
theorem mextDeriv_mlogDeriv {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 2 u) (hu₀ : ∀ x, u x ≠ 0) :
    mextDeriv (mlogDeriv I u) = 0 := by
  funext x
  obtain ⟨V, hV, hxV, g, hg, -, hdg⟩ := exists_mlogDeriv_eq_mextDerivWithin (by simp) hu (hu₀ x)
  rw [mextDeriv_congr_of_eventuallyEq (eventually_of_mem (hV.mem_nhds hxV) hdg),
    ← mextDerivWithin_of_isOpen hV hxV]
  exact mextDerivWithin_mextDerivWithin _
    (fun y hy ↦ (contMDiffAt_ofFunction_iff.mpr (hg y hy)).contMDiffWithinAt) hV.uniqueMDiffOn
    (hV.interior_eq.symm ▸ subset_closure) hxV

end Regularity

/-! ### Periods -/

/-- **The integral of `dlog u` along a curve exponentiates to the endpoint ratio.** Along a `C¹`
curve `γ` on which the `C¹` function `u` does not vanish,
`exp (∫_γ dlog u) = u (γ b) / u (γ a)`. -/
theorem exp_pathIntegral_mlogDeriv {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 1 u) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hu₀ : ∀ t ∈ uIcc a b, u (γ t) ≠ 0) :
    exp (pathIntegral (mlogDeriv I u) γ a b) = u (γ b) / u (γ a) := by
  have hc : ContDiff ℝ 1 (u ∘ γ) := contMDiff_iff_contDiff.mp (hu.comp hγ)
  have hd (t : ℝ) : HasDerivAt (u ∘ γ)
      (mvfderiv I u (γ t) (Manifold.curveVelocity I γ t)) t :=
    Manifold.hasDerivAt_comp_curve ((hu (γ t)).mdifferentiableAt one_ne_zero)
      (Manifold.hasMFDerivAt_curveVelocity ((hγ t).mdifferentiableAt one_ne_zero))
  -- The line integral is the winding-number integral of the plane curve `u ∘ γ`.
  have hint : pathIntegral (mlogDeriv I u) γ a b =
      ∫ t in a..b, ((u ∘ γ) t - 0)⁻¹ * deriv (u ∘ γ) t := by
    rw [pathIntegral_def]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [mlogDeriv_apply, (hd t).deriv, sub_zero, Function.comp_apply]
  have hcont : ContinuousOn (u ∘ γ) (uIcc a b) := hc.continuous.continuousOn
  have hii := Contour.intervalIntegrable_inv_sub_mul_deriv hcont hu₀
    (hc.continuous_deriv_one.intervalIntegrable a b)
  have he := Contour.exp_two_pi_I_mul_windingNumber_of_avoidance countable_empty hcont
    (fun t _ ↦ hc.differentiable one_ne_zero t) hu₀ hii
  rw [Contour.windingNumber_eq_integral_of_avoidance hcont hu₀ hii, ← mul_assoc,
    mul_inv_cancel₀ two_pi_I_ne_zero, one_mul] at he
  rw [hint, he, sub_zero, sub_zero, Function.comp_apply, Function.comp_apply]

/-- **The periods of `dlog u` lie in `2πiℤ`.** The integral of the logarithmic derivative of a
`C¹` function `u` around a closed `C¹` curve on which `u` does not vanish is an integer multiple
of `2πi`. -/
theorem exists_pathIntegral_mlogDeriv_eq_int_mul {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 1 u)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hu₀ : ∀ t ∈ uIcc a b, u (γ t) ≠ 0)
    (hab : γ a = γ b) : ∃ n : ℤ, pathIntegral (mlogDeriv I u) γ a b = n * (2 * π * Complex.I) := by
  rw [← exp_eq_one_iff, exp_pathIntegral_mlogDeriv hu hγ hu₀, hab,
    div_self (hu₀ b right_mem_uIcc)]

/-! ### Logarithmic derivatives of circle-valued functions -/

/-- **The logarithmic derivative of a circle-valued function is imaginary.** If `u` has modulus
one near `x` and is differentiable at `x`, then `dlog u` is imaginary at `x`. -/
theorem re_mlogDeriv_apply_eq_zero {u : M → ℂ} {x : M} (hu : MDifferentiableAt I 𝓘(ℝ, ℂ) u x)
    (hu₁ : ∀ᶠ y in 𝓝 x, ‖u y‖ = 1) (v : Fin 1 → TangentSpace I x) :
    (mlogDeriv I u x v).re = 0 := by
  have hux : ‖u x‖ = 1 := hu₁.self_of_nhds
  have hx : u x ≠ 0 := norm_ne_zero_iff.mp (hux.symm ▸ one_ne_zero)
  have h1 : u x / u x ∈ slitPlane := by rw [div_self hx]; exact one_mem_slitPlane
  -- Near `x`, `u = u x * exp g` for the branch `g = log (u / u x)`, which is imaginary.
  set g : M → ℂ := fun y ↦ log (u y / u x) with hg_def
  have hg : MDifferentiableAt I 𝓘(ℝ, ℂ) g x :=
    ((((differentiableAt_id (x := u x)).div_const (u x)).clog h1).restrictScalars ℝ)
      |>.comp_mdifferentiableAt hu
  have hug : ∀ᶠ y in 𝓝 x, u y = u x * exp (g y) := by
    filter_upwards [(hu.continuousAt.div_const (u x)).preimage_mem_nhds
      (isOpen_slitPlane.mem_nhds h1)] with y hy
    rw [hg_def, exp_log (slitPlane_ne_zero hy), mul_div_cancel₀ _ hx]
  have hre : (Complex.reCLM ∘ g) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hug, hu₁] with y hy hy₁
    have h := congrArg norm hy
    rw [norm_mul, hy₁, hux, one_mul, norm_exp] at h
    simpa using (Real.exp_eq_one_iff _).mp h.symm
  rw [mlogDeriv_eq_of_eventuallyEq_mul_exp hx hg hug, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  have h := mvfderiv_comp_apply_of_differentiableAt Complex.reCLM.differentiableAt hg (v 0)
  have h0 : mvfderiv I (fun _ : M ↦ (0 : ℝ)) x = 0 := mvfderiv_eq_zero_iff.mpr (mfderiv_const ..)
  rw [hre.mvfderiv_eq, h0, Complex.reCLM.fderiv, Complex.reCLM_apply] at h
  simpa using h.symm

/-- **A nowhere-vanishing function with imaginary logarithmic derivative has constant modulus**
on a connected manifold. -/
theorem norm_eq_of_re_mlogDeriv_apply_eq_zero [IsManifold I 2 M] [PreconnectedSpace M]
    {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 1 u) (hu₀ : ∀ x, u x ≠ 0)
    (hre : ∀ x v, (mlogDeriv I u x v).re = 0) (x y : M) : ‖u x‖ = ‖u y‖ := by
  obtain ⟨γ, hγ, hγ₀, hγ₁⟩ := exists_contMDiff_curve (I := I) (n := 2) x y
  replace hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ := hγ.of_le one_le_two
  have he := exp_pathIntegral_mlogDeriv hu hγ (a := 0) (b := 1) fun t _ ↦ hu₀ _
  rw [hγ₀ 0 le_rfl, hγ₁ 1 le_rfl] at he
  -- The integral of an imaginary form is imaginary.
  have hcont := (isSmoothForm_mlogDeriv (n := 0) (by simpa using hu)
    hu₀).continuous_apply_curveVelocity hγ
  have hre0 : (pathIntegral (mlogDeriv I u) γ 0 1).re = 0 := by
    rw [pathIntegral_def, ← Complex.reCLM_apply,
      ← Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)]
    simp only [Complex.reCLM_apply, hre, intervalIntegral.integral_zero]
  have h := congrArg norm he
  rw [norm_exp, hre0, Real.exp_zero, norm_div, eq_comm, div_eq_one_iff_eq
    (norm_ne_zero_iff.mpr (hu₀ x))] at h
  exact h.symm

/-! ### Closed forms with periods in `2πiℤ` -/

/-- If the integrals of `φ` along smooth loops at `x₀` lie in `2πiℤ`, then two smooth curves from
`x₀` to `y`, constant on `(-∞, 0]` and on `[1, ∞)`, have line integrals with the same
exponential. -/
private theorem exp_pathIntegral_eq_of_forall_pathIntegral_eq_int_mul [IsManifold I 1 M]
    {φ : RoughForm I M ℂ 1} (hφ : IsSmoothForm I 0 φ) {x₀ y : M}
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      ∃ n : ℤ, pathIntegral φ γ 0 1 = n * (2 * π * Complex.I))
    {γ γ' : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγ₀ : ∀ t ≤ 0, γ t = x₀)
    (hγ₁ : ∀ t, 1 ≤ t → γ t = y) (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (hγ'₀ : ∀ t ≤ 0, γ' t = x₀) (hγ'₁ : ∀ t, 1 ≤ t → γ' t = y) :
    exp (pathIntegral φ γ 0 1) = exp (pathIntegral φ γ' 0 1) := by
  obtain ⟨ℓ, hℓ, hℓ₀, hℓ₁, hℓφ⟩ :=
    exists_contMDiff_loop_pathIntegral_eq_sub hφ hγ hγ₀ hγ₁ hγ' hγ'₀ hγ'₁
  obtain ⟨n, hn⟩ := h ℓ hℓ hℓ₀ hℓ₁
  exact exp_eq_exp_iff_exists_int.mpr ⟨n, by rw [← hn, hℓφ]; ring⟩

/-- **Closed forms with periods in `2πiℤ` are logarithmic derivatives.** On a connected manifold,
a closed `C^r` complex `1`-form `φ` (`1 ≤ r`) whose integral along every smooth loop at a base
point `x₀` is an integer multiple of `2πi` is the logarithmic derivative of a nowhere-vanishing
`C^r` function `u` with `u x₀ = 1`. The function is `u y = exp (∫_γ φ)` along smooth curves `γ`
from `x₀` to `y`. -/
theorem exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M] [PreconnectedSpace M] {r : ℕ∞} (hr : 1 ≤ r)
    {φ : RoughForm I M ℂ 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) (x₀ : M)
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      ∃ n : ℤ, pathIntegral φ γ 0 1 = n * (2 * π * Complex.I)) :
    ∃ u : M → ℂ, ContMDiff I 𝓘(ℝ, ℂ) r u ∧ (∀ x, u x ≠ 0) ∧ u x₀ = 1 ∧ mlogDeriv I u = φ := by
  have hφ₀ : IsSmoothForm I 0 φ := hφ.of_le (by simp)
  -- The exponent `f` is the integral along chosen smooth curves from `x₀`.
  choose γ hγ hγ₀ hγ₁ using fun y : M ↦ exists_contMDiff_curve (I := I) (n := ⊤) x₀ y
  set f : M → ℂ := fun y ↦ pathIntegral φ (γ y) 0 1 with hf_def
  -- Near each point `x`, `exp ∘ f` is a constant multiple of `exp g` for a local primitive `g`.
  have hloc (x : M) : ∃ g : M → ℂ, ContMDiffAt I 𝓘(ℝ, ℂ) r g x ∧
      (∀ᶠ y in 𝓝 x, exp (f y) = exp (f x - g x) * exp (g y)) ∧
      mextDeriv (RoughForm.ofFunction I g) x = φ x := by
    obtain ⟨g, hg, hdg, hδ⟩ := exists_local_primitive_pathIntegral_eq_add_sub hr hφ
      (Eventually.of_forall fun y ↦ congrFun hclosed y) (hγ x) (hγ₀ x) (hγ₁ x)
    refine ⟨g, hg, ?_, hdg⟩
    filter_upwards [hδ] with y ⟨δ, hδ, hδ₀, hδ₁, hδφ⟩
    rw [hf_def, exp_pathIntegral_eq_of_forall_pathIntegral_eq_int_mul hφ₀ h (hγ y) (hγ₀ y)
      (hγ₁ y) hδ hδ₀ hδ₁, hδφ, ← exp_add]
    congr 1
    ring
  refine ⟨fun y ↦ exp (f y), fun x ↦ ?_, fun x ↦ exp_ne_zero _, ?_, funext fun x ↦ ?_⟩
  · obtain ⟨g, hg, hfg, -⟩ := hloc x
    exact ((contDiff_const.mul Complex.contDiff_exp).contDiffAt.comp_contMDiffAt hg)
      |>.congr_of_eventuallyEq hfg
  · obtain ⟨n, hn⟩ := h _ (hγ x₀) (hγ₀ x₀ 0 le_rfl) (hγ₁ x₀ 1 le_rfl)
    exact exp_eq_one_iff.mpr ⟨n, hn⟩
  · obtain ⟨g, hg, hfg, hdg⟩ := hloc x
    rw [mlogDeriv_eq_of_eventuallyEq_mul_exp (exp_ne_zero _)
      ((hg.of_le (by exact_mod_cast hr)).mdifferentiableAt one_ne_zero) hfg, hdg]

end TauCeti
