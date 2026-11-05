/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
-- Private: the derivative of the squared norm and the square-zero property of the exterior
-- derivative are used only inside proofs.
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# Logarithmic derivatives of nonvanishing complex functions

The logarithmic derivative of a complex function `u` on a manifold is the complex-valued `1`-form
`dlog u = u⁻¹ du` (`TauCeti.mlogDeriv`). Where `u` does not vanish it is locally the differential
of a branch of `log u`, so it is closed (`TauCeti.mextDeriv_mlogDeriv`) and as regular as `du`
(`TauCeti.isSmoothForm_mlogDeriv`). The logarithmic derivative turns products into sums
(`TauCeti.mlogDeriv_mul`) and is the differential of the exponent on exponentials
(`TauCeti.mlogDeriv_exp`). A function of modulus one, a `U(1)` gauge transformation, has an
imaginary logarithmic derivative (`TauCeti.re_mlogDeriv_apply_eq_zero`). Conversely, on a
connected manifold a differentiable function with imaginary logarithmic derivative has constant
modulus (`TauCeti.norm_eq_of_re_mlogDeriv_apply_eq_zero`).

The periods of `dlog u` and the construction of `u` from a closed form with periods in `2πiℤ` are
in `TauCeti.Geometry.Manifold.DeRham.LogDeriv`.

## Main declarations

* `TauCeti.mlogDeriv I u`: the logarithmic derivative `dlog u = u⁻¹ du`, with
  `TauCeti.mlogDeriv_def` and `TauCeti.mlogDeriv_apply`.
* `TauCeti.mlogDeriv_eq_of_eventuallyEq_mul_exp`: near a point, if `u = c exp g` then
  `dlog u = dg` there.
* `TauCeti.isSmoothForm_mlogDeriv`: `dlog u` is a `C^n` form for a nowhere-vanishing `C^(n+1)`
  function `u`.
* `TauCeti.mextDeriv_mlogDeriv`: `dlog u` is closed for a nowhere-vanishing `C²` function `u`.
* `TauCeti.re_mlogDeriv_apply_eq_zero`: functions of modulus one have imaginary logarithmic
  derivatives.
* `TauCeti.norm_eq_of_re_mlogDeriv_apply_eq_zero`: an imaginary logarithmic derivative forces
  constant modulus.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the gauge group of
  circle-valued maps and its logarithmic derivatives).
-/

public section

noncomputable section

open Set Filter Complex
open scoped Manifold Topology ComplexConjugate

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
  rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  field_simp [hc]

/-- The logarithmic derivative of `exp g` is the differential of `g`. -/
@[simp]
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
@[simp]
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

/-- **A function with imaginary logarithmic derivative has constant modulus** on a connected
manifold. The differential `2 Re (du * conj u)` of `‖u‖²` is `2 ‖u‖² Re (dlog u)`, which
vanishes; this also holds at the zeros of `u`. -/
theorem norm_eq_of_re_mlogDeriv_apply_eq_zero [IsManifold I 1 M] [PreconnectedSpace M]
    {u : M → ℂ} (hu : MDifferentiable I 𝓘(ℝ, ℂ) u)
    (hre : ∀ x v, (mlogDeriv I u x v).re = 0) (x y : M) : ‖u x‖ = ‖u y‖ := by
  have hsq := (contDiff_norm_sq ℝ (E := ℂ) (n := 1)).differentiable one_ne_zero
  have hd (x : M) : mfderiv I 𝓘(ℝ, ℝ) (fun y ↦ ‖u y‖ ^ 2) x = 0 := by
    rw [← mvfderiv_eq_zero_iff]
    ext w
    have h : mvfderiv I u x w * conj (u x) = normSq (u x) * mlogDeriv I u x fun _ ↦ w := by
      rw [mlogDeriv_apply, ← mul_conj]
      rcases eq_or_ne (u x) 0 with hx | hx
      · simp only [hx, map_zero, inv_zero, zero_mul]
        exact mul_zero (M₀ := ℂ) _
      · field_simp
    have hc := mvfderiv_comp_apply_of_differentiableAt (hsq (u x)) (hu x) w
    rw [Function.comp_def] at hc
    rw [hc, fderiv_norm_sq_apply, smul_apply, innerSL_apply_apply, Complex.inner, h,
      re_ofReal_mul, hre, mul_zero, smul_zero, zero_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (MDifferentiable.apply_eq_of_mfderiv_eq_zero
      (fun x ↦ (hsq (u x)).comp_mdifferentiableAt (hu x)) hd x y)

end TauCeti
