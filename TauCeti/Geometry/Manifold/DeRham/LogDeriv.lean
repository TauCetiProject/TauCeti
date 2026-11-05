/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
public import TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv
-- Private: the endpoint-ratio identity of winding numbers is used only inside proofs.
import TauCeti.Analysis.Contour.Winding.EndpointRatio

/-!
# Periods of logarithmic derivatives

The logarithmic derivative `dlog u = u⁻¹ du` of a complex function `u` on a manifold
(`TauCeti.mlogDeriv`, in `TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv`) integrates along
a `C¹` curve avoiding the zeros of `u` to a number whose exponential is the ratio of the endpoint
values,

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

Together with `TauCeti.re_mlogDeriv_apply_eq_zero` and
`TauCeti.norm_eq_of_re_mlogDeriv_apply_eq_zero` (in
`TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv`), imaginary closed `1`-forms with periods
in `2πiℤ` are exactly the logarithmic derivatives of circle-valued functions.

The endpoint-ratio identity extends to continuous paths, integrated through the covering space of
local primitives: `exp (∫_γ dlog u) = u y / u x` for every path class `γ` from `x` to `y`
(`TauCeti.exp_pathClassIntegral_mlogDeriv`). Along a lift of `γ` the primitive is locally a
branch of `log u` (`TauCeti.IsPrimitiveOn.eventually_mul_exp_neg_eq`). Consequently the periods
of `dlog u` on the first singular homology group `H₁(M; ℤ)` lie in `2πiℤ`
(`TauCeti.exists_homologyPeriodHom_mlogDeriv_eq_int_mul`): along each singular `1`-simplex the
integral differs from the change of `log u` by a multiple of `2πi`, and these changes cancel on
cycles.

For the group `C^∞(M, U(1))` of smooth circle-valued maps, the gauge group of a Hermitian line
bundle on `M`, this gives the period homomorphism `C^∞(M, U(1)) → Hom(H₁(M; ℤ), ℤ)`,
`u ↦ (c ↦ (2πi)⁻¹ ∫_c dlog u)` (`TauCeti.circlePeriodHom`). On a preconnected manifold:

* `dlog u = 0` exactly when `u` is constant (`TauCeti.mlogDeriv_coe_eq_zero_iff`);
* the periods of `u` vanish exactly when `u = exp (i f)` for a smooth real function `f`
  (`TauCeti.circlePeriodHom_eq_one_iff`); so the quotient of `C^∞(M, U(1))` by the subgroup of
  maps with a smooth logarithm embeds into `Hom(H₁(M; ℤ), ℤ)`;
* every smooth closed imaginary `1`-form with periods in `2πiℤ` on `H₁(M; ℤ)` is `dlog u` for a
  smooth circle-valued map `u` (`TauCeti.exists_mlogDeriv_coe_eq`), so the image of the period
  homomorphism consists of the integral period homomorphisms of such forms
  (`TauCeti.mem_range_circlePeriodHom_iff`).

## Main declarations

* `TauCeti.exp_pathIntegral_mlogDeriv`, `TauCeti.exists_pathIntegral_mlogDeriv_eq_int_mul`: the
  periods of `dlog u` lie in `2πiℤ`.
* `TauCeti.exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul`: a closed `1`-form with periods
  in `2πiℤ` is the logarithmic derivative of a nowhere-vanishing function.
* `TauCeti.exp_pathClassIntegral_mlogDeriv`: the endpoint-ratio identity along continuous paths.
* `TauCeti.exists_homologyPeriodHom_mlogDeriv_eq_int_mul`: the periods of `dlog u` on `H₁(M; ℤ)`
  lie in `2πiℤ`.
* `TauCeti.circlePeriodHom`: the period homomorphism of smooth circle-valued maps, characterized
  by `TauCeti.homologyPeriodHom_mlogDeriv_eq_circlePeriodHom`.
* `TauCeti.mlogDeriv_coe_eq_zero_iff`, `TauCeti.circlePeriodHom_eq_one_iff`,
  `TauCeti.exists_mlogDeriv_coe_eq`, `TauCeti.mem_range_circlePeriodHom_iff`: the kernel of `dlog`,
  the kernel and the image of the period homomorphism.

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

/-! ### Integrals of `dlog u` along continuous paths -/

/-- **Primitives of `dlog u` are branches of `log u`.** Near each point `x` of an open set `U`
on which `g` is a primitive of `dlog u`, for a differentiable `u` vanishing nowhere on `U`,
`u exp (-g)` is constant. -/
theorem IsPrimitiveOn.eventually_mul_exp_neg_eq [IsManifold I 1 M] {u g : M → ℂ} {U : Set M}
    (hg : IsPrimitiveOn (mlogDeriv I u) g U) (hu : MDifferentiableOn I 𝓘(ℝ, ℂ) u U)
    (hu₀ : ∀ y ∈ U, u y ≠ 0) {x : M} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x, u y * exp (-g y) = u x * exp (-g x) := by
  have hg' := hg.const_smul (-1)
  set w : M → ℂ := u * fun y ↦ exp (((-1 : ℝ) • g) y) with hw_def
  have hgy (y : M) (hy : y ∈ U) : MDifferentiableAt I 𝓘(ℝ, ℂ) ((-1 : ℝ) • g) y :=
    (hg'.mdifferentiableOn y hy).mdifferentiableAt (hg.isOpen.mem_nhds hy)
  have huy (y : M) (hy : y ∈ U) : MDifferentiableAt I 𝓘(ℝ, ℂ) u y :=
    (hu y hy).mdifferentiableAt (hg.isOpen.mem_nhds hy)
  have hey (y : M) (hy : y ∈ U) :
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun z ↦ exp (((-1 : ℝ) • g) z)) y :=
    ((Complex.hasDerivAt_exp _).differentiableAt.restrictScalars ℝ).comp_mdifferentiableAt
      (hgy y hy)
  -- `dlog w = dlog u - dg` vanishes on `U`, so `w` has zero differential there.
  have hzero (y : M) (hy : y ∈ U) : mfderiv I 𝓘(ℝ, ℂ) w y = 0 := by
    have hd : mlogDeriv I w y = 0 := by
      rw [hw_def, mlogDeriv_mul (huy y hy) (hey y hy) (hu₀ y hy) (exp_ne_zero _),
        mlogDeriv_exp (hgy y hy), hg'.mextDeriv_eq y hy]
      ext v
      simp
    exact (mlogDeriv_eq_zero_iff (u := w) (mul_ne_zero (hu₀ y hy) (exp_ne_zero _))).mp hd
  have hwd : MDifferentiableOn I 𝓘(ℝ, ℂ) w U := fun y hy ↦
    ((huy y hy).mul (hey y hy)).mdifferentiableWithinAt
  filter_upwards [hwd.eventuallyEq_const_of_mfderiv_eq_zero hg.isOpen hzero hx] with y hy
  simpa [w, neg_one_smul] using hy

section PathClass

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- **The integral of `dlog u` along a path exponentiates to the endpoint ratio.** For a
nowhere-vanishing `C²` function `u` and a homotopy class `γ` of continuous paths from `x` to `y`,
`exp (∫_γ dlog u) = u y / u x`. -/
theorem exp_pathClassIntegral_mlogDeriv {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 2 u)
    (hu₀ : ∀ x, u x ≠ 0) {x y : M} (γ : Path.Homotopic.Quotient x y) :
    exp (pathClassIntegral (mlogDeriv I u) γ) = u y / u x := by
  induction γ with | mk γ =>
  have hφ : IsSmoothForm I 1 (mlogDeriv I u) := isSmoothForm_mlogDeriv hu hu₀
  have hclosed : mextDeriv (mlogDeriv I u) = 0 := mextDeriv_mlogDeriv hu hu₀
  have hp := PrimitiveSpace.isCoveringMap_proj (r := 1) le_rfl hφ hclosed
  have he : γ 0 = PrimitiveSpace.proj _ (PrimitiveSpace.graph (mlogDeriv I u) 0 x) :=
    γ.source.trans (PrimitiveSpace.proj_graph x).symm
  set Γ := hp.liftPath γ _ he
  have hΓ (t : unitInterval) : PrimitiveSpace.proj _ (Γ t) = γ t :=
    congrFun (hp.liftPath_lifts γ _ he) t
  -- Along the lift, `u exp (-value)` is locally constant: the value runs along primitives.
  set w : unitInterval → ℂ := fun t ↦ u (γ t) * exp (-PrimitiveSpace.value _ (Γ t))
  have hw : IsLocallyConstant w := (IsLocallyConstant.iff_eventually_eq w).mpr fun t₀ ↦ by
    obtain ⟨g, -, U, hxU, hgU, c, hc⟩ :=
      PrimitiveSpace.exists_isPrimitiveOn_eventually_value_eq le_rfl hφ hclosed
        Γ.continuous.continuousAt (t := t₀)
    rw [hΓ] at hxU
    have hloc := hgU.eventually_mul_exp_neg_eq (hu.mdifferentiable (by norm_num)).mdifferentiableOn
      (fun y _ ↦ hu₀ y) hxU
    filter_upwards [hc, γ.continuous.continuousAt.preimage_mem_nhds hloc] with s hs hs'
    obtain ⟨-, hc₀⟩ := hc.self_of_nhds
    simp only [w, hs.2, hc₀, hΓ, neg_add, exp_add, ← mul_assoc]
    exact congrArg (· * exp (-c)) hs'
  have h := hw.apply_eq_of_preconnectedSpace 1 0
  simp only [w, γ.source, γ.target, Γ, hp.liftPath_zero, PrimitiveSpace.value_graph,
    Pi.zero_apply, neg_zero, exp_zero, mul_one] at h
  rw [pathClassIntegral_mk_eq_sub hφ hclosed Γ.continuous hΓ, hp.liftPath_zero,
    PrimitiveSpace.value_graph, Pi.zero_apply, sub_zero, eq_div_iff (hu₀ x), ← h, mul_comm,
    mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]

end PathClass

/-! ### Smooth circle-valued maps -/

section Circle

attribute [local instance] finrank_real_complex_fact'

/-- The complex values of a smooth circle-valued map form a smooth function. -/
private theorem contMDiff_coe_circle (u : C^∞⟮I, M; 𝓡 1, Circle⟯) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ fun x ↦ (u x : ℂ) :=
  (contMDiff_coe_sphere.of_le le_top).comp u.contMDiff

/-- `dlog` turns products of circle-valued maps into sums. -/
private theorem mlogDeriv_coe_mul (u v : C^∞⟮I, M; 𝓡 1, Circle⟯) :
    mlogDeriv I (fun x ↦ ((u * v) x : ℂ)) =
      mlogDeriv I (fun x ↦ (u x : ℂ)) + mlogDeriv I (fun x ↦ (v x : ℂ)) := by
  funext x
  have hu := ((contMDiff_coe_circle u) x).mdifferentiableAt (by simp)
  have hv := ((contMDiff_coe_circle v) x).mdifferentiableAt (by simp)
  exact mlogDeriv_mul hu hv (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)

/-- **The kernel of `dlog` on circle-valued maps is the constants.** On a preconnected manifold, a
smooth circle-valued map has vanishing logarithmic derivative exactly when it is constant. -/
theorem mlogDeriv_coe_eq_zero_iff [IsManifold I 1 M] [PreconnectedSpace M]
    {u : C^∞⟮I, M; 𝓡 1, Circle⟯} :
    mlogDeriv I (fun x ↦ (u x : ℂ)) = 0 ↔ ∃ z : Circle, ∀ x, u x = z := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hz⟩ ↦ by simp [hz]⟩
  have hd (x : M) : mfderiv I 𝓘(ℝ, ℂ) (fun x ↦ (u x : ℂ)) x = 0 :=
    (mlogDeriv_eq_zero_iff (u := fun x ↦ (u x : ℂ)) (Circle.coe_ne_zero (u x))).mp (congrFun h x)
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, isEmptyElim⟩
  · exact ⟨u x₀, fun x ↦ Circle.ext <| MDifferentiable.apply_eq_of_mfderiv_eq_zero
      ((contMDiff_coe_circle u).mdifferentiable (by simp)) hd x x₀⟩

end Circle

end TauCeti

namespace TauCeti

open CategoryTheory TauCeti.HurewiczOne TauCeti.TopCat
open scoped Simplicial

attribute [local instance] finrank_real_complex_fact'

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-! ### Periods on singular homology -/

/-- **The periods of `dlog u` on `H₁(M; ℤ)` lie in `2πiℤ`.** For a nowhere-vanishing `C²`
function `u`, the integral of `dlog u` over every singular `1`-cycle is an integer multiple of
`2πi`. Along a singular `1`-simplex the integral differs from the change of `log u` by such a
multiple, and the changes of `log u` cancel on cycles. -/
theorem exists_homologyPeriodHom_mlogDeriv_eq_int_mul {u : M → ℂ}
    (hu : ContMDiff I 𝓘(ℝ, ℂ) 2 u) (hu₀ : ∀ x, u x ≠ 0)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    ∃ n : ℤ, homologyPeriodHom (mlogDeriv I u) c = n * (2 * π * Complex.I) := by
  have hs (s : (_root_.TopCat.toSSet.obj (.of M)) _⦋1⦌) : ∃ n : ℤ,
      pathClassIntegral (mlogDeriv I u) (.mk (path₁ s)) =
        log (u (target₁ s)) - log (u (source₁ s)) + n * (2 * π * Complex.I) := by
    rw [← exp_eq_exp_iff_exists_int, exp_pathClassIntegral_mlogDeriv hu hu₀, exp_sub,
      exp_log (hu₀ _), exp_log (hu₀ _)]
  choose N hN using hs
  have hL : chainsDesc (fun s ↦ pathClassIntegral (mlogDeriv I u) (.mk (path₁ s))) =
      LinearMap.toSpanSingleton ℤ ℂ (2 * π * Complex.I) ∘ₗ chainsDesc N +
        chainsDesc (fun v ↦ log (u (_root_.TopCat.toSSetObj₀Equiv v))) ∘ₗ
          (((singularChains ℤ).obj (.of M)).d 1 0).hom :=
    singularChains_linearMap_ext fun s ↦ by
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        singularChains_d_simplexChain (n := 0), Fin.sum_univ_two]
      simp only [map_add, map_zsmul, chainsDesc_simplexChain_one]
      rw [toSSetObj₀Equiv_δ_zero, toSSetObj₀Equiv_δ_one, hN]
      simp [zsmul_eq_mul]
      ring
  obtain ⟨z, rfl⟩ := (H₁AddEquivHomology (.of M)).surjective.comp H₁.mk_surjective c
  refine ⟨chainsDesc N (z : ((singularChains ℤ).obj (.of M)).X 1), ?_⟩
  rw [Function.comp_apply, homologyPeriodHom_H₁AddEquivHomology_mk, hL, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, mem_cycles₁_iff.1 z.2, map_zero, add_zero,
    LinearMap.toSpanSingleton_apply, zsmul_eq_mul]

/-! ### Periods of smooth circle-valued maps -/

/-- The integers `n(c)` with `∫_c dlog u = 2πi n(c)`, for a smooth circle-valued map `u`. -/
private def circlePeriod (u : C^∞⟮I, M; 𝓡 1, Circle⟯) :
    ((singularChains ℤ).obj (.of M)).homology 1 → ℤ := fun c ↦
  (exists_homologyPeriodHom_mlogDeriv_eq_int_mul ((contMDiff_coe_circle u).of_le (by simp))
    (fun x ↦ Circle.coe_ne_zero (u x)) c).choose

/-- The defining property of `circlePeriod`. -/
private theorem homologyPeriodHom_mlogDeriv_eq_circlePeriod (u : C^∞⟮I, M; 𝓡 1, Circle⟯)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    homologyPeriodHom (mlogDeriv I fun x ↦ (u x : ℂ)) c = circlePeriod u c * (2 * π * Complex.I) :=
  (exists_homologyPeriodHom_mlogDeriv_eq_int_mul ((contMDiff_coe_circle u).of_le (by simp))
    (fun x ↦ Circle.coe_ne_zero (u x)) c).choose_spec

private theorem intCast_mul_two_pi_I_injective :
    Function.Injective fun n : ℤ ↦ (n : ℂ) * (2 * π * Complex.I) := fun _ _ h ↦
  Int.cast_injective (mul_right_cancel₀ two_pi_I_ne_zero h)

variable (I M) in
/-- The **periods of smooth circle-valued maps**: for a smooth map `u : M → U(1)`, the integral of
`dlog u` over a singular `1`-cycle is `2πi` times an integer, and these integers form a
homomorphism `H₁(M; ℤ) → ℤ`. Taking them is a homomorphism from the group of smooth circle-valued
maps, the gauge group of a Hermitian line bundle, to `Hom(H₁(M; ℤ), ℤ)`, since `dlog` turns
products into sums. -/
def circlePeriodHom :
    C^∞⟮I, M; 𝓡 1, Circle⟯ →* Multiplicative (((singularChains ℤ).obj (.of M)).homology 1 →+ ℤ)
    where
  toFun u := .ofAdd
    { toFun := circlePeriod u
      map_zero' := intCast_mul_two_pi_I_injective <| by
        simp only [← homologyPeriodHom_mlogDeriv_eq_circlePeriod, map_zero, Int.cast_zero,
          zero_mul]
      map_add' c c' := intCast_mul_two_pi_I_injective <| by
        simp only [Int.cast_add, add_mul, ← homologyPeriodHom_mlogDeriv_eq_circlePeriod,
          map_add] }
  map_one' := by
    refine congrArg Multiplicative.ofAdd (AddMonoidHom.ext fun c ↦ ?_)
    refine intCast_mul_two_pi_I_injective ?_
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply, Int.cast_zero,
      zero_mul, ← homologyPeriodHom_mlogDeriv_eq_circlePeriod, ContMDiffMap.coe_one, Pi.one_apply,
      Circle.coe_one, mlogDeriv_const, homologyPeriodHom_zero]
  map_mul' u v := by
    refine congrArg Multiplicative.ofAdd (AddMonoidHom.ext fun c ↦ ?_)
    refine intCast_mul_two_pi_I_injective ?_
    have hs (w : C^∞⟮I, M; 𝓡 1, Circle⟯) := isSmoothForm_mlogDeriv (n := 1)
      ((contMDiff_coe_circle w).of_le (by simp)) fun x ↦ Circle.coe_ne_zero (w x)
    have hc (w : C^∞⟮I, M; 𝓡 1, Circle⟯) := mextDeriv_mlogDeriv
      ((contMDiff_coe_circle w).of_le (by simp)) fun x ↦ Circle.coe_ne_zero (w x)
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toAdd_ofAdd,
      AddMonoidHom.add_apply, Int.cast_add, add_mul,
      ← homologyPeriodHom_mlogDeriv_eq_circlePeriod, mlogDeriv_coe_mul,
      homologyPeriodHom_add (hs u) (hc u) (hs v) (hc v)]

/-- **The periods of `dlog u`.** The integral of `dlog u` over a singular `1`-cycle `c` is `2πi`
times the period of the smooth circle-valued map `u` on `c`. -/
theorem homologyPeriodHom_mlogDeriv_eq_circlePeriodHom (u : C^∞⟮I, M; 𝓡 1, Circle⟯)
    (c : ((singularChains ℤ).obj (.of M)).homology 1) :
    homologyPeriodHom (mlogDeriv I fun x ↦ (u x : ℂ)) c =
      (Multiplicative.toAdd (circlePeriodHom I M u) c : ℂ) * (2 * π * Complex.I) :=
  homologyPeriodHom_mlogDeriv_eq_circlePeriod u c

/-- A smooth circle-valued map `u` with `u = exp g` has vanishing periods: `dlog u = dg` is
exact. -/
private theorem homologyPeriodHom_mlogDeriv_eq_zero_of_eq_exp {u : C^∞⟮I, M; 𝓡 1, Circle⟯}
    {g : M → ℂ} (hg : ContMDiff I 𝓘(ℝ, ℂ) 2 g) (hug : ∀ x, (u x : ℂ) = exp (g x)) :
    homologyPeriodHom (mlogDeriv I fun x ↦ (u x : ℂ)) = 0 := by
  have hψ : IsSmoothForm I 2 (RoughForm.ofFunction I g) := isSmoothForm_ofFunction_iff.mpr hg
  have hdlog : mlogDeriv I (fun x ↦ (u x : ℂ)) = mextDeriv (RoughForm.ofFunction I g) := by
    funext x
    rw [funext hug]
    exact mlogDeriv_exp ((hg x).mdifferentiableAt (by simp))
  refine homology_one_addMonoidHom_ext fun c ↦ ?_
  rw [hdlog, homologyPeriodHom_H₁AddEquivHomology_mk, AddMonoidHom.zero_apply,
    chainsDesc_pathClassIntegral_mextDeriv hψ, LinearMap.comp_apply, mem_cycles₁_iff.1 c.2,
    map_zero]

/-- On a smooth closed loop, the line integral of a closed `C¹` form is one of its periods on
singular homology. -/
private theorem pathIntegral_eq_homologyPeriodHom {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 1 φ)
    (hclosed : mextDeriv φ = 0) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {x₀ : M}
    (hγ₀ : γ 0 = x₀) (hγ₁ : γ 1 = x₀) :
    ∃ c, pathIntegral φ γ 0 1 = homologyPeriodHom φ c := by
  let p : Path x₀ x₀ :=
    ⟨⟨fun t ↦ γ t, hγ.continuous.comp continuous_subtype_val⟩, hγ₀, hγ₁⟩
  refine ⟨H₁AddEquivHomology (.of M) (loopClass (X := .of M) p), ?_⟩
  rw [homologyPeriodHom_loopClass,
    pathClassIntegral_mk_eq_pathIntegral hφ hclosed (hγ.of_le (by simp)) fun _ ↦ rfl]

/-- A smooth circle-valued map on a preconnected manifold whose `dlog` has vanishing periods is
`exp (i f)` for a smooth real function `f`. -/
private theorem exists_eq_circleExp_of_homologyPeriodHom_eq_zero [PreconnectedSpace M]
    {u : C^∞⟮I, M; 𝓡 1, Circle⟯} (h : homologyPeriodHom (mlogDeriv I fun x ↦ (u x : ℂ)) = 0) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ ∀ x, u x = Circle.exp (f x) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨0, contMDiff_const, isEmptyElim⟩
  have hu := contMDiff_coe_circle u
  have hu₀ (x : M) : (u x : ℂ) ≠ 0 := Circle.coe_ne_zero (u x)
  have hφ := isSmoothForm_mlogDeriv (n := ∞) (hu.of_le (by simp)) hu₀
  have hclosed := mextDeriv_mlogDeriv (hu.of_le (by simp)) hu₀
  -- Vanishing periods make `dlog u` exact: `dlog u = dg`.
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero (r := ⊤) le_top
    hφ hclosed x₀ fun γ hγ hγ₀ hγ₁ ↦ by
      obtain ⟨c, hc⟩ := pathIntegral_eq_homologyPeriodHom (hφ.of_le (by simp)) hclosed hγ hγ₀ hγ₁
      rw [hc, h, AddMonoidHom.zero_apply]
  rw [RoughForm.eq_ofFunction ψ] at hψ hdψ
  set g : M → ℂ := fun x ↦ ψ x 0
  have hg : ContMDiff I 𝓘(ℝ, ℂ) ∞ g := isSmoothForm_ofFunction_iff.mp hψ
  have hgU : IsPrimitiveOn (mlogDeriv I fun x ↦ (u x : ℂ)) g univ :=
    ⟨isOpen_univ, (hg.mdifferentiable (by simp)).mdifferentiableOn, fun y _ ↦ congrFun hdψ y⟩
  -- Hence `u exp (-g)` is locally constant, so constant: `u = exp (a + g)`.
  have hconst : IsLocallyConstant fun x ↦ (u x : ℂ) * exp (-g x) :=
    (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦
      hgU.eventually_mul_exp_neg_eq (hu.mdifferentiable (by simp)).mdifferentiableOn
        (fun y _ ↦ hu₀ y) (mem_univ x)
  set a := log ((u x₀ : ℂ) * exp (-g x₀))
  have hexp (x : M) : (u x : ℂ) = exp (a + g x) := by
    rw [exp_add, exp_log (mul_ne_zero (hu₀ x₀) (exp_ne_zero _)),
      hconst.apply_eq_of_preconnectedSpace x₀ x, mul_assoc, ← exp_add, neg_add_cancel,
      exp_zero, mul_one]
  -- The exponent is imaginary because `u` has modulus one.
  have hre (x : M) : (a + g x).re = 0 := by
    have h1 := congrArg norm (hexp x)
    rw [Circle.norm_coe, norm_exp] at h1
    exact (Real.exp_eq_one_iff _).mp h1.symm
  refine ⟨fun x ↦ (a + g x).im, imCLM.contDiff.contMDiff.comp (contMDiff_const.add hg),
    fun x ↦ Circle.ext ?_⟩
  rw [Circle.coe_exp, hexp x]
  congr 1
  apply Complex.ext <;> simp [hre x]

/-- **The kernel of the period map is the identity component.** On a preconnected manifold, a
smooth circle-valued map has vanishing periods exactly when it is `exp (i f)` for a smooth real
function `f`, that is, when it has a smooth logarithm. -/
theorem circlePeriodHom_eq_one_iff [PreconnectedSpace M] {u : C^∞⟮I, M; 𝓡 1, Circle⟯} :
    circlePeriodHom I M u = 1 ↔
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ ∀ x, u x = Circle.exp (f x) := by
  have hper : circlePeriodHom I M u = 1 ↔
      homologyPeriodHom (mlogDeriv I fun x ↦ (u x : ℂ)) = 0 := by
    rw [← toAdd_eq_zero]
    refine ⟨fun h ↦ AddMonoidHom.ext fun c ↦ ?_, fun h ↦ AddMonoidHom.ext fun c ↦ ?_⟩
    · rw [homologyPeriodHom_mlogDeriv_eq_circlePeriodHom, h]
      simp
    · refine intCast_mul_two_pi_I_injective ?_
      simpa [h] using (homologyPeriodHom_mlogDeriv_eq_circlePeriodHom u c).symm
  rw [hper]
  refine ⟨exists_eq_circleExp_of_homologyPeriodHom_eq_zero, fun ⟨f, hf, huf⟩ ↦ ?_⟩
  have hg : ContMDiff I 𝓘(ℝ, ℂ) 2 fun x ↦ (f x : ℂ) * Complex.I :=
    (ofRealCLM.contDiff.mul contDiff_const).contMDiff.comp (hf.of_le (by simp))
  exact homologyPeriodHom_mlogDeriv_eq_zero_of_eq_exp hg fun x ↦ by rw [huf x, Circle.coe_exp]

/-- **Closed imaginary forms with periods in `2πiℤ` are logarithmic derivatives of circle-valued
maps.** On a preconnected manifold, a smooth closed imaginary `1`-form whose integrals over
singular `1`-cycles lie in `2πiℤ` is `dlog u` for a smooth map `u : M → U(1)`. -/
theorem exists_mlogDeriv_coe_eq [PreconnectedSpace M] {φ : RoughForm I M ℂ 1}
    (hφ : IsSmoothForm I ∞ φ) (hclosed : mextDeriv φ = 0) (hre : ∀ x v, (φ x v).re = 0)
    (hper : ∀ c, ∃ n : ℤ, homologyPeriodHom φ c = n * (2 * π * Complex.I)) :
    ∃ u : C^∞⟮I, M; 𝓡 1, Circle⟯, mlogDeriv I (fun x ↦ (u x : ℂ)) = φ := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, funext isEmptyElim⟩
  obtain ⟨u, hu, -, hu₁, hdu⟩ := exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul
    (r := ⊤) le_top hφ hclosed x₀ fun γ hγ hγ₀ hγ₁ ↦ by
      obtain ⟨c, hc⟩ := pathIntegral_eq_homologyPeriodHom (hφ.of_le (by simp)) hclosed hγ hγ₀ hγ₁
      rw [hc]
      exact hper c
  have hnorm (x : M) : u x ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_eq_of_re_mlogDeriv_apply_eq_zero
      (hu.mdifferentiable (by simp)) (hdu ▸ hre) x x₀, hu₁, norm_one]
  exact ⟨⟨fun x ↦ ⟨u x, hnorm x⟩, hu.codRestrict_sphere hnorm⟩, hdu⟩

/-- **The image of the period map.** On a preconnected manifold, a homomorphism
`n : H₁(M; ℤ) → ℤ` is the period of a smooth circle-valued map exactly when `2πi n` is the period
homomorphism of a smooth closed imaginary `1`-form. -/
theorem mem_range_circlePeriodHom_iff [PreconnectedSpace M]
    {n : Multiplicative (((singularChains ℤ).obj (.of M)).homology 1 →+ ℤ)} :
    n ∈ (circlePeriodHom I M).range ↔ ∃ φ : RoughForm I M ℂ 1, IsSmoothForm I ∞ φ ∧
      mextDeriv φ = 0 ∧ (∀ x v, (φ x v).re = 0) ∧
      ∀ c, homologyPeriodHom φ c = (Multiplicative.toAdd n c : ℂ) * (2 * π * Complex.I) := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨φ, hφ, hclosed, hre, hper⟩ ↦ ?_⟩
  · have hc := contMDiff_coe_circle u
    have hu₀ (x : M) : (u x : ℂ) ≠ 0 := Circle.coe_ne_zero (u x)
    refine ⟨_, isSmoothForm_mlogDeriv (n := ∞) (hc.of_le (by simp)) hu₀,
      mextDeriv_mlogDeriv (hc.of_le (by simp)) hu₀,
      fun x v ↦ re_mlogDeriv_apply_eq_zero ((hc x).mdifferentiableAt (by simp))
        (Eventually.of_forall fun y ↦ Circle.norm_coe (u y)) v, fun c ↦ ?_⟩
    rw [homologyPeriodHom_mlogDeriv_eq_circlePeriodHom, hu]
  · obtain ⟨u, hu⟩ := exists_mlogDeriv_coe_eq hφ hclosed hre fun c ↦ ⟨_, hper c⟩
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    refine AddMonoidHom.ext fun c ↦ intCast_mul_two_pi_I_injective ?_
    simp only [← homologyPeriodHom_mlogDeriv_eq_circlePeriodHom, hu, hper]

end TauCeti
