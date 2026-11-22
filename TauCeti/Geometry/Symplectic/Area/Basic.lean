/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Geometry.Symplectic.Duality
import TauCeti.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Calculus.FDeriv.Submodule

/-!
# Integrability and Stokes formulas for symplectic area

For a constant symplectic form `ω`, the primitive `λₓ(v) = ½ ω(x, v)` identifies the
symplectic area of a `C²` map on a closed rectangle with the integral of `λ` over its positively
oriented boundary (`TauCeti.SymplecticForm.integral_fderiv_apply_prod_Icc`), and the symplectic
area of a `C²` map on a closed annulus with the difference of its boundary actions.
The outer and inner circles are both parametrized counterclockwise on `[-π, π]`, and the inner
action is subtracted. No extension across the inner disc is needed. Together with the
isoperimetric inequality for the boundary loops, this is the Stokes step used in energy decay
and removal of singularities for holomorphic curves. On a closed upper half-annulus, for a map
that is `C²` up to the diameter and sends it into a subspace on which `ω` vanishes, the
symplectic area is the difference of the actions of the two half-circles, parametrized on
`[0, π]`: the primitive vanishes along the diameter
(`TauCeti.SymplecticForm.integral_fderivWithin_apply_upperHalfAnnulus`).

For a loop `x : [0, 1] → V`, the integral of `λ` along it is the loop area
`a(x) = ½ ∫₀¹ ω(x(t), x'(t)) dt` (`TauCeti.SymplecticForm.loopArea`). If the bottom and top sides
of a map `u` on `[a, b] × [0, 1]` agree, so that each `t ↦ u(s, t)` is a loop, the rectangle
formula says that the symplectic area of `u` is `a(u(b, ·)) - a(u(a, ·))`
(`TauCeti.SymplecticForm.integral_symplecticForm_fderiv_eq_loopArea_sub`). In particular the loop
area of a closed loop is the symplectic area of the cone `r x(t)` bounding it
(`TauCeti.SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`). Reparametrizing one
period of a `2π`-periodic curve backwards as a loop on `[0, 1]` negates its area over `[-π, π]`
(`TauCeti.SymplecticForm.loopArea_comp_sub_mul`); in particular a circle traversed clockwise has
minus the loop area of the counterclockwise circle
(`TauCeti.SymplecticForm.loopArea_comp_circleMap_sub_mul`). Traversing a loop of period one
backwards negates its area (`TauCeti.SymplecticForm.loopArea_comp_neg`).
The area of `u` vanishes when `u` vanishes on the slices `s = a` and `s = b`
(`TauCeti.SymplecticForm.integral_symplecticForm_fderiv_prod_Icc_eq_zero_of_periodic`).

The loop area is Lipschitz for the uniform distance between closed loops whose speed is bounded
by `L`: `|a(x) - a(y)| ≤ ‖ω‖ L sup ‖x - y‖`, with no closeness of the derivatives required
(`TauCeti.SymplecticForm.abs_loopArea_sub_loopArea_le`). So the loop areas, and the actions, of
loops of bounded speed are controlled by their uniform limits.

A square-integrable differential also gives an integrable symplectic area density, on any domain
and along any two directions
(`TauCeti.SymplecticForm.integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq`).
Pairing bounded loops with functions whose norms have vanishing mean over `[0, 1]` gives
integrals of the symplectic form that tend to zero
(`TauCeti.SymplecticForm.tendsto_integral_apply_of_tendsto_integral_norm`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.5.
-/

public section

open Filter MeasureTheory Set Complex Topology
open scoped Real Interval

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A square-integrable differential has integrable symplectic area density
`ω(du(z) a, du(z) b)`, on any domain and for any two directions `a, b`; for maps of `ℂ` take
`a = 1`, `b = I`. -/
theorem integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq
    [FiniteDimensional ℝ V] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
    (ω : SymplecticForm V) {u : E → V} {D : Set E} (a b : E)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) D μ) :
    IntegrableOn (fun z ↦ ω (fderiv ℝ u z a) (fderiv ℝ u z b)) D μ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  let B := ω.toBilinForm.toContinuousBilinearMap
  have hmeas : AEStronglyMeasurable
      (fun z ↦ ω (fderiv ℝ u z a) (fderiv ℝ u z b)) (μ.restrict D) := by
    have hc : Continuous (fun p : V × V ↦ B p.1 p.2) := by fun_prop
    exact (hc.measurable.comp ((measurable_fderiv_apply_const ℝ u a).prodMk
      (measurable_fderiv_apply_const ℝ u b))).aestronglyMeasurable
  refine (henergy.const_mul (‖B‖ * ‖a‖ * ‖b‖)).mono' hmeas (ae_of_all _ fun z ↦ ?_)
  calc ‖ω (fderiv ℝ u z a) (fderiv ℝ u z b)‖
      ≤ ‖B‖ * ‖fderiv ℝ u z a‖ * ‖fderiv ℝ u z b‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (‖fderiv ℝ u z‖ * ‖a‖) * (‖fderiv ℝ u z‖ * ‖b‖) := by
      gcongr <;> exact (fderiv ℝ u z).le_opNorm _
    _ = ‖B‖ * ‖a‖ * ‖b‖ * ‖fderiv ℝ u z‖ ^ 2 := by ring

/-- **Pairing with functions of vanishing mean norm.** If the loops `y_i` are bounded by `R` and the
integrals over `[0, 1]` of the norms of the continuous `d_i` tend to `0`, then so do the integrals
`∫₀¹ ω(y_i(t), d_i(t)) dt`. -/
theorem tendsto_integral_apply_of_tendsto_integral_norm [FiniteDimensional ℝ V]
    {ω : SymplecticForm V} {ι : Type*} {l : Filter ι}
    {y d : ι → ℝ → V} {R : ℝ} (hy : ∀ i t, ‖y i t‖ ≤ R) (hd : ∀ i, Continuous (d i))
    (hdl : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ‖d i t‖) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ω (y i t) (d i t)) l (𝓝 0) := by
  set Bω := ω.toBilinForm.toContinuousBilinearMap
  have hω : ∀ v w, |ω v w| ≤ ‖Bω‖ * ‖v‖ * ‖w‖ := fun v w ↦ by
    simpa only [Bω, LinearMap.toContinuousBilinearMap_apply, Real.norm_eq_abs] using
      Bω.le_opNorm₂ v w
  have hlim := hdl.const_mul (‖Bω‖ * R)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm (fun i ↦ ?_) hlim
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall fun t _ ↦ ?_) ((continuous_const.mul (hd i).norm).intervalIntegrable _ _)
  rw [Real.norm_eq_abs]
  refine (hω _ _).trans ?_
  gcongr
  exact hy i t

/-- The area density of a map which is `C¹` near a compact set is integrable on it. -/
theorem integrableOn_fderiv_apply_of_contDiffAt [FiniteDimensional ℝ V] (ω : SymplecticForm V)
    {v : ℂ → V} {K : Set ℂ} (hK : IsCompact K) (hv : ∀ z ∈ K, ContDiffAt ℝ 1 v z) :
    IntegrableOn (fun z ↦ ω (fderiv ℝ v z 1) (fderiv ℝ v z I)) K := by
  have hcont : ContinuousOn (fderiv ℝ v) K := fun z hz ↦
    ((hv z hz).continuousAt_fderiv one_ne_zero).continuousWithinAt
  exact (ω.continuousOn_apply_comp (hcont.clm_apply continuousOn_const)
    (hcont.clm_apply continuousOn_const)).integrableOn_compact hK

/-- **Stokes' formula for symplectic area on a rectangle.** If `u` is `C²` at every point of the
rectangle `Icc a b ⊆ ℝ × ℝ`, its symplectic area over the rectangle is the integral of the
primitive `λₓ(v) = ½ ω(x, v)` along the positively oriented boundary: the right side minus the
left side of `t ↦ ½ ω(u, ∂t u)`, minus the top side minus the bottom side of
`s ↦ ½ ω(u, ∂s u)`. -/
theorem integral_fderiv_apply_prod_Icc [FiniteDimensional ℝ V] (ω : SymplecticForm V)
    {u : ℝ × ℝ → V} {a b : ℝ × ℝ} (hle : a ≤ b) (hu : ∀ z ∈ Icc a b, ContDiffAt ℝ 2 u z) :
    ∫ z in Icc a b, ω (fderiv ℝ u z (1, 0)) (fderiv ℝ u z (0, 1)) =
      (1 / 2 : ℝ) * (((∫ t in a.2..b.2, ω (u (b.1, t)) (fderiv ℝ u (b.1, t) (0, 1))) -
          ∫ t in a.2..b.2, ω (u (a.1, t)) (fderiv ℝ u (a.1, t) (0, 1))) -
        ((∫ s in a.1..b.1, ω (u (s, b.2)) (fderiv ℝ u (s, b.2) (1, 0))) -
          ∫ s in a.1..b.1, ω (u (s, a.2)) (fderiv ℝ u (s, a.2) (1, 0)))) := by
  let B := ω.toBilinForm.toContinuousBilinearMap
  have hgreen := B.integral_bilinear_fderiv_sub_prod_Icc hle hu
  simp only [B, toContinuousBilinearMap_sub_swap, integral_const_mul] at hgreen
  simp only [LinearMap.toContinuousBilinearMap_apply] at hgreen
  linarith

section LoopArea

/-- The symplectic area `½ ∫₀¹ ω(x(t), x'(t)) dt` of a loop `x : [0, 1] → V`: the integral of the
primitive `λₓ(v) = ½ ω(x, v)` of `ω` along the loop. For a closed loop it is the symplectic area
of the cone `r x(t)` bounding it (`SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`).
-/
noncomputable def loopArea (ω : SymplecticForm V) (x : ℝ → V) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, ω (x t) (deriv x t)

theorem loopArea_def (ω : SymplecticForm V) (x : ℝ → V) :
    ω.loopArea x = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, ω (x t) (deriv x t) :=
  (rfl)

/-- A constant loop has zero symplectic area. -/
@[simp]
theorem loopArea_const (ω : SymplecticForm V) (v : V) : ω.loopArea (fun _ ↦ v) = 0 := by
  simp [loopArea_def]

/-- **The loop area of a circle traversed backwards.** If `g` is `2π`-periodic, the loop
`t ↦ g(θ₀ - 2πt)` runs once through a period of `g` in the reverse direction, so its loop area
is minus the area `½ ∫_{-π}^{π} ω(g(θ), g'(θ)) dθ` of `g` over one period. -/
theorem loopArea_comp_sub_mul (ω : SymplecticForm V) {g : ℝ → V} (hg : Function.Periodic g (2 * π))
    (θ₀ : ℝ) :
    ω.loopArea (fun t ↦ g (θ₀ - 2 * π * t)) =
      -((1 / 2 : ℝ) * ∫ θ in -π..π, ω (g θ) (deriv g θ)) := by
  have hderiv (t : ℝ) :
      deriv (fun t ↦ g (θ₀ - 2 * π * t)) t = -(2 * π) • deriv g (θ₀ - 2 * π * t) := by
    rw [deriv_comp_mul_left (2 * π) (fun x ↦ g (θ₀ - x)) t, deriv_comp_const_sub, smul_neg,
      neg_smul]
  have hper : Function.Periodic (fun θ ↦ ω (g θ) (deriv g θ)) (2 * π) := fun θ ↦ by
    simp only [hg.deriv θ, hg θ]
  -- Substitute `θ = θ₀ - 2πt`, then shift the period interval to `[-π, π]`.
  have hsub := intervalIntegral.integral_comp_sub_mul (fun θ ↦ ω (g θ) (deriv g θ))
    (a := 0) (b := 1) (mul_ne_zero two_ne_zero Real.pi_ne_zero) θ₀
  have hshift := hper.intervalIntegral_add_eq (θ₀ - 2 * π) (-π)
  simp only [mul_one, mul_zero, sub_zero, sub_add_cancel,
    show -π + 2 * π = π by ring] at hsub hshift
  have hsmul (t : ℝ) : ω (g (θ₀ - 2 * π * t)) (-(2 * π) • deriv g (θ₀ - 2 * π * t)) =
      -(2 * π) * ω (g (θ₀ - 2 * π * t)) (deriv g (θ₀ - 2 * π * t)) := by
    simp
  rw [loopArea_def]
  simp only [hderiv, hsmul, intervalIntegral.integral_const_mul, hsub, hshift, smul_eq_mul]
  field_simp

/-- **The loop area of a circle traversed forwards.** If `g` is `2π`-periodic, the loop
`t ↦ g(θ₀ + 2πt)` runs once through a period of `g`, so its loop area is the area
`½ ∫_{-π}^{π} ω(g(θ), g'(θ)) dθ` of `g` over one period. -/
theorem loopArea_comp_add_mul (ω : SymplecticForm V) {g : ℝ → V} (hg : Function.Periodic g (2 * π))
    (θ₀ : ℝ) :
    ω.loopArea (fun t ↦ g (θ₀ + 2 * π * t)) =
      (1 / 2 : ℝ) * ∫ θ in -π..π, ω (g θ) (deriv g θ) := by
  -- Traverse the reflected function `θ ↦ g(-θ)` backwards.
  have hg' : Function.Periodic (fun θ ↦ g (-θ)) (2 * π) := fun θ ↦ by
    simp only
    rw [show -(θ + 2 * π) = -θ - 2 * π by ring, ← hg (-θ - 2 * π), sub_add_cancel]
  have h := ω.loopArea_comp_sub_mul hg' (-θ₀)
  have hloop : (fun t ↦ g (-(-θ₀ - 2 * π * t))) = fun t ↦ g (θ₀ + 2 * π * t) :=
    funext fun t ↦ congrArg g (by ring)
  simp only [hloop, deriv_comp_neg, map_neg] at h
  rw [h, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg (fun θ ↦ ω (g θ) (deriv g θ)), neg_neg]
  ring

/-- **The loop area of a circle traversed clockwise.** The loop `t ↦ u(c + r e^{i(θ₀ - 2πt)})`,
which runs once clockwise around the circle of radius `r` about `c`, has minus the loop area of
the counterclockwise loop `t ↦ u(c + r e^{2πit})`. -/
theorem loopArea_comp_circleMap_sub_mul (ω : SymplecticForm V) (u : ℂ → V) (c : ℂ) (r θ₀ : ℝ) :
    ω.loopArea (fun t ↦ u (circleMap c r (θ₀ - 2 * π * t))) =
      -ω.loopArea (fun t ↦ u (circleMap c r (2 * π * t))) := by
  have hg : Function.Periodic (fun θ ↦ u (circleMap c r θ)) (2 * π) :=
    (periodic_circleMap c r).comp u
  have h := ω.loopArea_comp_add_mul hg 0
  simp only [zero_add] at h
  rw [ω.loopArea_comp_sub_mul hg θ₀, h]

/-- **The loop area of a loop traversed backwards.** If `x` is `1`-periodic, the loop
`t ↦ x(-t)` has the opposite loop area. -/
theorem loopArea_comp_neg (ω : SymplecticForm V) {x : ℝ → V} (hx : Function.Periodic x 1) :
    ω.loopArea (fun t ↦ x (-t)) = -ω.loopArea x := by
  have hper : Function.Periodic (fun t ↦ ω (x t) (deriv x t)) 1 := fun t ↦ by
    simp only [hx t, hx.deriv t]
  have h := hper.intervalIntegral_add_eq (-1) 0
  rw [neg_add_cancel, zero_add] at h
  simp only [loopArea_def, deriv_comp_neg, map_neg, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg (fun t ↦ ω (x t) (deriv x t)), neg_zero, h]
  ring

variable [FiniteDimensional ℝ V] {u : ℝ × ℝ → V} {a b : ℝ}

/-- **The symplectic area of a cylinder.** Let `u` be `C²` near `[a, b] × [0, 1]`, with
`u(s, 1) = u(s, 0)` for `s ∈ [a, b]`, so that each `t ↦ u(s, t)` is a loop. Then the symplectic
area of `u` over the rectangle is the area of the loop at `s = b` minus the area of the loop at
`s = a`. -/
theorem integral_symplecticForm_fderiv_eq_loopArea_sub (ω : SymplecticForm V) (hab : a ≤ b)
    (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      ω.loopArea (fun t ↦ u (b, t)) - ω.loopArea (fun t ↦ u (a, t)) := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := (Icc_prod_Icc _ _ _ _)
  -- The partial derivatives of `u` are the derivatives of its restrictions to lines.
  have hpartial {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ u (s, t)) (fderiv ℝ u (s, t) (1, 0)) s ∧
        HasDerivAt (fun t ↦ u (s, t)) (fderiv ℝ u (s, t) (0, 1)) t := by
    have hd := ((hu (s, t) ⟨hs, ht⟩).differentiableAt (by norm_num)).hasFDerivAt
    exact ⟨hd.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t)),
      hd.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))⟩
  -- The vertical sides integrate the primitive along the loops `t ↦ u(s, t)`.
  have hvert {s : ℝ} (hs : s ∈ Icc a b) :
      ∫ t in (0 : ℝ)..1, ω (u (s, t)) (fderiv ℝ u (s, t) (0, 1)) =
        ∫ t in (0 : ℝ)..1, ω (u (s, t)) (deriv (fun t ↦ u (s, t)) t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [(hpartial hs ht).2.deriv]
  -- The bottom and top sides agree, so their contributions cancel.
  have hhor : ∫ s in a..b, ω (u (s, 1)) (fderiv ℝ u (s, 1) (1, 0)) =
      ∫ s in a..b, ω (u (s, 0)) (fderiv ℝ u (s, 0) (1, 0)) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
    have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
    have heq : (fun s ↦ u (s, 1)) =ᶠ[𝓝 s] fun s ↦ u (s, 0) :=
      eventually_of_mem (Icc_mem_nhds hs.1 hs.2) hper
    rw [← (hpartial hs' ⟨zero_le_one, le_rfl⟩).1.deriv,
      ← (hpartial hs' ⟨le_rfl, zero_le_one⟩).1.deriv, heq.deriv_eq, hper s hs']
  have harea := ω.integral_fderiv_apply_prod_Icc (Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩) (hR ▸ hu)
  rw [hvert ⟨hab, le_rfl⟩, hvert ⟨le_rfl, hab⟩, hhor, ← hR] at harea
  rw [loopArea_def, loopArea_def, stdComplexLineReal_eq, stdComplexLineImag_eq, harea]
  ring

/-- **The symplectic area of a cylinder with vanishing ends.** Let `u` be `C²` near
`[a, b] × [0, 1]`, with `u(s, 1) = u(s, 0)` for `s ∈ [a, b]`, and let `u` vanish on the slices
`s = a` and `s = b`. Then the symplectic area of `u` over the rectangle is zero. -/
theorem integral_symplecticForm_fderiv_prod_Icc_eq_zero_of_periodic (ω : SymplecticForm V)
    (hab : a ≤ b) (hu : ∀ z ∈ Icc a b ×ˢ Icc 0 1, ContDiffAt ℝ 2 u z)
    (hper : ∀ s ∈ Icc a b, u (s, 1) = u (s, 0)) (ha : ∀ t, u (a, t) = 0)
    (hb : ∀ t, u (b, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc 0 1,
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) = 0 := by
  rw [ω.integral_symplecticForm_fderiv_eq_loopArea_sub hab hu hper]
  simp only [ha, hb, loopArea_const, sub_self]

/-- **The loop area is the area of a cap.** For a loop `x` that is `C²` near `[0, 1]` with
`x 1 = x 0`, the symplectic area of the cone `D(r, t) = r x(t)` over `[0, 1] × [0, 1]`, a disc
bounding `x`, is the loop area of `x`. -/
theorem integral_symplecticForm_fderiv_smul_eq_loopArea (ω : SymplecticForm V) {x : ℝ → V}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 x t) (hx₁ : x 1 = x 0) :
    ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        ω (fderiv ℝ (fun w : ℝ × ℝ ↦ w.1 • x w.2) z stdComplexLineReal)
          (fderiv ℝ (fun w : ℝ × ℝ ↦ w.1 • x w.2) z stdComplexLineImag) =
      ω.loopArea x := by
  rw [integral_symplecticForm_fderiv_eq_loopArea_sub (u := fun w : ℝ × ℝ ↦ w.1 • x w.2) ω
    zero_le_one
    (fun z hz ↦ contDiffAt_fst.smul ((hx z.2 hz.2).comp z contDiffAt_snd))
    (fun s _ ↦ by simp only [hx₁])]
  simp

/-- **The loop area is Lipschitz for the uniform distance between loops of bounded speed.** Let
`x` and `y` be closed loops, `x 1 = x 0` and `y 1 = y 0`, differentiable at every point of
`[0, 1]` with derivatives continuous there and of norm at most `L`. If `‖x t - y t‖ ≤ η` on
`[0, 1]`, then their loop areas differ by at most `‖ω‖ L η`. No closeness of the derivatives is
needed: the difference of the areas is `½ ∫₀¹ ω(x - y, x' + y')`, because the remaining terms
`ω(y', x - y) + ω(y, x' - y')` are the derivative of `ω(y, x - y)`, which integrates to zero over
closed loops. -/
theorem abs_loopArea_sub_loopArea_le (ω : SymplecticForm V) {x y : ℝ → V} {L η : ℝ}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ x t)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ y t)
    (hx' : ContinuousOn (deriv x) (Icc 0 1)) (hy' : ContinuousOn (deriv y) (Icc 0 1))
    (hx₁ : x 1 = x 0) (hy₁ : y 1 = y 0) (hxL : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv x t‖ ≤ L)
    (hyL : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv y t‖ ≤ L) (hxy : ∀ t ∈ Icc (0 : ℝ) 1, ‖x t - y t‖ ≤ η) :
    |ω.loopArea x - ω.loopArea y| ≤ ‖ω.toBilinForm.toContinuousBilinearMap‖ * L * η := by
  have hC : 0 ≤ ‖ω.toBilinForm.toContinuousBilinearMap‖ :=
    ω.toBilinForm.toContinuousBilinearMap.opNorm_nonneg
  have hxc : ContinuousOn x (Icc 0 1) := fun t ht ↦ (hx t ht).continuousAt.continuousWithinAt
  have hyc : ContinuousOn y (Icc 0 1) := fun t ht ↦ (hy t ht).continuousAt.continuousWithinAt
  rw [← uIcc_of_le zero_le_one] at hx hy hx' hy' hxc hyc hxL hyL hxy
  -- The derivative of `ω(y, x - y)` integrates to zero over the closed loops.
  have hdi : IntervalIntegrable
      (fun t ↦ ω (deriv y t) (x t - y t) + ω (y t) (deriv x t - deriv y t)) volume 0 1 :=
    ((ω.continuousOn_apply_comp hy' (hxc.sub hyc)).add
      (ω.continuousOn_apply_comp hyc (hx'.sub hy'))).intervalIntegrable
  have hd : ∫ t in (0 : ℝ)..1, (ω (deriv y t) (x t - y t) + ω (y t) (deriv x t - deriv y t)) =
      0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ ω (y t) (x t - y t))
      (fun t ht ↦ ω.hasDerivAt_apply_comp (hy t ht).hasDerivAt
        ((hx t ht).hasDerivAt.sub (hy t ht).hasDerivAt)) hdi]
    simp [hx₁, hy₁]
  -- Pointwise, the difference of the area densities is `ω(x - y, x' + y')` plus that derivative.
  have hpt (t : ℝ) : ω (x t) (deriv x t) - ω (y t) (deriv y t) =
      ω (x t - y t) (deriv x t + deriv y t) +
        (ω (deriv y t) (x t - y t) + ω (y t) (deriv x t - deriv y t)) := by
    have h₁ : ω (deriv y t) (x t) = -ω (x t) (deriv y t) := (ω.neg_eq _ _).symm
    have h₂ : ω (deriv y t) (y t) = -ω (y t) (deriv y t) := (ω.neg_eq _ _).symm
    simp only [map_sub, map_add, LinearMap.sub_apply] at h₁ h₂ ⊢
    linear_combination h₂ - h₁
  have hmi : IntervalIntegrable (fun t ↦ ω (x t - y t) (deriv x t + deriv y t)) volume 0 1 :=
    (ω.continuousOn_apply_comp (hxc.sub hyc) (hx'.add hy')).intervalIntegrable
  have hdiff : ω.loopArea x - ω.loopArea y =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, ω (x t - y t) (deriv x t + deriv y t) := by
    rw [loopArea_def, loopArea_def, ← mul_sub, ← intervalIntegral.integral_sub
      (ω.continuousOn_apply_comp hxc hx').intervalIntegrable
      (ω.continuousOn_apply_comp hyc hy').intervalIntegrable,
      intervalIntegral.integral_congr (g := fun t ↦ ω (x t - y t) (deriv x t + deriv y t) +
        (ω (deriv y t) (x t - y t) + ω (y t) (deriv x t - deriv y t))) fun t _ ↦ hpt t,
      intervalIntegral.integral_add hmi hdi, hd, add_zero]
  -- The integrand of the remaining term is at most `‖ω‖ η (2 L)`.
  have hbound : ‖∫ t in (0 : ℝ)..1, ω (x t - y t) (deriv x t + deriv y t)‖ ≤
      ‖ω.toBilinForm.toContinuousBilinearMap‖ * η * (2 * L) * |(1 : ℝ) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    have ht' : t ∈ uIcc (0 : ℝ) 1 := uIoc_subset_uIcc ht
    have hL' : ‖deriv x t + deriv y t‖ ≤ 2 * L :=
      (norm_add_le _ _).trans (by linarith [hxL t ht', hyL t ht'])
    rw [Real.norm_eq_abs]
    exact (ω.abs_apply_le_opNorm_mul_norm_mul_norm _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (hxy t ht') hC) hL' (norm_nonneg _)
        (mul_nonneg hC ((norm_nonneg _).trans (hxy t ht'))))
  rw [hdiff, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.norm_eq_abs]
  rw [sub_zero, abs_one, mul_one] at hbound
  linarith

end LoopArea

/-- **Stokes' formula for symplectic area on an annulus.** The pullback area of a `C²` map is
the outer boundary action minus the inner boundary action for the primitive `λₓ(v) = ½ ω(x, v)`.
This identity does not require any regularity on the inner disc or a holomorphicity hypothesis. -/
theorem integral_fderiv_apply_annulus [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      (1 / 2 : ℝ) * ((∫ θ in -π..π, ω (u (circleMap z₀ b θ))
        (deriv (fun θ ↦ u (circleMap z₀ b θ)) θ)) -
      ∫ θ in -π..π, ω (u (circleMap z₀ a θ))
        (deriv (fun θ ↦ u (circleMap z₀ a θ)) θ)) := by
  let B := ω.toBilinForm.toContinuousBilinearMap
  have hcircle (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) :
      deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
        fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) := by
    have hm : circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
      circleMap_mem_setOf_le_norm_sub_le ha hr θ
    exact (((hu _ hm).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ)).deriv
  have hgreen := B.integral_bilinear_fderiv_sub_annulus z₀ ha hab hu
  simp only [B, toContinuousBilinearMap_sub_swap, integral_const_mul] at hgreen
  simp only [LinearMap.toContinuousBilinearMap_apply, ← hcircle b ⟨hab, le_rfl⟩,
    ← hcircle a ⟨le_rfl, hab⟩] at hgreen
  linarith

/-- **Stokes' formula for symplectic area on an upper half-annulus with isotropic diameter.** Let
`u` be `C²` on `{z | z₀.im ≤ z.im} ∩ O` for an open set `O` containing the closed upper half `S` of
the annulus of radii `0 ≤ a ≤ b` about `z₀`, with derivatives taken within the closed half-plane,
and let `u` map the points of `O` on the line `z.im = z₀.im` into a subspace `L` on which `ω`
vanishes. Then the symplectic area of `u` on `S` is the outer minus the inner half-circle action
for the primitive `λₓ(v) = ½ ω(x, v)`, both half-circles traversed from the angle `0` to `π`: the
diameter contributes nothing. -/
theorem integral_fderivWithin_apply_upperHalfAnnulus [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ} {O : Set ℂ} (hO : IsOpen O)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hSO : {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} ⊆ O)
    (hu : ContDiffOn ℝ 2 u ({z : ℂ | z₀.im ≤ z.im} ∩ O)) {L : Submodule ℝ V}
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ O, z.im = z₀.im → u z ∈ L) :
    ∫ z in {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderivWithin ℝ u {z | z₀.im ≤ z.im} z 1) (fderivWithin ℝ u {z | z₀.im ≤ z.im} z I) =
      (1 / 2 : ℝ) * ((∫ θ in 0..π, ω (u (circleMap z₀ b θ))
          (fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ b θ) (circleMap 0 b θ * I))) -
        ∫ θ in 0..π, ω (u (circleMap z₀ a θ))
          (fderivWithin ℝ u {z | z₀.im ≤ z.im} (circleMap z₀ a θ) (circleMap 0 a θ * I))) := by
  set H : Set ℂ := {z | z₀.im ≤ z.im}
  let B := ω.toBilinForm.toContinuousBilinearMap
  -- Along the diameter `u` and its derivative lie in `L`, so the diameter terms vanish.
  have hseg (z : ℂ) (hzO : z ∈ O) (hz : z.im = z₀.im) : B (u z) (fderivWithin ℝ u H z 1) = 0 := by
    have hzHO : z ∈ H ∩ O := ⟨hz.ge, hzO⟩
    have hline : ∀ᶠ t : ℝ in 𝓝 0, z + t • (1 : ℂ) ∈ O :=
      (Continuous.tendsto' (by fun_prop) 0 z (by simp)).eventually (hO.mem_nhds hzO)
    have him (t : ℝ) : (z + t • (1 : ℂ)).im = z₀.im := by simp [hz]
    have hmem := ((hu.differentiableOn (by norm_num)) z hzHO).hasFDerivWithinAt
      |>.apply_mem_of_eventually_add_smul_sub_mem L.isClosed_of_finiteDimensional
        (hline.mono fun t ht ↦ ⟨(him t).ge, ht⟩)
        (hline.mono fun t ht ↦ L.sub_mem (huL _ ht (him t)) (huL z hzO hz))
    rw [LinearMap.toContinuousBilinearMap_apply, ← fderivWithin_inter (hO.mem_nhds hzO)]
    exact hLω _ (huL z hzO hz) _ hmem
  have hdiam (ε : ℝ) (hε : |ε| = 1) :
      ∫ r in a..b, B (u (z₀ + ε * r)) (fderivWithin ℝ u H (z₀ + ε * r) 1) = 0 := by
    rw [← intervalIntegral.integral_zero (a := a) (b := b) (μ := volume) (E := ℝ)]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le hab] at hs
    have him : (z₀ + ε * s).im = z₀.im := by simp
    refine hseg _ (hSO ⟨him.ge, ?_⟩) him
    simpa [hε, abs_of_nonneg (ha.trans hs.1)] using hs
  have hright : ∫ r in a..b, B (u (z₀ + r)) (fderivWithin ℝ u H (z₀ + r) 1) = 0 := by
    simpa only [ofReal_one, one_mul] using hdiam 1 (by simp)
  have hleft : ∫ r in a..b, B (u (z₀ - r)) (fderivWithin ℝ u H (z₀ - r) 1) = 0 := by
    simpa only [ofReal_neg, ofReal_one, neg_one_mul, ← sub_eq_add_neg] using hdiam (-1) (by simp)
  have hgreen := B.integral_bilinear_fderivWithin_sub_upperHalfAnnulus z₀ hO ha hab hSO hu
  rw [hright, hleft, add_zero, add_zero] at hgreen
  simp only [B, toContinuousBilinearMap_sub_swap, integral_const_mul] at hgreen
  simp only [LinearMap.toContinuousBilinearMap_apply] at hgreen
  linarith

end SymplecticForm

end TauCeti
