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
import TauCeti.Geometry.Symplectic.Duality
import TauCeti.MeasureTheory.Integral.DivergenceTheorem

/-!
# Integrability and Stokes formulas for symplectic area

For a constant symplectic form `ω`, the primitive `λₓ(v) = ½ ω(x, v)` identifies the
symplectic area of a `C²` map on a closed rectangle with the integral of `λ` over its positively
oriented boundary (`TauCeti.SymplecticForm.integral_fderiv_apply_prod_Icc`), and the symplectic
area of a `C²` map on a closed annulus with the difference of its boundary actions.
The outer and inner circles are both parametrized counterclockwise on `[-π, π]`, and the inner
action is subtracted. No extension across the inner disc is needed. Together with the
isoperimetric inequality for the boundary loops, this is the Stokes step used in energy decay
and removal of singularities for holomorphic curves.

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
(`TauCeti.SymplecticForm.loopArea_comp_circleMap_sub_mul`).
The area of `u` vanishes when `u` vanishes on the slices `s = a` and `s = b`
(`TauCeti.SymplecticForm.integral_symplecticForm_fderiv_prod_Icc_eq_zero_of_periodic`).

The loop area is Lipschitz for the uniform distance between closed loops whose speed is bounded
by `L`: `|a(x) - a(y)| ≤ ‖ω‖ L sup ‖x - y‖`, with no closeness of the derivatives required
(`TauCeti.SymplecticForm.abs_loopArea_sub_loopArea_le`). So the loop areas, and the actions, of
loops of bounded speed are controlled by their uniform limits.

A square-integrable differential also gives an integrable symplectic area density, on any domain.
Pairing bounded loops with functions whose norms have vanishing mean over `[0, 1]` gives
integrals of the symplectic form that tend to zero
(`TauCeti.SymplecticForm.tendsto_integral_apply_of_tendsto_integral_norm`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.5.
-/

public section

open Filter MeasureTheory Set Complex Topology
open scoped Real

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A square-integrable differential has integrable symplectic area density. -/
theorem integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq
    [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {u : ℂ → V} {D : Set ℂ}
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) D) :
    IntegrableOn (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) D := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  let B := ω.toBilinForm.toContinuousBilinearMap
  have hmeas : AEStronglyMeasurable
      (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) (volume.restrict D) := by
    have hc : Continuous (fun p : V × V ↦ B p.1 p.2) := by fun_prop
    exact (hc.measurable.comp ((measurable_fderiv_apply_const ℝ u 1).prodMk
      (measurable_fderiv_apply_const ℝ u I))).aestronglyMeasurable
  refine (henergy.const_mul ‖B‖).mono' hmeas (ae_of_all _ fun z ↦ ?_)
  have h₁ : ‖fderiv ℝ u z 1‖ ≤ ‖fderiv ℝ u z‖ := by
    simpa using (fderiv ℝ u z).le_opNorm (1 : ℂ)
  have hI : ‖fderiv ℝ u z I‖ ≤ ‖fderiv ℝ u z‖ := by
    simpa using (fderiv ℝ u z).le_opNorm I
  calc ‖ω (fderiv ℝ u z 1) (fderiv ℝ u z I)‖
      ≤ ‖B‖ * ‖fderiv ℝ u z 1‖ * ‖fderiv ℝ u z I‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * ‖fderiv ℝ u z‖ ^ 2 := by
      rw [pow_two, ← mul_assoc]
      gcongr

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
  have hB (x y : V) : B x y = ω x y := by simp [B]
  have hskew (x y : V) : B x y - B y x = 2 * ω x y := by
    rw [hB, hB, ← ω.neg_eq]
    ring
  have hgreen := B.integral_bilinear_fderiv_sub_prod_Icc hle hu
  simp only [hskew, integral_const_mul] at hgreen
  simp only [hB] at hgreen
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
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp ω.toBilinForm)
  have hB (x y : V) : B x y = ω x y := by simp [B]
  have hskew (x y : V) : B x y - B y x = 2 * ω x y := by
    rw [hB, hB, ← ω.neg_eq]
    ring
  have hcircle (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) :
      deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
        fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) := by
    have hm : circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
      simpa only [mem_ofPred_eq, circleMap_sub_center, norm_circleMap_zero,
        abs_of_nonneg (le_trans ha hr.1)] using (mem_Icc.mp hr)
    exact (((hu _ hm).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ)).deriv
  have hgreen := B.integral_bilinear_fderiv_sub_annulus z₀ ha hab hu
  simp only [hskew, integral_const_mul] at hgreen
  simp only [hB, ← hcircle b ⟨hab, le_rfl⟩, ← hcircle a ⟨le_rfl, hab⟩] at hgreen
  linarith

end SymplecticForm

end TauCeti
