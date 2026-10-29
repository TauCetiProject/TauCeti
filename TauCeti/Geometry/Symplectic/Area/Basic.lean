/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
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
(`TauCeti.SymplecticForm.integral_symplecticForm_fderiv_smul_eq_loopArea`).

A square-integrable differential also gives an integrable symplectic area density, on any domain.

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
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
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

end LoopArea

/-- **Stokes' formula for symplectic area on an annulus.** The pullback area of a `C²` map is
the outer boundary action minus the inner boundary action for the primitive `λₓ(v) = ½ ω(x, v)`.
This identity does not require any regularity on the inner disc or a holomorphicity hypothesis. -/
theorem integral_fderiv_apply_annulus [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
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
        abs_of_nonneg (le_trans ha.le hr.1)] using (mem_Icc.mp hr)
    exact (((hu _ hm).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ)).deriv
  have hgreen := B.integral_bilinear_fderiv_sub_annulus z₀ ha.le hab hu
  simp only [hskew, integral_const_mul] at hgreen
  simp only [hB, ← hcircle b ⟨hab, le_rfl⟩, ← hcircle a ⟨le_rfl, hab⟩] at hgreen
  linarith

end SymplecticForm

end TauCeti
