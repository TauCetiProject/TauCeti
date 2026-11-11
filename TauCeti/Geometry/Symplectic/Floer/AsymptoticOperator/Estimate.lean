/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import TauCeti.Analysis.ODE.Periodic
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The `L²` estimate of the stationary cylinder operator at a nondegenerate orbit

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_t` a continuous family of
`ω`-compatible complex structures with associated inner products `g_t = ω(·, J_t ·)`, and
`S_t` a continuous family of infinitesimally symplectic maps, the linearized Hamiltonian vector
field along an orbit. The linearized Floer operator at the stationary cylinder over the orbit is

`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ) = ∂s ξ + A ξ`

(`TauCeti.Floer.stationaryCylinderOperator`), with the asymptotic operator
`A ζ = J_t (ζ' - S_t ζ)` (`TauCeti.Floer.asymptoticOperator`). This file proves that `D` is
bounded below in `L²` when the orbit is nondegenerate, that is, when the return map `Ψ(1)` of
`ζ' = S_t ζ` does not have `1` as an eigenvalue. This is the basic estimate behind the Fredholm
property of the linearized operator on the cylindrical ends of Floer's moduli spaces.

* **The loop estimate.** If `det (1 - Ψ(1)) ≠ 0`, there is a constant `C` such that every loop
  `ζ` with `ζ 1 = ζ 0` satisfies `∫₀¹ g(ζ, ζ) ≤ C ∫₀¹ g(ζ' - S ζ, ζ' - S ζ)`
  (`Floer.exists_forall_integral_associatedBilinForm_le_mul_integral`), that is,
  `∫₀¹ g(ζ, ζ) ≤ C ∫₀¹ g(A ζ, A ζ)`
  (`Floer.exists_forall_integral_associatedBilinForm_le_mul_integral_asymptoticOperator`). It is
  the `L²` estimate `TauCeti.exists_forall_integral_norm_sq_le_mul_integral_norm_sq` for the
  linear equation `ζ' = S_t ζ + f`, transported to the forms `g_t`, which are uniformly
  equivalent to the norm because `t` ranges over the compact interval `[0, 1]`.
* **The cylinder estimate.** The energy identity
  `Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator` writes
  `∫ g(D ξ, D ξ)` over `[a, b] × [0, 1]` as `∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ))` plus
  slice pairings at `s = a` and `s = b`, which vanish when `ξ` vanishes on those two slices.
  Applying the loop estimate on every slice and integrating over `s` bounds `∫ g(ξ, ξ)` by the
  same quantity, so

  `∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D ξ, D ξ)`

  with `C` independent of `a`, `b` and `ξ`
  (`Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`). For an actual
  nondegenerate one-periodic orbit of a Hamiltonian, the hypothesis on the return map holds
  (`SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`).

* **The estimate in norms, and its perturbations.** Since `g_t` is uniformly equivalent to the
  norm for `t ∈ [0, 1]` and `S_t` is bounded there, the cylinder estimate bounds the square of the
  `W^{1,2}` norm, `∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖D ξ‖²`. In this form it survives
  perturbation: there is `ε > 0` such that the same bound, with a new constant, holds with `D ξ`
  replaced by any `η` satisfying `‖η - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` on the rectangle, because the
  error term is absorbed into the left side.

The two bounds are
`Floer.exists_forall_setIntegral_norm_sq_le_mul_setIntegral_norm_sq_stationaryCylinderOperator`
and `Floer.exists_pos_forall_setIntegral_norm_sq_le_mul_setIntegral_norm_sq_of_norm_sub_le`. The
second is how the estimate passes to the linearized Floer operator along a solution far out on a
cylindrical end
(`SymplecticForm.exists_forall_setIntegral_norm_sq_le_mul_setIntegral_norm_sq_floerLinearization`).

In contrast, `Floer.eq_zero_of_stationaryCylinderOperator_eq_zero` shows that `D` is injective on
decaying maps with no nondegeneracy assumption, but without an estimate; at a degenerate orbit
the loops `t ↦ Ψ(t) v` with `Ψ(1) v = v`, cut off in `s`, show that no estimate of this form can
hold. The estimate is stated for maps vanishing on two slices, the form in which it is applied to
compactly supported maps on a cylindrical end; the Sobolev completion and the Fredholm property
themselves are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

open Function Filter Set MeasureTheory Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}

/-- **The `L²` loop estimate at a nondegenerate orbit.** Let each `J_t` be `ω`-tame and depend
continuously on `t`, let `S` be continuous, and suppose that `det (1 - Ψ(1)) ≠ 0` for the return
map `Ψ(1) = dysonSeriesLeft S 1` of `ζ' = S_t ζ`. Then there is a constant `C ≥ 0` such that
every solution of `ζ' = S_t ζ + f` with `f` continuous and `ζ 1 = ζ 0` satisfies
`∫₀¹ g_t(ζ, ζ) ≤ C ∫₀¹ g_t(f, f)` for `g_t = ω(·, J_t ·)`. -/
theorem exists_forall_integral_associatedBilinForm_le_mul_integral (hJ : ∀ t, ω.Tames (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ζ f : ℝ → V⦄, Continuous f → (∀ t, HasDerivAt ζ (S t (ζ t) + f t) t) →
      ζ 1 = ζ 0 → ∫ t in 0..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤
        C * ∫ t in 0..1, ω.associatedBilinForm (J t) (f t) (f t) := by
  have he : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, b, hb, hab⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    isCompact_Icc he.continuousOn fun t _ ↦ hJ t
  have hP : IsUnit ((1 : ℝ) • 1 - dysonSeriesLeft S 1) := by
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det]
    simpa using hdet
  obtain ⟨C, hC, hle⟩ := exists_forall_integral_norm_sq_le_mul_integral_norm_sq hSc zero_le_one hP
  refine ⟨b * C / a, by positivity, fun ζ f hf hζ hζ1 ↦ ?_⟩
  have hζc : Continuous ζ := continuous_iff_continuousAt.2 fun t ↦ (hζ t).continuousAt
  have h₁ : ∫ t in 0..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤ ∫ t in 0..1, b * ‖ζ t‖ ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one
      ((ω.continuous_apply_comp hζc (hJc.comp (continuous_id.prodMk hζc))).intervalIntegrable _ _)
      ((continuous_const.mul (hζc.norm.pow 2)).intervalIntegrable _ _)
      fun t ht ↦ (hab t ht _).2
  have h₂ : ∫ t in 0..1, a * ‖f t‖ ^ 2 ≤ ∫ t in 0..1, ω.associatedBilinForm (J t) (f t) (f t) :=
    intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul (hf.norm.pow 2)).intervalIntegrable _ _)
      ((ω.continuous_apply_comp hf (hJc.comp (continuous_id.prodMk hf))).intervalIntegrable _ _)
      fun t ht ↦ (hab t ht _).1
  rw [intervalIntegral.integral_const_mul] at h₁ h₂
  have h₃ := hle hf hζ (by rw [hζ1, one_smul])
  calc _ ≤ b * ∫ t in 0..1, ‖ζ t‖ ^ 2 := h₁
    _ ≤ b * (C * ∫ t in 0..1, ‖f t‖ ^ 2) := by gcongr
    _ = b * C / a * (a * ∫ t in 0..1, ‖f t‖ ^ 2) := by field_simp
    _ ≤ b * C / a * ∫ t in 0..1, ω.associatedBilinForm (J t) (f t) (f t) := by gcongr

/-- **The `L²` lower bound of the asymptotic operator at a nondegenerate orbit.** Under the
hypotheses of `exists_forall_integral_associatedBilinForm_le_mul_integral`, there is a constant
`C ≥ 0` such that every `C¹` loop `ζ` with `ζ 1 = ζ 0` satisfies
`∫₀¹ g_t(ζ, ζ) ≤ C ∫₀¹ g_t(A ζ, A ζ)` for the asymptotic operator `A ζ = J_t (ζ' - S_t ζ)`. -/
theorem exists_forall_integral_associatedBilinForm_le_mul_integral_asymptoticOperator
    (hJ : ∀ t, ω.Tames (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ζ : ℝ → V⦄, ContDiff ℝ 1 ζ → ζ 1 = ζ 0 →
      ∫ t in 0..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤
        C * ∫ t in 0..1, ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t)
          (asymptoticOperator J S ζ t) := by
  obtain ⟨C, hC, h⟩ := exists_forall_integral_associatedBilinForm_le_mul_integral hJ hJc hSc hdet
  refine ⟨C, hC, fun ζ hζ hζ1 ↦ ?_⟩
  have hd (t : ℝ) : HasDerivAt ζ (S t (ζ t) + (deriv ζ t - S t (ζ t))) t := by
    rw [add_sub_cancel]
    exact (hζ.differentiable one_ne_zero t).hasDerivAt
  simpa only [asymptoticOperator_def, SymplecticForm.associatedBilinForm_apply_apply_self_eq]
    using h (f := fun t ↦ deriv ζ t - S t (ζ t))
      ((hζ.continuous_deriv le_rfl).sub (hSc.clm_apply hζ.continuous)) hd hζ1

/-- **The cylinder estimate at a nondegenerate orbit.** Let each `J_t` be `ω`-compatible and
depend continuously on `t`, let each `S_t` be infinitesimally symplectic and `S` continuous, and
suppose that `det (1 - Ψ(1)) ≠ 0` for the return map `Ψ(1) = dysonSeriesLeft S 1`. Then there is
a constant `C ≥ 0` such that for every `C²` map `ξ` of period one in `t` and every `a ≤ b` with
`ξ` vanishing on the slices `s = a` and `s = b`,

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D ξ, D ξ)`

over `[a, b] × [0, 1]`, for `g_t = ω(·, J_t ·)` and the stationary cylinder operator
`D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`. The constant does not depend on `a`, `b` or `ξ`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) := by
  obtain ⟨C, hC, hloop⟩ :=
    exists_forall_integral_associatedBilinForm_le_mul_integral (fun t ↦ (hJ t).tames) hJc hSc hdet
  refine ⟨1 + C, by positivity, fun ξ hξ hper a b hab ha hb ↦ ?_⟩
  set w : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)
  have hw : Continuous w := ((hξ.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
    ((hSc.comp continuous_snd).clm_apply hξ.continuous)
  -- The energy identity, whose boundary slices vanish.
  have hid := setIntegral_associatedBilinForm_stationaryCylinderOperator
    (fun t ↦ (hJ t).invariant) hJc hS hSc hξ hper hab
  simp only [ha, hb, map_zero, intervalIntegral.integral_zero, sub_zero, add_zero] at hid
  -- On each slice, the loop estimate bounds `∫ g(ξ, ξ)` by `C ∫ g(w, w)`.
  have hslice (s : ℝ) : ∫ t in Icc (0 : ℝ) 1, ω.associatedBilinForm (J t) (ξ (s, t)) (ξ (s, t)) ≤
      C * ∫ t in Icc (0 : ℝ) 1, ω.associatedBilinForm (J t) (w (s, t)) (w (s, t)) := by
    have hd (t : ℝ) : HasDerivAt (fun t ↦ ξ (s, t)) (S t (ξ (s, t)) + w (s, t)) t := by
      have h := (hξ.differentiable (by norm_num) (s, t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_prodMk_right s t)
      simpa only [w, stdComplexLineImag_eq, add_sub_cancel, Function.comp_def] using h
    have h := hloop (hw.comp (Continuous.prodMk_right s)) hd (by simpa using hper s 0)
    simpa only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      Function.comp_def] using h
  have hrect := isCompact_Icc (a := a) (b := b) |>.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hQ := (continuous_associatedBilinForm_apply_self (ω := ω) hJc hξ.continuous).continuousOn
    |>.integrableOn_compact (μ := volume) hrect
  have hW := (continuous_associatedBilinForm_apply_self (ω := ω) hJc hw).continuousOn
    |>.integrableOn_compact (μ := volume) hrect
  have hE := (continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc
    (hξ.of_le one_le_two)).continuousOn |>.integrableOn_compact (μ := volume) hrect
  have hfub : ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (ξ z) (ξ z) ≤
      C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (w z) (w z) :=
    setIntegral_rect_le_mul_of_forall_setIntegral_le hQ hW fun s _ ↦ hslice s
  -- Hence `∫ (g(∂s ξ) + g(w)) + ∫ g(ξ) ≤ (1 + C) ∫ (g(∂s ξ) + g(w)) = (1 + C) ∫ g(D ξ)`.
  have hW' : ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (w z) (w z) ≤
      ∫ z in Icc a b ×ˢ Icc 0 1, (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) + ω.associatedBilinForm (J z.2) (w z) (w z)) :=
    setIntegral_mono hW hE fun z ↦ le_add_of_nonneg_left ((hJ _).associatedBilinForm_self_nonneg _)
  have hsplit := integral_add hE hQ
  simp only [w] at hsplit hfub hW'
  rw [hsplit, hid]
  linarith [mul_le_mul_of_nonneg_left hW' hC]

/-- The arithmetic step from the energy density to the `W^{1,2}` density: if `m p² ≤ g₁`,
`m w² ≤ g₂`, `m v² ≤ g₃` and `q ≤ w + σ v`, then `p² + q² + v² ≤ (2 + 2σ²) / m (g₁ + g₂ + g₃)`. -/
private theorem sq_add_sq_add_sq_le_of_le_add_mul {m σ p q w v g₁ g₂ g₃ : ℝ} (hm : 0 < m)
    (hq : 0 ≤ q) (h₁ : m * p ^ 2 ≤ g₁)
    (h₂ : m * w ^ 2 ≤ g₂) (h₃ : m * v ^ 2 ≤ g₃) (hqw : q ≤ w + σ * v) :
    p ^ 2 + q ^ 2 + v ^ 2 ≤ (2 + 2 * σ ^ 2) / m * ((g₁ + g₂) + g₃) := by
  have hq2 : q ^ 2 ≤ 2 * w ^ 2 + 2 * σ ^ 2 * v ^ 2 := by
    nlinarith [sq_nonneg (w - σ * v)]
  have hK : 0 ≤ 2 + 2 * σ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left h₁ hK, mul_le_mul_of_nonneg_left h₂ hK,
    mul_le_mul_of_nonneg_left h₃ hK, mul_le_mul_of_nonneg_left hq2 hm.le,
    mul_nonneg (mul_nonneg hm.le (sq_nonneg σ)) (sq_nonneg v),
    mul_nonneg (mul_nonneg hm.le (sq_nonneg σ)) (sq_nonneg w),
    mul_nonneg (mul_nonneg hm.le (sq_nonneg σ)) (sq_nonneg p),
    mul_nonneg hm.le (sq_nonneg p), mul_nonneg hm.le (sq_nonneg v), mul_nonneg hm.le (sq_nonneg w)]

/-- **The cylinder estimate in norms.** Under the hypotheses of
`exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`, there is a constant
`C ≥ 0` such that for every `C²` map `ξ` of period one in `t` and every `a ≤ b` with `ξ` vanishing
on the slices `s = a` and `s = b`,

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖D ξ‖²`

over `[a, b] × [0, 1]`, for the stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`.
The left side is the square of the `W^{1,2}` norm of `ξ` on the rectangle. -/
theorem exists_forall_setIntegral_norm_sq_le_mul_setIntegral_norm_sq_stationaryCylinderOperator
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ‖stationaryCylinderOperator J S ξ z‖ ^ 2 := by
  obtain ⟨C, hC, hcyl⟩ :=
    exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator hJ hJc hS hSc hdet
  -- On `t ∈ [0, 1]` the forms `g_t` are uniformly equivalent to the norm, and `S_t` is bounded.
  have he : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨m, hm, M, hM, hmM⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    isCompact_Icc he.continuousOn fun t _ ↦ (hJ t).tames
  obtain ⟨σ, hσ⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := S) (s := Icc (0 : ℝ) 1)
    hSc.continuousOn
  refine ⟨(2 + 2 * σ ^ 2) / m * (C * M), by positivity, fun ξ hξ hper a b hab ha hb ↦ ?_⟩
  have hξ₁ : ContDiff ℝ 1 ξ := hξ.of_le one_le_two
  have hdξ : Continuous (fderiv ℝ ξ) := hξ₁.continuous_fderiv one_ne_zero
  set R := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hint {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f R :=
    hf.continuousOn.integrableOn_compact hR
  set w : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)
  have hw : Continuous w :=
    (hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hξ.continuous)
  have hD := continuous_stationaryCylinderOperator hJc hSc hξ₁
  -- Pointwise, `‖∂t ξ‖² ≤ 2 ‖∂t ξ - S ξ‖² + 2 σ² ‖ξ‖²`, so the integrand is controlled by the
  -- energy density of the cylinder estimate.
  have hpt : ∀ z ∈ R, ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 ≤
      (2 + 2 * σ ^ 2) / m * ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
          (fderiv ℝ ξ z stdComplexLineReal) + ω.associatedBilinForm (J z.2) (w z) (w z)) +
        ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) := by
    rintro z ⟨-, hz⟩
    have hSz : ‖S z.2 (ξ z)‖ ≤ σ * ‖ξ z‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hσ z.2 hz) (norm_nonneg _))
    have ht : ‖fderiv ℝ ξ z stdComplexLineImag‖ ≤ ‖w z‖ + σ * ‖ξ z‖ := by
      calc _ = ‖w z + S z.2 (ξ z)‖ := by simp only [w, sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by gcongr)
    exact sq_add_sq_add_sq_le_of_le_add_mul hm (norm_nonneg _) (hmM z.2 hz _).1 (hmM z.2 hz _).1
      (hmM z.2 hz _).1 ht
  have hG := (continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc hξ₁).add
    (continuous_associatedBilinForm_apply_self (ω := ω) hJc hξ.continuous)
  calc _ ≤ ∫ z in R, (2 + 2 * σ ^ 2) / m * ((ω.associatedBilinForm (J z.2)
          (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2) (w z) (w z)) + ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) :=
        setIntegral_mono_on (hint (by fun_prop)) (hint (continuous_const.mul hG))
          (measurableSet_Icc.prod measurableSet_Icc) hpt
    _ = (2 + 2 * σ ^ 2) / m * ∫ z in R, ((ω.associatedBilinForm (J z.2)
          (fderiv ℝ ξ z stdComplexLineReal) (fderiv ℝ ξ z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2) (w z) (w z)) +
            ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) := integral_const_mul _ _
    _ ≤ (2 + 2 * σ ^ 2) / m * (C * ∫ z in R, ω.associatedBilinForm (J z.2)
          (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z)) := by
        gcongr ?_ * ?_
        exact hcyl hξ hper hab ha hb
    _ ≤ (2 + 2 * σ ^ 2) / m * (C * ∫ z in R, M * ‖stationaryCylinderOperator J S ξ z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (setIntegral_mono_on
          (hint (continuous_associatedBilinForm_apply_self (ω := ω) hJc hD))
          (hint (by fun_prop)) (measurableSet_Icc.prod measurableSet_Icc)
          fun z hz ↦ (hmM z.2 hz.2 _).2) hC) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- **Perturbations of the stationary cylinder operator.** Under the hypotheses of
`exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`, there are `ε > 0`
and `C ≥ 0` with the following property. Let `ξ` be a `C²` map of period one in `t` vanishing on
the slices `s = a` and `s = b` for some `a ≤ b`, and let `η` be square integrable on the
rectangle `[a, b] × [0, 1]` with

`‖η - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)`

there, for the stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`. Then

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖η‖²`

over the rectangle. Applied to `η = D' ξ`, this transfers the cylinder estimate to every operator
`D'` that differs from `D` by a small zeroth-order term and a small multiple of `∂t`, such as the
linearized Floer operator far out on a cylindrical end. -/
theorem exists_pos_forall_setIntegral_norm_sq_le_mul_setIntegral_norm_sq_of_norm_sub_le
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ ε > 0, ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∀ ⦃η : ℝ × ℝ → V⦄, IntegrableOn (fun z ↦ ‖η z‖ ^ 2) (Icc a b ×ˢ Icc 0 1) →
        (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖η z - stationaryCylinderOperator J S ξ z‖ ≤
          ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ‖η z‖ ^ 2 := by
  obtain ⟨C, hC, hcyl⟩ :=
    exists_forall_setIntegral_norm_sq_le_mul_setIntegral_norm_sq_stationaryCylinderOperator
      hJ hJc hS hSc hdet
  -- With `4 C ε² ≤ 1 / 2`, the error term is absorbed by the left side.
  set ε : ℝ := 1 / (3 * (C + 1))
  have hε : 0 < ε := by positivity
  have hCε : 4 * C * ε ^ 2 ≤ 1 / 2 := by
    simp only [ε]
    field_simp
    nlinarith
  refine ⟨ε, hε, 4 * C, by positivity, fun ξ hξ hper a b hab ha hb η hηi hηD ↦ ?_⟩
  have hξ₁ : ContDiff ℝ 1 ξ := hξ.of_le one_le_two
  have hdξ : Continuous (fderiv ℝ ξ) := hξ₁.continuous_fderiv one_ne_zero
  set R := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hD := continuous_stationaryCylinderOperator hJc hSc hξ₁
  set Q : ℝ × ℝ → ℝ := fun z ↦ ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2
  have hQ : Continuous Q := by fun_prop
  have hQi : IntegrableOn Q R := hQ.continuousOn.integrableOn_compact hR
  -- Pointwise, `‖D ξ‖² ≤ 2 ‖η‖² + 2 ‖η - D ξ‖² ≤ 2 ‖η‖² + 4 ε² Q`.
  have hpt : ∀ z ∈ R, ‖stationaryCylinderOperator J S ξ z‖ ^ 2 ≤
      2 * ‖η z‖ ^ 2 + 4 * ε ^ 2 * Q z := by
    intro z hz
    have hz' := hηD z hz
    have hD' : ‖stationaryCylinderOperator J S ξ z‖ ≤
        ‖η z‖ + ‖η z - stationaryCylinderOperator J S ξ z‖ :=
      (norm_le_insert' _ (η z)).trans_eq (by rw [norm_sub_rev])
    have h0 := norm_nonneg (η z - stationaryCylinderOperator J S ξ z)
    simp only [Q]
    nlinarith [norm_nonneg (stationaryCylinderOperator J S ξ z), norm_nonneg (η z),
      norm_nonneg (fderiv ℝ ξ z stdComplexLineImag), norm_nonneg (ξ z),
      sq_nonneg (‖fderiv ℝ ξ z stdComplexLineImag‖ - ‖ξ z‖),
      sq_nonneg ‖fderiv ℝ ξ z stdComplexLineReal‖,
      sq_nonneg (‖η z‖ - ‖η z - stationaryCylinderOperator J S ξ z‖)]
  have hDint : ∫ z in R, ‖stationaryCylinderOperator J S ξ z‖ ^ 2 ≤
      2 * (∫ z in R, ‖η z‖ ^ 2) + 4 * ε ^ 2 * ∫ z in R, Q z := by
    rw [← integral_const_mul 2, ← integral_const_mul (4 * ε ^ 2),
      ← integral_add (hηi.const_mul 2) (hQi.const_mul (4 * ε ^ 2))]
    exact setIntegral_mono_on ((hD.norm.pow 2).continuousOn.integrableOn_compact hR)
      ((hηi.const_mul _).add (hQi.const_mul _)) hRm hpt
  have hle := hcyl hξ hper hab ha hb
  have hQ0 : 0 ≤ ∫ z in R, Q z := setIntegral_nonneg hRm fun z _ ↦ by positivity
  nlinarith [mul_le_mul_of_nonneg_left hDint hC, mul_le_mul_of_nonneg_right hCε hQ0]

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The cylinder estimate at a nondegenerate Hamiltonian orbit.** Let `x` be a one-periodic
orbit of a one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field
is globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map, and let `J_t`
be `ω`-compatible complex structures depending continuously on `t`. Then the stationary cylinder
operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` along `x`, with `S_t = dX_{H_t}(x(t))`, satisfies the
estimate of `Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → AlmostComplexStructure V} (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z) := by
  have hSc : Continuous fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t) :=
    ω.continuous_fderiv_hamiltonianVectorField_comp hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt)
  exact Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (S := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) hJ hJc
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right t)).contDiffAt) hSc
    (det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt ω hX hH hHp hx hxp hnd)

end SymplecticForm

end TauCeti
