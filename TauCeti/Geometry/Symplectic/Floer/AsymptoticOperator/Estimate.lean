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
* **The weighted estimate.** The weighted operator `D - δ` is the stationary cylinder operator of
  `S_t - δ J_t`, whose return map stays nondegenerate for small `δ`, so the cylinder estimate
  holds for `D - δ` for every weight `δ` close to `0`
  (`eventually_exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul`,
  in `Floer` and, at a Hamiltonian orbit, in `SymplecticForm`). Moreover, the
  `e^{2 δ s}`-weighted energy of `η` is controlled by the energy of `e^{δ s} η` for the field
  `S_t - δ J_t` (`Floer.setIntegral_exp_mul_associatedBilinForm_le`), which turns estimates of
  `D - δ` into estimates in `L²` norms with weight `e^{δ s}`.
* **Stability under perturbation.** The cylinder estimate survives replacing `D ξ` by any `η`
  with `‖η - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` for a small `ε` depending only on the constant, `J` and `S`
  (`Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`).
  The perturbation is bounded by `ε` times the quantity being estimated and is absorbed. This is
  the form in which the estimate passes to the linearized operator of a Floer solution on a far
  part of a cylindrical end, which is such a perturbation of `D`
  (`TauCeti.Geometry.Symplectic.Floer.EndLinearization`).

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

/-- The pointwise comparison behind
`exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`, for
numbers: if `g_D ≤ M ‖D‖²`, the forms `g_η, g_s, g_w, g_ξ` dominate `m` times the squared norms,
and `‖D‖ ≤ ‖η‖ + ε N (‖w‖ + ‖ξ‖)`, then `m g_D ≤ 2 M g_η + 4 M ε² N² (g_s + g_w + g_ξ)`. -/
private theorem mul_le_of_norm_le_add {m M ε N gD gη gs gw gξ nD nη ns nw nξ : ℝ}
    (hM : 0 ≤ M) (hm : 0 ≤ m) (hnD : 0 ≤ nD)
    (hgD : gD ≤ M * nD ^ 2) (hgη : m * nη ^ 2 ≤ gη) (hgs : m * ns ^ 2 ≤ gs)
    (hgw : m * nw ^ 2 ≤ gw) (hgξ : m * nξ ^ 2 ≤ gξ) (hD : nD ≤ nη + ε * N * (nw + nξ)) :
    m * gD ≤ 2 * M * gη + 4 * M * ε ^ 2 * N ^ 2 * (gs + gw + gξ) := by
  have hsq : nD ^ 2 ≤ 2 * nη ^ 2 + 4 * ε ^ 2 * N ^ 2 * (nw ^ 2 + nξ ^ 2) := by
    have h₁ := pow_le_pow_left₀ hnD hD 2
    have h₂ : (nw + nξ) ^ 2 ≤ 2 * (nw ^ 2 + nξ ^ 2) := by nlinarith [sq_nonneg (nw - nξ)]
    calc nD ^ 2 ≤ (nη + ε * N * (nw + nξ)) ^ 2 := h₁
      _ ≤ 2 * nη ^ 2 + 2 * (ε * N) ^ 2 * (nw + nξ) ^ 2 := by
        nlinarith [sq_nonneg (nη - ε * N * (nw + nξ))]
      _ ≤ 2 * nη ^ 2 + 2 * (ε * N) ^ 2 * (2 * (nw ^ 2 + nξ ^ 2)) := by gcongr
      _ = _ := by ring
  have hgs₀ : 0 ≤ gs := (mul_nonneg hm (sq_nonneg ns)).trans hgs
  calc m * gD ≤ m * (M * nD ^ 2) := by gcongr
    _ ≤ m * (M * (2 * nη ^ 2 + 4 * ε ^ 2 * N ^ 2 * (nw ^ 2 + nξ ^ 2))) := by gcongr
    _ = 2 * M * (m * nη ^ 2) + 4 * M * ε ^ 2 * N ^ 2 * (m * nw ^ 2 + m * nξ ^ 2) := by ring
    _ ≤ 2 * M * gη + 4 * M * ε ^ 2 * N ^ 2 * (gw + gξ) := by gcongr
    _ ≤ _ := by gcongr; linarith

/-- The absorption step behind
`exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`, for
numbers: if `q ≤ C₀ d`, `m d ≤ 2 M e + k q` and `C₀ k ≤ m / 2` with `q ≥ 0`, then
`q ≤ (4 C₀ M / m) e`. -/
private theorem le_div_mul_of_le_mul_of_mul_le {m M C₀ k q d e : ℝ} (hm : 0 < m)
    (hC₀ : 0 ≤ C₀) (hq : 0 ≤ q) (hqd : q ≤ C₀ * d) (hd : m * d ≤ 2 * M * e + k * q)
    (hk : C₀ * k ≤ m / 2) : q ≤ 4 * C₀ * M / m * e := by
  have h₁ : m * q ≤ C₀ * (m * d) := by nlinarith
  have h₂ : C₀ * (m * d) ≤ C₀ * (2 * M * e) + C₀ * k * q := by nlinarith
  have h₃ : C₀ * k * q ≤ m / 2 * q := mul_le_mul_of_nonneg_right hk hq
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

/-- **The cylinder estimate persists under small perturbations of the operator.** Let each `J_t`
be `ω`-tame and depend continuously on `t`, and let `S` be continuous. For every `C₀ ≥ 0` there are
`ε > 0` and `C ≥ 0` with the following property. Let `ξ` be a `C¹` map satisfying the cylinder
estimate with constant `C₀` over `[a, b] × [0, 1]`, as
`exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator` provides at a
nondegenerate orbit, and let `η` be continuous on that rectangle and differ there from the
stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` by at most
`ε (‖∂t ξ‖ + ‖ξ‖)`. Then `η` controls the same quantity:

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(η, η)`

over `[a, b] × [0, 1]`, for `g_t = ω(·, J_t ·)`. The constants depend only on `C₀`, `J` and `S`,
not on `a`, `b`, `ξ` or `η`. -/
theorem exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le
    (hJ : ∀ t, ω.Tames (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ ε > 0, ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → ∀ ⦃a b : ℝ⦄,
      ∫ z in Icc a b ×ˢ Icc 0 1,
          ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
              (fderiv ℝ ξ z stdComplexLineReal) +
            ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
              (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
            ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
        C₀ * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
          (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) →
      ∀ ⦃η : ℝ × ℝ → V⦄, ContinuousOn η (Icc a b ×ˢ Icc 0 1) →
      (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖η z - stationaryCylinderOperator J S ξ z‖ ≤
        ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) →
      ∫ z in Icc a b ×ˢ Icc 0 1,
          ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
              (fderiv ℝ ξ z stdComplexLineReal) +
            ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
              (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
            ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
        C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (η z) (η z) := by
  have he : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  -- Over `t ∈ [0, 1]`, `m ‖v‖² ≤ g_t(v, v) ≤ M ‖v‖²` and `‖S_t‖ ≤ N - 1`.
  obtain ⟨m, hm, M, hM, hmM⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) he.continuousOn fun t _ ↦ hJ t
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hSc.continuousOn
  set N := |B| + 1 with hN
  -- The choice of `ε` makes `4 C₀ M ε² N² ≤ m / 2`, so the perturbation is absorbed.
  set κ := 8 * C₀ * M * N ^ 2 / m with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ε := 1 / (κ + 1) with hε
  have habs : C₀ * (4 * M * ε ^ 2 * N ^ 2) ≤ m / 2 := by
    have h : ε ^ 2 * κ ≤ 1 := by
      rw [hε, div_pow, one_pow, ← mul_div_right_comm, one_mul, div_le_one (by positivity)]
      nlinarith
    rw [hκ, mul_div_assoc', div_le_one hm] at h
    nlinarith
  refine ⟨ε, by positivity, 4 * C₀ * M / m, by positivity,
    fun ξ hξ a b hest η hη hclose ↦ ?_⟩
  have hR : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hw : Continuous fun z : ℝ × ℝ ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z) :=
    ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
      ((hSc.comp continuous_snd).clm_apply hξ.continuous)
  have hQi : IntegrableOn (fun z : ℝ × ℝ ↦
      (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
          (fderiv ℝ ξ z stdComplexLineReal) +
        ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
          (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
        ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) (Icc a b ×ˢ Icc 0 1) :=
    ((continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc hξ).add
    (continuous_associatedBilinForm_apply_self (ω := ω) hJc hξ.continuous)).continuousOn
    |>.integrableOn_compact (μ := volume) hR
  have hDc : Continuous (stationaryCylinderOperator J S ξ) :=
    (((hξ.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := stdComplexLineReal))).add
      (hJc.comp (continuous_snd.prodMk hw))).congr fun z ↦ by simp [stationaryCylinderOperator_def]
  have hdi := (continuous_associatedBilinForm_apply_self (ω := ω) hJc hDc).continuousOn
    |>.integrableOn_compact (μ := volume) hR
  have hηi : IntegrableOn (fun z ↦ ω.associatedBilinForm (J z.2) (η z) (η z))
      (Icc a b ×ˢ Icc 0 1) :=
    (ω.continuousOn_apply_comp hη (hJc.comp_continuousOn
      (continuous_snd.continuousOn.prodMk hη))).integrableOn_compact hR
  -- Integrate the pointwise comparison `m g(D ξ) ≤ 2 M g(η) + 4 M ε² N² Q` over the rectangle.
  refine le_div_mul_of_le_mul_of_mul_le hm hC₀ (setIntegral_nonneg hR.measurableSet
    fun z ⟨_, ht⟩ ↦ ?_) hest ?_ habs
  · have h := fun v ↦ (hmM z.2 ht v).1
    nlinarith [h (fderiv ℝ ξ z stdComplexLineReal),
      h (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)), h (ξ z)]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hηi.const_mul _) (hQi.const_mul _)]
  refine setIntegral_mono_on (hdi.const_mul _) ((hηi.const_mul _).add (hQi.const_mul _))
    hR.measurableSet fun z ⟨hs, ht⟩ ↦ ?_
  -- `‖∂t ξ‖ + ‖ξ‖ ≤ N (‖∂t ξ - S ξ‖ + ‖ξ‖)`, since `‖S_t‖ ≤ |B|`.
  have hdt : ‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖ ≤
      N * (‖fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)‖ + ‖ξ z‖) := by
    have h₁ : ‖S z.2 (ξ z)‖ ≤ |B| * ‖ξ z‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (by gcongr; exact (hB z.2 ht).trans (le_abs_self B))
    have h₂ := norm_le_norm_add_norm_sub' (fderiv ℝ ξ z stdComplexLineImag) (S z.2 (ξ z))
    rw [hN]
    nlinarith [mul_nonneg (abs_nonneg B) (norm_nonneg
      (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)))]
  have hD : ‖stationaryCylinderOperator J S ξ z‖ ≤ ‖η z‖ +
      ε * N * (‖fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)‖ + ‖ξ z‖) := by
    have h := norm_le_norm_add_norm_sub' (stationaryCylinderOperator J S ξ z) (η z)
    rw [norm_sub_rev] at h
    nlinarith [hclose z ⟨hs, ht⟩, mul_le_mul_of_nonneg_left hdt (le_of_lt (by positivity : 0 < ε))]
  have := mul_le_of_norm_le_add hM hm.le (norm_nonneg _)
    (hmM z.2 ht _).2 (hmM z.2 ht (η z)).1 (hmM z.2 ht (fderiv ℝ ξ z stdComplexLineReal)).1
    (hmM z.2 ht _).1 (hmM z.2 ht (ξ z)).1 hD
  simpa only [mul_add, add_assoc] using this

/-- **The weighted cylinder estimate.** Under the hypotheses of
`exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`, for every weight `δ`
close enough to `0` there is a constant `C ≥ 0` such that for every `C²` map `ξ` of period one in
`t` and every `a ≤ b` with `ξ` vanishing on the slices `s = a` and `s = b`,

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S_δ ξ, ∂t ξ - S_δ ξ) + g(ξ, ξ)) ≤ C ∫ g((D - δ) ξ, (D - δ) ξ)`

over `[a, b] × [0, 1]`, where `S_δ = S_t - δ J_t` is the linearized field of the weighted operator
`D - δ` (`stationaryCylinderOperator_sub_smul`), whose return map stays nondegenerate for small
`δ` (`eventually_det_one_sub_dysonSeriesLeft_sub_smul_ne_zero`). The constant does not depend on
`a`, `b` or `ξ`. -/
theorem eventually_exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) →
      (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag -
                  (S z.2 - δ • LinearMap.toContinuousLinearMap (J z.2).toLinearMap) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  (S z.2 - δ • LinearMap.toContinuousLinearMap (J z.2).toLinearMap) (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (stationaryCylinderOperator J S ξ z - δ • ξ z)
            (stationaryCylinderOperator J S ξ z - δ • ξ z) := by
  have hJo : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  filter_upwards [eventually_det_one_sub_dysonSeriesLeft_sub_smul_ne_zero hSc
    (AlmostComplexStructure.continuous_iff.2 hJo) hdet] with δ hdetδ
  obtain ⟨C, hC, hest⟩ := exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    hJ hJc (fun t ↦ sub_smul_apply_add_apply_eq_zero (hJ t).invariant (hS t) δ)
    (hSc.sub (hJo.const_smul δ)) hdetδ
  refine ⟨C, hC, fun ξ hξ hper a b hab ha hb ↦ ?_⟩
  simp only [← stationaryCylinderOperator_sub_smul]
  exact hest hξ hper hab ha hb

/-- **The energy density under the exponential weight.** For a compatible `J₀` with metric
`g = ω(·, J₀ ·)` and any `T`, the `e^{2 δ s}`-weighted energy density of `η` at `z` is at most
`2 + 4 δ²` times the energy density of `ξ = e^{δ s} η` for the shifted field `T - δ J₀`: one has
`e^{δ s} ∂s η = ∂s ξ - δ ξ` and `e^{δ s} (∂t η - T η) = (∂t ξ - (T - δ J₀) ξ) - δ J₀ ξ`. -/
theorem exp_mul_associatedBilinForm_le {J₀ : AlmostComplexStructure V} (hJ₀ : ω.Compatible J₀)
    (T : V →L[ℝ] V) (δ : ℝ) {η : ℝ × ℝ → V} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z) :
    Real.exp (2 * δ * z.1) * ((ω.associatedBilinForm J₀ (fderiv ℝ η z stdComplexLineReal)
          (fderiv ℝ η z stdComplexLineReal) +
        ω.associatedBilinForm J₀ (fderiv ℝ η z stdComplexLineImag - T (η z))
          (fderiv ℝ η z stdComplexLineImag - T (η z))) +
        ω.associatedBilinForm J₀ (η z) (η z)) ≤
      (2 + 4 * δ ^ 2) *
        ((ω.associatedBilinForm J₀
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineReal)
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineReal) +
          ω.associatedBilinForm J₀
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineImag -
              (T - δ • J₀.toLinearMap.toContinuousLinearMap) (Real.exp (δ * z.1) • η z))
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineImag -
              (T - δ • J₀.toLinearMap.toContinuousLinearMap) (Real.exp (δ * z.1) • η z))) +
          ω.associatedBilinForm J₀ (Real.exp (δ * z.1) • η z) (Real.exp (δ * z.1) • η z)) := by
  set e := Real.exp (δ * z.1)
  have hc : HasFDerivAt (fun w : ℝ × ℝ ↦ Real.exp (δ * w.1))
      (e • δ • ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
    simpa [e] using ((hasFDerivAt_fst (p := z)).const_smul δ).exp
  have hd : fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z =
      e • fderiv ℝ η z + (e • δ • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η z) :=
    (hc.smul hη.hasFDerivAt).fderiv
  -- The derivatives of `ξ = e^{δ s} η` in terms of those of `η`.
  have hs : fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineReal =
      e • fderiv ℝ η z stdComplexLineReal + δ • (e • η z) := by
    rw [hd]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', stdComplexLineReal_fst,
      smul_eq_mul, mul_one, smul_smul]
    ring_nf
  have ht : fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineImag -
      (T - δ • J₀.toLinearMap.toContinuousLinearMap) (e • η z) =
      e • (fderiv ℝ η z stdComplexLineImag - T (η z)) + δ • J₀ (e • η z) := by
    rw [hd]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst', stdComplexLineImag_fst,
      smul_eq_mul, mul_zero, zero_smul, add_zero, sub_apply,
      LinearMap.coe_toContinuousLinearMap', map_smul]
    module
  have hexp : Real.exp (2 * δ * z.1) = e * e := by
    rw [← Real.exp_add]
    ring_nf
  rw [hs, ht, hexp]
  have h := hJ₀.associatedBilinForm_add_add_le δ (e • fderiv ℝ η z stdComplexLineReal) (e • η z)
    (e • (fderiv ℝ η z stdComplexLineImag - T (η z)))
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
  linarith

/-- **The weighted energy under the exponential weight.** The integrated form of
`exp_mul_associatedBilinForm_le` over a compact set `R` of the cylinder: for compatible `J_t`
depending continuously on `t` and continuous `S`, the `e^{2 δ s}`-weighted energy of a `C¹` map
`η` is at most `2 + 4 δ²` times the energy of `e^{δ s} η` for the shifted field `S_t - δ J_t`. -/
theorem setIntegral_exp_mul_associatedBilinForm_le (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S) (δ : ℝ)
    {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) {R : Set (ℝ × ℝ)} (hR : IsCompact R) :
    ∫ z in R, Real.exp (2 * δ * z.1) *
        ((ω.associatedBilinForm (J z.2) (fderiv ℝ η z stdComplexLineReal)
            (fderiv ℝ η z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2) (fderiv ℝ η z stdComplexLineImag - S z.2 (η z))
            (fderiv ℝ η z stdComplexLineImag - S z.2 (η z))) +
          ω.associatedBilinForm (J z.2) (η z) (η z)) ≤
      (2 + 4 * δ ^ 2) * ∫ z in R,
        ((ω.associatedBilinForm (J z.2)
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineReal)
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2)
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineImag -
              (S z.2 - δ • (J z.2).toLinearMap.toContinuousLinearMap) (Real.exp (δ * z.1) • η z))
            (fderiv ℝ (fun w ↦ Real.exp (δ * w.1) • η w) z stdComplexLineImag -
              (S z.2 - δ • (J z.2).toLinearMap.toContinuousLinearMap) (Real.exp (δ * z.1) • η z))) +
          ω.associatedBilinForm (J z.2) (Real.exp (δ * z.1) • η z) (Real.exp (δ * z.1) • η z)) := by
  have hJo : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  have hξ : ContDiff ℝ 1 fun w : ℝ × ℝ ↦ Real.exp (δ * w.1) • η w :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).smul hη
  have hL := ((Real.continuous_exp.comp ((continuous_const (y := 2 * δ)).mul continuous_fst)).mul
    ((continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc hη).add
      (continuous_associatedBilinForm_apply_self (ω := ω) hJc hη.continuous))).continuousOn
    |>.integrableOn_compact (μ := volume) hR
  have hQ := ((continuous_associatedBilinForm_add_apply_self (ω := ω) hJc
    (hSc.sub (hJo.const_smul δ)) hξ).add
      (continuous_associatedBilinForm_apply_self (ω := ω) hJc hξ.continuous)).continuousOn
    |>.integrableOn_compact (μ := volume) hR
  rw [← integral_const_mul]
  exact setIntegral_mono_on hL (hQ.const_mul (2 + 4 * δ ^ 2)) hR.measurableSet
    fun z _ ↦ exp_mul_associatedBilinForm_le (hJ z.2) _ δ (hη.differentiable one_ne_zero z)

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The cylinder estimate at a nondegenerate Hamiltonian orbit.** Let `x` be an orbit of a
jointly `C²` time-dependent Hamiltonian `H` whose suspended vector field is globally Lipschitz,
with `x(0)` a nondegenerate fixed point of the time-one map, as for a nondegenerate one-periodic
orbit of a one-periodic Hamiltonian, and let `J_t` be `ω`-compatible complex structures depending
continuously on `t`. Then the stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` along
`x`, with `S_t = dX_{H_t}(x(t))`, satisfies the estimate of
`Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`; the hypothesis
on the return map is `det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
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
    (ω.det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt hX hH hx hnd)

/-- **The weighted cylinder estimate at a nondegenerate Hamiltonian orbit.** Under the hypotheses
of `exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`, for every weight `δ`
close enough to `0` the weighted operator `D - δ` along `x` satisfies the estimate of
`Floer.eventually_exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul`
for `S_t = dX_{H_t}(x(t))`: there is a constant `C ≥ 0` such that every `C²` map `ξ` of period one
in `t`, vanishing on two slices `s = a` and `s = b`, satisfies

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S_δ ξ, ∂t ξ - S_δ ξ) + g(ξ, ξ)) ≤ C ∫ g((D - δ) ξ, (D - δ) ξ)`

over `[a, b] × [0, 1]`, with `S_δ = S_t - δ J_t` and `g_t = ω(·, J_t ·)`. -/
theorem eventually_exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → AlmostComplexStructure V} (hJ : ∀ t, ω.Compatible (J t))
    (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ t, ξ (a, t) = 0) →
      (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag -
                  (fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) -
                    δ • LinearMap.toContinuousLinearMap (J z.2).toLinearMap) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  (fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) -
                    δ • LinearMap.toContinuousLinearMap (J z.2).toLinearMap) (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z - δ • ξ z)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z - δ • ξ z) :=
  Floer.eventually_exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul
    (S := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) hJ hJc
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right t)).contDiffAt)
    (ω.continuous_fderiv_hamiltonianVectorField_comp hH
      (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt))
    (ω.det_one_sub_dysonSeriesLeft_ne_zero_of_isNondegenerateFixedPt hX hH hx hnd)

end SymplecticForm

end TauCeti
