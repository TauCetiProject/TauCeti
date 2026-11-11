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
* **Stability of the cylinder estimate.** If `ξ` satisfies the cylinder estimate with constant
  `C₀`, then there are `ε > 0` and `C`, depending only on `C₀`, `J` and `S`, such that the
  estimate also holds with `C` and any continuous `f` in place of `D ξ` with
  `‖f - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` pointwise on the rectangle
  (`Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`). Since
  `∂t ξ = (∂t ξ - S ξ) + S ξ`, the error is bounded by the left-hand side with a small factor, and
  it is absorbed there. This is how the estimate passes to operators that converge to `D`, such
  as the linearized operator along a cylindrical end.

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

omit [FiniteDimensional ℝ V] in
/-- The pointwise step of the stability estimate. If `g = ω(·, J ·)` satisfies
`α ‖v‖² ≤ g(v, v) ≤ β ‖v‖²`, `‖T‖ ≤ σ`, and `f` differs from `d = p + J (q - T y)` by at most
`ε (‖q‖ + ‖y‖)` with `4 β ε² (1 + σ)² ≤ α κ`, then
`g(d, d) ≤ (2 β / α) g(f, f) + κ (g(p, p) + g(q - T y, q - T y) + g(y, y))`. -/
private theorem associatedBilinForm_le_of_norm_sub_le {J : AlmostComplexStructure V}
    {T : V →L[ℝ] V} {α β σ ε κ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    (hε : 0 ≤ ε) (hg : ∀ v, α * ‖v‖ ^ 2 ≤ ω.associatedBilinForm J v v ∧
      ω.associatedBilinForm J v v ≤ β * ‖v‖ ^ 2)
    (hT : ‖T‖ ≤ σ) (hεκ : 4 * β * ε ^ 2 * (1 + σ) ^ 2 ≤ α * κ) {f p q y : V}
    (hf : ‖f - (p + J (q - T y))‖ ≤ ε * (‖q‖ + ‖y‖)) :
    ω.associatedBilinForm J (p + J (q - T y)) (p + J (q - T y)) ≤
      2 * β / α * ω.associatedBilinForm J f f +
        κ * ((ω.associatedBilinForm J p p + ω.associatedBilinForm J (q - T y) (q - T y)) +
          ω.associatedBilinForm J y y) := by
  set d := p + J (q - T y)
  set w := q - T y
  have hσ : 0 ≤ σ := (norm_nonneg _).trans hT
  -- `‖q‖ ≤ ‖w‖ + σ ‖y‖`, hence `‖f - d‖ ≤ ε (1 + σ) (‖w‖ + ‖y‖)`.
  have hq : ‖q‖ ≤ ‖w‖ + σ * ‖y‖ := by
    calc ‖q‖ = ‖w + T y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w‖ + ‖T y‖ := norm_add_le _ _
      _ ≤ ‖w‖ + σ * ‖y‖ := by gcongr; exact (T.le_opNorm y).trans (by gcongr)
  have he : ‖f - d‖ ≤ ε * (1 + σ) * (‖w‖ + ‖y‖) := by
    refine hf.trans ?_
    have : ‖q‖ + ‖y‖ ≤ (1 + σ) * (‖w‖ + ‖y‖) := by
      nlinarith [norm_nonneg w, norm_nonneg y]
    calc ε * (‖q‖ + ‖y‖) ≤ ε * ((1 + σ) * (‖w‖ + ‖y‖)) := by gcongr
      _ = _ := by ring
  -- `‖d‖² ≤ 2 ‖f‖² + 4 ε² (1 + σ)² (‖w‖² + ‖y‖²)`.
  have hd : ‖d‖ ≤ ‖f‖ + ‖f - d‖ := by
    simpa using norm_sub_le f (f - d)
  have hd2 : ‖d‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 4 * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by
    have h1 : ‖d‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 2 * ‖f - d‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg d) hd 2, sq_nonneg (‖f‖ - ‖f - d‖)]
    have h2 : ‖f - d‖ ^ 2 ≤ (ε * (1 + σ)) ^ 2 * (‖w‖ + ‖y‖) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) he 2
    have h3 : (‖w‖ + ‖y‖) ^ 2 ≤ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith [sq_nonneg (‖w‖ - ‖y‖)]
    have h4 : 0 ≤ (ε * (1 + σ)) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hpJ := (mul_nonneg hα.le (sq_nonneg ‖p‖)).trans (hg p).1
  have hf' := (hg f).1
  have hw' := (hg w).1
  have hy' := (hg y).1
  have hd' := (hg d).2
  have hfq : 2 * β * ‖f‖ ^ 2 ≤ 2 * β / α * ω.associatedBilinForm J f f := by
    calc 2 * β * ‖f‖ ^ 2 = 2 * β / α * (α * ‖f‖ ^ 2) := by field_simp
      _ ≤ _ := by gcongr
  have hwy : 4 * β * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) ≤
      κ * (ω.associatedBilinForm J w w + ω.associatedBilinForm J y y) := by
    calc _ ≤ α * κ * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by gcongr
      _ = κ * (α * ‖w‖ ^ 2 + α * ‖y‖ ^ 2) := by ring
      _ ≤ _ := by gcongr
  calc ω.associatedBilinForm J d d ≤ β * ‖d‖ ^ 2 := hd'
    _ ≤ β * (2 * ‖f‖ ^ 2 + 4 * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2)) := by gcongr
    _ = 2 * β * ‖f‖ ^ 2 + 4 * β * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by ring
    _ ≤ 2 * β / α * ω.associatedBilinForm J f f +
        κ * (ω.associatedBilinForm J w w + ω.associatedBilinForm J y y) := add_le_add hfq hwy
    _ ≤ _ := by gcongr; linarith [mul_nonneg hκ hpJ]

/-- **Stability of the cylinder estimate.** Let each `J_t` be `ω`-tame and depend continuously
on `t`, let `S` be continuous, and let `C₀ ≥ 0`. There are `ε > 0` and `C ≥ 0` with the following
property. Let `ξ` be a `C¹` map satisfying, over `[a, b] × [0, 1]`, the cylinder estimate

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C₀ ∫ g(D ξ, D ξ)`

for `g_t = ω(·, J_t ·)` and the stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`.
Then every `f` continuous on the rectangle with `‖f - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` there satisfies
the same estimate with `C` in place of `C₀` and `f` in place of `D ξ`. The constants do not depend
on `a`, `b`, `ξ` or `f`. -/
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
      ∀ ⦃f : ℝ × ℝ → V⦄, ContinuousOn f (Icc a b ×ˢ Icc 0 1) →
        (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖f z - stationaryCylinderOperator J S ξ z‖ ≤
          ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (f z) (f z) := by
  have he : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨α, hα, β, hβ, hαβ⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    isCompact_Icc he.continuousOn fun t (_ : t ∈ Icc (0 : ℝ) 1) ↦ hJ t
  obtain ⟨σ, hσ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hSc.continuousOn
  -- The error is absorbed once `C₀ κ ≤ 1 / 2`, which the choice of `ε` arranges.
  set m := 1 + |σ|
  set κ := 1 / (2 * (C₀ + 1))
  set ε := min 1 (α / (8 * (β + 1) * m ^ 2 * (C₀ + 1)))
  have hm : 0 < m := by positivity
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hεκ : 4 * β * ε ^ 2 * m ^ 2 ≤ α * κ := by
    have h₁ : β * ε ^ 2 ≤ (β + 1) * ε := by
      have hε₁ : ε ≤ 1 := min_le_left _ _
      nlinarith [mul_le_mul_of_nonneg_left hε₁ (mul_nonneg hβ hε.le)]
    calc 4 * β * ε ^ 2 * m ^ 2 = 4 * m ^ 2 * (β * ε ^ 2) := by ring
      _ ≤ 4 * m ^ 2 * ((β + 1) * ε) := by gcongr
      _ ≤ 4 * m ^ 2 * ((β + 1) * (α / (8 * (β + 1) * m ^ 2 * (C₀ + 1)))) := by
        gcongr; exact min_le_right _ _
      _ = α * κ := by simp only [κ]; field_simp; ring
  refine ⟨ε, hε, 4 * C₀ * β / α, by positivity, fun ξ hξ a b hst f hf hfD ↦ ?_⟩
  set R := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  -- The integrands: `e` of the left-hand side, `gD` of `g(D ξ)` and `gF` of `g(f)`.
  set e : ℝ × ℝ → ℝ := fun z ↦
    (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) +
      ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
        (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
      ω.associatedBilinForm (J z.2) (ξ z) (ξ z)
  set gF : ℝ × ℝ → ℝ := fun z ↦ ω.associatedBilinForm (J z.2) (f z) (f z)
  -- Integrability of the three integrands on the compact rectangle.
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  have hDc : Continuous (stationaryCylinderOperator J S ξ) := by
    have hw : Continuous fun z : ℝ × ℝ ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z) :=
      (hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hξ.continuous)
    rw [funext (stationaryCylinderOperator_def J S ξ)]
    exact (hdξ.clm_apply continuous_const).add (hJc.comp (continuous_snd.prodMk hw))
  have hDi := (continuous_associatedBilinForm_apply_self (ω := ω) hJc hDc).continuousOn
    |>.integrableOn_compact (μ := volume) hR
  have hFi : IntegrableOn gF R :=
    (ω.continuousOn_apply_comp hf
      (hJc.comp_continuousOn (continuous_snd.continuousOn.prodMk hf))).integrableOn_compact hR
  have hEi : IntegrableOn e R :=
    ((continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc hξ).add
      (continuous_associatedBilinForm_apply_self (ω := ω) hJc hξ.continuous)).continuousOn
      |>.integrableOn_compact hR
  -- Pointwise, `g(D ξ) ≤ (2 β / α) g(f) + κ e`.
  have hpt : ∫ z in R, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z)
      (stationaryCylinderOperator J S ξ z) ≤ ∫ z in R, (2 * β / α * gF z + κ * e z) :=
    setIntegral_mono_on hDi ((hFi.const_mul (2 * β / α)).add (hEi.const_mul κ)) hRm
      fun z hz ↦ by
        have hz₂ : z.2 ∈ Icc (0 : ℝ) 1 := hz.2
        have hS : ‖S z.2‖ ≤ |σ| := (hσ z.2 hz₂).trans (le_abs_self σ)
        have h := hfD z hz
        rw [stationaryCylinderOperator_def] at h ⊢
        exact associatedBilinForm_le_of_norm_sub_le hα hβ (by positivity) hε.le
          (hαβ z.2 hz₂) hS hεκ h
  rw [integral_add (hFi.const_mul _) (hEi.const_mul _), integral_const_mul,
    integral_const_mul] at hpt
  -- Absorb: `E ≤ C₀ ((2 β / α) ∫ g(f) + κ E)` with `C₀ κ ≤ 1 / 2` and `E ≥ 0`.
  set E := ∫ z in R, e z
  have hg0 (z : ℝ × ℝ) (hz : z ∈ R) (v : V) : 0 ≤ ω.associatedBilinForm (J z.2) v v :=
    (mul_nonneg hα.le (sq_nonneg ‖v‖)).trans (hαβ z.2 hz.2 v).1
  have hE0 : 0 ≤ E := setIntegral_nonneg hRm fun z hz ↦
    add_nonneg (add_nonneg (hg0 z hz _) (hg0 z hz _)) (hg0 z hz _)
  have hκ : C₀ * κ ≤ 1 / 2 := by
    simp only [κ]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hfin := hst.trans (mul_le_mul_of_nonneg_left hpt hC₀)
  have hcross : C₀ * (κ * E) ≤ E / 2 := by
    rw [← mul_assoc]; nlinarith
  calc E ≤ 2 * (C₀ * (2 * β / α * ∫ z in R, gF z)) := by
        nlinarith
    _ = _ := by ring

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
  have hSp : Periodic (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 :=
    fun t ↦ by simp only [hHp t, hxp t]
  -- Nondegeneracy rules out a periodic kernel element, hence a fixed vector of `Ψ(1)`.
  have hdet : LinearMap.det ((1 - dysonSeriesLeft
      (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠
      0 := by
    intro h
    obtain ⟨ζ, hζ, hζp, hne, hA⟩ :=
      (Floer.exists_ne_zero_asymptoticOperator_eq_zero_iff_det_eq_zero (J := J) hSc hSp).2 h
    exact hne ((isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero ω hX hH
      hHp hx hxp J).1 hnd ζ hζ hζp hA)
  exact Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (S := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) hJ hJc
    (fun t ↦ ω.apply_fderiv_hamiltonianVectorField_add
      (hH.comp (contDiff_prodMk_right t)).contDiffAt) hSc hdet

end SymplecticForm

end TauCeti
