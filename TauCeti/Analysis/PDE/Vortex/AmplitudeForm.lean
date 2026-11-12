/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor
public import TauCeti.Analysis.PDE.Vortex.EndFraming
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Every framed plane vortex is a reconstructed amplitude field

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`. For an effective divisor `D` put
`f(w) = ∏_{a ∈ D} (w - a)`. For a real function `u`, the field `TauCeti.Vortex.amplitudeField u f`
has section `exp(u) f` and connection `i (-∂₂u ds + ∂₁u dt)`. It is a vortex exactly when `u`
solves the regularized scalar equation

`Δu = (exp(2u) |f|² - 1) / 8`,

and it has the degree-`m` end framing, `m = |D|`, exactly when `u + m log |z| → 0`
(`TauCeti.Vortex.equation_amplitudeField_eq_zero_iff`,
`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log`).

This file proves the converse reconstruction: **every** smooth vortex with the degree-`m` end
framing and zero divisor `D` is a smooth framed gauge transform of such an amplitude field
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_amplitudeField_eq`). The amplitude is determined by
the vortex: `exp(u) |f| = |α|`, so `2 u = log |α|² - log |f|²` off the zeros of `f`
(`TauCeti.Vortex.exp_mul_norm_eq_norm_sectionValue`), and two amplitudes giving gauge-equivalent
fields coincide (`TauCeti.Vortex.eq_of_framedGaugeGroup_smul_amplitudeField_eq`). Consequently a
smooth framed vortex with divisor `D` exists exactly when the scalar boundary problem for `D` has a
smooth solution (`TauCeti.Vortex.exists_equation_eq_zero_iff_exists_laplacian_eq`).

The argument compares the vortex `x` with the field of section `f` and zero connection. Their
sections have the same zero multiplicities, so `α_x = h f` for a smooth nowhere-vanishing `h`
(`TauCeti.Vortex.exists_contDiff_sectionValue_eq_mul`). Off the zeros of `f`, the scalar equations
`Δ log |α|² = (|α|² - 1) / 4` for `x` and `Δ log |f|² = 0` give the regularized equation for
`u = log |h|` (`TauCeti.Vortex.laplacian_log_norm_eq`); it extends across the finitely many zeros
by continuity (`TauCeti.Vortex.laplacian_log_norm_eq_of_dense`). Hence `amplitudeField u f` is a
smooth vortex with the same end framing and divisor as `x`, and Taubes's uniqueness theorem
(`TauCeti.Vortex.existsUnique_framedGaugeGroup_smul_eq`) supplies the framed gauge.

## Main results

* `TauCeti.Vortex.exists_framedGaugeGroup_smul_amplitudeField_eq`: every smooth framed vortex with
  divisor `D` is a framed gauge transform of the amplitude field of a smooth solution of the
  scalar boundary problem for `D`.
* `TauCeti.Vortex.exp_mul_norm_eq_norm_sectionValue`,
  `TauCeti.Vortex.eq_of_framedGaugeGroup_smul_amplitudeField_eq`: the amplitude is determined by
  the gauge orbit.
* `TauCeti.Vortex.exists_equation_eq_zero_iff_exists_laplacian_eq`: existence of a smooth framed
  vortex with divisor `D` is equivalent to solvability of the scalar boundary problem.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Polynomial InnerProductSpace Laplacian
open scoped Topology ContDiff

/-- **The amplitude is determined by the vortex.** If a framed gauge transform of the amplitude
field `amplitudeField u f` is `x`, then `exp(u) |f| = |α_x|`. -/
theorem exp_mul_norm_eq_norm_sectionValue {x : ℂ → EuclideanSpace ℝ (Fin 4)} {u : ℂ → ℝ}
    {f : ℂ → ℂ} {g : framedGaugeGroup} (hx : g • amplitudeField u f = x) (z : ℂ) :
    Real.exp (u z) * ‖f z‖ = ‖sectionValue x z‖ := by
  rw [← hx, framedGaugeGroup_smul, sectionValue_gaugeTransform, norm_mul, Circle.norm_coe,
    one_mul, sectionValue_amplitudeField, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- **Uniqueness of the amplitude.** If `f` vanishes only on a set with dense complement, two
continuous amplitudes whose amplitude fields are related by framed gauge transformations are
equal. -/
theorem eq_of_framedGaugeGroup_smul_amplitudeField_eq {u u' : ℂ → ℝ} (hu : Continuous u)
    (hu' : Continuous u') {f : ℂ → ℂ} (hf : Dense {z | f z ≠ 0}) {g g' : framedGaugeGroup}
    (h : g • amplitudeField u f = g' • amplitudeField u' f) : u = u' := by
  refine hu.ext_on hf hu' fun z hz ↦ Real.exp_injective ?_
  have hfz : 0 < ‖f z‖ := norm_pos_iff.2 hz
  have := (exp_mul_norm_eq_norm_sectionValue h z).trans
    (exp_mul_norm_eq_norm_sectionValue rfl z).symm
  exact mul_right_cancel₀ hfz.ne' this

/-- **Every framed vortex is a reconstructed amplitude field.** Let `x` be a smooth solution of
the vortex equation on the plane with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, and let
`D` be its zero divisor. Put `f(w) = ∏_{a ∈ D} (w - a)`. Then there is a smooth solution `u` of the
regularized scalar equation `Δu = (exp(2u) |f|² - 1) / 8` with `u + m log |z| → 0` at infinity,
and a smooth framed gauge `g` with `g • amplitudeField u f = x`. -/
theorem exists_framedGaugeGroup_smul_amplitudeField_eq {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    ∃ u : ℂ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ z, Δ u z = (Real.exp (2 * u z) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 - 1) / 8) ∧
      Tendsto (fun z ↦ u z + m * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) ∧
      ∃ g : framedGaugeGroup, g • amplitudeField u (fun w ↦ (D.map fun a ↦ w - a).prod) = x := by
  set f : ℂ → ℂ := fun w ↦ (D.map fun a ↦ w - a).prod
  set P : ℂ[X] := (D.map fun a ↦ X - C a).prod
  have hPf : P.eval = f := funext fun w ↦ by simp [P, f, eval_multiset_prod, Multiset.map_map]
  have hPm : P.Monic := monic_multisetProd_X_sub_C D
  have hPdeg : P.natDegree = m :=
    (natDegree_multiset_prod_X_sub_C_eq_card D).trans (hD.card_eq_of_tendsto_mul_inv_pow hframe)
  have hfd : Differentiable ℂ f := hPf ▸ P.differentiable
  have hfs : ContDiff ℝ ∞ f := (hfd.contDiff (n := ∞)).restrict_scalars ℝ
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hd {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) : Differentiable ℝ g := hg.differentiable (by simp)
  have hxhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hsol w]
  -- The vortex section is `h f` for a smooth nowhere-vanishing factor `h`.
  set y := amplitudeField (fun _ ↦ 0) f
  have hy : ContDiff ℝ ∞ y := contDiff_amplitudeField contDiff_const hfs
  have hyi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ y w i := (contDiff_piLp 2).1 hy i
  have hyhol (w : ℂ) : equation y w 1 = 0 ∧ equation y w 2 = 0 :=
    equation_amplitudeField_apply_one_eq_zero_and_apply_two_eq_zero (differentiableAt_const _)
      (hfd w)
  obtain ⟨h, hh, hh₀, hα⟩ := exists_contDiff_sectionValue_eq_mul (k := ⊤) le_top (hxi 0) (hxi 1)
    (hd (hxi 2)) (hd (hxi 3)) hxhol (hyi 0) (hyi 1) (hd (hyi 2)) (hd (hyi 3)) hyhol
    (isZeroMultiplicity_iff.1 hD)
    (isZeroMultiplicity_iff.1 (isZeroMultiplicity_sectionValue_amplitudeField_prod_sub
      continuous_const D))
  have hα' (z : ℂ) : sectionValue x z = h z * f z := by
    simpa [y, sectionValue_amplitudeField] using hα z
  -- The amplitude `u = log |h|` is smooth and solves the regularized scalar equation.
  set u : ℂ → ℝ := fun z ↦ Real.log ‖h z‖
  have hu : ContDiff ℝ ∞ u := (hh.norm ℝ hh₀).log fun z ↦ norm_ne_zero_iff.2 (hh₀ z)
  have hexp (z : ℂ) : Real.exp (u z) = ‖h z‖ := Real.exp_log (norm_pos_iff.2 (hh₀ z))
  have hexp2 (z : ℂ) : Real.exp (2 * u z) = ‖h z‖ ^ 2 := by
    rw [mul_comm, Real.exp_mul, hexp, Real.rpow_two]
  -- The zeros of `f` are the finitely many points of `D`.
  have hdense : Dense {z | f z ≠ 0} :=
    (dense_univ.sdiff_finite D.toFinset.finite_toSet).mono fun z hz ↦
      (isZeroMultiplicity_prod_sub D).eq_zero_iff.1 (Multiset.count_eq_zero.2 (by simpa using hz))
  have hΔ (z : ℂ) : Δ u z = (Real.exp (2 * u z) * ‖f z‖ ^ 2 - 1) / 8 := by
    rw [hexp2]
    exact laplacian_log_norm_eq_of_dense (hx.of_le (by simp)) hsol (hh.of_le (by simp)) hh₀ hfd
      hdense hα' z
  have hysol (z : ℂ) : equation (amplitudeField u f) z = 0 :=
    (equation_amplitudeField_eq_zero_iff ((hu.contDiffAt).of_le (by simp)) (hfd z)).2
      (hΔ z)
  -- The amplitude field has the same end framing as `x`.
  have hxnorm : Tendsto (fun z ↦ ‖sectionValue x z‖) (cocompact ℂ) (𝓝 1) := by
    have hn := hframe.norm
    rw [norm_one] at hn
    refine hn.congr' ?_
    filter_upwards [eventually_norm_inv_phase_eq_one m] with z hz
    rw [norm_mul, hz, mul_one]
  have hyfr : Tendsto (fun z ↦ sectionValue (amplitudeField u f) z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹)
      (cocompact ℂ) (𝓝 1) := by
    have := (tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_norm hPm u).2 <| by
      rw [hPf]
      refine hxnorm.congr fun z ↦ ?_
      rw [hα' z, sectionValue_amplitudeField, hexp, norm_mul, norm_mul, norm_real,
        Real.norm_eq_abs, abs_norm]
    rwa [hPf, hPdeg] at this
  have hbc : Tendsto (fun z ↦ u z + m * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
    have := (tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log hPm u).1
      (by rwa [hPf, hPdeg])
    rwa [hPdeg] at this
  -- Taubes's uniqueness theorem supplies the framed gauge.
  have hphase : Tendsto (fun z : ℂ ↦ ‖((z / (‖z‖ : ℂ)) ^ m)⁻¹‖) (cocompact ℂ) (𝓝 1) :=
    tendsto_const_nhds.congr' ((eventually_norm_inv_phase_eq_one m).mono fun _ h ↦ h.symm)
  obtain ⟨g, hg, -⟩ := existsUnique_framedGaugeGroup_smul_eq hx (contDiff_amplitudeField hu hfs)
    hsol hysol hphase hframe hyfr (isZeroMultiplicity_iff.1 hD)
    (isZeroMultiplicity_iff.1 (isZeroMultiplicity_sectionValue_amplitudeField_prod_sub
      hu.continuous D))
  exact ⟨u, hu, hΔ, hbc, g, hg⟩

/-- **Framed vortices with divisor `D` exist exactly when the scalar boundary problem is
solvable.** For an effective divisor `D` of degree `m` put `f(w) = ∏_{a ∈ D} (w - a)`. There is a
smooth solution of the vortex equation on the plane with the degree-`m` end framing and zero
divisor `D` if and only if there is a smooth solution `u` of `Δu = (exp(2u) |f|² - 1) / 8` with
`u + m log |z| → 0` at infinity. -/
theorem exists_equation_eq_zero_iff_exists_laplacian_eq (D : Multiset ℂ) :
    (∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ Multiset.card D)⁻¹)
        (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) ↔
    ∃ u : ℂ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ z, Δ u z = (Real.exp (2 * u z) * ‖(D.map fun a ↦ z - a).prod‖ ^ 2 - 1) / 8) ∧
      Tendsto (fun z ↦ u z + Multiset.card D * Real.log ‖z‖) (cocompact ℂ) (𝓝 0) := by
  refine ⟨fun ⟨x, hx, hsol, hframe, hD⟩ ↦ ?_, fun ⟨u, hu, hΔ, hbc⟩ ↦ ?_⟩
  · obtain ⟨u, hu, hΔ, hbc, -⟩ := exists_framedGaugeGroup_smul_amplitudeField_eq hx hsol hframe hD
    exact ⟨u, hu, hΔ, hbc⟩
  · set P : ℂ[X] := (D.map fun a ↦ X - C a).prod
    have hPf : P.eval = fun w ↦ (D.map fun a ↦ w - a).prod :=
      funext fun w ↦ by simp [P, eval_multiset_prod, Multiset.map_map]
    have hPdeg : P.natDegree = Multiset.card D := natDegree_multiset_prod_X_sub_C_eq_card D
    have hfd : Differentiable ℂ fun w ↦ (D.map fun a ↦ w - a).prod := hPf ▸ P.differentiable
    refine ⟨amplitudeField u fun w ↦ (D.map fun a ↦ w - a).prod,
      contDiff_amplitudeField hu ((hfd.contDiff (n := ∞)).restrict_scalars ℝ),
      fun z ↦ (equation_amplitudeField_eq_zero_iff ((hu.contDiffAt).of_le (by simp)) (hfd z)).2
        (hΔ z), ?_, isZeroMultiplicity_sectionValue_amplitudeField_prod_sub hu.continuous D⟩
    have := (tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log
      (monic_multisetProd_X_sub_C D) u).2 (by rwa [hPdeg])
    rwa [hPf, hPdeg] at this

end TauCeti.Vortex
