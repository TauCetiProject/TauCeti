/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Family
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.UniformDerivativeDecay
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

/-!
# Uniform decay of plane vortices in an end trivialization

Let `x` be a smooth plane vortex with the degree-`m` end framing and zero divisor `D`, whose section
is `|α|` times a gauge `u` near a point `z`; for a vortex normalized at its end, `u` is the winding
phase `(z / |z|)ᵐ` (`TauCeti.Vortex.windingPhase`). Near `z` the end trivialization `u⁻¹ · x` is
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, exp (ℓ / 2) / 2, 0)` with `ℓ = log |α|²`
(`TauCeti.Vortex.gaugeTransform_inv_apply_eq`), so its distance to the vacuum `(0, 1)` and the
derivatives of that distance are controlled by the derivatives of `ℓ`. For one vortex these decay
like `exp (-c |z|)` for every rate `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField`), with constants that
depend on the vortex. This file makes the constants uniform over vortices whose zeros lie in a fixed
disc, and so over every compact window of divisors, collisions of zeros included.

* `exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_forall_le_norm_sub`:
  for every degree `m`, order `n` and rate `0 ≤ c < 1 / 2` there are `K ≥ 0` and `R` such that
  `‖Dⁿ (u⁻¹ · x - (0, 1)) (z)‖ ≤ K exp (-c ρ)` at every point `z` at distance at least `ρ ≥ R` from
  the zeros, provided the section is `|α| u` near `z`. The derivatives of `ℓ` up to order `n + 1`
  obey such bounds (`TauCeti.Vortex.exists_forall_le_norm_iteratedFDeriv_log_normSq_le_mul_exp`);
  the connection part of the end field is linear in `Dℓ` (`TauCeti.Vortex.exists_endField_eq_add`),
  and the derivatives of its section part `exp (ℓ / 2) - 1` follow by the Faà di Bruno bound
  (`ContDiffAt.norm_iteratedFDeriv_exp_sub_one_le`) since `ℓ ≤ 0`.
* `exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_forall_mem_norm_le`:
  if the zeros lie in the closed disc of radius `r`, the same bound holds with `exp (-c |z|)` for
  `|z| ≥ R`, with `K` and `R` depending only on `m`, `n`, `c` and `r`.

These apply to the normalized family of Taubes's vortices. For lower coefficients `a ∈ ℂᵐ` let
`P_a` be the monic polynomial with these coefficients, `x_a` the plane vortex with zero divisor
`P_a` (`TauCeti.Vortex.polynomialVortex`) and `g_a` its end-normalizing polynomial gauge
(`TauCeti.Vortex.polynomialGauge`). Then `g_a · x_a` is a smooth framed vortex in `A_m^s`
(`TauCeti.Vortex.gaugeTransform_polynomialGauge_polynomialVortex_spec`) whose section is `|α|`
times the winding phase outside a disc that is uniform over bounded sets of coefficients
(`TauCeti.Vortex.exists_eventually_sectionValue_eq_norm_mul_windingPhase`), and the roots of
`P_a` have norm less than `‖a‖ + 1`
(`TauCeti.Polynomial.norm_lt_of_isRoot_monicOfCoeff`). Hence, in the winding-`m` end
trivialization, the fields `g_a · x_a` tend to the vacuum with all spatial derivatives bounded by
`K exp (-c |z|)`, uniformly over a bounded set of coefficients
(`exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded`) and over
a compact set of divisors in `Sym ℂ m`
(`exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isCompact`).
This is the spatial part of the decay of the normalized families over compact divisor windows;
derivatives in the coefficients are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology
open TauCeti.Polynomial
open scoped ContDiff _root_.Polynomial

/-! ### The end field of a function -/

open scoped Nat in
/-- Pointwise bounds for the end field `(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` of
a function `ℓ ≤ 0`: if the derivatives of `ℓ` of order at most `n + 1` have norm at most `K E` at
`z`, with `0 ≤ E ≤ 1`, then the derivative of order `n` of the end field at `z` has norm at most
`C E`, for a constant `C` depending only on `n` and `K`. -/
private theorem exists_norm_iteratedFDeriv_endField_le (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ C, 0 ≤ C ∧ ∀ (ℓ : ℂ → ℝ) (z : ℂ) (E : ℝ), ContDiffAt ℝ ∞ ℓ z → ℓ z ≤ 0 → 0 ≤ E →
      E ≤ 1 → (∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j ℓ z‖ ≤ K * E) →
      ‖iteratedFDeriv ℝ n (fun w ↦ !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2,
        (Real.exp (ℓ w / 2) - 1) / 2, 0]) z‖ ≤ C * E := by
  -- The end field is `L₁ (Dℓ) + L₂ (exp (ℓ / 2) - 1)` for two fixed linear maps.
  obtain ⟨L₁, L₂, hL⟩ := exists_endField_eq_add
  refine ⟨‖L₁‖ * K + ‖L₂‖ * (n ! * max 1 K ^ (n + 1)), by positivity,
    fun ℓ z E hℓ hℓ₀ hE₀ hE₁ hD ↦ ?_⟩
  have hDℓ : ContDiffAt ℝ ∞ (fderiv ℝ ℓ) z := hℓ.fderiv_right (by norm_cast)
  have hE : ContDiffAt ℝ ∞ (fun w ↦ Real.exp (ℓ w / 2) - 1) z :=
    (Real.contDiff_exp.contDiffAt.comp z (hℓ.div_const 2)).sub contDiffAt_const
  -- The connection part: its derivative of order `n` is controlled by `Dⁿ⁺¹ ℓ`.
  have h₁ : ‖iteratedFDeriv ℝ n (fun w ↦ L₁ (fderiv ℝ ℓ w)) z‖ ≤ ‖L₁‖ * (K * E) := by
    have h := L₁.norm_iteratedFDeriv_comp_left hDℓ (n := n) (by exact_mod_cast le_top)
    rw [Function.comp_def, norm_iteratedFDeriv_fderiv] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hD (n + 1) le_rfl) (norm_nonneg _))
  -- The section part: the derivatives of `ℓ / 2` of order at most `n` are at most `K E`.
  have hD₂ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun w ↦ ℓ w / 2) z‖ ≤ K * E := fun j hj ↦ by
    have h := iteratedFDeriv_fun_const_smul_apply ℓ (2⁻¹ : ℝ) z j
    simp only [smul_eq_mul] at h
    rw [show (fun w ↦ ℓ w / 2) = fun w ↦ 2⁻¹ * ℓ w by ext w; ring, h, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    have := hD j (by omega)
    nlinarith [norm_nonneg (iteratedFDeriv ℝ j ℓ z)]
  have hS := ((hℓ.div_const 2).of_le (by simp)).norm_iteratedFDeriv_exp_sub_one_le
    (by linarith) hE₀ hE₁ hD₂
  have h₂ : ‖iteratedFDeriv ℝ n (fun w ↦ L₂ (Real.exp (ℓ w / 2) - 1)) z‖ ≤
      ‖L₂‖ * (n ! * max 1 K ^ (n + 1) * E) :=
    (L₂.norm_iteratedFDeriv_comp_left hE (n := n) (by exact_mod_cast le_top)).trans
      (mul_le_mul_of_nonneg_left hS (norm_nonneg _))
  have hadd : iteratedFDeriv ℝ n (fun w ↦ L₁ (fderiv ℝ ℓ w) + L₂ (Real.exp (ℓ w / 2) - 1)) z =
      iteratedFDeriv ℝ n (fun w ↦ L₁ (fderiv ℝ ℓ w)) z +
        iteratedFDeriv ℝ n (fun w ↦ L₂ (Real.exp (ℓ w / 2) - 1)) z :=
    fun_iteratedFDeriv_add_apply ((L₁.contDiff.contDiffAt.comp z hDℓ).of_le (by simp))
      ((L₂.contDiff.contDiffAt.comp z hE).of_le (by simp))
  rw [hL ℓ, hadd]
  calc _ ≤ ‖L₁‖ * (K * E) + ‖L₂‖ * (n ! * max 1 K ^ (n + 1) * E) :=
        (norm_add_le _ _).trans (add_le_add h₁ h₂)
    _ = _ := by ring

/-! ### Uniform decay in the end trivialization -/

/-- **Uniform decay in an end trivialization, away from the zeros.** For every degree `m`, order
`n` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` with the following property. Let
`x` be a smooth plane vortex with the degree-`m` end framing and zero divisor `D`, and let `z` be a
point at distance at least `ρ ≥ R` from every zero of `x`, near which the section of `x` is `|α|`
times a gauge `u`. Then the end trivialization `u⁻¹ · x` satisfies
`‖Dⁿ (u⁻¹ · x - (0, 1)) (z)‖ ≤ K exp (-c ρ)`. -/
theorem
    exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_forall_le_norm_sub
    (m n : ℕ) {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ) (u : ℂ → Circle),
      ContDiff ℝ ∞ x → (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ z ρ, R ≤ ρ → (∀ a ∈ D, ρ ≤ ‖z - a‖) →
      (∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * u w) →
        ‖iteratedFDeriv ℝ n (fun w ↦ gaugeTransform u⁻¹ x w - vacuumField w) z‖ ≤
          K * Real.exp (-(c * ρ)) := by
  obtain ⟨K, R, hK, hLR, h⟩ :=
    exists_forall_le_norm_iteratedFDeriv_log_normSq_le_mul_exp m (n + 1) hc₀ hc
  obtain ⟨C, hC, hend⟩ := exists_norm_iteratedFDeriv_endField_le n hK
  refine ⟨C, R, hC, fun x D u hx hsol hframe hD z ρ hR hρ hphase ↦ ?_⟩
  have hp : ContDiff ℝ ∞ (fun w ↦ x w 2) := (contDiff_piLp 2).1 hx 2
  have hq : ContDiff ℝ ∞ (fun w ↦ x w 3) := (contDiff_piLp 2).1 hx 3
  have hs : ContDiff ℝ ∞ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) :=
    contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  -- At `z`, far from the zeros, `|α|² > 1 / 2`, and so the section does not vanish near `z`.
  have hz : 1 - 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    one_sub_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD (lt_add_one _) (by norm_num)
      fun a ha ↦ hLR.trans (hR.trans (hρ a ha))
  have hpos : ∀ᶠ w in 𝓝 z, 0 < 4 * (x w 2 ^ 2 + x w 3 ^ 2) :=
    continuousAt_const.eventually_lt hs.continuous.continuousAt (by linarith)
  -- Near `z` the end trivialization minus the vacuum is the end field of `ℓ = log |α|²`.
  have heq : (fun w ↦ gaugeTransform u⁻¹ x w - vacuumField w) =ᶠ[𝓝 z] fun w ↦
      !₂[-(fderiv ℝ (fun v ↦ Real.log (4 * (x v 2 ^ 2 + x v 3 ^ 2))) w I / 2),
        fderiv ℝ (fun v ↦ Real.log (4 * (x v 2 ^ 2 + x v 3 ^ 2))) w 1 / 2,
        (Real.exp (Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2) - 1) / 2, 0] := by
    filter_upwards [hpos, hphase.eventually_nhds] with w hw hph
    exact gaugeTransform_inv_apply_sub_vacuumField_eq (hp.differentiable (by simp) w)
      (hq.differentiable (by simp) w) (fun h0 ↦ by rw [h0, mul_zero] at hw; exact hw.false)
      (by simp [hsol w]) (by simp [hsol w]) hph EventuallyEq.rfl
  rw [(heq.iteratedFDeriv ℝ n).self_of_nhds]
  have hR₀ : 0 ≤ R := (Real.sqrt_nonneg _).trans hLR
  exact hend _ z _ (hs.contDiffAt.log (by linarith))
    (log_normSq_nonpos (hp.of_le (by simp)) (hq.of_le (by simp)) hsol
      (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) z)
    (Real.exp_pos _).le (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc₀ (by linarith))))
    fun j hj ↦ h x D hx hsol hframe hD z ρ hR hρ j hj

/-- **Uniform decay in an end trivialization, for zeros in a disc.** For every degree `m`, order
`n`, radius `r` and rate `0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` with the following
property. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros lie in the
closed disc of radius `r`, and let `|z| ≥ R` be a point near which the section of `x` is `|α|` times
a gauge `u`. Then the end trivialization `u⁻¹ · x` satisfies
`‖Dⁿ (u⁻¹ · x - (0, 1)) (z)‖ ≤ K exp (-c |z|)`. -/
theorem
    exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_forall_mem_norm_le
    (m n : ℕ) (r : ℝ) {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ) (u : ℂ → Circle),
      ContDiff ℝ ∞ x → (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ r) →
      ∀ z, R ≤ ‖z‖ → (∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * u w) →
        ‖iteratedFDeriv ℝ n (fun w ↦ gaugeTransform u⁻¹ x w - vacuumField w) z‖ ≤
          K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, R, hK, h⟩ :=
    exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_forall_le_norm_sub
      m n hc₀ hc
  refine ⟨K * Real.exp (c * r), R + r, by positivity,
    fun x D u hx hsol hframe hD hr z hz hphase ↦ ?_⟩
  -- Every zero is at distance at least `|z| - r` from `z`.
  have hρ (a : ℂ) (ha : a ∈ D) : ‖z‖ - r ≤ ‖z - a‖ := by
    linarith [norm_sub_norm_le z a, hr a ha]
  calc _ ≤ K * Real.exp (-(c * (‖z‖ - r))) :=
        h x D u hx hsol hframe hD z _ (by linarith) hρ hphase
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-! ### The normalized polynomial vortices -/

/-- For `m ≥ 1` and lower coefficients `a ∈ ℂᵐ`, the vortex `g_a · x_a` of the monic polynomial
`P_a` with these coefficients, normalized at its end by the polynomial gauge `g_a`, is a smooth
solution of the vortex equations with the degree-`m` end framing whose zero divisor is the multiset
of roots of `P_a`. -/
theorem gaugeTransform_polynomialGauge_polynomialVortex_spec {m : ℕ} (hm : 0 < m)
    (a : Fin m → ℂ) :
    ContDiff ℝ ∞ (gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))) ∧
      (∀ z, equation (gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a)))
        z = 0) ∧
      Tendsto (fun z ↦ sectionValue (gaugeTransform (polynomialGauge a)
        (polynomialVortex (monicOfCoeff a))) z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue (gaugeTransform (polynomialGauge a)
        (polynomialVortex (monicOfCoeff a)))) (fun z ↦ (monicOfCoeff a).roots.count z) := by
  have hP : (monicOfCoeff a).Monic := monic_monicOfCoeff a
  have hdeg : (monicOfCoeff a).natDegree = m := natDegree_monicOfCoeff a
  have hm' : 0 < (monicOfCoeff a).natDegree := by rw [hdeg]; exact hm
  have hx := contDiff_polynomialVortex (monicOfCoeff a)
  set g : framedGaugeGroup := ⟨polynomialGauge a, polynomialGauge_mem_framedGaugeGroup a⟩
  have hframe := tendsto_sectionValue_polynomialVortex hP hm'
  rw [hdeg] at hframe
  exact ⟨contDiff_framedGaugeGroup_smul g hx, fun w ↦ (equation_framedGaugeGroup_smul_eq_zero_iff g
    fun i ↦ (((contDiff_piLp 2).1 hx i).differentiable (by simp)) w).2
      (equation_polynomialVortex hP hm' w),
    tendsto_sectionValue_gaugeTransform ((mem_framedGaugeGroup _).1 g.property).2 hframe,
    isZeroMultiplicity_sectionValue_framedGaugeGroup_smul
      (isZeroMultiplicity_sectionValue_polynomialVortex hP.ne_zero) g⟩

/-- Outside a disc that is uniform over a bounded set of coefficients, the sections of the
normalized vortices `g_a · x_a` are `|α|` times the winding phase near every point, since the
section of `x_a` is a positive multiple of `P_a`. -/
theorem exists_eventually_sectionValue_eq_norm_mul_windingPhase {m : ℕ} {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) :
    ∃ R, ∀ a ∈ S, ∀ z : ℂ, R < ‖z‖ → ∀ᶠ w in 𝓝 z,
      sectionValue (gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))) w =
        ‖sectionValue (gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))) w‖ *
          windingPhase m w := by
  obtain ⟨R, hR⟩ := exists_forall_sectionValue_gaugeTransform_polynomialGauge hS
  refine ⟨R, fun a ha z hz ↦ ?_⟩
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
  exact hR a ha _ w _ (le_of_lt hw) (Real.exp_pos _).le
    (sectionValue_polynomialVortex (monicOfCoeff a) w)

/-- **Uniform decay of the normalized vortices over a bounded window of coefficients.** Let
`m ≥ 1`, and for lower coefficients `a ∈ ℂᵐ` let `x_a` be the plane vortex whose zero divisor is
the monic polynomial `P_a` with these coefficients, normalized at its end by the polynomial gauge
`g_a`. For every bounded set `S` of coefficients, order `n` and rate `0 ≤ c < 1 / 2` there are
constants `K ≥ 0` and `R` such that the winding-`m` end trivialization `y_a` of `g_a · x_a`
satisfies `‖Dⁿ (y_a - (0, 1)) (z)‖ ≤ K exp (-c |z|)` for every `a ∈ S` and `|z| ≥ R`. -/
theorem exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded
    {m : ℕ} (hm : 0 < m) {S : Set (Fin m → ℂ)} (hS : Bornology.IsBounded S) (n : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ a ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ n (fun w ↦ gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))) w -
        vacuumField w) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨r, hr⟩ := hS.exists_norm_le
  obtain ⟨K, R, hK, h⟩ :=
    exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_forall_mem_norm_le
      m n (r + 1) hc₀ hc
  obtain ⟨R', hR'⟩ := exists_eventually_sectionValue_eq_norm_mul_windingPhase hS
  refine ⟨K, max R (R' + 1), hK, fun a ha z hz ↦ ?_⟩
  obtain ⟨hx, hsol, hframe, hD⟩ := gaugeTransform_polynomialGauge_polynomialVortex_spec hm a
  refine h _ (monicOfCoeff a).roots (windingPhase m) hx hsol hframe hD (fun b hb ↦ ?_) z
    (le_of_max_le_left hz) (hR' a ha z (by linarith [le_of_max_le_right hz]))
  exact (norm_lt_of_isRoot_monicOfCoeff a (_root_.Polynomial.isRoot_of_mem_roots hb)).le.trans
    (by linarith [hr a ha])

/-- **Uniform decay of the normalized vortices over a compact window of divisors.** Let `m ≥ 1`,
and for an effective divisor `D` of degree `m` let `x_D` be the plane vortex with zero divisor `D`,
normalized at its end by the polynomial gauge `g_D` of the symmetric coordinates of `D`. For every
compact set `S` of divisors in `Sym ℂ m`, collisions of zeros included, every order `n` and rate
`0 ≤ c < 1 / 2` there are constants `K ≥ 0` and `R` such that the winding-`m` end trivialization
`y_D` of `g_D · x_D` satisfies `‖Dⁿ (y_D - (0, 1)) (z)‖ ≤ K exp (-c |z|)` for every `D ∈ S` and
`|z| ≥ R`. -/
theorem exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isCompact
    {m : ℕ} (hm : 0 < m) {S : Set (Sym ℂ m)} (hS : IsCompact S) (n : ℕ) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K R, 0 ≤ K ∧ ∀ D ∈ S, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ n (fun w ↦ gaugeTransform (windingPhase m)⁻¹
          (gaugeTransform (polynomialGauge (Sym.coeffEquiv ℂ m D))
            (polynomialVortex (Sym.toMonic D : ℂ[X]))) w -
        vacuumField w) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  have hS' : IsCompact (Sym.coeffEquiv ℂ m '' S) := by
    simpa only [Sym.coeffHomeomorph_apply] using hS.image (Sym.coeffHomeomorph ℂ m).continuous
  obtain ⟨K, R, hK, h⟩ :=
    exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded hm
      hS'.isBounded n hc₀ hc
  refine ⟨K, R, hK, fun D hD z hz ↦ ?_⟩
  rw [Sym.toMonic_eq_monicOfCoeff_coeffEquiv]
  exact h _ ⟨D, hD, rfl⟩ z hz

end TauCeti.Vortex
