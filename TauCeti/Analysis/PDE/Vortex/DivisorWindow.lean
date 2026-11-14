/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Decay
public import TauCeti.Analysis.PDE.Vortex.Existence
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.MeanValueInequality
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Uniform estimates for plane vortices with zeros in a fixed disc

A smooth framed plane vortex of degree `m` is determined, up to smooth framed gauge, by its zero
divisor `D ∈ Sym ℂ m` (`TauCeti.Vortex.framedVortexModuliEquiv`), and each such vortex has a
modulus defect `1 - |α|²` decaying like `exp (-c |z|)` for every rate `c < 1 / 2`
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`). The constant in that bound depends on the
vortex. This file proves that it depends only on a disc containing the zeros: for every `m`, every
radius `R` and every `c < 1 / 2` there is one constant `K` with

`1 - |α(z)|² ≤ K exp (-c |z|)`

for every smooth framed degree-`m` vortex whose zeros all lie in the closed disc of radius `R`
(`TauCeti.Vortex.exists_forall_one_sub_normSq_le_mul_exp`). These divisors form a compact subset
of `Sym ℂ m`, and every compact subset of `Sym ℂ m` lies in such a window. Uniform estimates of
this kind on compact sets of divisors are what a family of vortices parametrized by their zeros,
for instance in the gluing of vortices into the four-dimensional Seiberg–Witten equations, needs.

The proof follows the variational construction of the vortex with zero divisor `D`. Write
`P = ∏_{a ∈ D} (X - a)`, `h = ‖P‖² / (1 + ‖P‖²)` and `u₀ = -log (1 + ‖P‖²) / 2`. The vortex is
gauge equivalent to the field with section `exp (u₀ + w) P`, where `w` is the smooth
representative of a minimizer of Taubes's functional `I_P`; its squared modulus is
`|α|² = exp (2w) h`.

1. **Uniform coefficients.** For `‖a‖ ≤ R` the polynomial satisfies `‖P(z)‖ ≥ 1` outside the
   disc of radius `R + 1` (`Polynomial.pow_le_norm_eval_multiset_prod_X_sub_C`), and the
   coefficient `g = 2 ‖P'‖² / (1 + ‖P‖²)²` and the defect `(1 + ‖P‖²)⁻¹` are bounded by
   `A (1 + ‖z‖)⁻²`, with `A` depending only on `m` and `R`. So the linear coefficient of `I_P`
   has `L²` norm bounded independently of `D`, and the uniform coercivity of Taubes's functional
   (`TauCeti.Vortex.exists_forall_norm_le_of_sobolevReducedFunctional_le`) bounds the minimizer,
   which has `I_P ≤ I_P(0) = 0`, in `H¹(ℂ)` independently of `D`.
2. **A uniform sup bound.** The reduced equation `Δw = (exp (2w) h - 1) / 8 + g` gives
   `Δw ≥ -1 / 8`, so the mean-value inequality on unit discs
   (`TauCeti.le_one_div_two_add_integral_sq_div_add_of_neg_le_laplacian`) bounds `w` above by
   its `L²` norm. Then `Δw ≤ exp (2 sup w) / 8 + A`, and the same inequality for `-w` bounds `w`
   below. Hence `|w| ≤ M` uniformly (`TauCeti.Vortex.exists_forall_abs_le_of_laplacian_eq`), and
   `|α|² ≥ exp (-2M) / 2` outside the disc of radius `R + 1`
   (`TauCeti.Vortex.exists_forall_le_sq_norm_sectionValue`).
3. **Exterior decay.** Outside that disc `-log |α|²` is a subsolution of `-Δ + c₀²` for
   `4 c₀² = exp (-2M) / 2`, so it decays at the rate `c₀` with uniform constants
   (`TauCeti.Vortex.neg_log_normSq_le_mul_exp_of_le_normSq`). Past a uniform radius this forces
   `|α|² ≥ 4 c²`, and a second application of the same comparison gives the rate `c`.

The degree-zero case is the vacuum, with `|α| = 1`.

## Main results

* `TauCeti.Vortex.exists_forall_abs_le_of_laplacian_eq`: the smooth solution of the reduced
  equation obtained from a minimizer of Taubes's functional is bounded, uniformly over divisors
  in a fixed disc.
* `TauCeti.Vortex.exists_forall_le_sq_norm_sectionValue`: outside a disc containing the zeros,
  the squared modulus `|α|²` of a smooth framed vortex is bounded below, uniformly over divisors
  in that disc.
* `TauCeti.Vortex.exists_forall_one_sub_normSq_le_mul_exp`: the modulus defect of a smooth framed
  vortex decays like `K exp (-c |z|)`, for every `c < 1 / 2`, with `K` uniform over divisors in a
  fixed disc.
* `TauCeti.Vortex.exists_forall_abs_curvature_le_mul_exp`: the same uniform bound for the
  curvature.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Polynomial Topology InnerProductSpace Laplacian
open scoped ContDiff

namespace TauCeti.Vortex

/-! ### The reduced equation for divisors in a disc -/

section Window

/-- The coefficients of the reduced equation for `P = ∏_{a ∈ D} (X - a)` decay like
`(1 + ‖z‖)⁻²`, with a constant depending only on the degree and on a disc containing the roots:
`g (1 + ‖z‖)² ≤ A` and `(1 + ‖P‖²)⁻¹ (1 + ‖z‖)² ≤ A`, where `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. -/
private theorem exists_coefficient_bound (m : ℕ) (R : ℝ) :
    ∃ A, ∀ D : Multiset ℂ, Multiset.card D = m → 0 < m → (∀ a ∈ D, ‖a‖ ≤ R) → 0 ≤ R →
      ∀ z, 2 * ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ ^ 2 /
          (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2) ^ 2 * (1 + ‖z‖) ^ 2 ≤ A ∧
        (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2)⁻¹ * (1 + ‖z‖) ^ 2 ≤ A := by
  set Λ := 1 + R
  set A := 2 * (Λ ^ m) ^ 2 * ((2 : ℝ) ^ m) ^ 4 + ((2 : ℝ) ^ m) ^ 2 +
    2 * (Λ ^ m) ^ 2 * ((2 * Λ) ^ m) ^ 2 * (2 * Λ) ^ 2 + (2 * Λ) ^ 2 with hA
  refine ⟨A, fun D hDm hm hD hR z ↦ ?_⟩
  set P := (D.map fun a ↦ X - C a).prod
  set N := ‖P.eval z‖
  set N' := ‖P.derivative.eval z‖
  set T := 1 + ‖z‖
  have hT : 1 ≤ T := le_add_of_nonneg_right (norm_nonneg z)
  have hΛ : 1 ≤ Λ := le_add_of_nonneg_right hR
  have hA₁ : 0 ≤ 2 * (Λ ^ m) ^ 2 * ((2 : ℝ) ^ m) ^ 4 := by positivity
  have hA₂ : 0 ≤ ((2 : ℝ) ^ m) ^ 2 := by positivity
  have hA₃ : 0 ≤ 2 * (Λ ^ m) ^ 2 * ((2 * Λ) ^ m) ^ 2 * (2 * Λ) ^ 2 := by positivity
  have hA₄ : 0 ≤ (2 * Λ) ^ 2 := by positivity
  -- `‖P'(z)‖ ≤ (Λ T)ᵐ`, since `‖z‖ + R + 1 ≤ (1 + R) (1 + ‖z‖)`.
  have hN' : N' ≤ Λ ^ m * T ^ m := by
    rw [← mul_pow, ← hDm]
    refine (norm_derivative_eval_multiset_prod_X_sub_C_le hR hD z).trans
      (pow_le_pow_left₀ (by positivity) ?_ _)
    nlinarith [norm_nonneg z]
  have hTm : T ≤ T ^ m := le_self_pow₀ hT hm.ne'
  have hden : 1 ≤ (1 + N ^ 2) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg N))
  rcases le_or_gt (2 * R + 1) ‖z‖ with hz | hz
  · -- Far from the roots, `‖P(z)‖ ≥ (T / 2)ᵐ`.
    have hN : T ^ m / 2 ^ m ≤ N := by
      rw [← div_pow, ← hDm]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_norm_eval_multiset_prod_X_sub_C hD (by linarith))
    have hTm₀ : 0 < T ^ m / 2 ^ m := by positivity
    have hNpos : 0 < N := hTm₀.trans_le hN
    -- `N ≥ Tᵐ / 2ᵐ` gives `N⁴ ≥ T⁴ᵐ / 2⁴ᵐ` and `N² ≥ T²ᵐ / 2²ᵐ`.
    have hN2 : (T ^ m / 2 ^ m) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hTm₀.le hN 2
    have hN4 : (T ^ m / 2 ^ m) ^ 4 ≤ (1 + N ^ 2) ^ 2 := by
      calc (T ^ m / 2 ^ m) ^ 4 = ((T ^ m / 2 ^ m) ^ 2) ^ 2 := by ring
        _ ≤ (N ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hN2 2
        _ ≤ (1 + N ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    constructor
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc 2 * N' ^ 2 * T ^ 2 ≤ 2 * (Λ ^ m * T ^ m) ^ 2 * (T ^ m) ^ 2 := by gcongr
        _ = 2 * (Λ ^ m) ^ 2 * (2 ^ m) ^ 4 * (T ^ m / 2 ^ m) ^ 4 := by
          field_simp
        _ ≤ A * (1 + N ^ 2) ^ 2 := by
          gcongr
          rw [hA]
          linarith
    · rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
      calc T ^ 2 ≤ (T ^ m) ^ 2 := by gcongr
        _ = (2 ^ m) ^ 2 * (T ^ m / 2 ^ m) ^ 2 := by field_simp
        _ ≤ A * (1 + N ^ 2) := by
          gcongr
          · rw [hA]; linarith
          · linarith
  · -- Near the roots, `T < 2 Λ`.
    have hT2 : T ≤ 2 * Λ := by simp only [T, Λ]; linarith
    have hTm2 : T ^ m ≤ (2 * Λ) ^ m := pow_le_pow_left₀ (by positivity) hT2 m
    constructor
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc 2 * N' ^ 2 * T ^ 2 ≤ 2 * (Λ ^ m * (2 * Λ) ^ m) ^ 2 * (2 * Λ) ^ 2 := by
            gcongr
            exact hN'.trans (by gcongr)
        _ = (2 * (Λ ^ m) ^ 2 * ((2 * Λ) ^ m) ^ 2 * (2 * Λ) ^ 2) * 1 := by ring
        _ ≤ A * (1 + N ^ 2) ^ 2 := by
          gcongr
          rw [hA]
          linarith
    · rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
      calc T ^ 2 ≤ (2 * Λ) ^ 2 := by gcongr
        _ = (2 * Λ) ^ 2 * 1 := by ring
        _ ≤ A * (1 + N ^ 2) := by
          gcongr
          · rw [hA]; linarith
          · linarith [sq_nonneg N]

/-- The linear coefficient `c = g - (1 + ‖P‖²)⁻¹ / 8` of Taubes's functional for
`P = ∏_{a ∈ D} (X - a)` has `∫ c² ≤ K`, with `K` depending only on the degree and on a disc
containing the roots. -/
private theorem exists_integral_sq_le (m : ℕ) (R : ℝ) :
    ∃ K, ∀ D : Multiset ℂ, Multiset.card D = m → 0 < m → (∀ a ∈ D, ‖a‖ ≤ R) → 0 ≤ R →
      ∫ z, (2 * ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ ^ 2 /
          (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2) ^ 2 -
        (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2)⁻¹ / 8) ^ 2 ≤ K := by
  obtain ⟨A, hbound⟩ := exists_coefficient_bound m R
  refine ⟨∫ z : ℂ, (2 * A) ^ 2 * (1 + ‖z‖) ^ (-(4 : ℝ)), fun D hDm hm hD hR ↦ ?_⟩
  have hint : Integrable (fun z : ℂ ↦ (2 * A) ^ 2 * (1 + ‖z‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _
  refine integral_mono_of_nonneg (.of_forall fun z ↦ sq_nonneg _) hint (.of_forall fun z ↦ ?_)
  dsimp only
  obtain ⟨hg, hi⟩ := hbound D hDm hm hD hR z
  set P := (D.map fun a ↦ X - C a).prod
  set g := 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2
  set i := (1 + ‖P.eval z‖ ^ 2)⁻¹
  set T := 1 + ‖z‖
  have hT : 0 < T := by positivity
  have hg0 : 0 ≤ g := by positivity
  have hi0 : 0 ≤ i := by positivity
  -- `|c| ≤ g + (1 + ‖P‖²)⁻¹ ≤ 2 A / T²`.
  have habs : |g - i / 8| * T ^ 2 ≤ 2 * A := by
    have : |g - i / 8| ≤ g + i := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg T)]
  rw [Real.rpow_neg hT.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (g - i / 8) ^ 2 * T ^ 4 = (|g - i / 8| * T ^ 2) ^ 2 := by rw [mul_pow, sq_abs]; ring
    _ ≤ (2 * A) ^ 2 := pow_le_pow_left₀ (by positivity) habs 2

/-- **A uniform bound for the reduced vortex correction.** Let `m ≥ 1` and `R` be given. There is
a constant `M` with the following property. Let `D` be a multiset of `m` points of the closed disc
of radius `R`, `P = ∏_{a ∈ D} (X - a)`, and `u ∈ H¹(ℂ)` with `I_P(u) ≤ 0` for Taubes's functional
`I_P = TauCeti.Vortex.sobolevReducedFunctional P`, for instance a minimizer. If `w` is a `C²`
representative of `u` solving the reduced equation
`Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²`, `h = ‖P‖² / (1 + ‖P‖²)`, then `|w| ≤ M`
everywhere. -/
theorem exists_forall_abs_le_of_laplacian_eq (m : ℕ) (hm : 0 < m) (R : ℝ) :
    ∃ M, ∀ D : Multiset ℂ, Multiset.card D = m → (∀ a ∈ D, ‖a‖ ≤ R) →
      ∀ u : W1p (volume : Measure ℂ) ⊤ 2,
        sobolevReducedFunctional ((D.map fun a ↦ X - C a).prod) u ≤ 0 →
      ∀ w : ℂ → ℝ, ContDiff ℝ 2 w → W1p.value u =ᵐ[volume] w →
      (∀ z, Δ w z = (Real.exp (2 * w z) *
          backgroundWeight ((D.map fun a ↦ X - C a).prod).eval z - 1) / 8 +
        2 * ‖deriv ((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2 /
          (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2) ^ 2) →
      ∀ z, |w z| ≤ M := by
  set R' := max R 0
  obtain ⟨A, hbound⟩ := exists_coefficient_bound m R'
  obtain ⟨K, hK⟩ := exists_integral_sq_le m R'
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_sobolevReducedFunctional_le (R' + 1) K 0
  set V := volume.real (ball (0 : ℂ) 1)
  set κ₁ := 1 / 2 + B ^ 2 / (2 * V) + 1 / 8 / 8
  set κ₂ := 1 / 2 + B ^ 2 / (2 * V) + (Real.exp (2 * κ₁) / 8 + A) / 8
  refine ⟨max κ₁ κ₂, fun D hDm hD u hu w hw huw hΔ z ↦ ?_⟩
  have hR' : 0 ≤ R' := le_max_right _ _
  have hD' : ∀ a ∈ D, ‖a‖ ≤ R' := fun a ha ↦ (hD a ha).trans (le_max_left _ _)
  set P := (D.map fun a ↦ X - C a).prod
  have hdeg : 0 < P.natDegree := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hDm]
    exact hm
  -- `‖P‖ ≥ 1` outside the disc of radius `R' + 1`.
  have hP1 : ∀ z ∉ closedBall (0 : ℂ) (R' + 1), 1 ≤ ‖P.eval z‖ := fun z hz ↦
    one_le_norm_eval_multiset_prod_X_sub_C hD' (by simpa using (not_le.1 (by simpa using hz)).le)
  -- The uniform `H¹` bound gives `∫ w² ≤ B²`.
  have huB := hB P hdeg hP1 (hK D hDm hm hD' hR') u hu
  have hwL : MemLp w 2 := (W1p.memLp_value u).ae_eq huw
  have hw2 : Integrable fun x ↦ w x ^ 2 :=
    (memLp_two_iff_integrable_sq hwL.aestronglyMeasurable).1 hwL
  have hint : ∫ x, w x ^ 2 ≤ B ^ 2 := by
    have h1 : ∫ x, w x ^ 2 = ‖W1p.value u‖ ^ 2 := by
      rw [← W1p.integral_value_sq_eq_norm_value_sq]
      simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
      exact integral_congr_ae (huw.mono fun x hx ↦ by simp only [hx])
    have h2 := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
    rw [h1]
    nlinarith [sq_nonneg ‖W1p.gradient u‖, norm_nonneg u]
  -- The coefficient `g` of the reduced equation is at most `A`.
  have hg : ∀ x, 2 * ‖deriv P.eval x‖ ^ 2 / (1 + ‖P.eval x‖ ^ 2) ^ 2 ≤ A := fun x ↦ by
    have h := (hbound D hDm hm hD' hR' x).1
    rw [← Polynomial.deriv] at h
    refine le_trans ?_ h
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by simp))
  -- The mean-value inequality on unit discs, with `∫ v² ≤ B²` and `Δ v ≥ -L`.
  have hV : 0 < V := by
    simp only [V, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hmv : ∀ v : ℂ → ℝ, ContDiff ℝ 2 v → Integrable (fun x ↦ v x ^ 2) →
      ∫ x, v x ^ 2 ≤ B ^ 2 → ∀ L, (∀ x, -L ≤ Δ v x) → ∀ x, v x ≤ 1 / 2 + B ^ 2 / (2 * V) + L / 8 :=
    fun v hv hv2 hvB L hL x ↦ by
      have h := le_one_div_two_add_integral_sq_div_add_of_neg_le_laplacian (μ := volume) hv hv2
        hL x
      rw [Complex.finrank_real_complex] at h
      have := div_le_div_of_nonneg_right hvB (by positivity : 0 ≤ 2 * V)
      norm_num at h
      linarith
  -- Upper bound: `Δw ≥ -1 / 8`.
  have hup : ∀ x, w x ≤ κ₁ := hmv w hw hw2 hint _ fun x ↦ by
    rw [hΔ x]
    have := mul_nonneg (Real.exp_pos (2 * w x)).le (backgroundWeight_nonneg P.eval x)
    have : 0 ≤ 2 * ‖deriv P.eval x‖ ^ 2 / (1 + ‖P.eval x‖ ^ 2) ^ 2 := by positivity
    linarith
  -- Lower bound: `Δw ≤ exp (2 κ₁) / 8 + A`, applied to `-w`.
  have hlow : -w z ≤ κ₂ := hmv (-w) hw.neg (by simpa using hw2) (by simpa using hint) _
    (fun x ↦ by
      rw [congrFun laplacian_neg x, Pi.neg_apply, hΔ x]
      have hh := mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hup x) zero_le_two))
        (backgroundWeight_lt_one P.eval x).le (backgroundWeight_nonneg P.eval x)
        (Real.exp_pos _).le
      linarith [hg x]) z
  exact abs_le.mpr ⟨by linarith [le_max_right κ₁ κ₂], (hup z).trans (le_max_left _ _)⟩

end Window

/-! ### Framed vortices with zeros in a disc -/

section Framed

variable {m : ℕ}

/-- A smooth framed vortex of degree zero has `|α| = 1`: it is gauge equivalent to the vacuum. -/
private theorem sq_norm_sectionValue_eq_one (x : framedVortexSubMulAction 0) (z : ℂ) :
    ‖sectionValue x z‖ ^ 2 = 1 := by
  have hvac : amplitudeField 0 (fun _ ↦ 1) ∈ framedVortexSubMulAction 0 := by
    refine mem_framedVortexSubMulAction.2
      ⟨contDiff_amplitudeField (n := ⊤) contDiff_const contDiff_const, fun z ↦ ?_, ?_⟩
    · rw [equation_amplitudeField_eq_zero_iff (u := 0) (f := fun _ ↦ 1) contDiffAt_const
        (differentiableAt_const _)]
      simp [Pi.zero_def]
    · simp [sectionValue_amplitudeField]
  obtain ⟨v, hv⟩ := framedVortexDivisor_eq_framedVortexDivisor_iff.1
    ((Sym.eq_nil_of_card_zero _).trans (Sym.eq_nil_of_card_zero _).symm :
      framedVortexDivisor x = framedVortexDivisor ⟨_, hvac⟩)
  rw [← hv, SubMulAction.val_smul, norm_sectionValue_smul]
  simp [sectionValue_amplitudeField]

/-- A smooth framed vortex of degree `m ≥ 1` with divisor `D` has squared modulus
`|α|² = exp (2w) h`, where `h = ‖P‖² / (1 + ‖P‖²)` for `P = ∏_{a ∈ D} (X - a)` and `w` is a
smooth representative of a minimizer of Taubes's functional for `P`, solving the reduced
equation. -/
private theorem exists_sq_norm_sectionValue_eq (hm : 0 < m) (x : framedVortexSubMulAction m) :
    ∃ (u : W1p (volume : Measure ℂ) ⊤ 2) (w : ℂ → ℝ),
      sobolevReducedFunctional
        (((framedVortexDivisor x : Multiset ℂ).map fun a ↦ X - C a).prod) u ≤ 0 ∧
      ContDiff ℝ ∞ w ∧ W1p.value u =ᵐ[volume] w ∧
      (∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight
          (((framedVortexDivisor x : Multiset ℂ).map fun a ↦ X - C a).prod).eval z - 1) / 8 +
        2 * ‖deriv (((framedVortexDivisor x : Multiset ℂ).map fun a ↦ X - C a).prod).eval z‖ ^ 2 /
          (1 + ‖(((framedVortexDivisor x : Multiset ℂ).map fun a ↦ X - C a).prod).eval z‖ ^ 2) ^
            2) ∧
      ∀ z, ‖sectionValue x z‖ ^ 2 = Real.exp (2 * w z) * backgroundWeight
        (((framedVortexDivisor x : Multiset ℂ).map fun a ↦ X - C a).prod).eval z := by
  set D := framedVortexDivisor x
  set P : ℂ[X] := ((D : Multiset ℂ).map fun a ↦ X - C a).prod
  have hdeg : 0 < P.natDegree := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, Sym.card_coe]
    exact hm
  obtain ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hdeg
  obtain ⟨w, hw, huw, hΔ⟩ :=
    exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le hdeg hu
  obtain ⟨hy, hysol, hyfr, hyD⟩ :=
    contDiff_equation_eq_zero_isZeroMultiplicity_amplitudeField_prod_X_sub_C hm D hw
      ((W1p.memLp_value u).ae_eq huw) hΔ
  -- The reconstructed vortex has divisor `D`, so it is gauge equivalent to `x`.
  set y : framedVortexSubMulAction m := ⟨_, mem_framedVortexSubMulAction.2 ⟨hy, hysol, hyfr⟩⟩
  obtain ⟨v, hv⟩ := framedVortexDivisor_eq_framedVortexDivisor_iff.1
    (framedVortexDivisor_eq_iff (x := y) (D := D) |>.2 hyD).symm
  refine ⟨u, w, (hu 0).trans_eq sobolevReducedFunctional_zero, hw, huw, hΔ, fun z ↦ ?_⟩
  rw [← hv, SubMulAction.val_smul, norm_sectionValue_smul,
    sq_norm_sectionValue_amplitudeField_backgroundAmplitude_add]

/-- **A uniform lower bound for `|α|²` on a window of divisors.** Let `m` be a degree and `R` a
radius. There is a constant `δ > 0` such that every smooth framed degree-`m` vortex whose zeros
all lie in the closed disc of radius `R` has `δ ≤ |α(z)|²` whenever `R + 1 ≤ |z|`. -/
theorem exists_forall_le_sq_norm_sectionValue (m : ℕ) (R : ℝ) :
    ∃ δ, 0 < δ ∧ ∀ x : framedVortexSubMulAction m, (∀ a ∈ framedVortexDivisor x, ‖a‖ ≤ R) →
      ∀ z, R + 1 ≤ ‖z‖ → δ ≤ ‖sectionValue x z‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- The vacuum has `|α| = 1`.
    exact ⟨1, one_pos, fun x _ z _ ↦ (sq_norm_sectionValue_eq_one x z).ge⟩
  obtain ⟨M, hM⟩ := exists_forall_abs_le_of_laplacian_eq m hm R
  refine ⟨Real.exp (-(2 * M)) / 2, by positivity, fun x hx z hz ↦ ?_⟩
  obtain ⟨u, w, hu, hw, huw, hΔ, hs⟩ := exists_sq_norm_sectionValue_eq hm x
  have hD : ∀ a ∈ (framedVortexDivisor x : Multiset ℂ), ‖a‖ ≤ R :=
    fun a ha ↦ hx a (Sym.mem_coe.1 ha)
  have hwM := hM _ Sym.card_coe hD u hu w (hw.of_le (by simp)) huw hΔ z
  rw [hs z]
  have hP1 := one_le_norm_eval_multiset_prod_X_sub_C hD hz
  have hh : 1 / 2 ≤ backgroundWeight
      (((framedVortexDivisor x : Multiset ℂ).map fun a ↦ X - C a).prod).eval z := by
    rw [backgroundWeight_def, le_div_iff₀ (by positivity)]
    nlinarith
  have he : Real.exp (-(2 * M)) ≤ Real.exp (2 * w z) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hwM).1])
  calc Real.exp (-(2 * M)) / 2 = Real.exp (-(2 * M)) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul he hh (by norm_num) (Real.exp_pos _).le

/-- **Uniform exponential decay of the modulus defect on a window of divisors.** Let `m` be a
degree, `R` a radius and `c < 1 / 2` a rate. There is a constant `K` such that every smooth
framed degree-`m` vortex whose zeros all lie in the closed disc of radius `R` satisfies

`1 - |α(z)|² ≤ K exp (-c |z|)`

at every point `z`, where `|α|² = 4 (p² + q²)` is the squared modulus of its section. -/
theorem exists_forall_one_sub_normSq_le_mul_exp (m : ℕ) (R : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ x : framedVortexSubMulAction m, (∀ a ∈ framedVortexDivisor x, ‖a‖ ≤ R) →
      ∀ z, 1 - 4 * ((x : ℂ → EuclideanSpace ℝ (Fin 4)) z 2 ^ 2 +
        (x : ℂ → EuclideanSpace ℝ (Fin 4)) z 3 ^ 2) ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨δ₀, hδ₀, hlow⟩ := exists_forall_le_sq_norm_sectionValue m R
  set R' := max R 0
  -- Outside the disc of radius `R' + 1`, `|α|² ≥ δ`.
  set δ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  -- The rates and radii of the two comparison steps, independent of the vortex.
  set c' := max c (1 / 4)
  have hc'0 : 0 < c' := lt_max_of_lt_right (by norm_num)
  have hc'1 : c' < 1 / 2 := max_lt hc (by norm_num)
  set c₀ := √δ / 2
  have hc₀ : 0 < c₀ := by positivity
  have h4c₀ : 4 * c₀ ^ 2 = δ := by
    simp only [c₀, div_pow, Real.sq_sqrt hδ.le]
    ring
  set R₀ := R' + 1
  have hR₀ : 0 < R₀ := by positivity
  set M₀ := -Real.log δ
  have hM₀ : 0 ≤ M₀ := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  have h4c'0 : 0 < 4 * c' ^ 2 := by positivity
  have h4c'1 : 4 * c' ^ 2 < 1 := by nlinarith
  set M₁ := -Real.log (4 * c' ^ 2)
  have hM₁ : 0 < M₁ := neg_pos.mpr (Real.log_neg h4c'0 h4c'1)
  -- `M₀ exp (-c₀ T) → 0`, so it is at most `M₁` for some `T ≥ 0`.
  obtain ⟨T, hT0, hT⟩ : ∃ T, 0 ≤ T ∧ M₀ * Real.exp (-(c₀ * T)) ≤ M₁ := by
    have h : Tendsto (fun T ↦ M₀ * Real.exp (-(c₀ * T))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hc₀)).const_mul M₀
    exact ((eventually_ge_atTop 0).and (h.eventually (ge_mem_nhds hM₁))).exists
  set R₁ := R₀ + T
  have hR₁ : 0 < R₁ := by positivity
  refine ⟨max M₁ 1 * Real.exp (c' * R₁), fun x hx z ↦ ?_⟩
  obtain ⟨hxs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 x.2
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    (contDiff_piLp 2).1 hxs i
  have hp : ContDiff ℝ 2 fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w 2 := (hxi 2).of_le (by simp)
  have hq : ContDiff ℝ 2 fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w 3 := (hxi 3).of_le (by simp)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfr
  set s : ℂ → ℝ := fun z ↦ 4 * ((x : ℂ → EuclideanSpace ℝ (Fin 4)) z 2 ^ 2 +
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) z 3 ^ 2)
  have hlowx : ∀ z, R₀ ≤ ‖z‖ → δ ≤ s z := fun z hz ↦ by
    have h := hlow x hx z (by linarith [le_max_left R 0])
    rw [sq_norm_sectionValue] at h
    exact (min_le_left _ _).trans h
  have hpos : ∀ z, R₀ ≤ ‖z‖ → 0 < s z := fun z hz ↦ hδ.trans_le (hlowx z hz)
  -- First step: decay at the rate `c₀` outside the disc of radius `R₀`.
  have hstep₁ : ∀ z, R₀ ≤ ‖z‖ → -Real.log (s z) ≤ M₀ * Real.exp (-(c₀ * (‖z‖ - R₀))) :=
    fun z hz ↦ neg_log_normSq_le_mul_exp_of_le_normSq hp hq hsol hlim hR₀ hc₀.le hM₀
      (fun w hw ↦ h4c₀ ▸ hlowx w hw) hpos
      (fun w hw ↦ neg_le_neg (Real.log_le_log hδ (hlowx w hw.ge))) hz
  -- Past the radius `R₁`, `-log |α|² ≤ M₁`, that is `|α|² ≥ 4 c'²`.
  have hfar : ∀ z, R₁ ≤ ‖z‖ → -Real.log (s z) ≤ M₁ := fun z hz ↦ by
    have hz₀ : R₀ ≤ ‖z‖ := by linarith
    refine (hstep₁ z hz₀).trans (le_trans ?_ hT)
    gcongr
    linarith
  have hsR₁ : ∀ z, R₁ ≤ ‖z‖ → 4 * c' ^ 2 ≤ s z := fun z hz ↦ by
    have hz₀ : R₀ ≤ ‖z‖ := by linarith
    have := hfar z hz
    rw [neg_le_neg_iff] at this
    exact (Real.log_le_log_iff h4c'0 (hpos z hz₀)).mp this
  -- Second step: decay at the rate `c'` outside the disc of radius `R₁`.
  have hstep₂ : ∀ z, R₁ ≤ ‖z‖ → -Real.log (s z) ≤ M₁ * Real.exp (-(c' * (‖z‖ - R₁))) :=
    fun z hz ↦ neg_log_normSq_le_mul_exp_of_le_normSq hp hq hsol hlim hR₁ hc'0.le hM₁.le
      hsR₁ (fun w hw ↦ hpos w (by linarith)) (fun w hw ↦ hfar w hw.ge) hz
  have hcc' : Real.exp (-(c' * ‖z‖)) ≤ Real.exp (-(c * ‖z‖)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (norm_nonneg z)))
  have hK : 0 ≤ max M₁ 1 * Real.exp (c' * R₁) := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hcc' hK)
  -- The left side is `1 - s z` up to `β`-reduction.
  change 1 - s z ≤ _
  rcases le_or_gt R₁ ‖z‖ with hz | hz
  · calc 1 - s z ≤ -Real.log (s z) := by
          linarith [Real.log_le_sub_one_of_pos (hpos z (by linarith))]
      _ ≤ M₁ * Real.exp (-(c' * (‖z‖ - R₁))) := hstep₂ z hz
      _ = M₁ * Real.exp (c' * R₁) * Real.exp (-(c' * ‖z‖)) := by
          rw [exp_neg_mul_sub, mul_assoc]
      _ ≤ max M₁ 1 * Real.exp (c' * R₁) * Real.exp (-(c' * ‖z‖)) := by
          gcongr
          exact le_max_left _ _
  · have hs0 : 0 ≤ s z := by positivity
    calc 1 - s z ≤ 1 * 1 := by linarith
      _ ≤ max M₁ 1 * Real.exp (c' * R₁ - c' * ‖z‖) := by
          gcongr
          · exact le_max_right _ _
          · exact Real.one_le_exp (by nlinarith)
      _ = max M₁ 1 * Real.exp (c' * R₁) * Real.exp (-(c' * ‖z‖)) := by
          rw [sub_eq_add_neg, Real.exp_add, mul_assoc]

/-- **Uniform exponential decay of the curvature on a window of divisors.** Let `m` be a degree,
`R` a radius and `c < 1 / 2` a rate. There is a constant `K` such that every smooth framed
degree-`m` vortex whose zeros all lie in the closed disc of radius `R` has curvature coefficient
`∂₁ b₂ - ∂₂ b₁` bounded by `K exp (-c |z|)`. -/
theorem exists_forall_abs_curvature_le_mul_exp (m : ℕ) (R : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ x : framedVortexSubMulAction m, (∀ a ∈ framedVortexDivisor x, ‖a‖ ≤ R) →
      ∀ z, |fderiv ℝ (fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w 1) z 1 -
        fderiv ℝ (fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w 0) z I| ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_forall_one_sub_normSq_le_mul_exp m R hc
  refine ⟨K / 8, fun x hx z ↦ ?_⟩
  obtain ⟨hxs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 x.2
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    (contDiff_piLp 2).1 hxs i
  have h₁ := normSq_le_one_of_tendsto ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfr) z
  rw [curvature_eq_of_equation_eq_zero (hsol z), abs_neg, abs_of_nonneg (by linarith)]
  linarith [hK x hx z]

end Framed

end TauCeti.Vortex
