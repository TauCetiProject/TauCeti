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
   disc of radius `R + 1` (`Polynomial.one_le_norm_eval_multiset_prod_X_sub_C`), and the
   coefficient `g = 2 ‖P'‖² / (1 + ‖P‖²)²` and the defect `(1 + ‖P‖²)⁻¹` are bounded by
   `A (1 + ‖z‖)⁻²`, with `A` depending only on `m` and `R`
   (`Polynomial.norm_derivative_eval_multiset_prod_X_sub_C_sq_div_mul_le`,
   `Polynomial.inv_one_add_norm_eval_multiset_prod_X_sub_C_sq_mul_le`). So the linear coefficient
   of `I_P` has `L²` norm bounded independently of `D`, and the uniform coercivity of Taubes's
   functional (`TauCeti.Vortex.exists_forall_norm_le_of_sobolevReducedFunctional_le`) bounds the
   minimizer, which has `I_P ≤ I_P(0) = 0`, in `H¹(ℂ)` independently of `D`.
2. **A uniform sup bound.** The reduced equation `Δw = (exp (2w) h - 1) / 8 + g` gives
   `Δw ≥ -1 / 8`, so the mean-value inequality on unit discs
   (`TauCeti.le_one_div_two_add_integral_sq_div_add_of_neg_le_laplacian`) bounds `w` above by
   its `L²` norm. Then `Δw ≤ exp (2 sup w) / 8 + A`, and the same inequality for `-w` bounds `w`
   below (`TauCeti.Vortex.exists_forall_abs_le_of_integral_sq_le_of_laplacian_eq`). Hence
   `|w| ≤ M` uniformly (`TauCeti.Vortex.exists_forall_abs_le_of_laplacian_eq`), and
   `|α|² ≥ exp (-2M) / 2` outside the disc of radius `R + 1`
   (`TauCeti.Vortex.exists_forall_le_sq_norm_sectionValue`).
3. **Exterior decay.** A positive lower bound for `|α|²` outside a fixed disc gives the decay
   `1 - |α|² ≤ K exp (-c |z|)` with `K` depending only on the bound, the disc and `c`
   (`TauCeti.Vortex.exists_forall_one_sub_normSq_le_mul_exp_of_le_normSq`).

The degree-zero case is the vacuum, with `|α| = 1` (`TauCeti.Vortex.norm_sectionValue_eq_one`).

## Main results

* `exists_forall_integral_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight_sq_le`, in
  `TauCeti.Vortex`: the linear coefficient of Taubes's functional for `∏_{a ∈ D} (X - a)` has
  square integral bounded uniformly over multisets `D` of `m ≥ 1` points of a fixed closed disc.
* `TauCeti.Vortex.exists_forall_abs_le_of_integral_sq_le_of_laplacian_eq`: a `C²` solution of
  `Δw = (exp (2w) h - 1) / 8 + g` with `0 ≤ h ≤ 1`, `0 ≤ g ≤ A` and `∫ w² ≤ B²` is bounded by a
  constant depending only on `A` and `B`.
* `TauCeti.Vortex.exists_forall_abs_le_of_laplacian_eq`: the smooth solution of the reduced
  equation obtained from a minimizer of Taubes's functional is bounded, uniformly over divisors
  in a fixed disc.
* `TauCeti.Vortex.exists_forall_le_sq_norm_sectionValue`: for the smooth framed degree-`m`
  vortices whose zeros lie in the closed disc of radius `R`, `|α|²` has a positive lower bound on
  `R + 1 ≤ |z|`, uniform over these vortices.
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

/-- **A uniform bound on the linear coefficient of Taubes's functional.** Let `m ≥ 1` and `R` be
given. There is a constant `K` such that for every multiset `D` of `m` points of the closed disc
of radius `R`, the linear coefficient `c = 2 ‖P'‖² / (1 + ‖P‖²)² - (1 + ‖P‖²)⁻¹ / 8` of
`TauCeti.Vortex.sobolevReducedFunctional P` for `P = ∏_{a ∈ D} (X - a)` satisfies `∫ c² ≤ K`. -/
theorem exists_forall_integral_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight_sq_le
    (m : ℕ) (R : ℝ) :
    ∃ K, ∀ D : Multiset ℂ, Multiset.card D = m → 0 < m → (∀ a ∈ D, ‖a‖ ≤ R) →
      ∫ z, (2 * ‖((D.map fun a ↦ X - C a).prod).derivative.eval z‖ ^ 2 /
          (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2) ^ 2 -
        (1 + ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2)⁻¹ / 8) ^ 2 ≤ K := by
  set A := 2 * (2 * (m : ℝ) ^ 2 * (2 * (1 + R)) ^ (4 * m)) + 2 * (2 * (1 + R)) ^ (2 * m)
  refine ⟨∫ z : ℂ, A ^ 2 * (1 + ‖z‖) ^ (-(4 : ℝ)), fun D hDm hm hD ↦ ?_⟩
  have hint : Integrable (fun z : ℂ ↦ A ^ 2 * (1 + ‖z‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _
  refine integral_mono_of_nonneg (.of_forall fun z ↦ sq_nonneg _) hint (.of_forall fun z ↦ ?_)
  dsimp only
  have hD₀ : D ≠ 0 := Multiset.card_pos.1 (hDm ▸ hm)
  set P := (D.map fun a ↦ X - C a).prod
  set g := 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2
  set i := (1 + ‖P.eval z‖ ^ 2)⁻¹
  set T := 1 + ‖z‖
  have hT : 0 < T := by positivity
  -- `g T² ≤ 4 m² (2 (1 + R))⁴ᵐ` and `(1 + ‖P‖²)⁻¹ T² ≤ 2 (2 (1 + R))²ᵐ`.
  have hg : g * T ^ 2 ≤ 2 * (2 * (m : ℝ) ^ 2 * (2 * (1 + R)) ^ (4 * m)) := by
    have h := norm_derivative_eval_multiset_prod_X_sub_C_sq_div_mul_le hD z
    rw [hDm] at h
    calc g * T ^ 2 = 2 * (‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 * T ^ 2) := by
          simp only [g]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h zero_le_two
  have hi : i * T ^ 2 ≤ 2 * (2 * (1 + R)) ^ (2 * m) := by
    have h := inv_one_add_norm_eval_multiset_prod_X_sub_C_sq_mul_le hD hD₀ z
    rwa [hDm] at h
  -- `|c| ≤ g + (1 + ‖P‖²)⁻¹ ≤ A / T²`.
  have habs : |g - i / 8| * T ^ 2 ≤ A := by
    have hg0 : 0 ≤ g := by positivity
    have hi0 : 0 ≤ i := by positivity
    have : |g - i / 8| ≤ g + i := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg T)]
  rw [Real.rpow_neg hT.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (g - i / 8) ^ 2 * T ^ 4 = (|g - i / 8| * T ^ 2) ^ 2 := by rw [mul_pow, sq_abs]; ring
    _ ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) habs 2

/-- **A sup bound for the reduced vortex equation.** Let `A` and `B` be constants. There is a
constant `M` such that every `C²` function `w` on the plane with `∫ w² ≤ B²` solving
`Δw = (exp (2w) h - 1) / 8 + g` for some functions `0 ≤ h ≤ 1` and `0 ≤ g ≤ A` satisfies
`|w| ≤ M` everywhere. -/
theorem exists_forall_abs_le_of_integral_sq_le_of_laplacian_eq (A B : ℝ) :
    ∃ M, ∀ w h g : ℂ → ℝ, ContDiff ℝ 2 w → Integrable (fun x ↦ w x ^ 2) →
      ∫ x, w x ^ 2 ≤ B ^ 2 → (∀ x, 0 ≤ h x ∧ h x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ A) →
      (∀ x, Δ w x = (Real.exp (2 * w x) * h x - 1) / 8 + g x) → ∀ z, |w z| ≤ M := by
  set V := volume.real (ball (0 : ℂ) 1)
  set κ₁ := 1 / 2 + B ^ 2 / (2 * V) + 1 / 8 / 8
  set κ₂ := 1 / 2 + B ^ 2 / (2 * V) + (Real.exp (2 * κ₁) / 8 + A) / 8
  refine ⟨max κ₁ κ₂, fun w h g hw hw2 hint hh hg hΔ z ↦ ?_⟩
  -- The mean-value inequality on unit discs, with `∫ v² ≤ B²` and `Δ v ≥ -L`.
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
    have := mul_nonneg (Real.exp_pos (2 * w x)).le (hh x).1
    linarith [(hg x).1]
  -- Lower bound: `Δw ≤ exp (2 κ₁) / 8 + A`, applied to `-w`.
  have hlow : -w z ≤ κ₂ := hmv (-w) hw.neg (by simpa using hw2) (by simpa using hint) _
    (fun x ↦ by
      rw [congrFun laplacian_neg x, Pi.neg_apply, hΔ x]
      have := mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hup x) zero_le_two))
        (hh x).2 (hh x).1 (Real.exp_pos _).le
      linarith [(hg x).2]) z
  exact abs_le.mpr ⟨by linarith [le_max_right κ₁ κ₂], (hup z).trans (le_max_left _ _)⟩

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
  obtain ⟨K, hK⟩ :=
    exists_forall_integral_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight_sq_le m R
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_sobolevReducedFunctional_le (R + 1) K 0
  obtain ⟨M, hM⟩ := exists_forall_abs_le_of_integral_sq_le_of_laplacian_eq
    (2 * (2 * (m : ℝ) ^ 2 * (2 * (1 + R)) ^ (4 * m))) B
  refine ⟨M, fun D hDm hD u hu w hw huw hΔ ↦ ?_⟩
  set P := (D.map fun a ↦ X - C a).prod
  have hdeg : 0 < P.natDegree := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hDm]
    exact hm
  -- `‖P‖ ≥ 1` outside the disc of radius `R + 1`, so the uniform `H¹` bound gives `∫ w² ≤ B²`.
  have huB := hB P hdeg (fun z hz ↦ one_le_norm_eval_multiset_prod_X_sub_C hD
    (by simpa using (not_le.1 (by simpa using hz)).le)) (hK D hDm hm hD) u hu
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
  refine hM w _ _ hw hw2 hint
    (fun x ↦ ⟨backgroundWeight_nonneg P.eval x, (backgroundWeight_lt_one P.eval x).le⟩)
    (fun x ↦ ⟨by positivity, ?_⟩) hΔ
  -- The coefficient `g` of the reduced equation is at most `2 · 2 m² (2 (1 + R))⁴ᵐ`.
  have h := norm_derivative_eval_multiset_prod_X_sub_C_sq_div_mul_le hD x
  rw [← Polynomial.deriv, hDm] at h
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ h) zero_le_two
  exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by simp))

end Window

/-! ### Framed vortices with zeros in a disc -/

section Framed

variable {m : ℕ}

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
  have hy := amplitudeField_backgroundAmplitude_add_mem_framedVortexSubMulAction hm D hw
    ((W1p.memLp_value u).ae_eq huw) hΔ
  -- The reconstructed vortex has divisor `D`, so it is gauge equivalent to `x`.
  obtain ⟨v, hv⟩ := framedVortexDivisor_eq_framedVortexDivisor_iff.1
    (framedVortexDivisor_amplitudeField_backgroundAmplitude_add hw.continuous hy).symm
  refine ⟨u, w, (hu 0).trans_eq sobolevReducedFunctional_zero, hw, huw, hΔ, fun z ↦ ?_⟩
  rw [← hv, SubMulAction.val_smul, norm_sectionValue_framedGaugeGroup_smul,
    sq_norm_sectionValue_amplitudeField_backgroundAmplitude_add]

/-- **A uniform lower bound for `|α|²` on a window of divisors.** Let `m` be a degree and `R` a
radius. There is a constant `δ > 0` such that every smooth framed degree-`m` vortex whose zeros
all lie in the closed disc of radius `R` has `δ ≤ |α(z)|²` whenever `R + 1 ≤ |z|`. -/
theorem exists_forall_le_sq_norm_sectionValue (m : ℕ) (R : ℝ) :
    ∃ δ, 0 < δ ∧ ∀ x : framedVortexSubMulAction m, (∀ a ∈ framedVortexDivisor x, ‖a‖ ≤ R) →
      ∀ z, R + 1 ≤ ‖z‖ → δ ≤ ‖sectionValue x z‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- The vacuum has `|α| = 1`.
    exact ⟨1, one_pos, fun x _ z _ ↦ by rw [norm_sectionValue_eq_one, one_pow]⟩
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

at every point `z`. -/
theorem exists_forall_one_sub_normSq_le_mul_exp (m : ℕ) (R : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ x : framedVortexSubMulAction m, (∀ a ∈ framedVortexDivisor x, ‖a‖ ≤ R) →
      ∀ z, 1 - ‖sectionValue x z‖ ^ 2 ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_forall_le_sq_norm_sectionValue m R
  obtain ⟨K, hK⟩ := exists_forall_one_sub_normSq_le_mul_exp_of_le_normSq (R + 1) hδ hc
  refine ⟨K, fun x hx z ↦ ?_⟩
  obtain ⟨hxs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 x.2
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    ((contDiff_piLp 2).1 hxs i).of_le (by simp)
  rw [sq_norm_sectionValue]
  exact hK x (hxi 2) (hxi 3) hsol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfr)
    (fun w hw ↦ sq_norm_sectionValue (x : ℂ → EuclideanSpace ℝ (Fin 4)) w ▸ hlow x hx w hw) z

/-- **Uniform exponential decay of the curvature on a window of divisors.** Let `m` be a degree,
`R` a radius and `c < 1 / 2` a rate. There is a constant `K` such that every smooth framed
degree-`m` vortex whose zeros all lie in the closed disc of radius `R` has curvature coefficient
`∂₁ b₂ - ∂₂ b₁` bounded by `K exp (-c |z|)`. -/
theorem exists_forall_abs_curvature_le_mul_exp (m : ℕ) (R : ℝ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ x : framedVortexSubMulAction m, (∀ a ∈ framedVortexDivisor x, ‖a‖ ≤ R) →
      ∀ z, |curvature x z| ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := exists_forall_one_sub_normSq_le_mul_exp m R hc
  refine ⟨K / 8, fun x hx z ↦ ?_⟩
  obtain ⟨hxs, hsol, hfr⟩ := mem_framedVortexSubMulAction.1 x.2
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ (x : ℂ → EuclideanSpace ℝ (Fin 4)) w i :=
    ((contDiff_piLp 2).1 hxs i).of_le (by simp)
  have h₁ := normSq_le_one_of_tendsto (hxi 2) (hxi 3) hsol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hfr) z
  have h := hK x hx z
  rw [sq_norm_sectionValue] at h
  rw [curvature_apply, curvature_eq_of_equation_eq_zero (hsol z), abs_neg,
    abs_of_nonneg (by linarith)]
  linarith

end Framed

end TauCeti.Vortex
