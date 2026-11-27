/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Flux.Moment
public import TauCeti.Analysis.PDE.Vortex.ModulusBound
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Newton variance of dilated plane vortices

Let `x` be a smooth framed degree-`m` plane vortex with zero divisor `D`. Its normalized flux
density `μ = (1 - |α|²) / (16π) dw` is a nonnegative measure of mass `m`
(`TauCeti.Vortex.integral_one_sub_normSq_eq_mul_card`) whose holomorphic moments are those of the
counting measure of `D` (`TauCeti.Vortex.integral_one_sub_normSq_smul_eval_eq`). Dilate it by a
factor `ε`, `W = ε w`. In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic
curve, `ε = h / a` is the ratio of the vortex scale `h = (2r)^(-1/2)` to the size `a` of the zero
set in the normal direction, and the dilated flux density models a normal slice `μ_z` of the
normalized curvature current, with its zeros in a disc of fixed radius `R` in the coordinate `W`.

The moments `M_k = ∫ Wᵏ dμ_ε` of the dilated density are the power sums of the dilated divisor
`ε D`, so the Newton polynomial `P` of degree `m` of these moments is `∏_{a ∈ D} (W - ε a)`
(`TauCeti.Vortex.newtonPolynomial_integral_one_sub_normSq_smul_mul_pow`). This file proves that the
**Newton variance** `∫ |P(W)|² dμ_ε(W)` is at most `C ε²`, with a constant `C` depending only on
the degree `m` and the radius `R`
(`TauCeti.Vortex.exists_integral_norm_eval_newtonPolynomial_sq_mul_le`). The constant does not
depend on the configuration of the zeros: collisions and every intermediate separation scale of the
zeros are included. Since the density is nonnegative, the negative mass vanishes, and the variance
tends to zero as `ε → 0` uniformly over all such vortices. These supply the small-variance and
small-negative-mass hypotheses of the compact moment lemma
(`TauCeti.exists_forall_abs_integral_sub_sum_roots_le`), which compares a slice with the counting
measure of the roots of its Newton polynomial; its compact-support hypothesis is not supplied here,
since the dilated density is positive everywhere, and still needs a separate cutoff or tail
estimate.

The proof is pointwise (`TauCeti.Vortex.exists_integral_norm_prod_sq_mul_one_sub_normSq_le`). At a
point `w` at distance `d` from the nearest zero `a₀`, the factor `W - ε a₀` of `P(ε w)` has norm
`ε d`, and every factor has norm at most `d + 2R`, so `|P(ε w)|² ≤ ε² (d + 2R)^(2m)`. The modulus
defect `1 - |α(w)|²` is at most `K exp (-d / 4)` with `K` depending only on `m`
(`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub`), which absorbs the
polynomial factor into `exp (-d / 8)`, and `exp (-d / 8)` is at most the sum over the zeros `a` of
`exp (-|w - a| / 8)`, whose integral is `m` times a constant.

## Main results

* `TauCeti.Vortex.exists_integral_norm_prod_sq_mul_one_sub_normSq_le`:
  `∫ |∏_{a ∈ D} (ε w - ε a)|² (1 - |α(w)|²) dw ≤ C ε²`, uniformly over smooth framed degree-`m`
  vortices whose zeros satisfy `ε |a| ≤ R`.
* `TauCeti.Vortex.exists_integral_norm_eval_newtonPolynomial_sq_mul_le`: the Newton variance of the
  dilated flux density is at most `C ε²`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open Complex Filter Metric MeasureTheory Polynomial Topology
open scoped ContDiff Real

namespace TauCeti.Vortex

/-! ### The polynomial factor -/

/-- At a point `w` and a zero `a₀ ∈ D`, if `ε ∈ [0, 1]` and `ε |a| ≤ R` for every `a ∈ D`, then
`|∏_{a ∈ D} (ε w - ε a)| ≤ ε (|w - a₀| + 2R)^(deg D)`: the factor at `a₀` has norm
`ε |w - a₀|`, and every factor has norm at most `|w - a₀| + 2R`. -/
private theorem norm_prod_smul_sub_le {D : Multiset ℂ} {R ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hR : ∀ a ∈ D, ε * ‖a‖ ≤ R) {a₀ : ℂ} (ha₀ : a₀ ∈ D) (w : ℂ) :
    ‖(D.map fun a ↦ (ε : ℂ) * w - ε * a).prod‖ ≤
      ε * (‖w - a₀‖ + 2 * R) ^ Multiset.card D := by
  have hR₀ : 0 ≤ R := (by positivity : 0 ≤ ε * ‖a₀‖).trans (hR a₀ ha₀)
  have hfac (a : ℂ) : ‖(ε : ℂ) * w - ε * a‖ = ε * ‖w - a‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_of_nonneg hε₀]
  -- Every factor has norm at most `|w - a₀| + 2R`.
  have hle (a : ℂ) (ha : a ∈ D) : ‖(ε : ℂ) * w - ε * a‖ ≤ ‖w - a₀‖ + 2 * R := by
    have htri : ‖w - a‖ ≤ ‖w - a₀‖ + ‖a₀‖ + ‖a‖ := by
      calc ‖w - a‖ = ‖(w - a₀) + a₀ - a‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - a₀‖ + ‖a₀‖ + ‖a‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    rw [hfac]
    nlinarith [hR a ha, hR a₀ ha₀, norm_nonneg (w - a₀), norm_nonneg (w - a)]
  have hB : 0 ≤ ‖w - a₀‖ + 2 * R := by positivity
  have hprod (s : Multiset ℂ) (hs : ∀ a ∈ s, ‖(ε : ℂ) * w - ε * a‖ ≤ ‖w - a₀‖ + 2 * R) :
      ‖(s.map fun a ↦ (ε : ℂ) * w - ε * a).prod‖ ≤ (‖w - a₀‖ + 2 * R) ^ Multiset.card s := by
    rw [Multiset.norm_prod, Multiset.map_map]
    refine (Multiset.prod_map_le_prod_map₀ _ (fun _ ↦ ‖w - a₀‖ + 2 * R)
      (fun _ _ ↦ norm_nonneg _) hs).trans_eq ?_
    rw [Multiset.map_const', Multiset.prod_replicate]
  obtain ⟨D', rfl⟩ := Multiset.exists_cons_of_mem ha₀
  have hrest := hprod D' fun a ha ↦ hle a (Multiset.mem_cons_of_mem ha)
  rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, hfac, Multiset.card_cons, pow_succ',
    mul_assoc]
  have hd : ‖w - a₀‖ ≤ ‖w - a₀‖ + 2 * R := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul hd hrest (norm_nonneg _) hB) hε₀

/-- **Pointwise domination.** Let `D` be a multiset of `m` points with `ε |a| ≤ R` for every
`a ∈ D`, where `0 ≤ ε ≤ 1`, and let `u ≥ 0` be at most `K exp (-ρ / 4)` whenever `w` is at distance
at least `ρ` from every point of `D`. Then
`|∏_{a ∈ D} (ε w - ε a)|² u ≤ ε² A ∑_{a ∈ D} exp (-|w - a| / 8)`, with
`A = K (2m)! 8^(2m) exp (R / 4)`, the sum running over the points of `D` with multiplicity. -/
private theorem norm_prod_sq_mul_le_sum {D : Multiset ℂ} {m : ℕ} (hm : Multiset.card D = m)
    {R ε K u : ℝ} (hK₀ : 0 ≤ K) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) (hR : ∀ a ∈ D, ε * ‖a‖ ≤ R)
    {w : ℂ} (hu₀ : 0 ≤ u)
    (hu : ∀ ρ, (∀ a ∈ D, ρ ≤ ‖w - a‖) → u ≤ K * Real.exp (-(1 / 4 * ρ))) :
    ‖(D.map fun a ↦ (ε : ℂ) * w - ε * a).prod‖ ^ 2 * u ≤
      ε ^ 2 * (K * ((2 * m).factorial / (1 / 8) ^ (2 * m) * Real.exp (R / 4))) *
        (D.map fun a ↦ Real.exp (-(1 / 8 * ‖w - a‖))).sum := by
  classical
  rcases D.empty_or_exists_mem with rfl | ⟨b, hb⟩
  · -- Without points `u` vanishes, being at most `K exp (-ρ / 4)` for every `ρ`.
    simpa using nonpos_of_forall_le_mul_exp (by norm_num : (0 : ℝ) < 1 / 4) fun ρ ↦ hu ρ (by simp)
  -- Otherwise compare with the nearest point `a₀`, at distance `d`.
  obtain ⟨a₀, ha₀, hmin⟩ := D.toFinset.exists_min_image (fun a ↦ ‖w - a‖)
    ⟨b, Multiset.mem_toFinset.2 hb⟩
  rw [Multiset.mem_toFinset] at ha₀
  set d := ‖w - a₀‖
  have hR₀ : 0 ≤ R := (by positivity : 0 ≤ ε * ‖a₀‖).trans (hR a₀ ha₀)
  have hd : 0 ≤ d + 2 * R := by positivity
  have hprod : ‖(D.map fun a ↦ (ε : ℂ) * w - ε * a).prod‖ ^ 2 ≤
      ε ^ 2 * (d + 2 * R) ^ (2 * m) := by
    rw [pow_mul', ← mul_pow, ← hm]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_prod_smul_sub_le hε₀ hε₁ hR ha₀ w) 2
  -- Half of the decay rate absorbs the polynomial factor `(d + 2R)^(2m)`.
  have hpoly : (d + 2 * R) ^ (2 * m) * Real.exp (-(1 / 4 * d)) ≤
      (2 * m).factorial / (1 / 8) ^ (2 * m) * Real.exp (R / 4) * Real.exp (-(1 / 8 * d)) := by
    have hsplit : Real.exp (-(1 / 4 * d)) =
        Real.exp (-(1 / 8) * (d + 2 * R)) * (Real.exp (R / 4) * Real.exp (-(1 / 8 * d))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hsplit, ← mul_assoc, mul_assoc _ (Real.exp (R / 4))]
    exact mul_le_mul_of_nonneg_right (pow_mul_exp_neg_mul_le (by norm_num) hd _) (by positivity)
  have hsum : Real.exp (-(1 / 8 * d)) ≤ (D.map fun a ↦ Real.exp (-(1 / 8 * ‖w - a‖))).sum := by
    refine Multiset.single_le_sum (fun y hy ↦ ?_) _ (Multiset.mem_map_of_mem _ ha₀)
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
    positivity
  calc ‖(D.map fun a ↦ (ε : ℂ) * w - ε * a).prod‖ ^ 2 * u
      ≤ ε ^ 2 * (d + 2 * R) ^ (2 * m) * (K * Real.exp (-(1 / 4 * d))) :=
        mul_le_mul hprod (hu d fun a ha ↦ hmin a (Multiset.mem_toFinset.2 ha)) hu₀
          (by positivity)
    _ = ε ^ 2 * K * ((d + 2 * R) ^ (2 * m) * Real.exp (-(1 / 4 * d))) := by ring
    _ ≤ ε ^ 2 * K * ((2 * m).factorial / (1 / 8) ^ (2 * m) * Real.exp (R / 4) *
          Real.exp (-(1 / 8 * d))) := mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = ε ^ 2 * (K * ((2 * m).factorial / (1 / 8) ^ (2 * m) * Real.exp (R / 4))) *
          Real.exp (-(1 / 8 * d)) := by ring
    _ ≤ _ := by gcongr

/-! ### The variance bound -/

/-- **The variance of the zero polynomial against a dilated plane vortex.** For every degree `m`
and radius `R` there is a constant `C ≥ 0` with the following property. Let `x` be a smooth plane
vortex with the degree-`m` end framing and zero divisor `D`, and let `0 ≤ ε ≤ 1` with
`ε |a| ≤ R` for every zero `a`. Then

`∫ |∏_{a ∈ D} (ε w - ε a)|² (1 - |α(w)|²) dw ≤ C ε²`.

The constant depends only on `m` and `R`, not on the vortex or on the configuration of its zeros,
so collisions and every separation scale of the zeros are included. -/
theorem exists_integral_norm_prod_sq_mul_one_sub_normSq_le (m : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → (∀ a ∈ D, ε * ‖a‖ ≤ R) →
        ∫ w, ‖(D.map fun a ↦ (ε : ℂ) * w - ε * a).prod‖ ^ 2 *
          (1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2)) ≤ C * ε ^ 2 := by
  obtain ⟨K, hK₀, hK⟩ := exists_one_sub_normSq_le_mul_exp_of_forall_le_norm_sub m
    (c := 1 / 4) (by norm_num) (by norm_num)
  set I := ∫ w : ℂ, Real.exp (-(1 / 8 * ‖w‖))
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  set A := K * ((2 * m).factorial / (1 / 8) ^ (2 * m) * Real.exp (R / 4))
  have hA : 0 ≤ A := by positivity
  refine ⟨A * m * I, mul_nonneg (mul_nonneg hA m.cast_nonneg) hI,
    fun x D hx hsol hframe hD ε hε₀ hε₁ hR ↦ ?_⟩
  classical
  have hm : Multiset.card D = m := hD.card_eq_of_tendsto_mul_inv_pow hframe
  have hu₀ (w : ℂ) : 0 ≤ 1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2) := by
    rw [← sq_norm_sectionValue]
    exact one_sub_sq_norm_sectionValue_nonneg (hx.of_le (by simp)) hsol
      (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) w
  -- The integrand is dominated by `ε² A ∑_{a ∈ D} exp (-|w - a| / 8)`, of integral at most
  -- `ε² A m I`.
  have hGint : Integrable fun w ↦
      ε ^ 2 * A * (D.map fun a ↦ Real.exp (-(1 / 8 * ‖w - a‖))).sum :=
    (integrable_sum_map_exp_neg_mul_norm_sub volume (by norm_num) D).const_mul _
  refine (integral_mono_of_nonneg (.of_forall fun w ↦ mul_nonneg (by positivity) (hu₀ w)) hGint
    (.of_forall fun w ↦ norm_prod_sq_mul_le_sum hm hK₀ hε₀ hε₁ hR (hu₀ w)
      fun ρ hρ ↦ hK x D hx hsol hframe hD w ρ hρ)).trans ?_
  rw [integral_const_mul, integral_sum_map_exp_neg_mul_norm_sub volume (by norm_num) D, hm]
  exact (by ring : ε ^ 2 * A * (m * I) = A * m * I * ε ^ 2).le

/-- **The Newton variance of a dilated plane vortex.** For every degree `m` and radius `R` there is
a constant `C ≥ 0` with the following property. Let `x` be a smooth plane vortex with the degree-`m`
end framing and zero divisor `D`, and let `0 ≤ ε ≤ 1` with `ε |a| ≤ R` for every zero `a`. Let
`μ_ε` be the flux density `(1 - |α(w)|²) / (16π) dw` dilated by `ε`, a nonnegative measure of mass
`m`, and `P` the Newton polynomial of degree `m` of its moments `M_k = ∫ Wᵏ dμ_ε(W)`. Then the
Newton variance satisfies

`∫ |P(W)|² dμ_ε(W) = ∫ |P(ε w)|² (1 - |α(w)|²) / (16π) dw ≤ C ε²`.

The constant depends only on `m` and `R`, not on the vortex or on the configuration of its
zeros. -/
theorem exists_integral_norm_eval_newtonPolynomial_sq_mul_le (m : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → (∀ a ∈ D, ε * ‖a‖ ≤ R) →
        ∫ w, ‖(newtonPolynomial (fun k ↦ (16 * π : ℂ)⁻¹ *
            ∫ w, (1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2)) • ((ε : ℂ) * w) ^ k) m).eval ((ε : ℂ) * w)‖ ^ 2 *
          ((1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2)) / (16 * π)) ≤ C * ε ^ 2 := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_integral_norm_prod_sq_mul_one_sub_normSq_le m R
  refine ⟨C₀ / (16 * π), by positivity, fun x D hx hsol hframe hD ε hε₀ hε₁ hR ↦ ?_⟩
  have hm : Multiset.card D = m := hD.card_eq_of_tendsto_mul_inv_pow hframe
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := ((contDiff_piLp 2).1 hx i).of_le (by simp)
  have hP := newtonPolynomial_integral_one_sub_normSq_smul_mul_pow (hxi 0) (hxi 1) (hxi 2) (hxi 3)
    hsol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD (ε : ℂ)
  rw [hm] at hP
  -- The Newton polynomial evaluates at `ε w` to `∏_{a ∈ D} (ε w - ε a)`.
  have heval (w : ℂ) : (newtonPolynomial (fun k ↦ (16 * π : ℂ)⁻¹ *
      ∫ w, (1 - 4 * (x w 2 ^ 2 + x w 3 ^ 2)) • ((ε : ℂ) * w) ^ k) m).eval ((ε : ℂ) * w) =
      (D.map fun a ↦ (ε : ℂ) * w - ε * a).prod := by
    rw [hP, eval_multiset_prod, Multiset.map_map]
    simp
  simp_rw [heval, mul_div_assoc', integral_div]
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
  exact hC x D hx hsol hframe hD ε hε₀ hε₁ hR

end TauCeti.Vortex
