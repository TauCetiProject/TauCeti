/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.RadialCoefficient
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Sobolev.Wkp.NormRpow
import TauCeti.MeasureTheory.Measure.Haar.Average

/-!
# `W^{2,p}` regularity fails for a discontinuous coefficient

For `b ≥ 0` let `a = TauCeti.PDE.radialCoefficient 1 b` be the coefficient field on `ℝⁿ`

`a(x) = I + b x̂ x̂ᵀ`, where `x̂ = x / ‖x‖`,

whose eigenvalue in the radial direction `x̂` is `1 + b` and in the directions orthogonal to `x`
is `1`. It is measurable, symmetric and uniformly elliptic with constants `1` and `1 + b`
(`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`), and for `n ≥ 2` and `b ≠ 0` it has no
limit at the origin (`TauCeti.PDE.not_exists_tendsto_radialCoefficient`). Its diagonal entries do
not even have vanishing mean oscillation (`TauCeti.PDE.not_memVMO_radialCoefficient_apply_self`):
every ball `B(0, r)` contains a ball of radius `r / 8` on which the entry stays `|b| / 10` away
from its average over `B(0, r)`, so the mean oscillation over `B(0, r)` is at least
`|b| / (10 · 8ⁿ)`, however small `r` is. In the plane it is
`1 + b` times Meyers' coefficient field `TauCeti.PDE.meyersCoefficient μ` with
`μ² = 1 / (1 + b)`, the corresponding counterexample for divergence-form equations. Away from the
origin the power `u(x) = ‖x‖ ^ γ` satisfies

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = γ (n + γ - 2 + b (γ - 1)) ‖x‖ ^ (γ - 2)`,

because the Hessian of `u` is `γ ‖x‖ ^ (γ - 2)` on the directions orthogonal to `x` and
`γ (γ - 1) ‖x‖ ^ (γ - 2)` on `x`. For `n ≥ 2`, `0 < γ < 1` and `b = (n + γ - 2) / (1 - γ) > 0`
the right side vanishes, so `u` solves the homogeneous non-divergence equation almost everywhere,
with its weak Hessian. On a bounded open set containing the origin, `u` lies in `W^{2,p}` exactly
for `p < n / (2 - γ)`, an exponent strictly between `n / 2` and `n`
(`TauCeti.exists_wkp_two_value_ae_eq_norm_rpow_iff`), so `u` is a `W^{2,p}` strong solution
exactly for these `p`
(`TauCeti.PDE.exists_wkp_two_value_ae_eq_norm_rpow_and_sum_radialCoefficient_eq_zero_iff`).

So for coefficients that are bounded, measurable and uniformly elliptic but discontinuous, a
`W^{2,p₀}` strong solution of `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = 0` with `p₀ < n` need not lie in `W^{2,p}` for
any `p > p₀` with `p > n / 2`, not even for `p = n`: the interior `W^{2,p}` regularity of
strong solutions needs a regularity hypothesis on the coefficients, such as continuity, under
which the interior estimate of
`TauCeti/Analysis/PDE/Regularity/Hessian/ContinuousCoefficient/Basic.lean` holds, or vanishing mean
oscillation. The ellipticity ratio `1 + b` of the counterexample tends to infinity as
`n / (2 - γ)` approaches `n`.

## Main declarations

* `TauCeti.PDE.not_memVMO_radialCoefficient_apply_self`: for `n ≥ 2` and `b ≠ 0`, the diagonal
  entries of the radial coefficient are not in VMO.
* `TauCeti.PDE.ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq`: the non-divergence
  operator applied to an element of `W^{2,p}` equal to `‖x‖ ^ γ`, with its weak Hessian.
* `TauCeti.PDE.exists_radialCoefficient_not_exists_wkp`: for `1 ≤ p₀ < p < ∞` with `p₀ < n` and
  `n / 2 < p`, some such coefficient field has a `W^{2,p₀}` strong solution of the homogeneous
  equation on every bounded open set containing the origin that is not in `W^{2,p}` there.
* `TauCeti.PDE.exists_wkp_two_value_ae_eq_norm_rpow_and_sum_radialCoefficient_eq_zero_iff`: for
  `γ ≠ 0` with `2 - n < γ < 1` and `b = (n + γ - 2) / (1 - γ)`, the function `‖x‖ ^ γ` is a
  `W^{2,p}` strong solution exactly for `p < n / (2 - γ)`.

## References

* D. Gilbarg and J. Serrin, *On isolated singularities of solutions of second order elliptic
  differential equations*, J. Analyse Math. 4 (1955/56), 309–340, for the coefficient field
  `δᵢⱼ + b xᵢ xⱼ / ‖x‖²` and its power solutions.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 9, for the `W^{2,p}` theory of strong solutions.
* F. Chiarenza, M. Frasca, P. Longo, *Interior `W^{2,p}` estimates for non divergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. 40 (1991), 149–168, for the theory
  with coefficients of vanishing mean oscillation.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace Module
open scoped InnerProductSpace ENNReal Topology Matrix

namespace TauCeti

namespace PDE

variable {n : ℕ} {b γ : ℝ}

/-! ### The coefficient does not have vanishing mean oscillation -/

/-- For every constant `m` and `r > 0`, the ball `B(0, r)` in dimension `n ≥ 2` contains a ball of
radius `r / 8` on which `xᵢ² / ‖x‖²` stays at distance at least `1 / 10` from `m`: around
`(r / 2) eᵢ` it is at least `9 / 25`, and around `(r / 2) eⱼ`, `j ≠ i`, at most `1 / 9`. -/
private theorem exists_ball_le_abs_sq_div_norm_sq_sub (hn : 2 ≤ n) (i : Fin n) (m : ℝ) {r : ℝ}
    (hr : 0 < r) : ∃ z : EuclideanSpace ℝ (Fin n), ball z (r / 8) ⊆ ball 0 r ∧
      ∀ y ∈ ball z (r / 8), 1 / 10 ≤ |y i ^ 2 / ‖y‖ ^ 2 - m| := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  obtain ⟨j, hji⟩ := exists_ne i
  set c : Fin n → EuclideanSpace ℝ (Fin n) := fun k => (r / 2) • EuclideanSpace.single k 1
  have hc : ∀ k, ‖c k‖ = r / 2 := fun k => by
    simp [c, norm_smul, abs_of_pos hr]
  have hnorm : ∀ k, ∀ y ∈ ball (c k) (r / 8), 3 * r / 8 < ‖y‖ ∧ ‖y‖ < 5 * r / 8 :=
    fun k y hy => by
      have hy' := mem_ball_iff_norm.1 hy
      constructor
      · linarith [norm_sub_norm_le (c k) y, norm_sub_rev (c k) y, hc k]
      · linarith [norm_le_insert' y (c k), hc k]
  have hcoord : ∀ k, ∀ y ∈ ball (c k) (r / 8), |y i - (if i = k then r / 2 else 0)| < r / 8 :=
    fun k y hy => by
      have := (PiLp.norm_apply_le (y - c k) i).trans_lt (mem_ball_iff_norm.1 hy)
      simpa [c, PiLp.single_apply, Real.norm_eq_abs, apply_ite] using this
  have hsub : ∀ k, ball (c k) (r / 8) ⊆ ball 0 r :=
    fun k y hy => mem_ball_zero_iff.2 (by linarith [(hnorm k y hy).2])
  rcases le_or_gt m (1 / 4) with hm | hm
  · refine ⟨c i, hsub i, fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := hnorm i y hy
    have hyi := (abs_lt.1 (hcoord i y hy)).1
    simp only [↓reduceIte] at hyi
    have hq : 9 / 25 ≤ y i ^ 2 / ‖y‖ ^ 2 := by
      rw [le_div_iff₀ (by nlinarith)]
      nlinarith [mul_self_lt_mul_self (norm_nonneg y) h2,
        mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 3 * r / 8) (by linarith : 3 * r / 8 < y i)]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨c j, hsub j, fun y hy => ?_⟩
    have h1 := (hnorm j y hy).1
    have hyi := abs_lt.1 (hcoord j y hy)
    simp only [hji.symm, ↓reduceIte, sub_zero] at hyi
    have hq : y i ^ 2 / ‖y‖ ^ 2 ≤ 1 / 9 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith [sq_lt_sq' hyi.1 hyi.2,
        mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ 3 * r / 8) h1]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The radial coefficient is not in VMO.** For `n ≥ 2` and `b ≠ 0`, each diagonal entry
`α + b xᵢ² / ‖x‖²` of `TauCeti.PDE.radialCoefficient α b` does not have vanishing mean
oscillation: its mean oscillation over every ball `B(0, r)` is at least `|b| / (10 · 8ⁿ)`. -/
theorem not_memVMO_radialCoefficient_apply_self {α : ℝ} (hn : 2 ≤ n) (hb : b ≠ 0) (i : Fin n) :
    ¬ MemVMO (fun x : EuclideanSpace ℝ (Fin n) => radialCoefficient α b x i i) volume := by
  intro h
  set δ := ENNReal.ofReal (|b| / 10 * (1 / 8) ^ finrank ℝ (EuclideanSpace ℝ (Fin n)))
  have hδ : δ ≠ 0 := by
    simp only [δ, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := abs_pos.2 hb
    positivity
  obtain ⟨r, hr, hle⟩ := (memVMO_iff.1 h).2 (δ / 2) (ENNReal.half_pos hδ)
  set a := ⨍ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, radialCoefficient α b z i i
  obtain ⟨z, hsub, hz⟩ := exists_ball_le_abs_sq_div_norm_sq_sub hn i ((a - α) / b) hr
  -- On the small ball, `|a(y)ᵢᵢ - a| = |b| |yᵢ² / ‖y‖² - (a - α) / b| ≥ |b| / 10`.
  have hfar : ∀ y ∈ ball z (r / 8),
      ENNReal.ofReal (|b| / 10) ≤ ‖radialCoefficient α b y i i - a‖ₑ := fun y hy => by
    have heq : radialCoefficient α b y i i - a = b * (y i ^ 2 / ‖y‖ ^ 2 - (a - α) / b) := by
      rw [mul_sub, mul_div_cancel₀ _ hb]
      simp only [radialCoefficient_apply_apply, ↓reduceIte]
      ring
    rw [Real.eNorm_eq_ofReal_abs, heq, abs_mul]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hz y hy, abs_nonneg b])
  have hlow := mul_ofReal_div_pow_le_setLAverage_ball (μ := volume)
    (by positivity : (0 : ℝ) < r / 8) hsub hfar
  rw [← ENNReal.ofReal_mul (by positivity), show r / 8 / r = 1 / 8 by field_simp] at hlow
  exact (ENNReal.half_lt_self hδ ENNReal.ofReal_ne_top).not_ge
    (hlow.trans ((setLAverage_enorm_sub_setAverage_le_vmoModulus _ volume 0 le_rfl).trans hle))

/-! ### The norm power as a strong solution -/

/-- The double sum of the radial coefficient against a matrix of the form
`A δᵢⱼ + B xᵢ xⱼ`. -/
private theorem sum_radialCoefficient_mul (x : EuclideanSpace ℝ (Fin n)) (A B : ℝ) :
    ∑ i, ∑ j, radialCoefficient 1 b x i j * (A * (if i = j then 1 else 0) + B * (x i * x j)) =
      n * A + (B + b / ‖x‖ ^ 2 * A) * ‖x‖ ^ 2 + b / ‖x‖ ^ 2 * B * (‖x‖ ^ 2) ^ 2 := by
  have hsq : ∑ i, x i * x i = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm
  simp only [radialCoefficient_apply_apply, add_mul, mul_add, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ i, b / ‖x‖ ^ 2 * (x i * x i) * A = b / ‖x‖ ^ 2 * A * ‖x‖ ^ 2 := by
    rw [← hsq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, B * (x i * x i) = B * ‖x‖ ^ 2 := by rw [← hsq, Finset.mul_sum]
  have h3 : ∑ i, ∑ j, b / ‖x‖ ^ 2 * (x i * x j) * (B * (x i * x j)) =
      b / ‖x‖ ^ 2 * B * (‖x‖ ^ 2) ^ 2 := by
    rw [← hsq, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, h3]
  ring

/-- **The non-divergence operator of the radial coefficient on a norm power.** Let `γ > 2 - n`
and let `W ∈ W^{2,p}(Ω)` be equal to `‖x‖ ^ γ`. Then, with its weak Hessian `D²W`,

`∑ᵢⱼ aᵢⱼ(x) ⟪D²W eᵢ, eⱼ⟫ = γ (n + γ - 2 + b (γ - 1)) ‖x‖ ^ (γ - 2)`

almost everywhere on `Ω`, for the radial coefficient `a = TauCeti.PDE.radialCoefficient 1 b`. -/
theorem ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq (hγ : 2 - (n : ℝ) < γ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (W : Wkp volume Ω p 2)
    (hW : Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
      fun x => ‖x‖ ^ γ) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))),
      ∑ i, ∑ j, radialCoefficient 1 b x i j *
        ⟪Wkp.iteratedGradient 1 W x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        γ * (n + γ - 2 + b * (γ - 1)) * ‖x‖ ^ (γ - 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- In dimension zero both sides vanish, since `γ > 2`.
    refine Eventually.of_forall fun x => ?_
    have hγ2 : γ - 2 ≠ 0 := by
      simp only [CharP.cast_eq_zero, sub_zero] at hγ
      linarith
    simp [Subsingleton.elim x 0, Real.zero_rpow hγ2]
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  have hH := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_norm_rpow
    (by simpa only [finrank_euclideanSpace_fin] using hγ) W hW
  filter_upwards [hH, ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin n)))]
    with x hx hx0
  have : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx0)
  have h42 : ‖x‖ ^ (γ - 4) * ‖x‖ ^ 2 = ‖x‖ ^ (γ - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.2 hx0)]
    congr 1
    ring
  -- The entries of `w ↦ A w + B ⟪x, w⟫ x` are `A δᵢⱼ + B xᵢ xⱼ`.
  have hentry : ∀ (A B : ℝ) (i j : Fin n),
      ⟪(A • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + B • (innerSL ℝ x).smulRight x)
        (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        A * (if i = j then 1 else 0) + B * (x i * x j) := by
    intro A B i j
    by_cases h : i = j
    · subst h
      simp [inner_add_left, EuclideanSpace.inner_single_right]
    · simp [inner_add_left, EuclideanSpace.inner_single_right, h, Ne.symm h]
  rw [hx]
  calc _ = ∑ i, ∑ j, radialCoefficient 1 b x i j * (γ * ‖x‖ ^ (γ - 2) * (if i = j then 1 else 0) +
        γ * (γ - 2) * ‖x‖ ^ (γ - 4) * (x i * x j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [hentry]
    _ = _ := by
        rw [sum_radialCoefficient_mul, ← h42]
        field_simp
        ring

/-- For `1 ≤ p₀ < p < ∞` with `p₀ < n` and `n / 2 < p` there is `0 < γ < 1` with
`p₀ < n / (2 - γ) ≤ p`, stated as `(γ - 2) p₀ > -n ≥ (γ - 2) p`. -/
private theorem exists_exponent_lt_of_lt (hn : 2 ≤ n) {p₀ p : ℝ≥0∞} (hp : p ≠ ∞) (hp₀n : p₀ < n)
    (hpn : (n : ℝ≥0∞) / 2 < p) (hp₀p : p₀ < p) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ -(n : ℝ) < (γ - 2) * p₀.toReal ∧ (γ - 2) * p.toReal ≤ -n := by
  have hp₀top : p₀ ≠ ∞ := hp₀n.ne_top
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hP₀n : p₀.toReal < n := by
    simpa using (ENNReal.toReal_lt_toReal hp₀top (ENNReal.natCast_ne_top n)).2 hp₀n
  have hPn : (n : ℝ) / 2 < p.toReal := by
    simpa [ENNReal.toReal_div] using
      (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (ENNReal.natCast_ne_top n) two_ne_zero)
        hp).2 hpn
  have hP₀P : p₀.toReal < p.toReal := (ENNReal.toReal_lt_toReal hp₀top hp).2 hp₀p
  -- The critical exponent `t = n / (2 - γ)` lies strictly between `max p₀ (n / 2)` and
  -- `min p n`.
  have hlt : max p₀.toReal (n / 2) < min p.toReal n :=
    max_lt (lt_min hP₀P hP₀n) (lt_min hPn (by linarith))
  set t : ℝ := (max p₀.toReal (n / 2) + min p.toReal n) / 2
  have ht₁ : max p₀.toReal (n / 2) < t := by simp only [t]; linarith
  have ht₂ : t < min p.toReal n := by simp only [t]; linarith
  have htn : n / 2 < t := (le_max_right _ _).trans_lt ht₁
  have htp₀ : p₀.toReal < t := (le_max_left _ _).trans_lt ht₁
  have htp : t < p.toReal := ht₂.trans_le (min_le_left _ _)
  have htn' : t < n := ht₂.trans_le (min_le_right _ _)
  have ht0 : 0 < t := by linarith
  have hγt : ∀ q : ℝ, (2 - n / t - 2) * q = -(n * (q / t)) := fun q => by
    field_simp
    ring
  refine ⟨2 - n / t, ?_, ?_, ?_, ?_⟩
  · have : (n : ℝ) / t < 2 := by rw [div_lt_iff₀ ht0]; linarith
    linarith
  · have : 1 < (n : ℝ) / t := by rw [lt_div_iff₀ ht0]; linarith
    linarith
  · rw [hγt, neg_lt_neg_iff]
    have : p₀.toReal / t < 1 := (div_lt_one ht0).2 htp₀
    nlinarith
  · rw [hγt, neg_le_neg_iff]
    have : 1 ≤ p.toReal / t := (one_le_div ht0).2 htp.le
    nlinarith

/-- For `2 - n < γ < 1` and `b = (n + γ - 2) / (1 - γ)`, an element of `W^{2,p}` equal to
`‖x‖ ^ γ` solves `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere with its weak Hessian, for
`a = TauCeti.PDE.radialCoefficient 1 b`. -/
private theorem ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq_zero (hγ1 : γ < 1)
    (hγ : 2 - (n : ℝ) < γ) {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (W : Wkp volume Ω p 2)
    (hW : Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
      fun x => ‖x‖ ^ γ) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))),
      ∑ i, ∑ j, radialCoefficient 1 ((n + γ - 2) / (1 - γ)) x i j *
        ⟪Wkp.iteratedGradient 1 W x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        0 := by
  filter_upwards [ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq hγ W hW] with x hx
  rw [hx]
  have : (1 : ℝ) - γ ≠ 0 := by linarith
  field_simp
  ring

/-- **`W^{2,p}` regularity fails for discontinuous coefficients.** Let `n ≥ 2` and
`1 ≤ p₀ < p < ∞` with `p₀ < n` and `n / 2 < p`. Then there are `b > 0` and `0 < γ < 1` such that,
for the coefficient field `a = TauCeti.PDE.radialCoefficient 1 b`, uniformly elliptic with constants
`1` and `1 + b` (`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`) but discontinuous at the
origin (`TauCeti.PDE.not_exists_tendsto_radialCoefficient`), and for every bounded open
`Ω ⊆ ℝⁿ` containing the origin, the function `‖x‖ ^ γ` lies in `W^{2,p₀}(Ω)` and solves
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on `Ω` with its weak Hessian, but does not lie in
`W^{2,p}(Ω)`. -/
theorem exists_radialCoefficient_not_exists_wkp (hn : 2 ≤ n) {p₀ p : ℝ≥0∞} [Fact (1 ≤ p₀)]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp₀n : p₀ < n) (hpn : (n : ℝ≥0∞) / 2 < p) (hp₀p : p₀ < p) :
    ∃ b γ : ℝ, 0 < b ∧ 0 < γ ∧ γ < 1 ∧ ∀ {Ω : Opens (EuclideanSpace ℝ (Fin n))},
      Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin n))) →
      (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω →
      (∃ W : Wkp volume Ω p₀ 2,
        Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
          (fun x => ‖x‖ ^ γ) ∧
        ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))),
          ∑ i, ∑ j, radialCoefficient 1 b x i j * ⟪Wkp.iteratedGradient 1 W x
            (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0) ∧
      ¬ ∃ W : Wkp volume Ω p 2,
        Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
          fun x => ‖x‖ ^ γ := by
  have hp₀top : p₀ ≠ ∞ := hp₀n.ne_top
  obtain ⟨γ, hγ0, hγ1, hγp₀, hγp⟩ := exists_exponent_lt_of_lt hn hp hp₀n hpn hp₀p
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(n + γ - 2) / (1 - γ), γ, div_pos (by linarith) (by linarith), hγ0, hγ1,
    fun {Ω} hb h0 => ⟨?_, ?_⟩⟩
  · obtain ⟨W, hW⟩ := exists_wkp_two_value_ae_eq_norm_rpow (μ := volume) (s := γ) hb hp₀top
      (by rwa [finrank_euclideanSpace_fin])
    exact ⟨W, hW,
      ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq_zero hγ1 (by linarith) W hW⟩
  · rw [exists_wkp_two_value_ae_eq_norm_rpow_iff hb hp h0 hγ0.ne' (by
      rw [finrank_euclideanSpace_fin]
      linarith), finrank_euclideanSpace_fin, not_lt]
    exact hγp

/-- **The VMO hypothesis is load-bearing for `W^{2,p}` regularity.** Let `γ ≠ 0` with
`2 - n < γ < 1` (so `n ≥ 2`), and let `a = TauCeti.PDE.radialCoefficient 1 b` with
`b = (n + γ - 2) / (1 - γ) > 0`: a symmetric, measurable coefficient field, uniformly elliptic
with constants `1` and `1 + b` (`TauCeti.PDE.uniformlyEllipticOn_radialCoefficient`) and not in VMO
(`TauCeti.PDE.not_memVMO_radialCoefficient_apply_self`). On a bounded open set `Ω` containing the
origin and for `1 ≤ p < ∞`, the function `‖x‖ ^ γ` is a `W^{2,p}(Ω)` strong solution of
`aⁱʲ ∂ᵢ∂ⱼu = 0` exactly when `p < n / (2 - γ)`. For `0 < γ`, since `n / 2 < n / (2 - γ) < n`,
it is a continuous `W^{2,p}` solution for some `p > n / 2`, but not a `W^{2,n}` solution. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow_and_sum_radialCoefficient_eq_zero_iff
    (hγ0 : γ ≠ 0) (hγn : 2 - (n : ℝ) < γ) (hγ1 : γ < 1) {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin n))))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∃ W : Wkp volume Ω p 2,
      Wkp.value 2 W =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n)))]
        (fun x => ‖x‖ ^ γ) ∧
      ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin n))),
        ∑ i, ∑ j, radialCoefficient 1 ((n + γ - 2) / (1 - γ)) x i j *
          ⟪Wkp.iteratedGradient 1 W x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
            0) ↔
      p < ENNReal.ofReal (n / (2 - γ)) := by
  have key := exists_wkp_two_value_ae_eq_norm_rpow_iff (μ := volume) hb hp h0 hγ0
    (by rwa [finrank_euclideanSpace_fin])
  rw [finrank_euclideanSpace_fin] at key
  rw [ENNReal.lt_ofReal_iff_toReal_lt hp, lt_div_iff₀ (by linarith), ← neg_lt_neg_iff,
    show -(p.toReal * (2 - γ)) = (γ - 2) * p.toReal by ring, ← key]
  exact exists_congr fun W => and_iff_left_of_imp
    (ae_sum_radialCoefficient_mul_inner_iteratedGradient_eq_zero hγ1 hγn W)

end PDE

end TauCeti
