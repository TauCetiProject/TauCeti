/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The local maximum principle for non-divergence-form operators

Let the coefficient matrix `a` satisfy `λ ‖ξ‖² ≤ ξᵀ a ξ` and `|ηᵀ a ξ| ≤ Λ ‖η‖ ‖ξ‖` on the ball
`B = B(c, R) ⊆ ℝⁿ`, `n ≥ 1`, with `Λ ≤ κ λ`, and let `u` be continuous on `closedBall c R` and
`C²` in `B` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` there. The **local maximum principle** bounds the supremum
of `u` on the concentric half ball by an integral norm of `u⁺` and the `Lⁿ` norm of `f⁻`: for every
`p > 0` there is a constant `C`, depending only on `n`, `κ` and `p`, with

`u x ≤ C (R^(-n/p) ‖u⁺‖_{Lᵖ(B)} + R ‖f⁻‖_{Lⁿ(B)} / λ)` for `x ∈ B(c, R / 2)`

(`TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`). No regularity of `a` beyond the
pointwise bounds is used, and `a` need not be symmetric. The estimate is invariant under the
scaling `u ↦ u(c + R ·)` and under `a ↦ a / λ`, and it is quantitative in `u`, as it must be: no
bound by the data alone holds for the homogeneous equation. Together with the weak Harnack
inequality it gives the Harnack inequality and the interior Hölder estimate of Krylov and Safonov.

## The argument

This is the proof of Gilbarg–Trudinger, Theorem 9.20. Let `s = 1 - ‖· - c‖² / R²` and apply the
Aleksandrov–Bakelman–Pucci estimate on `B` to `v = η u`, where `η = s^(m + 2)` vanishes on the
sphere. At the points of the upper contact set of `v` where its gradient is smaller than
`M / diam B`, `M = max v`, the supporting affine functions are nonnegative on `B`
(`TauCeti.PDE.norm_mul_le_sub_of_forall_le_add_inner`), which bounds the gradient of `v` by
`v / (R - ‖· - c‖)`; that part of the contact set suffices for the Aleksandrov measure estimate
(`TauCeti.PDE.addHaar_ball_le_lintegral_inter_preimage_abs_det_hessianOperator`). Expanding
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼ(η u)` (`TauCeti.PDE.sum_mul_fderiv_fderiv_mul`) then gives, there,

`-∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ f⁻ + K Λ R⁻² s^m u ≤ f⁻ + K Λ R⁻² M^(m / (m + 2)) (u⁺)^(2 / (m + 2))`,

and the Aleksandrov–Bakelman–Pucci estimate yields
`M ≤ C (R ‖f⁻‖ₙ / λ + κ R⁻¹ M^(m / (m + 2)) ‖u⁺‖_q^(2 / (m + 2)))` with `q = 2 n / (m + 2)`. Young's
inequality absorbs the power of `M`, and `η ≥ (3 / 4)^(m + 2)` on `B(c, R / 2)` returns from `v` to
`u`. For a general exponent `p`, choose `m` with `q < p` and apply Hölder's inequality.

## Main declarations

* `TauCeti.PDE.exists_le_mul_rpow_mul_eLpNorm_posPart_add`: **the local maximum principle**.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7, Theorem 9.20.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open InnerProductSpace Matrix Metric MeasureTheory Set
open scoped ENNReal Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : E} {R : ℝ}

/-- **The cross term on the contact set.** Let `η` be the cutoff `(1 - ‖· - c‖² / R²)^(m + 2)` and
`s = 1 - ‖y - c‖² / R²` at `y ∈ B(c, R)`. If `u y ≥ 0` and the gradient of `v = η u` is controlled
by the distance to the sphere, `‖Dv(y)‖ (R - ‖y - c‖) ≤ v y`, then
`‖Dη(y)‖ ‖Du(y)‖ ≤ 4 (m + 2) (m + 3) R⁻² s^m u(y)`. -/
private theorem norm_fderiv_cutoff_mul_norm_fderiv_le {u : E → ℝ} {y : E} (m : ℕ)
    (hy : y ∈ ball c R) (hu : DifferentiableAt ℝ u y) (hu0 : 0 ≤ u y)
    (hgrad : ‖fderiv ℝ ((fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) * u) y‖ *
      (R - ‖y - c‖) ≤ (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ (m + 2) * u y) :
    ‖fderiv ℝ (fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) y‖ * ‖fderiv ℝ u y‖ ≤
      4 * (m + 2) * (m + 3) / R ^ 2 * (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ m * u y := by
  set η : E → ℝ := fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)
  set s := 1 - ‖y - c‖ ^ 2 / R ^ 2 with hs_def
  have hR : 0 < R := pos_of_mem_ball hy
  have hρ : ‖y - c‖ < R := mem_ball_iff_norm.1 hy
  obtain ⟨hs0, -⟩ := one_sub_norm_sq_sub_div_mem_Ioc hy
  have hηy : η y = s ^ (m + 2) := rfl
  -- `‖Dη‖ ≤ 2 (m + 2) s^(m + 1) / R`.
  have hDη : ‖fderiv ℝ η y‖ ≤ (m + 2) * s ^ (m + 1) * (2 / R) := by
    rw [norm_fderiv_one_sub_norm_sq_sub_div_pow c y R m hs0.le]
    have : 2 / R ^ 2 * ‖y - c‖ ≤ 2 / R := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hR]
      nlinarith [norm_nonneg (y - c)]
    calc (m + 2) * s ^ (m + 1) * (2 / R ^ 2) * ‖y - c‖
        = (m + 2) * s ^ (m + 1) * (2 / R ^ 2 * ‖y - c‖) := by ring
      _ ≤ (m + 2) * s ^ (m + 1) * (2 / R) := by gcongr
  -- `R - ‖y - c‖ ≥ R s / 2`, so `‖Dv‖ ≤ 2 s^(m + 1) u / R`.
  have hRs : R * s / 2 ≤ R - ‖y - c‖ := by
    have e : R * s / 2 = (R - ‖y - c‖) * ((R + ‖y - c‖) / (2 * R)) := by
      rw [hs_def]
      field_simp
      ring
    rw [e]
    refine mul_le_of_le_one_right (by linarith) ?_
    rw [div_le_one (by positivity)]
    linarith
  have hV : ‖fderiv ℝ (η * u) y‖ ≤ 2 * s ^ (m + 1) * u y / R := by
    rw [le_div_iff₀ hR]
    have h := (mul_le_mul_of_nonneg_left hRs (norm_nonneg (fderiv ℝ (η * u) y))).trans hgrad
    rw [pow_succ] at h
    have : ‖fderiv ℝ (η * u) y‖ * R * s ≤ 2 * s ^ (m + 1) * u y * s := by nlinarith
    exact le_of_mul_le_mul_right this hs0
  -- From `Dv = η Du + u Dη`, `s ‖Du‖ ≤ 2 (m + 3) u / R`.
  have hDu : s * ‖fderiv ℝ u y‖ ≤ 2 * (m + 3) * u y / R := by
    have hDv : fderiv ℝ (η * u) y = η y • fderiv ℝ u y + u y • fderiv ℝ η y :=
      fderiv_mul (((contDiff_one_sub_norm_sq_sub_div c R (k := 1)).pow _).differentiable
        one_ne_zero y) hu
    have htri : η y * ‖fderiv ℝ u y‖ ≤ ‖fderiv ℝ (η * u) y‖ + u y * ‖fderiv ℝ η y‖ := by
      have h := norm_sub_le (fderiv ℝ (η * u) y) (u y • fderiv ℝ η y)
      rw [hDv, add_sub_cancel_right, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg hu0] at h
      rw [hDv]
      exact h
    have h3 : s ^ (m + 1) * (s * ‖fderiv ℝ u y‖) ≤ s ^ (m + 1) * (2 * (m + 3) * u y / R) := by
      calc s ^ (m + 1) * (s * ‖fderiv ℝ u y‖) = η y * ‖fderiv ℝ u y‖ := by
            rw [hηy, pow_succ]; ring
        _ ≤ 2 * s ^ (m + 1) * u y / R + u y * ((m + 2) * s ^ (m + 1) * (2 / R)) :=
            htri.trans (add_le_add hV (mul_le_mul_of_nonneg_left hDη hu0))
        _ = s ^ (m + 1) * (2 * (m + 3) * u y / R) := by ring
    exact le_of_mul_le_mul_left h3 (by positivity)
  calc ‖fderiv ℝ η y‖ * ‖fderiv ℝ u y‖ ≤ (m + 2) * s ^ (m + 1) * (2 / R) * ‖fderiv ℝ u y‖ :=
        mul_le_mul_of_nonneg_right hDη (norm_nonneg _)
    _ = (m + 2) * s ^ m * (2 / R) * (s * ‖fderiv ℝ u y‖) := by ring
    _ ≤ (m + 2) * s ^ m * (2 / R) * (2 * (m + 3) * u y / R) := by gcongr
    _ = 4 * (m + 2) * (m + 3) / R ^ 2 * s ^ m * u y := by field_simp; ring

end Cutoff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The operator applied to the cutoff.** If the matrix `A` has nonnegative quadratic form, then
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ (1 - ‖· - c‖² / R²)^(m + 2) ≥ -(m + 2) s^(m + 1) (2 / R²) tr A` wherever
`s = 1 - ‖x - c‖² / R² ≥ 0`. -/
private theorem neg_le_sum_mul_fderiv_fderiv_cutoff {A : Matrix ι ι ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ A.toQuadraticForm' ξ) (c x : EuclideanSpace ℝ ι) (R : ℝ)
    (m : ℕ) (hs : 0 ≤ 1 - ‖x - c‖ ^ 2 / R ^ 2) :
    -((m + 2) * (1 - ‖x - c‖ ^ 2 / R ^ 2) ^ (m + 1) * (2 / R ^ 2) * A.trace) ≤
      ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y : EuclideanSpace ℝ ι ↦
        (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ (m + 2)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) := by
  have hδ (i : ι) : ∑ j, A i j * ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1⟫ =
      A i i := by
    simp [EuclideanSpace.inner_single_right, PiLp.single_apply]
  have hz (k : ι) : ⟪x - c, EuclideanSpace.single k (1 : ℝ)⟫ = (x - c) k := by
    simp [EuclideanSpace.inner_single_right]
  have h1 : ∑ i, ∑ j, A i j * ((m + 2) * (m + 1) * (1 - ‖x - c‖ ^ 2 / R ^ 2) ^ m *
      (2 / R ^ 2) ^ 2 * (x - c) i * (x - c) j) =
      (m + 2) * (m + 1) * (1 - ‖x - c‖ ^ 2 / R ^ 2) ^ m * (2 / R ^ 2) ^ 2 *
        A.toQuadraticForm' (x - c) := by
    simp only [toQuadraticForm'_apply, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [WithLp.ofLp_sub, Pi.sub_apply]
      ring
  have h2 : ∑ i, ∑ j, A i j * ((m + 2) * (1 - ‖x - c‖ ^ 2 / R ^ 2) ^ (m + 1) * (2 / R ^ 2) *
      ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1⟫) =
      (m + 2) * (1 - ‖x - c‖ ^ 2 / R ^ 2) ^ (m + 1) * (2 / R ^ 2) * A.trace := by
    simp only [trace, diag, Finset.mul_sum, ← hδ]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [fderiv_fderiv_one_sub_norm_sq_sub_div_pow_apply, hz, mul_sub, Finset.sum_sub_distrib,
    h1, h2]
  rw [neg_le_sub_iff_le_add, le_add_iff_nonneg_left]
  exact mul_nonneg (by positivity) (hA (x - c))

/-- **The equation for the localized function on the contact set.** Let `η` be the cutoff
`(1 - ‖· - c‖² / R²)^(m + 2)`, `s = 1 - ‖y - c‖² / R²` its base at `y ∈ B(c, R)`, and let
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` at `y` with `u y ≥ 0`. If the gradient of `v = η u` at `y` is controlled by the
distance to the sphere, `‖Dv(y)‖ (R - ‖y - c‖) ≤ v y`, then
`-∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv(y) ≤ f⁻(y) + 2 (m + 2) (4 m + 12 + n) Λ R⁻² s^m u(y)`. -/
private theorem neg_sum_mul_fderiv_fderiv_cutoff_mul_le {lam Lam R : ℝ}
    {c y : EuclideanSpace ℝ ι} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {u f : EuclideanSpace ℝ ι → ℝ} (m : ℕ) (ha : UniformlyEllipticOn (ball c R) a lam Lam)
    (hy : y ∈ ball c R) (hu : ContDiffAt ℝ 2 u y)
    (hf : f y ≤ ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1))
    (hu0 : 0 ≤ u y)
    (hgrad : ‖fderiv ℝ ((fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) * u) y‖ *
      (R - ‖y - c‖) ≤ (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ (m + 2) * u y) :
    -∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ ((fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) * u))
        y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤
      (f y)⁻ + 2 * (m + 2) * (4 * m + 12 + Fintype.card ι) * Lam / R ^ 2 *
        (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ m * u y := by
  set η : EuclideanSpace ℝ ι → ℝ := fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)
  set s := 1 - ‖y - c‖ ^ 2 / R ^ 2
  set n : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨hs0, hs1⟩ := one_sub_norm_sq_sub_div_mem_Ioc hy
  have hLam := ha.upper_nonneg
  have hη : ContDiffAt ℝ 2 η y := ((contDiff_one_sub_norm_sq_sub_div c R).pow _).contDiffAt
  -- The three terms of the expansion of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼ(η u)`.
  rw [sum_mul_fderiv_fderiv_mul (a y) hη hu]
  set T₁ := ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)
  set T₂ := ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ η) y (EuclideanSpace.single i 1)
    (EuclideanSpace.single j 1)
  set A₁ := ∑ i, ∑ j, a y i j * (fderiv ℝ η y (EuclideanSpace.single i 1) *
    fderiv ℝ u y (EuclideanSpace.single j 1))
  set A₂ := ∑ i, ∑ j, a y i j * (fderiv ℝ u y (EuclideanSpace.single i 1) *
    fderiv ℝ η y (EuclideanSpace.single j 1))
  have hsplit : ∑ i, ∑ j, a y i j * (fderiv ℝ η y (EuclideanSpace.single i 1) *
      fderiv ℝ u y (EuclideanSpace.single j 1) + fderiv ℝ u y (EuclideanSpace.single i 1) *
        fderiv ℝ η y (EuclideanSpace.single j 1)) = A₁ + A₂ := by
    simp only [A₁, A₂, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  -- The principal term: `η ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ η f ≥ -f⁻`, since `0 ≤ η ≤ 1`.
  have h₁ : -(f y)⁻ ≤ η y * T₁ := by
    have hη0 : 0 ≤ η y := by positivity
    have hη1 : η y ≤ 1 := pow_le_one₀ hs0.le hs1
    have := neg_le_negPart (f y)
    nlinarith [negPart_nonneg (f y)]
  -- The cutoff term: `u ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼη ≥ -(m + 2) s^(m + 1) (2 / R²) (tr a) u`, which is at least
  -- `-2 (m + 2) n Λ R⁻² s^m u`.
  have h₂ : -(2 * (m + 2) * n * Lam / R ^ 2 * s ^ m * u y) ≤ u y * T₂ := by
    have hT₂ := neg_le_sum_mul_fderiv_fderiv_cutoff (ha.quadraticForm_nonneg hy) c y R m hs0.le
    have htr0 : 0 ≤ (a y).trace := Finset.sum_nonneg fun i _ => by
      simpa [toQuadraticForm'_apply] using ha.quadraticForm_nonneg hy (EuclideanSpace.single i 1)
    have htr := ha.trace_le hy
    have hsm : s ^ (m + 1) ≤ s ^ m := pow_le_pow_of_le_one hs0.le hs1 (Nat.le_succ m)
    have hkey : -(2 * (m + 2) * n * Lam / R ^ 2 * s ^ m) ≤ T₂ := by
      refine le_trans ?_ hT₂
      rw [neg_le_neg_iff]
      calc (m + 2) * s ^ (m + 1) * (2 / R ^ 2) * (a y).trace
          ≤ (m + 2) * s ^ m * (2 / R ^ 2) * (n * Lam) := by gcongr
        _ = 2 * (m + 2) * n * Lam / R ^ 2 * s ^ m := by ring
    nlinarith
  -- The cross terms: `|Aₖ| ≤ Λ ‖Dη‖ ‖Du‖ ≤ 4 (m + 2) (m + 3) Λ R⁻² s^m u`.
  have hc := mul_le_mul_of_nonneg_left (norm_fderiv_cutoff_mul_norm_fderiv_le m hy
    (hu.differentiableAt two_ne_zero) hu0 hgrad) hLam
  have e1 := abs_sum_mul_apply_single_mul_apply_single_le (ha.upper_bound hy)
    (fderiv ℝ η y) (fderiv ℝ u y)
  have e2 := abs_sum_mul_apply_single_mul_apply_single_le (ha.upper_bound hy)
    (fderiv ℝ u y) (fderiv ℝ η y)
  have e3 : Lam * ‖fderiv ℝ u y‖ * ‖fderiv ℝ η y‖ = Lam * (‖fderiv ℝ η y‖ * ‖fderiv ℝ u y‖) := by
    ring
  rw [mul_assoc] at e1
  have : 2 * (m + 2) * (4 * m + 12 + n) * Lam / R ^ 2 * s ^ m * u y =
      2 * (m + 2) * n * Lam / R ^ 2 * s ^ m * u y +
        2 * (Lam * (4 * (m + 2) * (m + 3) / R ^ 2 * s ^ m * u y)) := by ring
  linarith [neg_abs_le A₁, neg_abs_le A₂]

/-- **The determinant bound on the contact set.** Let `u` be `C²` in `B = B(c, R)` with
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` there, and let `v = (1 - ‖· - c‖² / R²)^(m + 2) u` be at most
`M = v x₀` on `B`. At a point `y` of the upper contact set of `v` on `B` where
`‖∇v(y)‖ diam B ≤ M`, with `θ = m / (m + 2)`, `q = 2 / (m + 2)` and
`K = 2 (m + 2) (4 m + 12 + n)`,
`|det D²v(y)| ≤ ((f⁻(y) + K Λ R⁻² M^θ u⁺(y)^q) / n)ⁿ / λⁿ`. -/
private theorem abs_det_hessianOperator_cutoff_mul_le {lam Lam R M : ℝ}
    {c x₀ y : EuclideanSpace ℝ ι} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {u f : EuclideanSpace ℝ ι → ℝ} (m : ℕ) (ha : UniformlyEllipticOn (ball c R) a lam Lam)
    (hu : ContDiffOn ℝ 2 u (ball c R))
    (hsub : ∀ x ∈ ball c R, f x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hx₀ : x₀ ∈ ball c R) (hmax : ∀ y ∈ ball c R, (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ (m + 2) * u y ≤ M)
    (hM : (1 - ‖x₀ - c‖ ^ 2 / R ^ 2) ^ (m + 2) * u x₀ = M)
    (hy : y ∈ upperContactSet ((fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) * u) (ball c R))
    (hyM : ‖∇ ((fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) * u) y‖ * diam (ball c R) ≤ M) :
    |(hessianOperator ((fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)) * u) y).det| ≤
      (((f y)⁻ + 2 * (m + 2) * (4 * m + 12 + Fintype.card ι) * Lam / R ^ 2 *
        M ^ ((m : ℝ) / (m + 2)) * (u y)⁺ ^ ((2 : ℝ) / (m + 2))) / Fintype.card ι) ^
          Fintype.card ι / lam ^ Fintype.card ι := by
  set N := Fintype.card ι
  set η : EuclideanSpace ℝ ι → ℝ := fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)
  set v := η * u
  set G := (f y)⁻ + 2 * (m + 2) * (4 * m + 12 + (N : ℝ)) * Lam / R ^ 2 *
    M ^ ((m : ℝ) / (m + 2)) * (u y)⁺ ^ ((2 : ℝ) / (m + 2))
  have hyB : y ∈ ball c R := upperContactSet_subset hy
  have hlam := ha.pos
  have hLam := ha.upper_nonneg
  have hv2 : ContDiffOn ℝ 2 v (ball c R) :=
    ((contDiff_one_sub_norm_sq_sub_div c R).pow _).contDiffOn.mul hu
  -- The gradient of `v` at `y` is controlled by the distance to the sphere.
  have hgrad : ‖∇ v y‖ * (R - ‖y - c‖) ≤ v y - 0 := by
    refine norm_mul_le_sub_of_forall_le_add_inner isBounded_ball hx₀
      ((mem_upperContactSet_iff_gradient isOpen_ball (hv2.differentiableOn two_ne_zero)).1 hy).2
      (by rw [sub_zero]; exact hyM.trans_eq hM.symm) (sub_pos.2 (mem_ball_iff_norm.1 hyB))
      (ball_subset_ball' ?_)
    rw [dist_eq_norm]
    linarith
  rw [sub_zero, norm_gradient_eq_norm_fderiv] at hgrad
  obtain ⟨hs0, -⟩ := one_sub_norm_sq_sub_div_mem_Ioc hyB
  have hu0 : 0 ≤ u y := by
    have hv0 : 0 ≤ v y := (mul_nonneg (norm_nonneg _) (by
      linarith [mem_ball_iff_norm.1 hyB] : (0 : ℝ) ≤ R - ‖y - c‖)).trans hgrad
    exact nonneg_of_mul_nonneg_right hv0 (by positivity)
  -- So `-∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ G` at `y`.
  have hLG : -∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ v) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) ≤ G := by
    refine (neg_sum_mul_fderiv_fderiv_cutoff_mul_le m ha hyB
      (hu.contDiffAt (isOpen_ball.mem_nhds hyB)) (hsub y hyB) hu0 hgrad).trans ?_
    have hpow := Real.pow_mul_le_rpow_mul_rpow (b := 2) two_pos hs0.le hu0 (hmax y hyB)
    push_cast at hpow
    calc (f y)⁻ + 2 * (m + 2) * (4 * m + 12 + (N : ℝ)) * Lam / R ^ 2 *
          (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ m * u y
        = (f y)⁻ + 2 * (m + 2) * (4 * m + 12 + (N : ℝ)) * Lam / R ^ 2 *
          ((1 - ‖y - c‖ ^ 2 / R ^ 2) ^ m * u y) := by ring
      _ ≤ (f y)⁻ + 2 * (m + 2) * (4 * m + 12 + (N : ℝ)) * Lam / R ^ 2 *
          (M ^ ((m : ℝ) / (m + 2)) * u y ^ ((2 : ℝ) / (m + 2))) := by gcongr
      _ = G := by simp only [G, posPart_eq_self.2 hu0]; ring
  -- On the contact set, `|det D²v| det A ≤ (-∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼv / n)ⁿ` for the symmetric part `A`.
  have haS := ha.coefficientSymmetricPart
  have hsymm := coefficientSymmetricPart_isSymm (a y)
  have hdet := abs_det_hessianOperator_mul_det_le_of_mem_upperContactSet isOpen_ball hv2 hy
    (haS.posDef hyB hsymm).posSemidef
  rw [sum_coefficientSymmetricPart_mul_fderiv_fderiv (hv2.contDiffAt
    (isOpen_ball.mem_nhds hyB))] at hdet
  have hnonpos := sum_mul_fderiv_fderiv_nonpos_of_mem_upperContactSet isOpen_ball hv2 hy
    (ha.quadraticForm_nonneg hyB)
  rw [le_div_iff₀ (by positivity)]
  calc |(hessianOperator v y).det| * lam ^ N
      ≤ |(hessianOperator v y).det| * (coefficientSymmetricPart (a y)).det :=
        mul_le_mul_of_nonneg_left (haS.pow_card_le_det hyB hsymm) (abs_nonneg _)
    _ ≤ _ := hdet
    _ ≤ (G / N) ^ N := by
        gcongr
        exact div_nonneg (neg_nonneg.2 hnonpos) (Nat.cast_nonneg _)

variable [Nonempty ι]

/-- **The Aleksandrov–Bakelman–Pucci step for the localized function.** Let `u` be continuous on
`closedBall c R`, `C²` in `B = B(c, R)`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` there, and let
`v = (1 - ‖· - c‖² / R²)^(m + 2) u` be at most `M = v x₀ > 0` on `B`. With `θ = m / (m + 2)` and
`q = 2 n / (m + 2)`,
`M ≤ 2 R / (n ωₙ^(1/n) λ) (‖f⁻‖_{Lⁿ(B)} + K Λ R⁻² M^θ ‖u⁺‖_{L^q(B)}^(1 - θ))`,
`K = 2 (m + 2) (4 m + 12 + n)`. -/
private theorem le_mul_add_of_cutoff_mul_le {lam Lam R M : ℝ} {c x₀ : EuclideanSpace ℝ ι}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u f : EuclideanSpace ℝ ι → ℝ} (m : ℕ)
    (ha : UniformlyEllipticOn (ball c R) a lam Lam) (hcont : ContinuousOn u (closedBall c R))
    (hu : ContDiffOn ℝ 2 u (ball c R))
    (hsub : ∀ x ∈ ball c R, f x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hf : MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (volume.restrict (ball c R)))
    (hx₀ : x₀ ∈ ball c R) (hmax : ∀ y ∈ ball c R, (1 - ‖y - c‖ ^ 2 / R ^ 2) ^ (m + 2) * u y ≤ M)
    (hM : (1 - ‖x₀ - c‖ ^ 2 / R ^ 2) ^ (m + 2) * u x₀ = M) (hM0 : 0 ≤ M) :
    M ≤ 2 * R / (Fintype.card ι * (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^
        (Fintype.card ι : ℝ)⁻¹) / lam *
      ((eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (volume.restrict (ball c R))).toReal +
        2 * (m + 2) * (4 * m + 12 + Fintype.card ι) * Lam / R ^ 2 * M ^ ((m : ℝ) / (m + 2)) *
          (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal (2 * Fintype.card ι / (m + 2)))
            (volume.restrict (ball c R))).toReal ^ ((2 : ℝ) / (m + 2))) := by
  set N := Fintype.card ι
  set n : ℝ := (N : ℝ)
  set η : EuclideanSpace ℝ ι → ℝ := fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)
  set v := η * u
  set B := ball c R
  set q : ℝ := (2 : ℝ) / (m + 2)
  set K' : ℝ := 2 * (m + 2) * (4 * m + 12 + n) * Lam / R ^ 2 * M ^ ((m : ℝ) / (m + 2))
  have hq : 0 < q := by positivity
  have hR : 0 < R := pos_of_mem_ball hx₀
  have hlam := ha.pos
  have hK' : 0 ≤ K' := by have := ha.upper_nonneg; positivity
  have hηc : ContDiff ℝ 2 η := (contDiff_one_sub_norm_sq_sub_div c R).pow _
  have hvcont : ContinuousOn v (closure B) := by
    rw [closure_ball c hR.ne']
    exact hηc.continuous.continuousOn.mul hcont
  have hv2 : ContDiffOn ℝ 2 v B := hηc.contDiffOn.mul hu
  have hfront : ∀ z ∈ frontier B, v z ≤ 0 := by
    intro z hz
    rw [frontier_ball c hR.ne', mem_sphere_iff_norm] at hz
    simp [v, η, hz, hR.ne']
  have hdiam : diam B = 2 * R := Metric.diam_ball_eq c hR.le
  -- The Aleksandrov–Bakelman–Pucci estimate, on the part `Γ` of the upper contact set where
  -- `‖∇v‖ < M / diam B`, with `λ I` in place of the coefficients and `G = f⁻ + K' (u⁺)^q`.
  set G : EuclideanSpace ℝ ι → ℝ := fun y ↦ (f y)⁻ + K' * (u y)⁺ ^ q
  have hG0 (y : EuclideanSpace ℝ ι) : 0 ≤ G y := by positivity
  set Γ := upperContactSet v B ∩ ∇ v ⁻¹' ball 0 ((v x₀ - 0) / diam B)
  have hΓB : Γ ⊆ B := inter_subset_left.trans upperContactSet_subset
  have hΓm : MeasurableSet Γ :=
    (measurableSet_upperContactSet isOpen_ball (hv2.of_le (by norm_num))).inter
      (measurable_gradient v measurableSet_ball)
  have hpt (y : EuclideanSpace ℝ ι) (hy : y ∈ Γ) : ENNReal.ofReal |(hessianOperator v y).det| ≤
      ENNReal.ofReal (((-G y)⁻ / N) ^ N / (lam • (1 : Matrix ι ι ℝ)).det) := by
    have hyM : ‖∇ v y‖ * diam B ≤ M := by
      have h : ‖∇ v y‖ < (v x₀ - 0) / diam B := mem_ball_zero_iff.1 hy.2
      rw [lt_div_iff₀ (by rw [hdiam]; positivity), sub_zero] at h
      exact hM ▸ h.le
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Matrix.det_smul, det_one, mul_one, negPart_neg, posPart_eq_self.2 (hG0 y)]
    exact abs_det_hessianOperator_cutoff_mul_le m ha hu hsub hx₀ hmax hM hy.1 hyM
  have hkey : volume (ball (0 : EuclideanSpace ℝ ι) ((v x₀ - 0) / diam B)) ≤
      ∫⁻ y in B, ENNReal.ofReal (((-G y)⁻ / N) ^ N / (lam • (1 : Matrix ι ι ℝ)).det) :=
    (addHaar_ball_le_lintegral_inter_preimage_abs_det_hessianOperator volume isBounded_ball
      isOpen_ball hvcont hv2 hfront hx₀ le_rfl).trans
      ((setLIntegral_mono' hΓm hpt).trans (lintegral_mono_set hΓB))
  -- `G ∈ Lⁿ(B)`: `u⁺` and `(u⁺)^q` are continuous on the compact `closedBall c R ⊇ B`.
  have hposc : ContinuousOn (fun y ↦ (u y)⁺) (closedBall c R) :=
    continuous_posPart.comp_continuousOn hcont
  have hupos : AEStronglyMeasurable (fun y ↦ (u y)⁺) (volume.restrict B) :=
    (hposc.memLp_restrict_of_subset_isCompact (isCompact_closedBall c R) measurableSet_ball
      ball_subset_closedBall ⊤).aestronglyMeasurable
  have hupq : MemLp (fun y ↦ (u y)⁺ ^ q) N (volume.restrict B) :=
    (hposc.rpow_const fun _ _ ↦ Or.inr hq.le).memLp_restrict_of_subset_isCompact
      (isCompact_closedBall c R) measurableSet_ball ball_subset_closedBall N
  have hfun : (fun y ↦ (-G y)⁻ / (lam • (1 : Matrix ι ι ℝ)).det ^ (N : ℝ)⁻¹) =
      fun y ↦ lam⁻¹ * G y := by
    funext y
    rw [Matrix.det_smul, det_one, mul_one, negPart_neg, posPart_eq_self.2 (hG0 y),
      Real.pow_rpow_inv_natCast hlam.le Fintype.card_ne_zero, div_eq_inv_mul]
  have habp := le_add_mul_eLpNorm_negPart_div_det_rpow_of_volume_ball_le isBounded_ball
    isOpen_ball hx₀ (Γ := B) (a := fun _ ↦ lam • (1 : Matrix ι ι ℝ)) (f := fun y ↦ -G y)
    (ae_of_all _ fun _ ↦ PosDef.one.smul hlam)
    (by rw [hfun]; exact (hf.add (hupq.const_mul K')).const_mul _) hkey
  have hvx₀ : v x₀ = M := hM
  rw [hfun, hvx₀, zero_add, hdiam] at habp
  -- The `Lⁿ` norm of `G / λ`, by Minkowski's inequality and `‖(u⁺)^q‖ₙ = ‖u⁺‖_{n q}^q`.
  have hq' : (N : ℝ≥0∞) * ENNReal.ofReal q = ENNReal.ofReal (2 * n / (m + 2)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    simp only [q, n]
    ring
  have hGfun : (fun y ↦ lam⁻¹ * G y) =
      lam⁻¹ • ((fun y ↦ (f y)⁻) + fun y ↦ K' * (u y)⁺ ^ q) := by
    funext y
    simp only [G, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hKu : (fun y ↦ K' * (u y)⁺ ^ q) = K' • fun y ↦ ‖(u y)⁺‖ ^ q := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (posPart_nonneg _)]
  have hfin := (hupq.const_mul K').eLpNorm_ne_top
  have hadd := eLpNorm_add_le (μ := volume.restrict B) (f := fun y ↦ (f y)⁻)
    (g := fun y ↦ K' * (u y)⁺ ^ q)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero : (1 : ℝ≥0∞) ≤ N)
  have hnorm : (eLpNorm (fun y ↦ lam⁻¹ * G y) N (volume.restrict B)).toReal ≤
      lam⁻¹ * ((eLpNorm (fun y ↦ (f y)⁻) N (volume.restrict B)).toReal +
        K' * (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal (2 * n / (m + 2)))
          (volume.restrict B)).toReal ^ q) := by
    rw [hGfun, eLpNorm_const_smul, ENNReal.toReal_mul, toReal_eNorm,
      Real.norm_of_nonneg (inv_nonneg.2 hlam.le), ← hq']
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hlam.le)
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hfin⟩) hadd).trans_eq ?_
    rw [ENNReal.toReal_add hf.eLpNorm_ne_top hfin, hKu, eLpNorm_const_smul, ENNReal.toReal_mul,
      toReal_eNorm, Real.norm_of_nonneg hK', eLpNorm_norm_rpow _ hupos hq, ENNReal.toReal_rpow]
  calc M ≤ 2 * R / (n * (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (n : ℝ)⁻¹) *
        (eLpNorm (fun y ↦ lam⁻¹ * G y) N (volume.restrict B)).toReal := habp
    _ ≤ _ := by
        rw [div_eq_mul_inv _ lam, mul_assoc]
        gcongr

/-- **The local maximum principle at the exponents `q = 2 n / (m + 2)`.** With
`C₀ = 2 / (n ωₙ^(1/n))` and `K = 2 (m + 2) (4 m + 12 + n)`, for `x ∈ B(c, R / 2)`,
`u x ≤ (4 / 3)^(m + 2) ((m + 2) / 2 C₀ R ‖f⁻‖_{Lⁿ(B)} / λ +
(C₀ K κ)^((m + 2) / 2) R^(-(m + 2) / 2) ‖u⁺‖_{L^q(B)})`. -/
private theorem le_mul_add_mul_of_two_mul_card_div {κ lam Lam R : ℝ}
    {c x : EuclideanSpace ℝ ι} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {u f : EuclideanSpace ℝ ι → ℝ} (m : ℕ) (ha : UniformlyEllipticOn (ball c R) a lam Lam)
    (hLam : Lam ≤ κ * lam) (hcont : ContinuousOn u (closedBall c R))
    (hu : ContDiffOn ℝ 2 u (ball c R))
    (hsub : ∀ x ∈ ball c R, f x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hf : MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (volume.restrict (ball c R)))
    (hx : x ∈ ball c (R / 2)) :
    u x ≤ (4 / 3) ^ (m + 2) * ((m + 2) / 2 * (2 / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹)) *
          (R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι)
            (volume.restrict (ball c R))).toReal) +
        (2 / (Fintype.card ι * (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^
          (Fintype.card ι : ℝ)⁻¹) * (2 * (m + 2) * (4 * m + 12 + Fintype.card ι)) * κ) ^
            (((m : ℝ) + 2) / 2) *
          (R ^ (-(((m : ℝ) + 2) / 2)) * (eLpNorm (fun y ↦ (u y)⁺)
            (ENNReal.ofReal (2 * Fintype.card ι / (m + 2)))
              (volume.restrict (ball c R))).toReal)) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  set C₀ := 2 / (n * ω ^ n⁻¹)
  set K : ℝ := 2 * (m + 2) * (4 * m + 12 + n)
  set F := (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (volume.restrict (ball c R))).toReal
  set Nq := (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal (2 * n / (m + 2)))
    (volume.restrict (ball c R))).toReal
  set η : EuclideanSpace ℝ ι → ℝ := fun z ↦ (1 - ‖z - c‖ ^ 2 / R ^ 2) ^ (m + 2)
  have hR : 0 < R := by linarith [pos_of_mem_ball hx]
  have hlam := ha.pos
  have hκ : 0 < κ := by
    by_contra h
    nlinarith [ha.le]
  have hNq : 0 ≤ Nq := ENNReal.toReal_nonneg
  have hvc : ContinuousOn (fun y ↦ η y * u y) (closedBall c R) :=
    ((contDiff_one_sub_norm_sq_sub_div c R (k := 0)).pow _).continuous.continuousOn.mul hcont
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_closedBall c R).exists_isMaxOn (nonempty_closedBall.2 hR.le) hvc
  set M := η x₀ * u x₀
  have hvx : η x * u x ≤ M := hmax (ball_subset_closedBall (ball_subset_ball (by linarith) hx))
  -- On `B(c, R / 2)` the cutoff is at least `(3 / 4)^(m + 2)`.
  have hηx : (3 / 4 : ℝ) ^ (m + 2) ≤ η x := by
    refine pow_le_pow_left₀ (by norm_num) ?_ _
    have hxc : ‖x - c‖ < R / 2 := mem_ball_iff_norm.1 hx
    have : ‖x - c‖ ^ 2 / R ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg (x - c)]
    linarith
  have hη0 : 0 < η x := (by positivity : (0 : ℝ) < (3 / 4) ^ (m + 2)).trans_le hηx
  rcases le_or_gt M 0 with hM | hM
  · -- If `v ≤ 0`, then `u ≤ 0` on `B(c, R / 2)`.
    have hux : u x ≤ 0 := nonpos_of_mul_nonpos_right (hvx.trans hM) hη0
    exact hux.trans (by positivity)
  -- Otherwise `v` attains its positive maximum `M` inside the ball.
  have hx₀b : x₀ ∈ ball c R := by
    refine mem_ball_iff_norm.2 (lt_of_le_of_ne (mem_closedBall_iff_norm.1 hx₀) fun h => ?_)
    simp [M, η, h, hR.ne'] at hM
  have habp := le_mul_add_of_cutoff_mul_le m ha hcont hu hsub hf hx₀b
    (fun y hy => hmax (ball_subset_closedBall hy)) rfl hM.le
  have hθ : (2 : ℝ) / (m + 2) = 1 - m / (m + 2) := by field_simp; ring
  rw [hθ] at habp
  have hcoef : 2 * R / (n * ω ^ n⁻¹) / lam * (K * Lam / R ^ 2) ≤ C₀ * K * κ / R :=
    calc 2 * R / (n * ω ^ n⁻¹) / lam * (K * Lam / R ^ 2) = C₀ * K / R * (Lam / lam) := by
          simp only [C₀]; field_simp
      _ ≤ C₀ * K / R * κ := by
          gcongr
          rw [div_le_iff₀ hlam]
          exact hLam
      _ = C₀ * K * κ / R := by ring
  have hstep : M ≤ C₀ * R / lam * F + C₀ * K * κ / R * M ^ ((m : ℝ) / (m + 2)) *
      Nq ^ (1 - (m : ℝ) / (m + 2)) :=
    calc M ≤ _ := habp
      _ = C₀ * R / lam * F + 2 * R / (n * ω ^ n⁻¹) / lam * (K * Lam / R ^ 2) *
          M ^ ((m : ℝ) / (m + 2)) * Nq ^ (1 - (m : ℝ) / (m + 2)) := by simp only [C₀]; ring
      _ ≤ _ := by gcongr
  have habs := Real.le_div_add_rpow_mul_of_le_add_mul_rpow_mul_rpow (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith) hM.le (by positivity) hNq hstep
  have he : 1 / (1 - (m : ℝ) / (m + 2)) = ((m : ℝ) + 2) / 2 := by field_simp; ring
  rw [he, div_eq_mul_one_div (C₀ * R / lam * F), he, Real.div_rpow (by positivity) hR.le] at habs
  -- Back from `v = η u` to `u` on `B(c, R / 2)`.
  have hux : u x ≤ (4 / 3) ^ (m + 2) * M := by
    rcases le_or_gt (u x) 0 with h | h
    · exact h.trans (by positivity)
    have h1 : (3 / 4 : ℝ) ^ (m + 2) * u x ≤ M := (mul_le_mul_of_nonneg_right hηx h.le).trans hvx
    have h2 : (4 / 3 : ℝ) ^ (m + 2) * (3 / 4) ^ (m + 2) = 1 := by
      rw [← mul_pow]
      norm_num
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4 / 3) (m + 2)]
  refine hux.trans (mul_le_mul_of_nonneg_left (habs.trans_eq ?_) (by positivity))
  rw [Real.rpow_neg hR.le]
  ring

/-- **The local maximum principle** (Gilbarg–Trudinger, Theorem 9.20, for classical
subsolutions without lower-order terms). Let `p > 0` and `κ` be given. There is a constant `C`,
depending only on the dimension `n`, on `κ` and on `p`, with the following property. Let the
coefficient matrix `a` be uniformly elliptic on `B = B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let
`u` be continuous on `closedBall c R` and `C²` in `B`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` in `B` and
`f⁻ ∈ Lⁿ(B)`. Then for every `x ∈ B(c, R / 2)`,

`u x ≤ C (R^(-n/p) ‖u⁺‖_{Lᵖ(B)} + R ‖f⁻‖_{Lⁿ(B)} / λ)`. -/
theorem exists_le_mul_rpow_mul_eLpNorm_posPart_add {κ p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball c R) a lam Lam →
        Lam ≤ κ * lam → ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ ball c R, f x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
        MemLp (fun x ↦ (f x)⁻) (Fintype.card ι) (volume.restrict (ball c R)) →
        ∀ x ∈ ball c (R / 2), u x ≤ C * (R ^ (-(Fintype.card ι : ℝ) / p) *
          (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal +
          R / lam * (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι)
            (volume.restrict (ball c R))).toReal) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  -- Work at the exponent `q = 2 n / (m + 2) < p`, then compare with `p` by Hölder's inequality.
  set m := ⌈2 * n / p⌉₊
  set q : ℝ := 2 * n / (m + 2)
  have hq : 0 < q := by positivity
  have hqp : q < p := by
    rw [div_lt_iff₀ (by positivity)]
    have := Nat.le_ceil (2 * n / p)
    rw [div_le_iff₀ hp] at this
    nlinarith
  set C₀ := 2 / (n * ω ^ n⁻¹)
  set K : ℝ := 2 * (m + 2) * (4 * m + 12 + n)
  set e : ℝ := ((m : ℝ) + 2) / 2
  set D := (C₀ * K * max κ 0) ^ e * ω ^ (1 / q - 1 / p)
  refine ⟨(4 / 3) ^ (m + 2) * ((m + 2) / 2 * C₀ + D), by positivity, ?_⟩
  intro lam Lam R c a u f ha hLam hcont hu hsub hf x hx
  have hR : 0 < R := by linarith [pos_of_mem_ball hx]
  have hlam := ha.pos
  have hκ0 : 0 < κ := by
    by_contra h
    nlinarith [ha.le]
  have hκ : max κ 0 = κ := max_eq_left hκ0.le
  have hD : D = (C₀ * K * κ) ^ e * ω ^ (1 / q - 1 / p) := by simp only [D, hκ]
  set F := (eLpNorm (fun y ↦ (f y)⁻) (Fintype.card ι) (volume.restrict (ball c R))).toReal
  set Np := (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal
  set Nq := (eLpNorm (fun y ↦ (u y)⁺) (ENNReal.ofReal q) (volume.restrict (ball c R))).toReal
  have hcore : u x ≤ (4 / 3) ^ (m + 2) * ((m + 2) / 2 * C₀ * (R / lam * F) +
      (C₀ * K * κ) ^ e * (R ^ (-e) * Nq)) :=
    le_mul_add_mul_of_two_mul_card_div m ha hLam hcont hu hsub hf hx
  -- Hölder's inequality, with `e = n / q`.
  have he : e = n / q := by
    simp only [e, q]
    field_simp
  have hX : (C₀ * K * κ) ^ e * (R ^ (-e) * Nq) ≤ D * (R ^ (-n / p) * Np) := by
    have hNp : MemLp (fun y ↦ (u y)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R)) :=
      (continuous_posPart.comp_continuousOn hcont).memLp_restrict_of_subset_isCompact
        (isCompact_closedBall c R) measurableSet_ball ball_subset_closedBall _
    have h := Measure.rpow_neg_mul_toReal_eLpNorm_ball_le volume hR hq hqp.le hNp
    rw [finrank_euclideanSpace, measureReal_def] at h
    rw [hD, he, neg_div]
    calc (C₀ * K * κ) ^ (n / q) * (R ^ (-(n / q)) * Nq)
        ≤ (C₀ * K * κ) ^ (n / q) * (ω ^ (1 / q - 1 / p) * (R ^ (-(n / p)) * Np)) := by gcongr
      _ = _ := by ring
  refine hcore.trans ?_
  rw [mul_assoc ((4 / 3 : ℝ) ^ (m + 2))]
  gcongr (4 / 3 : ℝ) ^ (m + 2) * ?_
  have h1 : 0 ≤ (m + 2) / 2 * C₀ * (R ^ (-n / p) * Np) := by positivity
  have h2 : 0 ≤ D * (R / lam * F) := by positivity
  calc (m + 2) / 2 * C₀ * (R / lam * F) + (C₀ * K * κ) ^ e * (R ^ (-e) * Nq)
      ≤ (m + 2) / 2 * C₀ * (R / lam * F) + D * (R ^ (-n / p) * Np) := by gcongr
    _ ≤ _ := by linarith

end PDE

end TauCeti
