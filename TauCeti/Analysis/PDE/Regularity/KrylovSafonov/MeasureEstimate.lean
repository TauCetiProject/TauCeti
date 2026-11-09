/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Matrix.PosSemidef.Determinant
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence

/-!
# The basic measure estimate of Krylov and Safonov

Let `u` be a `C²` supersolution of a non-divergence-form equation
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` on a ball `B(c, R) ⊆ ℝⁿ`, `n ≥ 1`, with a symmetric coefficient matrix
satisfying `λ ‖ξ‖² ≤ ξᵀ a ξ` and `|ηᵀ a ξ| ≤ Λ ‖η‖ ‖ξ‖`, and `Λ ≤ κ λ`. The estimate says that if
`u ≥ 0` on the boundary sphere and `u ≤ 1` somewhere in the concentric ball `B(c, τ R)`, then `u`
stays below a fixed level `M` on a fixed fraction `μ` of the small ball `B(c, θ R)`, provided the
right-hand side is small, `R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`:

`μ |B(c, θ R)| ≤ |{u < M} ∩ B(c, θ R)|`

(`TauCeti.PDE.exists_mul_volume_ball_le_volume_setOf_lt_inter_ball`). The constants `M`, `μ`
and `ε₀` depend only on the dimension, on `κ` and on the radii ratios `θ > 0` and `0 < τ < 1`;
they do not depend on `R`, the centre, `λ`, the coefficients or `u`. This is the step that
converts the Aleksandrov–Bakelman–Pucci maximum principle into information about the distribution
of `u`.
Iterated with the Krylov–Safonov covering lemma on dyadic cubes
(`TauCeti.volume_le_mul_volume_of_forall_dyadicCube`), it gives the power decay
`|{u > t}| ≤ C t^(-ε)` of a nonnegative supersolution behind the weak Harnack inequality, the
Harnack inequality and the interior Hölder estimate of Krylov and Safonov.

## The barrier

The proof compares `u` with the radial barrier

`g(y) = (σ ‖y - c‖² + ε)^(-β)`, `σ = R⁻²`, `ε = θ²`, `β = n κ`.

Its second derivative is computed in
`TauCeti.PDE.sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add`:
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼg = 2 σ β s^(-β-2) (2 σ (β + 1) yᵀ A y - s tr A)` with `y = x - c` and
`s = σ ‖y‖² + ε`. Once `ε ≤ σ ‖y‖²`, that is outside `B(c, θ R)`, this is nonnegative as soon as
`tr A ≤ (β + 1) λ` (`TauCeti.PDE.sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add_nonneg`), and
everywhere it is bounded below by `-2 σ β ε^(-β-1) T` for every bound `0 ≤ T` of `tr A`
(`TauCeti.PDE.neg_mul_le_sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add`). So `g` is a
subsolution of every operator in the ellipticity class away from the small ball.

## The argument

Normalize the barrier to `φ = A (g|_{∂B} - g)` with `A` chosen so that `φ = 0` on the sphere and
`φ ≤ -2` on `B(c, τ R)`. Then `v = -(u + φ)` is at most `0` on the frontier of the open set
`Ω' = {v > 0} ∩ B(c, R)`, it is at least `1` at the point where `u ≤ 1`, and
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≥ -f - K 1_{B(c, θ R)}`. The Aleksandrov–Bakelman–Pucci estimate in measure form
(`TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet`) on `Ω'` bounds the volume of a ball of
radius `1 / (2 R)` by an integral over the upper contact set of `v`. That contact set lies in
`Ω'`, where `u < -φ ≤ M`, so the integral is at most a multiple of `‖f⁺‖ⁿ_{Lⁿ}` plus a multiple of
`|{u < M} ∩ B(c, θ R)|`. When `f` is small the first term is absorbed.

The estimate is proved for classical supersolutions, the class to which
`TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet` applies; no regularity of `a` beyond the
pointwise bounds is used, not even measurability.

## Main declarations

* `TauCeti.PDE.sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add`: the operator applied to the
  barrier `(σ ‖y - c‖² + ε)^(-β)`.
* `TauCeti.PDE.sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add_nonneg`: the barrier is a
  subsolution away from its centre.
* `TauCeti.PDE.neg_mul_le_sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add`: the global lower bound.
* `TauCeti.PDE.exists_mul_volume_ball_le_volume_setOf_lt_inter_ball`: **the basic measure
  estimate**.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Lemma 4.1 (the barrier) and Lemma 4.5 (the measure estimate).
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7.
* N. V. Krylov and M. V. Safonov, *A certain property of solutions of parabolic equations with
  measurable coefficients*, Izv. Akad. Nauk SSSR Ser. Mat. **44** (1980), 161–175.
-/

public section

noncomputable section

open InnerProductSpace Matrix Metric MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace TauCeti

namespace PDE

section Profile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem hasFDerivAt_mul_norm_sq_sub_add (σ ε : ℝ) (c y : E) :
    HasFDerivAt (fun y : E ↦ σ * ‖y - c‖ ^ 2 + ε)
      ((σ • 2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) (y - c)) y := by
  simpa using (((hasFDerivAt_id y).sub_const c).norm_sq.const_mul σ).add_const ε

private theorem fderiv_mul_norm_sq_sub_add_apply (σ ε : ℝ) (c x v : E) :
    fderiv ℝ (fun y : E ↦ σ * ‖y - c‖ ^ 2 + ε) x v = 2 * σ * ⟪x - c, v⟫ := by
  rw [(hasFDerivAt_mul_norm_sq_sub_add σ ε c x).fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  ring

private theorem fderiv_fderiv_mul_norm_sq_sub_add_apply (σ ε : ℝ) (c x v w : E) :
    fderiv ℝ (fderiv ℝ fun y : E ↦ σ * ‖y - c‖ ^ 2 + ε) x v w = 2 * σ * ⟪v, w⟫ := by
  set L : E →L[ℝ] E →L[ℝ] ℝ := σ • 2 • innerSL ℝ
  have hd : HasFDerivAt (fun y ↦ L (y - c)) L x :=
    (L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)).congr_fderiv L.comp_id
  rw [funext fun y ↦ (hasFDerivAt_mul_norm_sq_sub_add σ ε c y).fderiv, hd.fderiv]
  simp only [L, smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  ring

variable {σ ε : ℝ} {c x : E}

private theorem contDiffAt_rpow_mul_norm_sq_sub_add (hσ : 0 ≤ σ) (hε : 0 < ε) (β : ℝ)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun y : E ↦ (σ * ‖y - c‖ ^ 2 + ε) ^ (-β)) x :=
  ((contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ)).add
    contDiffAt_const).rpow_const_of_ne (by positivity)

/-- The second derivative of the barrier profile `(σ ‖y - c‖² + ε)^(-β)`. -/
private theorem fderiv_fderiv_rpow_mul_norm_sq_sub_add_apply (hσ : 0 ≤ σ) (hε : 0 < ε) (β : ℝ)
    (v w : E) :
    fderiv ℝ (fderiv ℝ fun y : E ↦ (σ * ‖y - c‖ ^ 2 + ε) ^ (-β)) x v w =
      4 * σ ^ 2 * β * (β + 1) * (σ * ‖x - c‖ ^ 2 + ε) ^ (-β - 2) * ⟪x - c, v⟫ * ⟪x - c, w⟫ -
        2 * σ * β * (σ * ‖x - c‖ ^ 2 + ε) ^ (-β - 1) * ⟪v, w⟫ := by
  have hs : 0 < σ * ‖x - c‖ ^ 2 + ε := by positivity
  have hf : ContDiffAt ℝ 2 (fun y : E ↦ σ * ‖y - c‖ ^ 2 + ε) x :=
    (contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ)).add contDiffAt_const
  have h := fderiv_fderiv_scalar_comp_apply (f := fun y : E ↦ σ * ‖y - c‖ ^ 2 + ε)
    (Real.contDiffAt_rpow_const_of_ne (p := -β) hs.ne') hf v w
  simp only [Function.comp_def] at h
  rw [h, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, Real.deriv_rpow_const,
    fderiv_mul_norm_sq_sub_add_apply, fderiv_mul_norm_sq_sub_add_apply,
    fderiv_fderiv_mul_norm_sq_sub_add_apply, smul_eq_mul, smul_eq_mul]
  simp only [descPochhammer_succ_right, descPochhammer_zero, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_zero,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero]
  ring_nf

end Profile

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {σ ε β lam T : ℝ} {c x : EuclideanSpace ℝ ι}

/-- **The operator applied to the Krylov–Safonov barrier.** For `σ ≥ 0` and `ε > 0`, with
`s = σ ‖x - c‖² + ε`,
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ (σ ‖· - c‖² + ε)^(-β) (x) = 2 σ β s^(-β-2) (2 σ (β + 1) (x - c)ᵀ A (x - c) - s tr A)`.
-/
theorem sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add (A : Matrix ι ι ℝ) (hσ : 0 ≤ σ)
    (hε : 0 < ε) (β : ℝ) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y : EuclideanSpace ℝ ι ↦
        (σ * ‖y - c‖ ^ 2 + ε) ^ (-β)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      2 * σ * β * (σ * ‖x - c‖ ^ 2 + ε) ^ (-β - 2) *
        (2 * σ * (β + 1) * A.toQuadraticForm' (x - c) - (σ * ‖x - c‖ ^ 2 + ε) * A.trace) := by
  have hs : 0 < σ * ‖x - c‖ ^ 2 + ε := by positivity
  have hpow : (σ * ‖x - c‖ ^ 2 + ε) ^ (-β - 1) =
      (σ * ‖x - c‖ ^ 2 + ε) * (σ * ‖x - c‖ ^ 2 + ε) ^ (-β - 2) := by
    rw [show -β - 1 = 1 + (-β - 2) by ring, Real.rpow_add hs, Real.rpow_one]
  simp only [fderiv_fderiv_rpow_mul_norm_sq_sub_add_apply hσ hε]
  set s := σ * ‖x - c‖ ^ 2 + ε
  set y := x - c
  have hδ (i : ι) : ∑ j, A i j * ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1⟫ =
      A i i := by
    simp [EuclideanSpace.inner_single_right, PiLp.single_apply]
  have hy (k : ι) : ⟪y, EuclideanSpace.single k (1 : ℝ)⟫ = y k := by
    simp [EuclideanSpace.inner_single_right]
  have hterm (i j : ι) : A i j * (4 * σ ^ 2 * β * (β + 1) * s ^ (-β - 2) *
      ⟪y, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪y, EuclideanSpace.single j (1 : ℝ)⟫ -
      2 * σ * β * (s * s ^ (-β - 2)) *
        ⟪EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)⟫) =
      4 * σ ^ 2 * β * (β + 1) * s ^ (-β - 2) * (y i * (A i j * y j)) -
        2 * σ * β * s * s ^ (-β - 2) * (A i j * ⟪EuclideanSpace.single i (1 : ℝ),
          EuclideanSpace.single j 1⟫) := by
    rw [hy, hy]
    ring
  simp only [hpow, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hδ, toQuadraticForm'_apply,
    dotProduct, mulVec, trace, diag]
  simp only [y, WithLp.ofLp_sub]
  ring

/-- **The barrier is a subsolution away from its centre.** If `λ ‖ξ‖² ≤ ξᵀ A ξ` with `λ ≥ 0`,
`tr A ≤ (β + 1) λ` and `ε ≤ σ ‖x - c‖²`, then `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ (σ ‖· - c‖² + ε)^(-β) (x) ≥ 0`. -/
theorem sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add_nonneg {A : Matrix ι ι ℝ} (hσ : 0 ≤ σ)
    (hε : 0 < ε) (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (htr : A.trace ≤ (β + 1) * lam) (hx : ε ≤ σ * ‖x - c‖ ^ 2) :
    0 ≤ ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y : EuclideanSpace ℝ ι ↦
        (σ * ‖y - c‖ ^ 2 + ε) ^ (-β)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  rw [sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add A hσ hε]
  have hs : 0 < σ * ‖x - c‖ ^ 2 + ε := by positivity
  refine mul_nonneg (by positivity) ?_
  have hQ := hA (x - c)
  simp only [WithLp.ofLp_sub] at hQ ⊢
  have hN : 0 ≤ ‖x - c‖ ^ 2 := by positivity
  have hσβ : 0 ≤ σ * (β + 1) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hQ hσβ
  -- `s tr A ≤ 2 σ ‖x - c‖² (β + 1) λ ≤ 2 σ (β + 1) (x - c)ᵀ A (x - c)`, splitting on the sign of
  -- the trace.
  rcases le_total 0 A.trace with htr0 | htr0
  · have h1 := mul_le_mul_of_nonneg_right hx htr0
    have h2 := mul_le_mul_of_nonneg_left htr (mul_nonneg hσ hN)
    linarith
  · have h4 := mul_nonneg hσβ (mul_nonneg hlam hN)
    have h5 := mul_nonneg hs.le (neg_nonneg.2 htr0)
    linarith

/-- **The global lower bound for the barrier.** If `ξᵀ A ξ ≥ 0` and `tr A ≤ T` with `T ≥ 0`, then
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ (σ ‖· - c‖² + ε)^(-β) ≥ -2 σ β ε^(-β-1) T` everywhere. -/
theorem neg_mul_le_sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add {A : Matrix ι ι ℝ}
    (hσ : 0 ≤ σ) (hε : 0 < ε) (hβ : 0 ≤ β) (hA : ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ A.toQuadraticForm' ξ)
    (htr : A.trace ≤ T) (hT : 0 ≤ T) :
    -(2 * σ * β * ε ^ (-β - 1) * T) ≤ ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun y :
        EuclideanSpace ℝ ι ↦ (σ * ‖y - c‖ ^ 2 + ε) ^ (-β)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  rw [sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add A hσ hε]
  set s := σ * ‖x - c‖ ^ 2 + ε
  have hs : ε ≤ s := le_add_of_nonneg_left (by positivity)
  have hpow : s ^ (-β - 1) = s * s ^ (-β - 2) := by
    rw [show -β - 1 = 1 + (-β - 2) by ring, Real.rpow_add (hε.trans_le hs), Real.rpow_one]
  have hmono : s ^ (-β - 1) ≤ ε ^ (-β - 1) := Real.rpow_le_rpow_of_nonpos hε hs (by linarith)
  have hP : 0 ≤ 2 * σ * β * s ^ (-β - 2) := by positivity
  have hQ : 0 ≤ 2 * σ * (β + 1) * A.toQuadraticForm' (x - c) :=
    mul_nonneg (by positivity) (hA _)
  have hσβ : 0 ≤ 2 * σ * β := by positivity
  calc -(2 * σ * β * ε ^ (-β - 1) * T) ≤ -(2 * σ * β * s ^ (-β - 1) * T) := by
        nlinarith [mul_le_mul_of_nonneg_left hmono hσβ]
    _ ≤ -(2 * σ * β * s ^ (-β - 1) * A.trace) := by
        nlinarith [mul_le_mul_of_nonneg_left htr (mul_nonneg hσβ (Real.rpow_nonneg
          (hε.le.trans hs) (-β - 1)))]
    _ = 2 * σ * β * s ^ (-β - 2) * (0 - s * A.trace) := by rw [hpow]; ring
    _ ≤ 2 * σ * β * s ^ (-β - 2) * (2 * σ * (β + 1) * A.toQuadraticForm' (x - c) - s * A.trace) :=
        mul_le_mul_of_nonneg_left (by linarith) hP

/-- A symmetric coefficient matrix with `λ ‖ξ‖² ≤ ξᵀ a ξ` has determinant at least `λⁿ`. -/
private theorem pow_card_le_det {X : Type*} {Ω : Set X} {a : X → Matrix ι ι ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hsymm : (a x).IsSymm) :
    lam ^ Fintype.card ι ≤ (a x).det := by
  have h1 : (lam • (1 : Matrix ι ι ℝ)).PosSemidef := PosSemidef.one.smul h.pos.le
  have h2 : lam • (1 : Matrix ι ι ℝ) ≤ a x := by
    rw [Matrix.le_iff]
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun ξ => ?_
    · exact isHermitian_iff_isSymm.2 (hsymm.sub (isSymm_one.smul lam))
    · have := h.lower_bound hx (WithLp.toLp 2 ξ)
      simp only [toQuadraticForm'_apply, EuclideanSpace.norm_sq_eq] at this
      simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
        dotProduct_smul, smul_eq_mul, sub_nonneg]
      simpa [dotProduct, Real.norm_eq_abs, sq_abs, sq] using this
  simpa [det_smul] using h1.det_le_det h2

/-- The pointwise bound behind the Aleksandrov–Bakelman–Pucci integrand. -/
private theorem div_pow_div_le {n : ℕ} {lam d F p q : ℝ} (hn : 0 < n) (hlam : 0 < lam)
    (hd : lam ^ n ≤ d) (hF : F⁻ ≤ p + q) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (F⁻ / n) ^ n / d ≤ (2 / (n * lam)) ^ n * p ^ n + (2 / (n * lam)) ^ n * q ^ n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hF0 : 0 ≤ F⁻ / n := div_nonneg (negPart_nonneg F) hn'.le
  calc (F⁻ / n) ^ n / d ≤ (F⁻ / n) ^ n / lam ^ n :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = (F⁻ / (n * lam)) ^ n := by rw [← div_pow]; congr 1; field_simp
    _ ≤ (2 / (n * lam) * max p q) ^ n := by
        refine pow_le_pow_left₀ (by positivity) ?_ n
        rw [div_le_iff₀ (by positivity)]
        calc F⁻ ≤ p + q := hF
          _ ≤ 2 * max p q := by linarith [le_max_left p q, le_max_right p q]
          _ = _ := by field_simp
    _ ≤ _ := by
        rw [mul_pow, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total p q with hpq | hpq
        · rw [max_eq_right hpq]; exact le_add_of_nonneg_left (by positivity)
        · rw [max_eq_left hpq]; exact le_add_of_nonneg_right (by positivity)

/-- An `Lⁿ` bound on `f⁺` bounds `∫ (f⁺)ⁿ`. -/
private theorem setLIntegral_ofReal_posPart_pow_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {n : ℕ} (hn : n ≠ 0) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm (fun x ↦ (f x)⁺) n μ ≤ ENNReal.ofReal B) :
    ∫⁻ x, ENNReal.ofReal ((f x)⁺ ^ n) ∂μ ≤ ENNReal.ofReal (B ^ n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have heq := lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := fun x ↦ (f x)⁺) hn'
  have hnorm : eLpNorm (fun x ↦ (f x)⁺) n μ = eLpNorm' (fun x ↦ (f x)⁺) n μ := by
    simpa using eLpNorm_eq_eLpNorm' (μ := μ) (f := fun x ↦ (f x)⁺) (p := n) (by simpa using hn)
      (ENNReal.natCast_ne_top n) (aestronglyMeasurable_of_eLpNorm_ne_top
        (h.trans_lt ENNReal.ofReal_lt_top).ne)
  have hint : ∫⁻ x, ENNReal.ofReal ((f x)⁺ ^ n) ∂μ = eLpNorm (fun x ↦ (f x)⁺) n μ ^ n := by
    rw [hnorm, ← ENNReal.rpow_natCast, ← heq]
    refine lintegral_congr fun x ↦ ?_
    rw [Real.enorm_eq_ofReal (posPart_nonneg _), ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (posPart_nonneg _)]
  rw [hint, ENNReal.ofReal_pow hB]
  gcongr

/-- The operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ` applied to `r g - u - C` is
`r (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ g) - ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ u`. -/
private theorem sum_mul_fderiv_fderiv_mul_sub_sub_const (A : Matrix ι ι ℝ)
    {u g : EuclideanSpace ℝ ι → ℝ} {y : EuclideanSpace ℝ ι} (hu : ContDiffAt ℝ 2 u y)
    (hg : ContDiffAt ℝ 2 g y) (r C : ℝ) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ r * g z - u z - C) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      r * ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) -
        ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) := by
  have hv : (fun z ↦ r * g z - u z - C) = fun z ↦ (-u + r • g) z - C := by
    ext z
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hlin := sum_mul_fderiv_fderiv_add_fderiv_add_smul (A := A) (f := -u) hu.neg hg r 0
  rw [sum_mul_fderiv_fderiv_add_fderiv_neg] at hlin
  simp only [map_zero, add_zero] at hlin
  have hD : (fderiv ℝ fun z ↦ (-u + r • g) z - C) = fderiv ℝ (-u + r • g) :=
    funext fun z ↦ fderiv_sub_const C
  rw [hv, hD, hlin]
  ring

omit [DecidableEq ι] in
/-- **The comparison set.** Let `u` be continuous on `closedBall c R`, `C²` in `B(c, R)` and
nonnegative on the sphere, let `g` be `C²` with the constant value `g₁` on the sphere, and let
`x₀ ∈ B(c, R)` satisfy `u x₀ ≤ 1` and `A g x₀ - A g₁ ≥ 2`. Then `v = A g - u - A g₁` is
continuous on the closure of the open set `Ω' = B(c, R) ∩ {v > 0}`, `C²` in `Ω'` and at most `0`
on its frontier, and `x₀ ∈ Ω'` with `v x₀ ≥ 1`. -/
private theorem barrier_comparison {R A g₁ : ℝ} {c x₀ : EuclideanSpace ℝ ι}
    {u g : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn u (closedBall c R))
    (hu : ContDiffOn ℝ 2 u (ball c R)) (hg : ContDiff ℝ 2 g)
    (hbdry : ∀ z ∈ sphere c R, 0 ≤ u z) (hg₁ : ∀ z ∈ sphere c R, g z = g₁)
    (hx₀ : x₀ ∈ ball c R) (hux₀ : u x₀ ≤ 1) (hgx₀ : 2 ≤ A * g x₀ - A * g₁) :
    let v := fun y ↦ A * g y - u y - A * g₁
    IsOpen (ball c R ∩ v ⁻¹' Ioi 0) ∧ ContinuousOn v (closure (ball c R ∩ v ⁻¹' Ioi 0)) ∧
      ContDiffOn ℝ 2 v (ball c R ∩ v ⁻¹' Ioi 0) ∧ x₀ ∈ ball c R ∩ v ⁻¹' Ioi 0 ∧ 1 ≤ v x₀ ∧
      ∀ z ∈ frontier (ball c R ∩ v ⁻¹' Ioi 0), v z ≤ 0 := by
  intro v
  have hvc : ContinuousOn v (closedBall c R) :=
    ((continuous_const.mul hg.continuous).continuousOn.sub hcont).sub continuousOn_const
  have hΩ' : IsOpen (ball c R ∩ v ⁻¹' Ioi 0) :=
    (hvc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hcl : closure (ball c R ∩ v ⁻¹' Ioi 0) ⊆ closedBall c R :=
    (closure_mono inter_subset_left).trans closure_ball_subset_closedBall
  have hv₀ : 1 ≤ v x₀ := by linarith
  refine ⟨hΩ', hvc.mono hcl, ((contDiff_const.mul hg).contDiffOn.sub
    (hu.mono inter_subset_left)).sub contDiffOn_const, ⟨hx₀, show (0 : ℝ) < v x₀ by linarith⟩,
    hv₀, fun z hz ↦ ?_⟩
  -- On the frontier of `Ω'`, either `v = 0` inside the ball, or `v = -u ≤ 0` on the sphere.
  rw [frontier, hΩ'.interior_eq] at hz
  by_cases hzb : z ∈ ball c R
  · exact not_lt.1 fun h ↦ hz.2 ⟨hzb, h⟩
  · have hzs : z ∈ sphere c R := by
      rw [mem_sphere]
      exact le_antisymm (mem_closedBall.1 (hcl hz.1)) (not_lt.1 fun h ↦ hzb (mem_ball.2 h))
    simp only [v, hg₁ z hzs]
    linarith [hbdry z hzs]

variable [Nonempty ι]

/-- **The barrier inequality inside and outside the small ball.** For `y ∈ B(c, R)`, the barrier
`g = (R⁻² ‖· - c‖² + θ²)^(-β)` with `β = n κ` satisfies `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼg ≥ 0` outside `B(c, θ R)`,
and `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼg ≥ -K₀` inside it, for the explicit constant `K₀` below. -/
private theorem neg_indicator_le_mul_sum_mul_fderiv_fderiv_barrier {lam Lam κ R θ A : ℝ}
    {c : EuclideanSpace ℝ ι} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : UniformlyEllipticOn (ball c R) a lam Lam) (hLam : Lam ≤ κ * lam) (hκ : 0 < κ)
    (hR : 0 < R) (hθ : 0 < θ) (hA : 0 ≤ A) {y : EuclideanSpace ℝ ι} (hy : y ∈ ball c R) :
    -(ball c (θ * R)).indicator (fun _ ↦ A * (2 * (R ^ 2)⁻¹ * (Fintype.card ι * κ) *
        (θ ^ 2) ^ (-(Fintype.card ι * κ) - 1) * (Fintype.card ι * κ * lam))) y ≤
      A * ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ fun z : EuclideanSpace ℝ ι ↦
        ((R ^ 2)⁻¹ * ‖z - c‖ ^ 2 + θ ^ 2) ^ (-(Fintype.card ι * κ))) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  have hlam := ha.pos
  have htr : (a y).trace ≤ n * κ * lam := by
    calc (a y).trace ≤ n * Lam := ha.trace_le hy
      _ ≤ n * (κ * lam) := mul_le_mul_of_nonneg_left hLam hn.le
      _ = n * κ * lam := by ring
  by_cases hyθ : y ∈ ball c (θ * R)
  · rw [indicator_of_mem hyθ, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (neg_mul_le_sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add
      (by positivity) (by positivity) (by positivity) (ha.quadraticForm_nonneg hy) htr
      (by positivity)) hA
  · rw [indicator_of_notMem hyθ, neg_zero]
    refine mul_nonneg hA (sum_mul_fderiv_fderiv_rpow_mul_norm_sq_sub_add_nonneg (by positivity)
      (by positivity) (by positivity) hlam.le (ha.lower_bound hy) (by nlinarith) ?_)
    have hd : θ * R ≤ ‖y - c‖ := by simpa [mem_ball, dist_eq_norm] using hyθ
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hd hd (by positivity) (norm_nonneg _)]

/-- **The Aleksandrov–Bakelman–Pucci estimate with a split right-hand side.** Let `Ω ⊆ B(c, R)` be
open, `v` continuous on `closure Ω` and `C²` in `Ω`, at most `0` on `frontier Ω` and at least `1`
at some point of `Ω`. If on the upper contact set `Γ⁺` the matrices `a` are positive definite with
`det a ≥ λⁿ`, `F ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv` and `F⁻ ≤ p + q 1_B` with `p ≥ 0`, `q ≥ 0`, then
`|B(0, 1 / (2 R))| ≤ (2 / (n λ))ⁿ (∫_{Γ⁺} pⁿ + qⁿ |B ∩ Γ⁺|)`. -/
private theorem volume_ball_le_of_upperContactSet {Ω B : Set (EuclideanSpace ℝ ι)}
    {v F p : EuclideanSpace ℝ ι → ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam q R : ℝ}
    {c x₀ : EuclideanSpace ℝ ι} (hΩR : Ω ⊆ ball c R) (hΩ : IsOpen Ω)
    (hcont : ContinuousOn v (closure Ω)) (hv : ContDiffOn ℝ 2 v Ω) (hlam : 0 < lam)
    (ha : ∀ y ∈ upperContactSet v Ω, (a y).PosDef ∧ lam ^ Fintype.card ι ≤ (a y).det)
    (hF : ∀ y ∈ upperContactSet v Ω, F y ≤ ∑ i, ∑ j, a y i j *
      fderiv ℝ (fderiv ℝ v) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hFp : ∀ y ∈ upperContactSet v Ω, (F y)⁻ ≤ p y + B.indicator (fun _ ↦ q) y)
    (hp : ∀ y, 0 ≤ p y) (hq : 0 ≤ q) (hB : MeasurableSet B)
    (hfront : ∀ z ∈ frontier Ω, v z ≤ 0) (hx₀ : x₀ ∈ Ω) (hvx₀ : 1 ≤ v x₀) :
    volume (ball (0 : EuclideanSpace ℝ ι) (1 / (2 * R))) ≤
      ENNReal.ofReal ((2 / (Fintype.card ι * lam)) ^ Fintype.card ι) *
          (∫⁻ y in upperContactSet v Ω, ENNReal.ofReal (p y ^ Fintype.card ι)) +
        ENNReal.ofReal ((2 / (Fintype.card ι * lam)) ^ Fintype.card ι * q ^ Fintype.card ι) *
          volume (B ∩ upperContactSet v Ω) := by
  set N := Fintype.card ι
  set c₁ : ℝ := (2 / (N * lam)) ^ N
  have hΓ := measurableSet_upperContactSet hΩ (hv.of_le (by norm_num))
  have hABP := volume_ball_le_setLIntegral_upperContactSet (isBounded_ball.subset hΩR) hΩ hcont
    hv (fun y hy ↦ (ha y hy).1) hF hfront hx₀
  -- `Ω` is a nonempty open subset of `B(c, R)`, so `0 < diam Ω ≤ 2 R`.
  have hR : 0 < R := pos_of_mem_ball (hΩR hx₀)
  have hdiam0 : 0 < diam Ω := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
    calc 0 < 2 * ε := by positivity
      _ = diam (ball x₀ ε) := (Metric.diam_ball_eq x₀ hε.le).symm
      _ ≤ diam Ω := diam_mono hball (isBounded_ball.subset hΩR)
  have hdiam : diam Ω ≤ 2 * R := (diam_mono hΩR isBounded_ball).trans (diam_ball hR.le)
  have hrad : 1 / (2 * R) ≤ (v x₀ - 0) / diam Ω := by
    rw [sub_zero, div_le_div_iff₀ (by positivity) hdiam0]
    nlinarith
  -- Split the integrand into the `p` part and the part carried by `B`.
  have hpt : ∀ y ∈ upperContactSet v Ω, ENNReal.ofReal (((F y)⁻ / N) ^ N / (a y).det) ≤
      ENNReal.ofReal c₁ * ENNReal.ofReal (p y ^ N) +
        B.indicator (fun _ ↦ ENNReal.ofReal (c₁ * q ^ N)) y := by
    intro y hy
    have h := div_pow_div_le Fintype.card_pos hlam (ha y hy).2 (hFp y hy) (hp y)
      (indicator_nonneg (fun _ _ ↦ hq) y)
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_add_le.trans
      (add_le_add_right ?_ _))
    by_cases hyB : y ∈ B
    · simp only [indicator_of_mem hyB]
      exact le_rfl
    · simp [indicator_of_notMem hyB, Fintype.card_ne_zero]
  refine (measure_mono (ball_subset_ball hrad)).trans (hABP.trans
    ((setLIntegral_mono' hΓ hpt).trans_eq ?_))
  rw [lintegral_add_right _ (measurable_const.indicator hB), lintegral_indicator_const hB,
    Measure.restrict_apply hB, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

omit [DecidableEq ι] in
/-- **The conclusion of the measure estimate.** If `|B(0, 1 / (2 R))|` is bounded by
`c₁ ∫_Γ (f⁺)ⁿ + c₁ qⁿ |S|` with `Γ ⊆ B(c, R)`, `c₁ = (2 / (n λ))ⁿ`, `2 q / (n λ) = K₁ / R²` and
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ` for the threshold `ε₀ = n (ω / 2)^{1/n} / 4`, `ω = |B(0, 1)|`, then
`|S|` is at least the fraction `1 / (2ⁿ⁺¹ K₁ⁿ θⁿ)` of `|B(c, θ R)|`. -/
private theorem ofReal_mul_volume_ball_le_of_volume_ball_le {Γ S : Set (EuclideanSpace ℝ ι)}
    {f : EuclideanSpace ℝ ι → ℝ} {c : EuclideanSpace ℝ ι} {lam q R θ K₁ : ℝ} (hlam : 0 < lam)
    (hR : 0 < R) (hθ : 0 < θ) (hK₁ : 0 < K₁) (hΓ : Γ ⊆ ball c R) (hS : volume S ≠ ∞)
    (hq0 : 0 ≤ q) (hq : 2 / (Fintype.card ι * lam) * q = K₁ * (R ^ 2)⁻¹)
    (hf : ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
      (volume.restrict (ball c R)) ≤ ENNReal.ofReal (Fintype.card ι *
        ((volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal / 2) ^ (Fintype.card ι : ℝ)⁻¹ / 4 *
          lam))
    (h : volume (ball (0 : EuclideanSpace ℝ ι) (1 / (2 * R))) ≤
      ENNReal.ofReal ((2 / (Fintype.card ι * lam)) ^ Fintype.card ι) *
          (∫⁻ y in Γ, ENNReal.ofReal ((f y)⁺ ^ Fintype.card ι)) +
        ENNReal.ofReal ((2 / (Fintype.card ι * lam)) ^ Fintype.card ι * q ^ Fintype.card ι) *
          volume S) :
    ENNReal.ofReal (1 / (2 ^ (Fintype.card ι + 1) * K₁ ^ Fintype.card ι * θ ^ Fintype.card ι)) *
      volume (ball c (θ * R)) ≤ volume S := by
  set N := Fintype.card ι
  set n : ℝ := (N : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  set B := n * (ω / 2) ^ n⁻¹ / 4 * lam / R
  -- The `Lⁿ` part is at most half of the left-hand side.
  have hfn : eLpNorm (fun x ↦ (f x)⁺) N (volume.restrict (ball c R)) ≤ ENNReal.ofReal B := by
    rw [ENNReal.ofReal_div_of_pos hR, ENNReal.le_div_iff_mul_le
      (Or.inl (by simpa using hR)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hf
  have h1 : ∫⁻ y in Γ, ENNReal.ofReal ((f y)⁺ ^ N) ≤ ENNReal.ofReal (B ^ N) :=
    (lintegral_mono_set hΓ).trans (setLIntegral_ofReal_posPart_pow_le Fintype.card_ne_zero
      (by positivity) hfn)
  have hvol (z : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
      volume (ball z r) = ENNReal.ofReal (r ^ N * ω) := by
    rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  have hkey : volume (ball (0 : EuclideanSpace ℝ ι) (1 / (2 * R))) ≤
      ENNReal.ofReal ((2 / (n * lam)) ^ N) * ENNReal.ofReal (B ^ N) +
        ENNReal.ofReal ((2 / (n * lam)) ^ N * q ^ N) * volume S :=
    h.trans (by gcongr)
  rw [hvol _ (by positivity)] at hkey
  -- Pass to real numbers.
  have hreal := ENNReal.toReal_mono (by finiteness) hkey
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [hvol _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have e1 : (2 / (n * lam)) ^ N * B ^ N = (1 / (2 * R)) ^ N * ω / 2 := by
    have : 2 / (n * lam) * B = (ω / 2) ^ n⁻¹ * (1 / (2 * R)) := by
      simp only [B]
      field_simp
      ring
    rw [← mul_pow, this, mul_pow, Real.rpow_inv_natCast_pow (by positivity) Fintype.card_ne_zero]
    ring
  have e3 : 1 / (2 ^ (N + 1) * K₁ ^ N * θ ^ N) * ((θ * R) ^ N * ω) * (K₁ * (R ^ 2)⁻¹) ^ N =
      (1 / (2 * R)) ^ N * ω / 2 := by
    simp only [one_div, mul_pow, inv_pow, ← pow_mul, pow_succ]
    field_simp
    ring
  rw [e1, ← mul_pow, hq] at hreal
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < (K₁ * (R ^ 2)⁻¹) ^ N)
  rw [e3]
  linarith

/-- The measure estimate for a fixed normalization `A` of the barrier, with `β = n κ`,
`A ((τ² + θ²)^(-β) - (1 + θ²)^(-β)) = 2`, `M = A (θ²)^(-β)` and
`K₁ = 4 A β κ (θ²)^(-β-1)`. -/
private theorem ofReal_mul_volume_ball_le_volume_lt_inter_ball {κ θ τ A lam Lam R : ℝ}
    {c x₀ : EuclideanSpace ℝ ι} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {u f : EuclideanSpace ℝ ι → ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hτ : τ < 1) (hA : 0 < A)
    (hAG : A * ((τ ^ 2 + θ ^ 2) ^ (-(Fintype.card ι * κ)) -
      (1 ^ 2 + θ ^ 2) ^ (-(Fintype.card ι * κ))) = 2)
    (hR : 0 < R) (ha : UniformlyEllipticOn (ball c R) a lam Lam) (hLam : Lam ≤ κ * lam)
    (hsymm : ∀ x ∈ ball c R, (a x).IsSymm) (hcont : ContinuousOn u (closedBall c R))
    (hu : ContDiffOn ℝ 2 u (ball c R)) (hbdry : ∀ x ∈ sphere c R, 0 ≤ u x)
    (hsuper : ∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x)
    (hf : ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
      (volume.restrict (ball c R)) ≤ ENNReal.ofReal (Fintype.card ι *
        ((volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal / 2) ^ (Fintype.card ι : ℝ)⁻¹ / 4 *
          lam))
    (hx₀ : x₀ ∈ ball c (τ * R)) (hux₀ : u x₀ ≤ 1) :
    ENNReal.ofReal (1 / (2 ^ (Fintype.card ι + 1) *
        (4 * A * (Fintype.card ι * κ) * κ * (θ ^ 2) ^ (-(Fintype.card ι * κ) - 1)) ^
          Fintype.card ι * θ ^ Fintype.card ι)) * volume (ball c (θ * R)) ≤
      volume ({x | u x < A * (θ ^ 2) ^ (-(Fintype.card ι * κ))} ∩ ball c (θ * R)) := by
  set n : ℝ := (Fintype.card ι : ℝ)
  set β := n * κ
  have hβ : 0 < β := by positivity
  have hlam := ha.pos
  set g : EuclideanSpace ℝ ι → ℝ := fun y ↦ ((R ^ 2)⁻¹ * ‖y - c‖ ^ 2 + θ ^ 2) ^ (-β)
  have hgG (y : EuclideanSpace ℝ ι) : g y = ((‖y - c‖ / R) ^ 2 + θ ^ 2) ^ (-β) := by
    simp only [g, div_pow, inv_mul_eq_div]
  have hg2 (y : EuclideanSpace ℝ ι) : ContDiffAt ℝ 2 g y :=
    contDiffAt_rpow_mul_norm_sq_sub_add (by positivity) (by positivity) β
  -- The barrier has risen by `2 / A` at `x₀`, and it is constant on the sphere.
  have hgx₀ : (τ ^ 2 + θ ^ 2) ^ (-β) ≤ g x₀ := by
    have : ‖x₀ - c‖ / R ≤ τ := (div_le_iff₀ hR).2 (mem_ball_iff_norm.1 hx₀).le
    exact hgG x₀ ▸ Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by nlinarith)
  obtain ⟨hΩ', hvc, hv2, hx₀Ω', hvx₀, hfront⟩ := barrier_comparison (A := A)
    (g₁ := (1 ^ 2 + θ ^ 2) ^ (-β)) hcont hu (contDiff_iff_contDiffAt.2 hg2) hbdry
    (fun z hz ↦ by rw [hgG, mem_sphere_iff_norm.1 hz, div_self hR.ne'])
    (ball_subset_ball (by nlinarith) hx₀) hux₀ (by nlinarith [mul_le_mul_of_nonneg_left hgx₀ hA.le])
  set v : EuclideanSpace ℝ ι → ℝ := fun y ↦ A * g y - u y - A * (1 ^ 2 + θ ^ 2) ^ (-β)
  have hΓ : upperContactSet v (ball c R ∩ v ⁻¹' Ioi 0) ⊆ ball c R :=
    upperContactSet_subset.trans inter_subset_left
  set K := A * (2 * (R ^ 2)⁻¹ * β * (θ ^ 2) ^ (-β - 1) * (n * κ * lam))
  have hK : 0 ≤ K := by positivity
  -- `v = -(u + φ)` satisfies `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≥ -f - K 1_{B(c, θ R)}`, by the barrier inequality.
  have h := volume_ball_le_of_upperContactSet (p := fun y ↦ (f y)⁺)
    (F := fun y ↦ -f y - (ball c (θ * R)).indicator (fun _ ↦ K) y) inter_subset_left hΩ' hvc
    hv2 hlam (fun y hy ↦ ⟨ha.posDef (hΓ hy) (hsymm _ (hΓ hy)),
      pow_card_le_det ha (hΓ hy) (hsymm _ (hΓ hy))⟩)
    (fun y hy ↦ by
      rw [sum_mul_fderiv_fderiv_mul_sub_sub_const _ (hu.contDiffAt (isOpen_ball.mem_nhds
        (hΓ hy))) (hg2 y)]
      linarith [neg_indicator_le_mul_sum_mul_fderiv_fderiv_barrier ha hLam hκ hR hθ hA.le (hΓ hy),
        hsuper y (hΓ hy)])
    (fun y _ ↦ sup_le (by linarith [le_posPart (f y)])
      (add_nonneg (posPart_nonneg _) (indicator_nonneg (fun _ _ ↦ hK) _)))
    (fun y ↦ posPart_nonneg _) hK measurableSet_ball hfront hx₀Ω' hvx₀
  -- On the contact set `v > 0`, so `u < A g ≤ M`.
  have hS : ball c (θ * R) ∩ upperContactSet v (ball c R ∩ v ⁻¹' Ioi 0) ⊆
      {x | u x < A * (θ ^ 2) ^ (-β)} ∩ ball c (θ * R) := by
    rintro y ⟨hyθ, hy⟩
    have hv : 0 < A * g y - u y - A * (1 ^ 2 + θ ^ 2) ^ (-β) := (upperContactSet_subset hy).2
    have hgle : A * g y ≤ A * (θ ^ 2) ^ (-β) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) (le_add_of_nonneg_left (by positivity))
        (by linarith)) hA.le
    exact ⟨(by nlinarith [(by positivity : 0 < A * (1 ^ 2 + θ ^ 2) ^ (-β))] : u y < _), hyθ⟩
  refine ofReal_mul_volume_ball_le_of_volume_ball_le hlam hR hθ (by positivity) hΓ
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne hK ?_ hf
    (h.trans (by gcongr))
  simp only [K, β, n]
  field_simp
  norm_num

/-- **The basic measure estimate of Krylov and Safonov** (Caffarelli–Cabré, Lemma 4.5, for
classical supersolutions of linear equations). Let `θ > 0`, `0 < τ < 1` and `κ > 0`. There are
constants `M, μ, ε₀ > 0`, depending only on the dimension, `κ`, `θ` and `τ`, with the following
property. Let `R > 0`, let the symmetric coefficient matrix `a` be uniformly elliptic on
`B(c, R)` with constants `λ ≤ Λ ≤ κ λ`, and let `u` be continuous on `closedBall c R`, `C²` in
`B(c, R)`, nonnegative on the sphere `‖x - c‖ = R`, with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` in `B(c, R)` and
`R ‖f⁺‖_{Lⁿ(B(c, R))} ≤ ε₀ λ`. If `u ≤ 1` somewhere in `B(c, τ R)`, then
`μ |B(c, θ R)| ≤ |{u < M} ∩ B(c, θ R)|`. -/
theorem exists_mul_volume_ball_le_volume_setOf_lt_inter_ball {κ θ τ : ℝ} (hκ : 0 < κ)
    (hθ : 0 < θ) (hτ₀ : 0 < τ) (hτ : τ < 1) :
    ∃ M μ ε₀ : ℝ, 0 < M ∧ 0 < μ ∧ 0 < ε₀ ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < R → UniformlyEllipticOn (ball c R) a lam Lam →
        Lam ≤ κ * lam → (∀ x ∈ ball c R, (a x).IsSymm) →
        ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ sphere c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ f x) →
        ENNReal.ofReal R * eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι)
          (volume.restrict (ball c R)) ≤ ENNReal.ofReal (ε₀ * lam) →
        (∃ x ∈ ball c (τ * R), u x ≤ 1) →
        ENNReal.ofReal μ * volume (ball c (θ * R)) ≤
          volume ({x | u x < M} ∩ ball c (θ * R)) := by
  set N := Fintype.card ι
  set n : ℝ := (N : ℝ)
  have hn : 0 < n := Nat.cast_pos.2 Fintype.card_pos
  set β : ℝ := n * κ
  have hβ : 0 < β := by positivity
  -- The barrier `(t² + θ²)^(-β)` drops by `2 / A` between the radii `τ` and `1`.
  have hG : (1 ^ 2 + θ ^ 2) ^ (-β) < (τ ^ 2 + θ ^ 2) ^ (-β) :=
    Real.rpow_lt_rpow_of_neg (by positivity) (by nlinarith) (by nlinarith)
  set A := 2 / ((τ ^ 2 + θ ^ 2) ^ (-β) - (1 ^ 2 + θ ^ 2) ^ (-β))
  have hA : 0 < A := div_pos two_pos (sub_pos.2 hG)
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  refine ⟨A * (θ ^ 2) ^ (-β), 1 / (2 ^ (N + 1) * (4 * A * β * κ * (θ ^ 2) ^ (-β - 1)) ^ N *
    θ ^ N), n * (ω / 2) ^ n⁻¹ / 4, by positivity, by positivity, by positivity, ?_⟩
  intro lam Lam R c a u f hR ha hLam hsymm hcont hu hbdry hsuper hf ⟨x₀, hx₀, hux₀⟩
  exact ofReal_mul_volume_ball_le_volume_lt_inter_ball hκ hθ hτ hA
    (div_mul_cancel₀ _ (sub_pos.2 hG).ne') hR ha hLam hsymm hcont hu hbdry hsuper hf hx₀ hux₀

end PDE

end TauCeti
