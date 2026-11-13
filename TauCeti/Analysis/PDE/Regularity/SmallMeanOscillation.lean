/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeanOscillation
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.MeasureTheory.Integral.SharpMaximalFunction
import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction

/-!
# The `W^{1,p}` estimate for coefficients of small mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, and let `u ∈ H¹(ℝ^{n+1})` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G`,

that is `∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`. Suppose that `a` is bounded by `Λ`
and has small mean oscillation at every scale: on every ball `B` there is a constant matrix `A`,
uniformly elliptic with constants `0 < λ ≤ Λ`, whose mean deviation `⨍_B ‖a - A‖` from `a` is at
most `δ`. Both norms are operator norms of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`. For `A` the average of `a` over `B` this is the mean oscillation
of `a`. Uniformly elliptic coefficients are bounded by `Λ`
(`TauCeti.PDE.UniformlyEllipticOn.opNorm_matrixBilinearForm_le`), but ellipticity is only needed
for the frozen matrices `A`. This file proves the a priori estimate

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ` and is integrable, with `C` and the threshold `δ`
depending only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`). Only the
mean oscillation of `a` is controlled, not its modulus of continuity. Coefficients of vanishing
mean oscillation have small mean oscillation on small balls only; the passage from small balls to
all scales, by localization, is not treated here. The integrability of `∇u` is the a priori
integrability that the Fefferman–Stein inequality requires; it holds for instance when `∇u ∈ Lᵖ`
vanishes outside a bounded set, as for a cutoff of a local solution.

## The argument

The proof is Krylov's sharp function method, applied to Krylov's mean oscillation estimate for the
gradient in `TauCeti.Analysis.PDE.Regularity.MeanOscillation`.

* **One ball.** Let `x ∈ B_ρ = ball c ρ` and `r = κ ρ` with `κ ≥ 1`, and freeze the coefficients on
  `B_r` at the matrix `A` given by the hypothesis. The mean oscillation estimate, with the square
  mean oscillation of `∇u` on `B_r` bounded by `4 ⨍_{B_r} ‖∇u‖²`, and the bound `‖a - A‖ ≤ 2Λ`,
  bound the square mean oscillation of `∇u` on `B_ρ` by
  `κ⁻² ⨍_{B_r} ‖∇u‖² + κ^(n + 1) (⨍_{B_r} ‖G‖² + δ^(1/q') (⨍_{B_r} ‖∇u‖^(2q))^(1/q))`, up to
  constants, for Hölder conjugate exponents `q, q'`.
* **The sharp function.** Every average over `B_r ∋ x` is at most `2^(n + 1)` times the centred
  maximal function at `x` (`TauCeti.ofReal_setAverage_norm_rpow_le_two_pow_mul_maximalFunction`).
  Taking the supremum over the
  balls containing `x`, the square of the sharp maximal function of `∇u` is bounded pointwise by
  `κ⁻² M(‖∇u‖²) + κ^(n + 1) M(‖G‖²) + κ^(n + 1) δ^(1/q') M(‖∇u‖^(2q))^(1/q)`.
* **Absorption.** The Fefferman–Stein inequality for Euclidean balls
  (`TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow`) and the strong
  maximal inequality with the exponents `p / 2` and `p / (2q)`, where `1 < q < p / 2`
  (`TauCeti.lintegral_rpow_le_of_sq_le_maximalFunction`) turn this into
  `∫ ‖∇u‖^p ≤ (c₁ κ^(-p) + c₃ δ^(p/(2q'))) ∫ ‖∇u‖^p + c₂ ∫ ‖G‖^p`. Choosing first `κ` large and
  then `δ` small, the first term is absorbed, since `∫ ‖∇u‖^p` is finite.

The restriction `p > 2` comes from the `L²` mean oscillation estimate.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`: the
  `W^{1,p}` estimate for coefficients of small mean oscillation, `2 < p < ∞`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* S.-S. Byun, L. Wang, *Elliptic equations with BMO coefficients in Reifenberg domains*, Comm.
  Pure Appl. Math. **57** (2004), 1283–1310 (coefficients of small mean oscillation at every
  scale).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The constant of Krylov's mean oscillation estimate
`TauCeti.PDE.setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`.
-/
private noncomputable def oscConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)

/-- The constant of the decaying term in the one-ball estimate. -/
private noncomputable def decayConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  16 * oscConst n lam Lam

/-- The constant of the forcing term in the one-ball estimate. -/
private noncomputable def forcingConst (n : ℕ) (lam Lam : ℝ) : ℝ :=
  2 * (4 * oscConst n lam Lam + 2) / lam ^ 2

/-- The coefficient of the maximal function of `‖∇u‖²` in the one-ball estimate
`sq_setLAverage_enorm_gradient_sub_le`. -/
private noncomputable def decayCoeff (n : ℕ) (lam Lam κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1))

/-- The coefficient of the maximal function of `‖G‖²` in the one-ball estimate
`sq_setLAverage_enorm_gradient_sub_le`. -/
private noncomputable def forcingCoeff (n : ℕ) (lam Lam κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) * 2 ^ (n + 1))

/-- The coefficient of the `1/q`-th power of the maximal function of `‖∇u‖^(2q)` in the one-ball
estimate `sq_setLAverage_enorm_gradient_sub_le`; it carries the coefficient deviation `δ`. -/
private noncomputable def deviationCoeff (n : ℕ) (lam Lam κ q q' δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (forcingConst n lam Lam * κ ^ (n + 1) *
    ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹)

/-- **The mean oscillation estimate on one ball, in averages.** Let `u ∈ H¹(ℝ^{n+1})` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, let `κ ≥ 1`, and freeze the coefficients on `B_{κρ}` at an elliptic
constant matrix `A` whose mean deviation from `a` there is at most `δ`. Then the square mean
oscillation of `g = ∇u` on `B_ρ` is bounded by the averages over `B_{κρ}` of `‖g‖²`, of `‖G‖²` and
of `‖g‖^(2q)`, the first with the small factor `κ⁻²` and the last with the factor `δ^(1/q')`. -/
private theorem setAverage_norm_gradient_sub_sq_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' : ℝ} (hq : q.HolderConjugate q')
    (hqp : ENNReal.ofReal (2 * q) ≤ p)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam)
    (hδ : ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ) :
    ⨍ y in ball c ρ, ‖W1p.gradient u y - ⨍ z in ball c ρ, W1p.gradient u z‖ ^ 2 ≤
      decayConst n lam Lam / κ ^ 2 * (⨍ y in ball c (κ * ρ), ‖W1p.gradient u y‖ ^ 2) +
        forcingConst n lam Lam * κ ^ (n + 1) * ((⨍ y in ball c (κ * ρ), ‖G y‖ ^ 2) +
          ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ y in ball c (κ * ρ), ‖W1p.gradient u y‖ ^ (2 * q)) ^ q⁻¹) := by
  set r := κ * ρ with hr_def
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hr : 0 < r := mul_pos hκ0 hρ
  have hρr : ρ ≤ r := le_mul_of_one_le_left hρ.le hκ
  have hLam : 0 ≤ Lam := (norm_nonneg (matrixBilinearForm (a c))).trans (hbd c)
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- The coefficient deviation is at most `2Λ` on `B_r`.
  have haK : ∀ y ∈ ball c r, ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ 2 * Lam :=
    fun y _ =>
    (norm_sub_le (matrixBilinearForm (a y)) (matrixBilinearForm A)).trans (by
      linarith [hbd y,
        hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)])
  have hg2 := (hgp.restrict (ball c r)).mono_exponent h2p
  have hG2 := (hGp.restrict (ball c r)).mono_exponent h2p
  have hgq := (hgp.restrict (ball c r)).mono_exponent hqp
  -- Krylov's mean oscillation estimate, with `c = 0`.
  have key :=
    setAverage_ball_norm_gradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le
      hA ha.restrict haK (G := G) (c := 0) (u := u) (fun φ => by simpa using hu φ) (by simp)
      (by simpa using hG2) hq hgq hρ hρr
  simp only [sub_zero] at key
  rw [show ρ / r = κ⁻¹ by rw [hr_def]; field_simp, show r / ρ = κ by rw [hr_def]; field_simp]
    at key
  set g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  refine key.trans ?_
  unfold decayConst forcingConst oscConst
  set D := 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)
  rw [show 16 * D / κ ^ 2 = 4 * D * κ⁻¹ ^ 2 * 4 by field_simp; ring, mul_assoc _ (4 : ℝ)]
  -- `gcongr` compares the coefficient deviations by `hδ`; the remaining goals are proved below.
  gcongr
  -- The square mean oscillation on `B_r` is at most `4 ⨍_{B_r} ‖g‖²`.
  · simp only [setAverage_eq, smul_eq_mul]
    rw [mul_left_comm]
    gcongr
    simpa [setAverage_eq] using setIntegral_norm_sub_setAverage_sq_le measure_ball_lt_top.ne
      (hg2.integrableOn_of_subset one_le_two subset_rfl measure_ball_lt_top.ne)
      (hg2.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne 0)
  · exact Real.rpow_nonneg (average_nonneg fun y => by positivity) _
  · exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (average_nonneg fun y => norm_nonneg (matrixBilinearForm (a y) - matrixBilinearForm A))
  · exact inv_nonneg.2 hq.symm.pos.le

/-- **The mean oscillation estimate on one ball.** Under the hypotheses of
`setAverage_norm_gradient_sub_sq_le`, for `x ∈ B_ρ = ball c ρ` the square of the mean oscillation
of `g = ∇u` on `B_ρ` is bounded by the maximal functions at `x` of `‖g‖²`, of `‖G‖²` and of
`‖g‖^(2q)`, the first with the small factor `κ⁻²` and the last with the factor `δ^(1/q')`: every
average over `B_{κρ} ∋ x` is at most `2^(n + 1)` times the centred maximal function at `x`. -/
private theorem sq_setLAverage_enorm_gradient_sub_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' : ℝ} (hq : q.HolderConjugate q')
    (hqp : ENNReal.ofReal (2 * q) ≤ p)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {c x : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ) (hx : x ∈ ball c ρ)
    (hA : UniformlyEllipticOn (ball c (κ * ρ)) (fun _ => A) lam Lam)
    (hδ : ⨍ y in ball c (κ * ρ), ‖matrixBilinearForm (a y) - matrixBilinearForm A‖ ≤ δ) :
    (⨍⁻ y in ball c ρ, ‖W1p.gradient u y - ⨍ z in ball c ρ, W1p.gradient u z‖ₑ) ^ 2 ≤
      decayCoeff n lam Lam κ * maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ 2) x +
        forcingCoeff n lam Lam κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        deviationCoeff n lam Lam κ q q' δ *
          maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
  have h1 := setAverage_norm_gradient_sub_sq_le ha hbd hu h2p hgp hGp hq hqp hρ hκ hA hδ
  set g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set r := κ * ρ
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hxr : x ∈ ball c r := ball_subset_ball (le_mul_of_one_le_left hρ.le hκ) hx
  have hq1 : 0 ≤ q⁻¹ := inv_nonneg.2 hq.pos.le
  -- Every average over `B_r ∋ x` is at most `2^(n + 1)` times the centred maximal function at `x`.
  have hM : ∀ (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) {k : ℝ},
      0 ≤ k → ENNReal.ofReal (⨍ y in ball c r, ‖h y‖ ^ k) ≤
        ENNReal.ofReal (2 ^ (n + 1)) * maximalFunction volume (fun y => ‖h y‖ₑ ^ k) x :=
    fun h k hk => by
      simpa only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow zero_le_two,
        ENNReal.ofReal_ofNat] using
        ofReal_setAverage_norm_rpow_le_two_pow_mul_maximalFunction volume hk hxr
  have hE1 := hM g zero_le_two
  have hE2 := hM G zero_le_two
  simp only [Real.rpow_two, ENNReal.rpow_two] at hE1 hE2
  have hE3 : ENNReal.ofReal ((⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹) ≤
      ENNReal.ofReal ((2 ^ (n + 1)) ^ q⁻¹) *
        maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (average_nonneg fun y => by positivity) hq1,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq1, ← ENNReal.mul_rpow_of_nonneg _ _ hq1]
    gcongr
    exact hM g (by linarith [hq.pos])
  -- Jensen's inequality on `B_ρ`.
  have : IsFiniteMeasure (volume.restrict (ball c ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hjensen := sq_setLAverage_enorm_le_ofReal_setAverage_norm_sq
    (h := fun y => g y - ⨍ z in ball c ρ, g z)
    (((hgp.restrict (ball c ρ)).mono_exponent h2p).integrableOn_norm_sub_sq_of_subset subset_rfl
      measure_ball_lt_top.ne _)
  have hX : 0 ≤ ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ := by
    have hLam : 0 ≤ Lam := (norm_nonneg (matrixBilinearForm (a c))).trans (hbd c)
    exact Real.rpow_nonneg (mul_nonneg (by positivity)
      ((average_nonneg fun y =>
        norm_nonneg (matrixBilinearForm (a y) - matrixBilinearForm A)).trans hδ)) _
  have hd : 0 ≤ decayConst n lam Lam / κ ^ 2 := by unfold decayConst oscConst; positivity
  have hF : 0 ≤ forcingConst n lam Lam * κ ^ (n + 1) :=
    mul_nonneg (by unfold forcingConst oscConst; positivity) (pow_nonneg hκ0.le _)
  -- Each term of the real bound `h1`, multiplied by its coefficient, passes to `ℝ≥0∞`.
  have hmul : ∀ {e K I : ℝ} {M : ℝ≥0∞}, 0 ≤ e → ENNReal.ofReal I ≤ ENNReal.ofReal K * M →
      ENNReal.ofReal (e * I) ≤ ENNReal.ofReal (e * K) * M := fun he h => by
    rw [ENNReal.ofReal_mul he, ENNReal.ofReal_mul he, mul_assoc]
    gcongr
  unfold decayCoeff forcingCoeff deviationCoeff
  refine hjensen.trans ((ENNReal.ofReal_le_ofReal (h1.trans_eq (by ring))).trans
    (ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_add_le.trans
      (add_le_add (hmul hd hE1) (hmul hF hE2))) (hmul (mul_nonneg hF hX) hE3))))

/-- **Krylov's pointwise estimate for the sharp maximal function of the gradient.** Under the
hypotheses of the main theorem, for every `κ ≥ 1` the square of the sharp maximal function of
`g = ∇u` is bounded pointwise by the maximal functions of `‖g‖²`, of `‖G‖²` and of `‖g‖^(2q)`. -/
private theorem sq_sharpMaximalFunction_gradient_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {δ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' : ℝ} (hq : q.HolderConjugate q')
    (hqp : ENNReal.ofReal (2 * q) ≤ p) {κ : ℝ} (hκ : 1 ≤ κ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sharpMaximalFunction volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x ^ 2 ≤
      decayCoeff n lam Lam κ * maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ 2) x +
        forcingCoeff n lam Lam κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        deviationCoeff n lam Lam κ q q' δ *
          maximalFunction volume (fun y => ‖W1p.gradient u y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
  rw [← ENNReal.rpow_two, ← ENNReal.le_rpow_inv_iff two_pos]
  refine sharpMaximalFunction_le fun c ρ hx => ?_
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.1 hx)
  obtain ⟨A, hA, hδ⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  rw [ENNReal.le_rpow_inv_iff two_pos, ENNReal.rpow_two]
  exact sq_setLAverage_enorm_gradient_sub_le ha hbd hu h2p hgp hGp hq hqp hρ hκ hx hA hδ

/-- The estimate before absorption: `∫ ‖∇u‖^s` is bounded by the Fefferman–Stein constant times
the integrated pointwise bound for the sharp maximal function, in which `∫ ‖∇u‖^s` reappears with
the factors `κ⁻²` and `δ^(1/q')`. -/
private theorem lintegral_enorm_gradient_rpow_le
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {δ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (h2p : 2 ≤ p)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' s : ℝ} (hqq : q.HolderConjugate q')
    (hqs : 2 * q < s) (hqp : ENNReal.ofReal (2 * q) ≤ p) {κ : ℝ} (hκ : 1 ≤ κ) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s ≤
      CFS * ∫⁻ x, sharpMaximalFunction volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x ^ s) :
    ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s ≤ CFS * (2 ^ (s / 2 - 1) * (2 ^ (s / 2 - 1) *
        (decayCoeff n lam Lam κ ^ (s / 2) *
            (maximalFunctionConst (n + 1) (s / 2) * ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s) +
          forcingCoeff n lam Lam κ ^ (s / 2) *
            (maximalFunctionConst (n + 1) (s / 2) * ∫⁻ x, ‖G x‖ₑ ^ s)) +
      deviationCoeff n lam Lam κ q q' δ ^ (s / 2) *
        (maximalFunctionConst (n + 1) (s / 2 / q) * ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s))) := by
  have hpt := sq_sharpMaximalFunction_gradient_le ha hbd hosc hu h2p hgp hGp hqq hqp hκ
  generalize (⇑(W1p.gradient u) : EuclideanSpace ℝ (Fin (n + 1)) →
    EuclideanSpace ℝ (Fin (n + 1))) = g at hgp hpt hFS ⊢
  have hgm : AEStronglyMeasurable g volume := hgp.aestronglyMeasurable
  have hsq : ∀ (y : ℝ≥0∞) (e : ℝ), e * (s / e) = s → (y ^ e) ^ (s / e) = y ^ s :=
    fun y e he => by rw [← ENNReal.rpow_mul, he]
  have hy2 : ∀ y : ℝ≥0∞, (y ^ 2) ^ (s / 2) = y ^ s := fun y => by
    rw [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    exact hsq y 2 (by ring)
  have hq0 : q ≠ 0 := hqq.pos.ne'
  have hy3 : ∀ y : ℝ≥0∞, (y ^ (2 * q)) ^ (s / 2 / q) = y ^ s := fun y => by
    rw [div_div]; exact hsq y (2 * q) (by field_simp)
  have hbound := lintegral_rpow_le_of_sq_le_maximalFunction (g := fun x =>
      sharpMaximalFunction volume g x) volume
    (h₁ := fun y => ‖g y‖ₑ ^ 2) (h₂ := fun y => ‖G y‖ₑ ^ 2) (h₃ := fun y => ‖g y‖ₑ ^ (2 * q))
    (hgm.eNorm.pow_const 2) (hGp.aestronglyMeasurable.eNorm.pow_const 2)
    (hgm.eNorm.pow_const _) hqq.lt hqs hpt
  simp only [hy2, hy3, finrank_euclideanSpace, Fintype.card_fin] at hbound
  exact hFS.trans (mul_le_mul_right hbound _)

/-- The choice of the parameters: for finite `K₁, K₃`, there are `κ ≥ 1` and `δ > 0` making the
decaying term and the coefficient term of the estimate before absorption at most `1/4`. -/
private theorem exists_one_le_and_pos_of_ne_top (lam Lam : ℝ) {q q' s : ℝ} (hq' : 0 < q')
    (hs : 0 < s) {K₁ K₃ : ℝ≥0∞} (hK₁ : K₁ ≠ ∞) (hK₃ : K₃ ≠ ∞) :
    ∃ κ : ℝ, 1 ≤ κ ∧
      K₁ * decayCoeff n lam Lam κ ^ (s / 2) ≤ 2⁻¹ / 2 ∧
      ∃ δ : ℝ, 0 < δ ∧ K₃ * deviationCoeff n lam Lam κ q q' δ ^ (s / 2) ≤ 2⁻¹ / 2 := by
  have hquarter : (0 : ℝ≥0∞) < 2⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  have hs2 : 0 < s / 2 := by linarith
  have h1 : Tendsto (fun κ : ℝ => decayConst n lam Lam / κ ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h0 := h1.mul_const ((2 : ℝ) ^ (n + 1))
  rw [zero_mul] at h0
  have h0' : Tendsto (fun κ : ℝ => ENNReal.ofReal (decayConst n lam Lam / κ ^ 2 * 2 ^ (n + 1)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h0
  obtain ⟨κ, hκ, hκ1⟩ := ((eventually_ge_atTop 1).and
    (((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK₁ hs2).comp h0').eventually
      (gt_mem_nhds hquarter))).exists
  refine ⟨κ, hκ, hκ1.le, ?_⟩
  have hq'' : 0 < q'⁻¹ := inv_pos.2 hq'
  set c₃ : ℝ → ℝ := fun δ => forcingConst n lam Lam * κ ^ (n + 1) *
    ((2 * Lam) ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹
  have hc : ContinuousAt c₃ 0 := by
    refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hq''.le)).comp (by fun_prop)
  have hc0' : Tendsto c₃ (𝓝[>] 0) (𝓝 0) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hc0 : c₃ 0 = 0 := by simp [c₃, Real.zero_rpow hq''.ne']
    rwa [hc0] at h
  have hc0'' : Tendsto (fun δ => ENNReal.ofReal (c₃ δ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hc0'
  obtain ⟨δ, hδ1, hδ⟩ := ((((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK₃ hs2).comp
    hc0'').eventually (gt_mem_nhds hquarter)).and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ, hδ1.le⟩

/-- The estimate for fixed parameters `κ` and `δ` small enough for the absorption. -/
private theorem eLpNorm_gradient_le_of_le_quarter
    {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {δ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
        ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      p volume)
    (hGp : MemLp G p volume) {q q' s : ℝ} (hs_def : s = p.toReal)
    (hqq : q.HolderConjugate q') (hqs : 2 * q < s) {κ : ℝ} (hκ : 1 ≤ κ) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s ≤
      CFS * ∫⁻ x, sharpMaximalFunction volume
        (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x ^ s)
    (hκ1 : CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2) *
        decayCoeff n lam Lam κ ^ (s / 2) ≤ 2⁻¹ / 2)
    (hδ1 : CFS * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2 / q) *
        deviationCoeff n lam Lam κ q q' δ ^ (s / 2) ≤ 2⁻¹ / 2) :
    eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1))) p volume ≤
      (CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * forcingCoeff n lam Lam κ ^ (s / 2) *
        maximalFunctionConst (n + 1) (s / 2) * 2) ^ (1 / s) * eLpNorm G p volume := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans hp).ne'
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.2 (by linarith [hqq.lt])
  have hqp : ENNReal.ofReal (2 * q) ≤ p := by
    rw [← ENNReal.ofReal_toReal hp_top, ← hs_def]
    exact ENNReal.ofReal_le_ofReal hqs.le
  have key := lintegral_enorm_gradient_rpow_le ha hbd hosc hu hp.le hgp hGp hqq hqs hqp hκ hFS
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hgp.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hGp.aestronglyMeasurable, ← hs_def,
    ← ENNReal.mul_rpow_of_nonneg _ _ hs1]
  have hI := (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp_top hgp.eLpNorm_lt_top).ne
  rw [← hs_def] at hI
  refine ENNReal.rpow_le_rpow ((ENNReal.le_mul_two_of_le_add_div_two hI ?_).trans_eq
    (mul_right_comm _ _ _)) hs1
  -- The terms with the factors `κ⁻²` and `δ^(1/q')` are at most a quarter of `I = ∫ ‖∇u‖^s` each,
  -- so together they are absorbed.
  set I := ∫⁻ x, ‖W1p.gradient u x‖ₑ ^ s
  set J := ∫⁻ x, ‖G x‖ₑ ^ s
  calc I ≤ CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2) *
          decayCoeff n lam Lam κ ^ (s / 2) * I +
        CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * forcingCoeff n lam Lam κ ^ (s / 2) *
          maximalFunctionConst (n + 1) (s / 2) * J +
        CFS * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2 / q) *
          deviationCoeff n lam Lam κ q q' δ ^ (s / 2) * I :=
        key.trans_eq (by ring)
    _ ≤ 2⁻¹ / 2 * I +
        CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * forcingCoeff n lam Lam κ ^ (s / 2) *
          maximalFunctionConst (n + 1) (s / 2) * J +
        2⁻¹ / 2 * I := by
        gcongr
    _ = _ := by
        rw [add_right_comm, ← add_mul, ENNReal.add_halves, add_comm, ENNReal.div_eq_inv_mul]

/-- **The `W^{1,p}` estimate for coefficients of small mean oscillation.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ`, such
that on every ball `B` some constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of the attached bilinear
forms. Let `u ∈ H¹(ℝ^{n+1})` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ Lᵖ`, and let `∇u` be integrable
and in `Lᵖ`. Then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

Neither continuity nor symmetry of `a` is assumed. -/
theorem exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le {p : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          Integrable
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p volume →
          MemLp G p volume →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) p volume ≤ C * eLpNorm G p volume := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = p.toReal := ⟨_, rfl⟩
  have hs : 2 < s := by
    rw [hs_def]
    simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp_top).2 hp
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = (1 + s / 2) / 2 := ⟨_, rfl⟩
  have hq : 1 < q := by rw [hq_def]; linarith
  have hqs : 2 * q < s := by rw [hq_def]; linarith
  obtain ⟨q', hqq⟩ : ∃ q' : ℝ, q.HolderConjugate q' :=
    ⟨_, Real.HolderConjugate.conjExponent hq⟩
  obtain ⟨CFS, hFS⟩ := exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow
    (ι := Fin (n + 1)) (show 1 < s by linarith)
  have hcM := maximalFunctionConst_ne_top (n + 1)
  have h2 : (2 : ℝ≥0∞) ^ (s / 2 - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  obtain ⟨κ, hκ, hκ1, δ, hδ, hδ1⟩ := exists_one_le_and_pos_of_ne_top (n := n) lam Lam (q := q)
    hqq.symm.pos (by linarith : 0 < s)
    (K₁ := (CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2))
    (K₃ := (CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2 / q))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
      (hcM _))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) (hcM _))
  set C : ℝ≥0∞ := ((CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) *
    forcingCoeff n lam Lam κ ^ (s / 2) * maximalFunctionConst (n + 1) (s / 2) * 2) ^ (1 / s)
  have hK₂ : C ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (by linarith)) (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)) (hcM _))
      ENNReal.ofNat_ne_top)
  refine ⟨C.toNNReal, δ, hδ, fun {a} ha hbd hosc u G hu hint hgp hGp => ?_⟩
  rw [ENNReal.coe_toNNReal hK₂]
  exact eLpNorm_gradient_le_of_le_quarter ha hbd hosc hu hp hp_top hgp hGp hs_def hqq hqs hκ
    (hFS _ hint) hκ1 hδ1

end PDE

end TauCeti
