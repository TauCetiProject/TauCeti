/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeanOscillation
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
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
mean oscillation of `a` is controlled, not its modulus of continuity. The integrability of `∇u` is
the a priori integrability that the Fefferman–Stein inequality requires; it holds for instance when
`∇u ∈ Lᵖ` vanishes outside a bounded set, as for a cutoff of a local solution.

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

## Small mean oscillation below a radius

Coefficients of vanishing mean oscillation have small mean oscillation only on balls of radius at
most some `r₀`. The estimate still holds for them, with the same constants, for every `u` whose
gradient vanishes outside a ball `B(x₀, r₀ / 4)`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero`).
Such a `u` solves the same equation with `a` replaced by any field agreeing with `a` on
`B(x₀, r₀ / 4)`, and with `R = r₀ / 4` the field `b = ψ a + (1 - ψ) A₀` has small mean oscillation
at every scale (`TauCeti.PDE.exists_eqOn_ball_and_forall_setAverage_le`). Here `ψ` is a cutoff
equal to one on `B(x₀, R)`, vanishing outside `B(x₀, 2R)` and `2 / R`-Lipschitz, and `A₀` is a
frozen matrix of `B(x₀, 4R)`.

* On a ball `B` of radius `r ≥ R`, the field `b` stays close to `A₀`: the deviation `ψ ‖a - A₀‖`
  lives on `B(x₀, 2R)`, and its integral is at most `δ |B(x₀, 4R)| ≤ 4^(n + 1) δ |B|`.
* On a ball `B = B(c, r)` with `r < R` far from `x₀`, the field `b` is `A₀`.
* On a ball `B = B(c, r)` with `r < R` near `x₀`, freeze `b` at `ψ(c) A + (1 - ψ(c)) A₀`, where `A`
  is a frozen matrix of `B`. The error is at most `δ + (2 r / R) ‖A - A₀‖`, and frozen matrices of
  the concentric balls `B(c, 2ᵏ r)` drift by `O(δ)` per doubling, so `‖A - A₀‖ = O(log(R / r) δ)`.
  Since `(r / R) log(R / r)` is bounded, the error is `O(δ)`.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`: the
  `W^{1,p}` estimate for coefficients of small mean oscillation, `2 < p < ∞`.
* `TauCeti.PDE.exists_eqOn_ball_and_forall_setAverage_le`: a coefficient field of small mean
  oscillation below a radius agrees near a ball with one of small mean oscillation at every scale.
* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero`:
  the `W^{1,p}` estimate for coefficients of small mean oscillation below a radius, for functions
  whose gradient vanishes outside a small ball.

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

/-! ### Localization to small balls -/

section Localization

variable {F : Type*} [NormedAddCommGroup F]

/-- The ratio of the volumes of two balls in `ℝ^{n+1}` is the `(n + 1)`-th power of the ratio of
their radii. -/
private theorem measureReal_ball_div_measureReal_ball (c c' : EuclideanSpace ℝ (Fin (n + 1)))
    {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    volume.real (ball c' r') / volume.real (ball c r) = (r' / r) ^ (n + 1) := by
  have h0 : (volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(measure_ball_pos _ _ one_pos).ne', measure_ball_lt_top.ne⟩
  simp only [measureReal_def, Measure.addHaar_ball_of_pos _ _ hr,
    Measure.addHaar_ball_of_pos _ _ hr', ENNReal.toReal_mul, finrank_euclideanSpace_fin,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), ENNReal.toReal_ofReal (pow_nonneg hr'.le _)]
  rw [div_pow]
  field_simp

/-- A bounded measurable field `β`, multiplied by a bounded measurable weight `w`, stays within
integrable distance of any constant on every ball. -/
private theorem integrableOn_mul_norm_sub {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : AEStronglyMeasurable β volume) {Lam : ℝ} (hbd : ∀ x, ‖β x‖ ≤ Lam)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hw : AEStronglyMeasurable w volume)
    (hw1 : ∀ x, |w x| ≤ 1) (P : F) (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    IntegrableOn (fun x => w x * ‖β x - P‖) (ball c r) := by
  refine Measure.integrableOn_of_bounded (M := Lam + ‖P‖) measure_ball_lt_top.ne
    (hw.mul (hβ.sub aestronglyMeasurable_const).norm) (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_norm]
  calc |w x| * ‖β x - P‖ ≤ 1 * (Lam + ‖P‖) :=
        mul_le_mul (hw1 x) ((norm_sub_le _ _).trans (by linarith [hbd x])) (norm_nonneg _)
          zero_le_one
    _ = Lam + ‖P‖ := one_mul _

/-- The case `w = 1` of `integrableOn_mul_norm_sub`. -/
private theorem integrableOn_norm_sub {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : AEStronglyMeasurable β volume) {Lam : ℝ} (hbd : ∀ x, ‖β x‖ ≤ Lam) (P : F)
    (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ) :
    IntegrableOn (fun x => ‖β x - P‖) (ball c r) := by
  simpa using integrableOn_mul_norm_sub (w := fun _ => 1) hβ hbd aestronglyMeasurable_const
    (by simp) P c r

/-- **Drift of approximating constants along concentric balls.** If on each ball `B(c, 2ᵏ r)`,
`k ≤ m`, the constant `P k` approximates `β` with mean deviation at most `δ`, then `P 0` and `P m`
differ by at most `m (1 + 2^(n + 1)) δ`. -/
private theorem norm_sub_le_of_forall_setAverage_le {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : AEStronglyMeasurable β volume) {Lam : ℝ} (hbd : ∀ x, ‖β x‖ ≤ Lam)
    {c : EuclideanSpace ℝ (Fin (n + 1))} {r δ : ℝ} (hr : 0 < r) {P : ℕ → F} :
    ∀ m : ℕ, (∀ k ≤ m, ⨍ x in ball c (2 ^ k * r), ‖β x - P k‖ ≤ δ) →
      ‖P 0 - P m‖ ≤ m * ((1 + 2 ^ (n + 1)) * δ)
  | 0, _ => by simp
  | m + 1, hP => by
    have ih := norm_sub_le_of_forall_setAverage_le hβ hbd hr m
      fun k hk => hP k (hk.trans m.le_succ)
    have hrm : 0 < 2 ^ m * r := by positivity
    have hstep := norm_sub_le_setAverage_add_div_mul_setAverage_of_subset
      (s := ball c (2 ^ m * r)) (t := ball c (2 ^ (m + 1) * r))
      (ball_subset_ball (by rw [pow_succ]; nlinarith)) (measure_ball_pos _ _ hrm).ne'
      measure_ball_lt_top.ne (integrableOn_norm_sub hβ hbd (P m) c _)
      (integrableOn_norm_sub hβ hbd (P (m + 1)) c _)
    rw [measureReal_ball_div_measureReal_ball _ _ hrm (by positivity),
      show 2 ^ (m + 1) * r / (2 ^ m * r) = 2 by field_simp; ring] at hstep
    calc ‖P 0 - P (m + 1)‖ ≤ ‖P 0 - P m‖ + ‖P m - P (m + 1)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ m * ((1 + 2 ^ (n + 1)) * δ) + (δ + 2 ^ (n + 1) * δ) := by
          gcongr
          exact hstep.trans (add_le_add (hP m m.le_succ)
            (mul_le_mul_of_nonneg_left (hP (m + 1) le_rfl) (by positivity)))
      _ = ((m + 1 : ℕ) : ℝ) * ((1 + 2 ^ (n + 1)) * δ) := by push_cast; ring

/-- **The cutoff field on a large ball.** Let `ψ ∈ [0, 1]` vanish outside `B(x₀, 2R)`, and let the
constant `P₀` approximate `β` on `B(x₀, 4R)` with mean deviation at most `δ`. On every ball of
radius `r ≥ R`, the field `ψ β + (1 - ψ) P₀` then deviates from `P₀` on average by at most
`4^(n + 1) δ`. -/
private theorem setAverage_norm_cutoff_sub_le_of_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : AEStronglyMeasurable β volume) {Lam : ℝ} (hbd : ∀ x, ‖β x‖ ≤ Lam)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψm : Continuous ψ) (hψ : ∀ x, ψ x ∈ Icc 0 1)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {R r δ : ℝ}
    (hψ0 : ∀ x, 2 * R ≤ dist x x₀ → ψ x = 0) (hR : 0 < R) (hRr : R ≤ r) {P₀ : F}
    (hδ : ⨍ x in ball x₀ (4 * R), ‖β x - P₀‖ ≤ δ) :
    ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - P₀‖ ≤ 4 ^ (n + 1) * δ := by
  have hr : 0 < r := hR.trans_le hRr
  have hψ1 : ∀ x, |ψ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hψ x).1], (hψ x).2⟩
  have hpt : ∀ x, ‖ψ x • β x + (1 - ψ x) • P₀ - P₀‖ = ψ x * ‖β x - P₀‖ := fun x => by
    rw [show ψ x • β x + (1 - ψ x) • P₀ - P₀ = ψ x • (β x - P₀) by module, norm_smul,
      Real.norm_of_nonneg (hψ x).1]
  have hint := integrableOn_mul_norm_sub hβ hbd hψm.aestronglyMeasurable hψ1 P₀ x₀ (4 * R)
  -- The integrand vanishes off `B(x₀, 2R)`, so its integral over `B(c, r)` is at most its
  -- integral over `B(x₀, 4R)`.
  have hI : ∫ x in ball c r, ψ x * ‖β x - P₀‖ ≤ ∫ x in ball x₀ (4 * R), ‖β x - P₀‖ := by
    calc ∫ x in ball c r, ψ x * ‖β x - P₀‖
        = ∫ x in ball c r, (ball x₀ (4 * R)).indicator (fun x => ψ x * ‖β x - P₀‖) x := by
          refine integral_congr_ae (.of_forall fun x => ?_)
          dsimp only
          by_cases hx : x ∈ ball x₀ (4 * R)
          · rw [indicator_of_mem hx]
          · rw [indicator_of_notMem hx, hψ0 x (by rw [mem_ball, not_lt] at hx; linarith),
              zero_mul]
      _ = ∫ x in ball c r ∩ ball x₀ (4 * R), ψ x * ‖β x - P₀‖ := setIntegral_indicator
          measurableSet_ball
      _ ≤ ∫ x in ball x₀ (4 * R), ψ x * ‖β x - P₀‖ :=
          setIntegral_mono_set hint (.of_forall fun x => mul_nonneg (hψ x).1 (norm_nonneg _))
            (.of_forall inter_subset_right)
      _ ≤ _ := setIntegral_mono_on hint (integrableOn_norm_sub hβ hbd P₀ x₀ _) measurableSet_ball
          fun x _ => mul_le_of_le_one_left (norm_nonneg _) (hψ x).2
  have hvol := measureReal_ball_div_measureReal_ball c x₀ hr (by positivity : 0 < 4 * R)
  have hvol0 : 0 < volume.real (ball c r) := ENNReal.toReal_pos (measure_ball_pos _ _ hr).ne'
    measure_ball_lt_top.ne
  simp_rw [hpt]
  simp only [setAverage_eq, smul_eq_mul] at hδ ⊢
  calc (volume.real (ball c r))⁻¹ * ∫ x in ball c r, ψ x * ‖β x - P₀‖
      ≤ (volume.real (ball c r))⁻¹ * ∫ x in ball x₀ (4 * R), ‖β x - P₀‖ := by gcongr
    _ = (4 * R / r) ^ (n + 1) * ((volume.real (ball x₀ (4 * R)))⁻¹ *
          ∫ x in ball x₀ (4 * R), ‖β x - P₀‖) := by
        have : volume.real (ball x₀ (4 * R)) ≠ 0 :=
          (ENNReal.toReal_pos (measure_ball_pos _ _ (by positivity)).ne'
            measure_ball_lt_top.ne).ne'
        rw [← hvol]
        field_simp
    _ ≤ 4 ^ (n + 1) * δ := by
        gcongr
        rw [div_le_iff₀ hr]
        linarith

/-- **The cutoff field on a small ball.** Let `ψ ∈ [0, 1]` be `K`-Lipschitz, and let the constant
`P` approximate `β` on `B(c, r)` with mean deviation at most `δ`. Then on `B(c, r)` the field
`ψ β + (1 - ψ) P₀` deviates on average from the constant `ψ(c) P + (1 - ψ(c)) P₀` by at most
`δ + K r ‖P - P₀‖`. -/
private theorem setAverage_norm_cutoff_sub_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hβ : AEStronglyMeasurable β volume) {Lam : ℝ} (hbd : ∀ x, ‖β x‖ ≤ Lam)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψm : Continuous ψ) (hψ : ∀ x, ψ x ∈ Icc 0 1)
    {K : ℝ≥0} (hψlip : LipschitzWith K ψ) {c : EuclideanSpace ℝ (Fin (n + 1))}
    {r δ : ℝ} (hr : 0 < r) {P₀ P : F} (hδ : ⨍ x in ball c r, ‖β x - P‖ ≤ δ) :
    ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖ ≤
      δ + K * r * ‖P - P₀‖ := by
  have hvol0 : 0 < volume.real (ball c r) := ENNReal.toReal_pos (measure_ball_pos _ _ hr).ne'
    measure_ball_lt_top.ne
  have hint := integrableOn_norm_sub hβ hbd P c r
  have hpt : ∀ x ∈ ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖ ≤
      ‖β x - P‖ + K * r * ‖P - P₀‖ := fun x hx => by
    rw [show ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀) =
      ψ x • (β x - P) + (ψ x - ψ c) • (P - P₀) by module]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg (hψ x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψ x).2
    · rw [norm_smul, ← dist_eq_norm]
      gcongr
      exact (hψlip.dist_le_mul x c).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hx).le K.coe_nonneg)
  have hmeas : AEStronglyMeasurable
      (fun x => ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖) volume :=
    (((hψm.aestronglyMeasurable.smul hβ).add
      ((continuous_const.sub hψm).aestronglyMeasurable.smul_const P₀)).sub
        aestronglyMeasurable_const).norm
  have hsum : IntegrableOn (fun x => ‖β x - P‖ + K * r * ‖P - P₀‖) (ball c r) :=
    hint.add (integrableOn_const measure_ball_lt_top.ne)
  have hint' : IntegrableOn
      (fun x => ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖) (ball c r) :=
    hsum.mono' hmeas.restrict
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun x hx => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt x hx))
  simp only [setAverage_eq, smul_eq_mul] at hδ ⊢
  calc _ ≤ (volume.real (ball c r))⁻¹ * ∫ x in ball c r, (‖β x - P‖ + K * r * ‖P - P₀‖) :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hint' hsum measurableSet_ball hpt)
          (inv_nonneg.2 hvol0.le)
    _ = (volume.real (ball c r))⁻¹ * (∫ x in ball c r, ‖β x - P‖) + K * r * ‖P - P₀‖ := by
        rw [integral_add hint (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
          smul_eq_mul]
        field_simp
    _ ≤ _ := by gcongr

/-- A convex combination of two vectors of norm at most `L` has norm at most `L`. -/
private theorem norm_smul_add_one_sub_smul_le [NormedSpace ℝ F] {t L : ℝ} (ht : t ∈ Icc 0 1)
    {P P' : F} (hP : ‖P‖ ≤ L) (hP' : ‖P'‖ ≤ L) : ‖t • P + (1 - t) • P'‖ ≤ L := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.1, Real.norm_of_nonneg (sub_nonneg.2 ht.2)]
  nlinarith [ht.1, ht.2]

/-- **The cutoff field on a ball where the cutoff vanishes** is the constant `P₀`. -/
private theorem setAverage_norm_cutoff_sub_eq_zero [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {c : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hψ0 : ∀ x ∈ ball c r, ψ x = 0) (P₀ : F) :
    ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - P₀‖ = 0 := by
  rw [setAverage_eq, setIntegral_congr_fun measurableSet_ball (g := fun _ => (0 : ℝ))
    fun x hx => by simp [hψ0 x hx]]
  simp

/-- **Approximating constants on small balls near the centre.** Let the constants satisfying a
property `Q c r` approximate `β` on every ball `B(c, r)` of radius at most `r₀` with mean deviation
at most `δ`, and let `P₀` approximate `β` on `B(x₀, 4R)`, `R ≤ r₀`. Then every ball `B(c, r)` with
`r ≤ R` and `c ∈ B(x₀, 3R)` has such a constant `P` with
`‖P - P₀‖ ≤ (R / r) (2 + 2^(n + 1) + 8^(n + 1)) δ`: the approximating constants drift at most
logarithmically in `R / r` along the dyadic balls `B(c, 2ᵏ r)`. -/
private theorem exists_setAverage_le_and_div_mul_norm_sub_le
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : AEStronglyMeasurable β volume) {Lam : ℝ}
    (hbd : ∀ x, ‖β x‖ ≤ Lam) {Q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → F → Prop} {δ r₀ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {R r : ℝ} {P₀ : F}
    (hδ₀ : ⨍ x in ball x₀ (4 * R), ‖β x - P₀‖ ≤ δ) (hRr₀ : R ≤ r₀) (hr : 0 < r) (hrR : r ≤ R)
    (hc : dist c x₀ < 3 * R) :
    ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ ∧
      r / R * ‖P - P₀‖ ≤ (2 + 2 ^ (n + 1) + 8 ^ (n + 1)) * δ := by
  have hR : 0 < R := hr.trans_le hrR
  have hδ : 0 ≤ δ := (average_nonneg fun _ => norm_nonneg _).trans hδ₀
  -- `2ᵐ r ≤ R < 2ᵐ⁺¹ r`.
  obtain ⟨m, hm, hm'⟩ := exists_nat_pow_near ((one_le_div hr).2 hrR) one_lt_two
  rw [le_div_iff₀ hr] at hm
  rw [div_lt_iff₀ hr] at hm'
  have hfam : ∀ k : ℕ, ∃ P, k ≤ m →
      Q c (2 ^ k * r) P ∧ ⨍ x in ball c (2 ^ k * r), ‖β x - P‖ ≤ δ := by
    intro k
    by_cases hk : k ≤ m
    · obtain ⟨P, hP⟩ := hosc c (2 ^ k * r) (by positivity)
        (le_trans (by gcongr; norm_num) (hm.trans hRr₀))
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose P hP using hfam
  have hchain := norm_sub_le_of_forall_setAverage_le hβ hbd hr m fun k hk => (hP k hk).2
  -- The last dyadic ball `B(c, 2ᵐ r)` lies in `B(x₀, 4R)`, with volume ratio below `8^(n + 1)`.
  have hmr : 0 < 2 ^ m * r := by positivity
  have hlast := norm_sub_le_setAverage_add_div_mul_setAverage_of_subset
    (s := ball c (2 ^ m * r)) (t := ball x₀ (4 * R))
    (ball_subset_ball' (by linarith)) (measure_ball_pos _ _ hmr).ne' measure_ball_lt_top.ne
    (integrableOn_norm_sub hβ hbd (P m) c _) (integrableOn_norm_sub hβ hbd P₀ x₀ _)
  rw [measureReal_ball_div_measureReal_ball _ _ hmr (by positivity)] at hlast
  have hratio : (4 * R / (2 ^ m * r)) ^ (n + 1) ≤ 8 ^ (n + 1) := by
    gcongr
    rw [div_le_iff₀ hmr]
    linarith [show (2 : ℝ) ^ (m + 1) * r = 2 * (2 ^ m * r) by ring]
  have hlast' : ‖P m - P₀‖ ≤ (1 + 8 ^ (n + 1)) * δ :=
    hlast.trans ((add_le_add (hP m le_rfl).2 (mul_le_mul hratio hδ₀
      (average_nonneg fun _ => norm_nonneg _) (by positivity))).trans_eq (by ring))
  -- `(r / R) m ≤ m / 2ᵐ ≤ 1` and `r / R ≤ 1`.
  have hrR1 : r / R ≤ 1 := (div_le_one hR).2 hrR
  have hrRm : r / R * m ≤ 1 := by
    have h2m : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self.le
    calc r / R * m ≤ r / R * 2 ^ m := by gcongr
      _ = 2 ^ m * r / R := by ring
      _ ≤ 1 := (div_le_one hR).2 hm
  refine ⟨P 0, by simpa using (hP 0 m.zero_le).1, by simpa using (hP 0 m.zero_le).2, ?_⟩
  calc r / R * ‖P 0 - P₀‖ ≤ r / R * (‖P 0 - P m‖ + ‖P m - P₀‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ r / R * (m * ((1 + 2 ^ (n + 1)) * δ) + (1 + 8 ^ (n + 1)) * δ) := by gcongr
    _ = r / R * m * ((1 + 2 ^ (n + 1)) * δ) + r / R * ((1 + 8 ^ (n + 1)) * δ) := by ring
    _ ≤ 1 * ((1 + 2 ^ (n + 1)) * δ) + 1 * ((1 + 8 ^ (n + 1)) * δ) := by gcongr
    _ = (2 + 2 ^ (n + 1) + 8 ^ (n + 1)) * δ := by ring

/-- **The cutoff field on a small ball near the centre.** Under the hypotheses of
`exists_setAverage_le_and_div_mul_norm_sub_le`, for a `K`-Lipschitz cutoff `ψ ∈ [0, 1]` with
`K R ≤ 2` the field `ψ β + (1 - ψ) P₀` has mean deviation at most `4 · 8^(n + 1) δ` on `B(c, r)`
from the constant `ψ(c) P + (1 - ψ(c)) P₀`, for some `P` satisfying `Q c r`. -/
private theorem exists_setAverage_norm_cutoff_sub_le [NormedSpace ℝ F]
    {β : EuclideanSpace ℝ (Fin (n + 1)) → F} (hβ : AEStronglyMeasurable β volume) {Lam : ℝ}
    (hbd : ∀ x, ‖β x‖ ≤ Lam) {Q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → F → Prop} {δ r₀ : ℝ}
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ P, Q c r P ∧ ⨍ x in ball c r, ‖β x - P‖ ≤ δ)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψm : Continuous ψ) (hψ : ∀ x, ψ x ∈ Icc 0 1)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {R r : ℝ} {K : ℝ≥0} (hψlip : LipschitzWith K ψ)
    (hKR : K * R ≤ 2) {P₀ : F}
    (hδ₀ : ⨍ x in ball x₀ (4 * R), ‖β x - P₀‖ ≤ δ) (hRr₀ : R ≤ r₀) (hr : 0 < r) (hrR : r ≤ R)
    (hc : dist c x₀ < 3 * R) :
    ∃ P, Q c r P ∧
      ⨍ x in ball c r, ‖ψ x • β x + (1 - ψ x) • P₀ - (ψ c • P + (1 - ψ c) • P₀)‖ ≤
        4 * 8 ^ (n + 1) * δ := by
  have hδ : 0 ≤ δ := (average_nonneg fun _ => norm_nonneg _).trans hδ₀
  obtain ⟨P, hQ, hPδ, hdrift⟩ :=
    exists_setAverage_le_and_div_mul_norm_sub_le hβ hbd hosc hδ₀ hRr₀ hr hrR hc
  have hR : 0 < R := hr.trans_le hrR
  refine ⟨P, hQ, (setAverage_norm_cutoff_sub_le hβ hbd hψm hψ hψlip hr hPδ).trans ?_⟩
  have hKr : K * r * ‖P - P₀‖ ≤ 2 * (r / R * ‖P - P₀‖) := by
    rw [show (K : ℝ) * r * ‖P - P₀‖ = K * R * (r / R * ‖P - P₀‖) by field_simp]
    exact mul_le_mul_of_nonneg_right hKR (by positivity)
  have h2 : (2 : ℝ) ≤ 2 ^ (n + 1) := le_self_pow₀ (by norm_num) n.succ_ne_zero
  have h4 : (4 : ℝ) ≤ 4 ^ (n + 1) := le_self_pow₀ (by norm_num) n.succ_ne_zero
  have h8 : (8 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 4 ^ (n + 1) := by rw [← mul_pow]; norm_num
  have hK : (5 + 2 * 2 ^ (n + 1) + 2 * 8 ^ (n + 1) : ℝ) ≤ 4 * 8 ^ (n + 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hK hδ]

/-- The bilinear form of a convex combination of two matrices is the convex combination of their
bilinear forms. -/
private theorem matrixBilinearForm_smul_add_one_sub_smul (t : ℝ)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    matrixBilinearForm (t • A + (1 - t) • B) =
      t • matrixBilinearForm A + (1 - t) • matrixBilinearForm B := by
  simp only [← matrixBilinearFormLinear_apply, map_add, map_smul]

/-- A constant coefficient field uniformly elliptic on a nonempty set is uniformly elliptic on
every set. -/
private theorem UniformlyEllipticOn.const_of_mem {X : Type*} {Ω : Set X} {A : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℝ} {lam Lam : ℝ} (h : UniformlyEllipticOn Ω (fun _ => A) lam Lam) {x : X}
    (hx : x ∈ Ω) (S : Set X) : UniformlyEllipticOn S (fun _ => A) lam Lam :=
  uniformlyEllipticOn_iff.2 ⟨h.pos, h.le, fun _ _ => (uniformlyEllipticOn_iff.1 h).2.2 hx⟩

/-- **The cutoff field on small balls.** Under the hypotheses of
`exists_eqOn_ball_and_forall_setAverage_le`, let `A₀` be the frozen matrix of `B(x₀, 4R)` and let
`ψ ∈ [0, 1]` be a `K`-Lipschitz cutoff, `K R ≤ 2`, vanishing where `dist x x₀ ≥ 2R`. On every ball
`B(c, r)` with `r < R`, the field `ψ a + (1 - ψ) A₀` has mean deviation at most `4 · 8^(n + 1) δ`
from an elliptic constant matrix: `A₀` if the ball is far from `x₀`, where the field is `A₀`, and
otherwise a convex combination of `A₀` and a frozen matrix of the ball. -/
private theorem exists_uniformlyEllipticOn_and_setAverage_cutoff_le {lam Lam δ r₀ R r : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    {x₀ c : EuclideanSpace ℝ (Fin (n + 1))} {A₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA₀ : UniformlyEllipticOn (ball x₀ (4 * R)) (fun _ => A₀) lam Lam)
    (hδ₀ : ⨍ x in ball x₀ (4 * R), ‖matrixBilinearForm (a x) - matrixBilinearForm A₀‖ ≤ δ)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψm : Continuous ψ) (hψ : ∀ x, ψ x ∈ Icc 0 1)
    (hψ0 : ∀ x, 2 * R ≤ dist x x₀ → ψ x = 0) {K : ℝ≥0} (hψlip : LipschitzWith K ψ)
    (hKR : K * R ≤ 2) (hRr₀ : 4 * R ≤ r₀) (hr : 0 < r) (hrR : r < R) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
        ⨍ x in ball c r, ‖ψ x • matrixBilinearForm (a x) + (1 - ψ x) • matrixBilinearForm A₀ -
          matrixBilinearForm A‖ ≤ 4 * 8 ^ (n + 1) * δ := by
  have hR : 0 < R := hr.trans hrR
  have hδ : 0 ≤ δ := (average_nonneg fun x =>
    norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A₀)).trans hδ₀
  have hβ : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) volume :=
    (matrixBilinearFormLinear.continuous.comp_aestronglyMeasurable ha).congr
      (.of_forall fun x => matrixBilinearFormLinear_apply (a x))
  rcases le_or_gt (3 * R) (dist c x₀) with hfar | hnear
  · -- A small ball far from `x₀`, where the field is `A₀`.
    refine ⟨A₀, hA₀.const_of_mem (mem_ball_self (by positivity)) _, ?_⟩
    rw [setAverage_norm_cutoff_sub_eq_zero
      (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
      fun x hx => hψ0 x (by linarith [dist_triangle_right c x₀ x, mem_ball'.1 hx, dist_comm x x₀])]
    positivity
  · -- A small ball near `x₀`: freeze at a convex combination of `A₀` and a frozen matrix of the
    -- ball.
    obtain ⟨P, ⟨A, rfl, hA⟩, hP⟩ := exists_setAverage_norm_cutoff_sub_le
      (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) hβ hbd
      (Q := fun c r P => ∃ A, matrixBilinearForm A = P ∧
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam)
      (fun c r hr hrr₀ => by
        obtain ⟨A, hA, hAδ⟩ := hosc c r hr hrr₀
        exact ⟨_, ⟨A, rfl, hA⟩, hAδ⟩)
      hψm hψ hψlip hKR hδ₀ (by linarith) hr hrR.le hnear
    refine ⟨ψ c • A + (1 - ψ c) • A₀, ?_, ?_⟩
    · exact (UniformlyEllipticOn.smul_add_one_sub_smul (hA.const_of_mem (mem_ball_self hr) _)
        (hA₀.const_of_mem (mem_ball_self (by positivity)) _) (fun _ => hψ c)
        fun x hx => absurd (mem_univ x) hx).mono_set (subset_univ _)
    · rw [matrixBilinearForm_smul_add_one_sub_smul]
      exact hP

/-- **Small mean oscillation below a radius extends to every scale near a ball.** Let `a` be a
measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ` such that on every ball of radius at most
`r₀` some constant matrix, uniformly elliptic with constants `λ, Λ`, has mean deviation at most
`δ` from `a`. Then for every ball `B(x₀, R)` with `4R ≤ r₀` there is a measurable coefficient
matrix `b`, bounded by `Λ`, which agrees with `a` on `B(x₀, R)` and has mean deviation at most
`4 · 8^(n + 1) δ` from an elliptic constant matrix on every ball, of any radius.

The field is `b = ψ a + (1 - ψ) A₀`, where `ψ` is a `2 / R`-Lipschitz cutoff equal to one on
`B(x₀, R)` and zero outside `B(x₀, 2R)`, and `A₀` is the frozen matrix of `B(x₀, 4R)`. This is how
coefficients of vanishing mean oscillation, which are close to constant matrices only on small
balls, meet estimates that ask for small mean oscillation at every scale: a function whose gradient
vanishes outside `B(x₀, R)` solves the same divergence-form equation with `b` in place of `a`. -/
theorem exists_eqOn_ball_and_forall_setAverage_le {lam Lam δ r₀ R : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
      ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ)
    (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (hR : 0 < R) (hRr₀ : 4 * R ≤ r₀) :
    ∃ b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      AEStronglyMeasurable b volume ∧ (∀ x, ‖matrixBilinearForm (b x)‖ ≤ Lam) ∧
        EqOn b a (ball x₀ R) ∧
          ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
            ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
              UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
                ⨍ x in ball c r, ‖matrixBilinearForm (b x) - matrixBilinearForm A‖ ≤
                  4 * 8 ^ (n + 1) * δ := by
  obtain ⟨A₀, hA₀, hδ₀⟩ := hosc x₀ (4 * R) (by positivity) hRr₀
  have hδ : 0 ≤ δ := (average_nonneg fun x =>
    norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A₀)).trans hδ₀
  have hβ : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) volume :=
    (matrixBilinearFormLinear.continuous.comp_aestronglyMeasurable ha).congr
      (.of_forall fun x => matrixBilinearFormLinear_apply (a x))
  obtain ⟨ψ, hψs, hψr, hψ1, hψsupp, hψlip⟩ :=
    exists_contDiff_cutoff_closedBall_lipschitzWith_mul_inv x₀ (r := R) hR (t := 2) one_lt_two
  have hψm : Continuous ψ := hψs.continuous
  have hψ : ∀ x, ψ x ∈ Icc 0 1 := fun x => hψr (mem_range_self x)
  have hψ0 : ∀ x, 2 * R ≤ dist x x₀ → ψ x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => (mem_ball.1 (hψsupp h)).not_ge (by linarith)
  have hKR : ((2 * R.toNNReal⁻¹ : ℝ≥0) : ℝ) * R ≤ 2 := by
    simp [Real.coe_toNNReal _ hR.le, hR.ne']
  refine ⟨fun x => ψ x • a x + (1 - ψ x) • A₀,
    (hψm.aestronglyMeasurable.smul ha).add
      ((continuous_const.sub hψm).aestronglyMeasurable.smul_const A₀), fun x => ?_,
    fun x hx => ?_, fun c r hr => ?_⟩
  · rw [matrixBilinearForm_smul_add_one_sub_smul]
    exact norm_smul_add_one_sub_smul_le
      (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
      (hψ x) (hbd x)
      (hA₀.opNorm_matrixBilinearForm_le (mem_ball_self (by positivity)))
  · simp [hψ1 (ball_subset_closedBall hx)]
  simp only [matrixBilinearForm_smul_add_one_sub_smul]
  rcases le_or_gt R r with hRr | hrR
  · -- A large ball: compare with `A₀`.
    refine ⟨A₀, hA₀.const_of_mem (mem_ball_self (by positivity)) _,
      (setAverage_norm_cutoff_sub_le_of_le
        (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
        hβ hbd hψm hψ hψ0 hR hRr hδ₀).trans (mul_le_mul_of_nonneg_right ?_ hδ)⟩
    have h48 : (4 : ℝ) ^ (n + 1) ≤ 8 ^ (n + 1) := by gcongr; norm_num
    linarith [pow_pos (by norm_num : (0 : ℝ) < 8) (n + 1)]
  exact exists_uniformlyEllipticOn_and_setAverage_cutoff_le ha hbd hosc hA₀ hδ₀ hψm hψ hψ0 hψlip
    hKR hRr₀ hr hrR

/-- The energy form `a(u, v)` without lower-order terms only sees the coefficients where `∇u` does
not vanish: it is unchanged when `a` is replaced by a field agreeing with it on a set `s` outside of
which `∇u = 0` almost everywhere. -/
private theorem energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero
    {a b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hab : EqOn a b s)
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hu : ∀ᵐ x, x ∉ s → W1p.gradient u x = 0)
    (v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2) :
    energyFormH1 a 0 0 u v = energyFormH1 b 0 0 u v := by
  rw [energyFormH1_def, energyFormH1_def]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hu] with x hx
  by_cases hxs : x ∈ s
  · rw [hab hxs]
  · simp [hx hxs]

/-- **The `W^{1,p}` estimate for coefficients of small mean oscillation below a radius.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`
bounded by `Λ`, such that on every ball `B` of radius at most `r₀` some constant matrix `A`,
uniformly elliptic with constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let
`u ∈ H¹(ℝ^{n+1})` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, with `G ∈ Lᵖ`, and let `∇u` be integrable,
in `Lᵖ`, and zero almost everywhere outside a ball of radius `r₀ / 4`. Then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`.

Unlike `exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`, smallness of the
mean oscillation is only asked for on balls of radius at most `r₀`, as for coefficients of
vanishing mean oscillation; the constants do not depend on `r₀`. -/
theorem exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1)))
          (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ᵐ x, x ∉ ball x₀ (r₀ / 4) → W1p.gradient u x = 0) →
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
  obtain ⟨C, δ, hδ, hC⟩ :=
    exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le (n := n) hp hp_top
      lam Lam
  refine ⟨C, δ / (4 * 8 ^ (n + 1)), by positivity,
    fun {a r₀} ha hbd hosc x₀ u G hsupp hu hint hgp hGp => ?_⟩
  rcases le_or_gt r₀ 0 with hr₀ | hr₀
  · -- The ball is empty, so `∇u = 0` almost everywhere.
    have h0 : (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        =ᵐ[volume] 0 :=
      hsupp.mono fun x hx => hx (by simp [ball_eq_empty.2 (by linarith : r₀ / 4 ≤ 0)])
    rw [eLpNorm_congr_ae h0, eLpNorm_zero]
    exact zero_le
  obtain ⟨b, hb, hbbd, hba, hbosc⟩ :=
    exists_eqOn_ball_and_forall_setAverage_le ha hbd hosc x₀ (R := r₀ / 4) (by positivity)
      (by linarith)
  refine hC hb hbbd (fun c r hr => ?_) u G (fun φ => ?_) hint hgp hGp
  · obtain ⟨A, hA, hAδ⟩ := hbosc c r hr
    exact ⟨A, hA, hAδ.trans_eq (by field_simp)⟩
  · rw [← hu φ]
    exact energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero hba hsupp _

end Localization

end PDE

end TauCeti
