/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeanOscillation
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.SmallMeanOscillation
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.PDE.EnergyForm.Measurability
import TauCeti.Analysis.PDE.FundamentalSolution.Divergence
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

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

for every such `u` whose gradient lies in `Lᵖ`, with `C` and the threshold `δ` depending only on
`n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`). Only the
mean oscillation of `a` is controlled, not its modulus of continuity. The membership `∇u ∈ Lᵖ` is
the a priori integrability that the Fefferman–Stein inequality requires; no further integrability
of `∇u`, such as `∇u ∈ L¹`, is needed.

## The argument

The proof is Krylov's sharp function method, applied to Krylov's mean oscillation estimate for the
gradient in `TauCeti.Analysis.PDE.Regularity.MeanOscillation`.

* **One ball.** Let `x ∈ B_ρ = ball c ρ` and `r = κ ρ` with `κ ≥ 1`, and freeze the coefficients on
  `B_r` at the matrix `A` given by the hypothesis. The mean oscillation estimate, with the square
  mean oscillation of `∇u` on `B_r` bounded by `4 ⨍_{B_r} ‖∇u‖²`, and the bound `‖a - A‖ ≤ 2Λ`,
  bound the square mean oscillation of `∇u` on `B_ρ` by
  `κ⁻² ⨍_{B_r} ‖∇u‖² + κ^(n + 1) (⨍_{B_r} ‖G‖² + δ^(1/q') (⨍_{B_r} ‖∇u‖^(2q))^(1/q))`, up to
  constants, for Hölder conjugate exponents `q, q'`.
* **Sharp function and absorption.** These bounds on all balls give the estimate by Krylov's sharp
  function method (`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le`): the
  Fefferman–Stein inequality and the maximal inequality bound `∫ ‖∇u‖^p` by
  `(c₁ κ^(-p) + c₃ δ^(p/(2q'))) ∫ ‖∇u‖^p + c₂ ∫ ‖G‖^p`. Choosing first `κ` large and then `δ`
  small, the first term is absorbed, since `∫ ‖∇u‖^p` is finite.

The restriction `p > 2` comes from the `L²` mean oscillation estimate.

## Small mean oscillation below a radius

Coefficients of vanishing mean oscillation have small mean oscillation only on balls of radius at
most some `r₀`. The estimate still holds for them, with the same constant `C` and the threshold `δ`
shrunk by the factor `4 · 8^(n + 1)`, both independent of `r₀`, for every `u` whose gradient
vanishes outside a ball `B(x₀, r₀ / 4)`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero`).
Such a `u` solves the same equation with `a` replaced by any field `b` agreeing with `a` on
`B(x₀, r₀ / 4)`, and some such `b` has small mean oscillation at every scale
(`TauCeti.PDE.exists_eqOn_ball_and_forall_setAverage_le`). In the proof, `b = ψ a + (1 - ψ) A₀`
for a cutoff `ψ` equal to one on `B(x₀, r₀ / 4)` and a frozen matrix `A₀` of `B(x₀, r₀)`, given by
the cutoff extension of locally integrable fields of small mean oscillation below a radius in
`TauCeti.MeasureTheory.Function.SmallMeanOscillation`
(`TauCeti.exists_forall_setAverage_norm_cutoff_sub_le`).

## The interior estimate

A weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` on an open set `Ω`, in dimension at least
two, with `u`, `∇u` and `G` in `Lᵖ(B)` on a ball `B = B(x₀, R) ⊆ Ω` with `4R ≤ r₀`, satisfies

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B)} + R⁻¹ (‖u - m‖_{Lᵖ(B)} + ‖∇u‖_{L^q(B)}))`

for every constant `m`, where `1 / q = 1 / p + 1 / (n + 1)`
(`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_setAverage_le`). For a smooth cutoff `ζ` equal
to one on `B(x₀, R/2)` and supported in `B`, the function `ζ (u - m)` lies in `H¹(ℝ^{n+1})`, and
testing the equation of `u` with `ζ φ` shows that it solves

`-∂ᵢ(aⁱʲ ∂ⱼ(ζ (u - m))) = -div (ζ G + (u - m) a ∇ζ) + ⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫`.

The scalar term is supported in `B` and bounded in `L^q` by `R⁻¹ (‖G‖_{L^q(B)} + Λ ‖∇u‖_{L^q(B)})`,
so it is minus the divergence of a field bounded in `Lᵖ` by the same quantity
(`TauCeti.exists_eLpNorm_le_and_integral_inner_gradient_eq`, the gradient of its Newtonian
potential). The estimate for gradients vanishing outside a small ball then applies to `ζ (u - m)`.
Finally Hölder's inequality bounds `R⁻¹ ‖G‖_{L^q(B)}` by a dimensional multiple of `‖G‖_{Lᵖ(B)}`,
since `|B|^(1/q - 1/p)` is a dimensional multiple of `R`.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`: the
  `W^{1,p}` estimate for coefficients of small mean oscillation, `2 < p < ∞`.
* `TauCeti.PDE.exists_eqOn_ball_and_forall_setAverage_le`: a coefficient field of small mean
  oscillation below a radius `r₀` agrees on a ball `B(x₀, R)`, `4R ≤ r₀`, with a field of small
  mean oscillation at every scale.
* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero`:
  the `W^{1,p}` estimate for coefficients of small mean oscillation below a radius, for functions
  whose gradient vanishes outside a small ball.
* `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_setAverage_le`: the interior `W^{1,p}` estimate
  for weak solutions on an open set, for coefficients of small mean oscillation below a radius.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* G. Di Fazio, *Lᵖ estimates for divergence form elliptic equations with discontinuous
  coefficients*, Boll. Un. Mat. Ital. A (7) **10** (1996), 409–420 (the interior estimate).
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
  -- The factor `(⨍_{B_r} ‖g‖^(2q))^(1/q)` is nonnegative.
  · exact Real.rpow_nonneg (average_nonneg fun y => by positivity) _
  -- The base `(2Λ)^(2q' - 1) ⨍_{B_r} ‖a - A‖` of the power compared through `hδ` is nonnegative.
  · exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (average_nonneg fun y => norm_nonneg (matrixBilinearForm (a y) - matrixBilinearForm A))
  -- The exponent `1/q'` of that power is nonnegative.
  · exact inv_nonneg.2 hq.symm.pos.le

/-- **The `W^{1,p}` estimate for coefficients of small mean oscillation.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ`, such
that on every ball `B` some constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`; both norms are operator norms of the attached bilinear
forms. Let `u ∈ H¹(ℝ^{n+1})` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩` for every test function `φ`, with `G ∈ Lᵖ`, and let `∇u` lie in `Lᵖ`.
Then

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
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p volume →
          MemLp G p volume →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) p volume ≤ C * eLpNorm G p volume := by
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le (n := n)
    (E := EuclideanSpace ℝ (Fin (n + 1))) (F := EuclideanSpace ℝ (Fin (n + 1))) hp hp_top
    (decayConst n lam Lam) (forcingConst n lam Lam) (forcingConst n lam Lam) (2 * Lam)
  refine ⟨C, δ, hδ, fun {a} ha hbd hosc u G hu hgp hGp =>
    h hgp hGp fun q q' hq hqp c ρ κ hρ hκ => ?_⟩
  -- Freeze the coefficients on `B_{κρ}` and apply the mean oscillation estimate on one ball.
  obtain ⟨A, hA, hδA⟩ := hosc c (κ * ρ) (mul_pos (zero_lt_one.trans_le hκ) hρ)
  exact (setAverage_norm_gradient_sub_sq_le ha hbd hu hp.le hgp hGp hq hqp hρ hκ hA hδA).trans_eq
    (by ring)

/-! ### Localization to small balls -/

section Localization

/-- A convex combination of two vectors of norm at most `L` has norm at most `L`: convexity of the
closed ball, stated in a general normed space because instantiating `convex_closedBall` directly at
the space of bilinear forms exhausts the heartbeat limit. -/
private theorem norm_smul_add_one_sub_smul_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {t L : ℝ} (ht : t ∈ Icc 0 1) {P P' : F} (hP : ‖P‖ ≤ L) (hP' : ‖P'‖ ≤ L) :
    ‖t • P + (1 - t) • P'‖ ≤ L :=
  mem_closedBall_zero_iff.1 (convex_closedBall (0 : F) L (mem_closedBall_zero_iff.2 hP)
    (mem_closedBall_zero_iff.2 hP') ht.1 (sub_nonneg.2 ht.2) (add_sub_cancel _ _))

/-- **Small mean oscillation below a radius extends to every scale near a ball**, for coefficient
matrices. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ` such that on every
ball of radius at most `r₀` some constant matrix, uniformly elliptic with constants `λ, Λ`, has mean
deviation at most `δ` from `a`. Then for every ball `B(x₀, R)` with `4R ≤ r₀` there is a measurable
coefficient matrix `b`, bounded by `Λ`, which agrees with `a` on `B(x₀, R)` and has mean deviation
at most `4 · 8^(n + 1) δ` from an elliptic constant matrix on every ball, of any radius.

This is how coefficients of vanishing mean oscillation, which are close to constant matrices only
on small balls, meet estimates that ask for small mean oscillation at every scale: a function whose
gradient vanishes outside `B(x₀, R)` sees only `b = a` there, so it solves the same divergence-form
equation with `b` in place of `a` (`TauCeti.PDE.energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero`).
The field `b` comes from `TauCeti.exists_forall_setAverage_norm_cutoff_sub_le`. -/
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
  obtain ⟨ψ, hψm, hψ, hψ1, P₀, ⟨A₀, rfl, hA₀⟩, hosc'⟩ :=
    TauCeti.exists_forall_setAverage_norm_cutoff_sub_le
      (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
      ((memLp_top_of_bound (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha) Lam
        (.of_forall hbd)).locallyIntegrable le_top)
      (Q := fun c r P => ∃ A, matrixBilinearForm A = P ∧
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam)
      (fun c r hr hrr₀ => by
        obtain ⟨A, hA, hAδ⟩ := hosc c r hr hrr₀
        exact ⟨_, ⟨A, rfl, hA⟩, hAδ⟩) x₀ hR hRr₀
  have hA₀' := hA₀.const_of_mem (mem_ball_self (by positivity))
  refine ⟨fun x => ψ x • a x + (1 - ψ x) • A₀,
    (hψm.aestronglyMeasurable.smul ha).add
      ((continuous_const.sub hψm).aestronglyMeasurable.smul_const A₀), fun x => ?_,
    fun x hx => ?_, fun c r hr => ?_⟩
  · rw [matrixBilinearForm_add, matrixBilinearForm_smul, matrixBilinearForm_smul]
    exact norm_smul_add_one_sub_smul_le
      (F := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
      (hψ x) (hbd x) (hA₀.opNorm_matrixBilinearForm_le (mem_ball_self (by positivity)))
  · simp [hψ1 hx]
  obtain ⟨P, hP, t, ht, havg⟩ := hosc' c r hr
  obtain ⟨A, rfl, hA⟩ : ∃ A, matrixBilinearForm A = P ∧
      UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam :=
    hP.elim (fun h => ⟨A₀, h.symm, hA₀' _⟩) id
  refine ⟨t • A + (1 - t) • A₀, (UniformlyEllipticOn.smul_add_one_sub_smul
    (hA.const_of_mem (mem_ball_self hr) _) (hA₀' _) (fun _ => ht)
      fun x hx => absurd (mem_univ x) hx).mono_set (subset_univ _), ?_⟩
  simpa only [matrixBilinearForm_add, matrixBilinearForm_smul, finrank_euclideanSpace_fin]
    using havg

/-- **The `W^{1,p}` estimate for coefficients of small mean oscillation below a radius.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`
bounded by `Λ`, such that on every ball `B` of radius at most `r₀` some constant matrix `A`,
uniformly elliptic with constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let
`u ∈ H¹(ℝ^{n+1})` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, with `G ∈ Lᵖ`, and let `∇u` lie in `Lᵖ` and
vanish almost everywhere outside a ball of radius `r₀ / 4`. Then

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
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p volume →
          MemLp G p volume →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) p volume ≤ C * eLpNorm G p volume := by
  obtain ⟨C, δ, hδ, hC⟩ :=
    exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le (n := n) hp hp_top
      lam Lam
  refine ⟨C, δ / (4 * 8 ^ (n + 1)), by positivity,
    fun {a r₀} ha hbd hosc x₀ u G hsupp hu hgp hGp => ?_⟩
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
  refine hC hb hbbd (fun c r hr => ?_) u G (fun φ => ?_) hgp hGp
  · obtain ⟨A, hA, hAδ⟩ := hbosc c r hr
    exact ⟨A, hA, hAδ.trans_eq (by field_simp)⟩
  · rw [← hu φ]
    exact energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero hba 0 0 (ae_restrict_of_ae hsupp) _

end Localization

/-! ### The interior estimate -/

section Interior

/-- Bounds on a compact set for a cutoff `ζ`, a smooth function `φ`, a third smooth function `ψ`
and their gradients. -/
private theorem exists_forall_mem_abs_le_and_norm_gradient_le
    {ζ φ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K) :
    ∃ M, (∀ x ∈ K, |ζ x| ≤ M) ∧ (∀ x ∈ K, ‖∇ ζ x‖ ≤ M) ∧ (∀ x ∈ K, |φ x| ≤ M) ∧
      (∀ x ∈ K, ‖∇ φ x‖ ≤ M) ∧ ∀ x ∈ K, ‖∇ ψ x‖ ≤ M := by
  obtain ⟨M₁, h₁⟩ := hK.exists_bound_of_continuousOn hζ.continuous.continuousOn
  obtain ⟨M₂, h₂⟩ := hK.exists_bound_of_continuousOn (hζ.continuous_gradient (by simp)).continuousOn
  obtain ⟨M₃, h₃⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  obtain ⟨M₄, h₄⟩ := hK.exists_bound_of_continuousOn (hφ.continuous_gradient (by simp)).continuousOn
  obtain ⟨M₅, h₅⟩ := hK.exists_bound_of_continuousOn (hψ.continuous_gradient (by simp)).continuousOn
  refine ⟨max (max (max M₁ M₂) (max M₃ M₄)) M₅, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  · exact (Real.norm_eq_abs _ ▸ h₁ x hx).trans (by simp)
  · exact (h₂ x hx).trans (by simp)
  · exact (Real.norm_eq_abs _ ▸ h₃ x hx).trans (by simp)
  · exact (h₄ x hx).trans (by simp)
  · exact (h₅ x hx).trans (by simp)

/-- The terms of the equation of a cutoff solution that involve `∇u` are integrable. -/
private theorem integrable_cutoff_terms_gradient
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hLam : 0 ≤ Lam)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Ω 2)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {ζ φ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : Continuous φ) {M : ℝ}
    (hgζM : ∀ x ∈ K, ‖∇ ζ x‖ ≤ M) (hφM : ∀ x ∈ K, |φ x| ≤ M) (hgψM : ∀ x ∈ K, ‖∇ ψ x‖ ≤ M)
    (hgζ0 : ∀ x ∉ K, ∇ ζ x = 0) (hgψ0 : ∀ x ∉ K, ∇ ψ x = 0) :
    Integrable (fun x => matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) ∧
      Integrable (fun x => matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x) * φ x) := by
  have hBa := continuous_matrixBilinearForm.comp_aestronglyMeasurable ha
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hguK : IntegrableOn (fun x => ‖W1p.gradient u x‖) K :=
    (((Lp.memLp (W1p.gradient u)).mono_measure
      (Measure.restrict_mono hKΩ le_rfl)).integrable one_le_two).norm
  have hgum := (Lp.aestronglyMeasurable (W1p.gradient u)).mono_measure
    (Measure.restrict_mono_set volume hKΩ)
  refine ⟨integrable_of_forall_notMem_eq_zero_of_norm_le hK.measurableSet
    (aestronglyMeasurable_matrixBilinearForm_apply hBa.restrict
      (measurable_gradient ψ).aestronglyMeasurable hgum) (hguK.const_mul (Lam * M))
    (fun x hx => by simp [hgψ0 x hx]) fun x hx =>
      (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hbd x) (hgψM x hx) le_rfl,
    integrable_of_forall_notMem_eq_zero_of_norm_le hK.measurableSet
    ((aestronglyMeasurable_matrixBilinearForm_apply hBa.restrict
      (measurable_gradient ζ).aestronglyMeasurable hgum).mul hφ.aestronglyMeasurable)
    (hguK.const_mul (Lam * M * M)) (fun x hx => by simp [hgζ0 x hx]) fun x hx => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hgζM x hx)
  rw [norm_mul, Real.norm_eq_abs (φ x)]
  calc ‖matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)‖ * |φ x|
      ≤ (Lam * M * ‖W1p.gradient u x‖) * M :=
        mul_le_mul ((matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hbd x) (hgζM x hx) le_rfl)
          (hφM x hx) (abs_nonneg _) (by positivity)
    _ = Lam * M * M * ‖W1p.gradient u x‖ := by ring

/-- The term of the equation of a cutoff solution that involves `u - m` is integrable. -/
private theorem integrable_cutoff_term_value
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
    (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Ω 2) {K : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {ζ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {M : ℝ}
    (hgζM : ∀ x ∈ K, ‖∇ ζ x‖ ≤ M) (hgφM : ∀ x ∈ K, ‖∇ φ x‖ ≤ M)
    (hgζ0 : ∀ x ∉ K, ∇ ζ x = 0) (m : ℝ) :
    Integrable (fun x => (W1p.value u x - m) * matrixBilinearForm (a x) (∇ φ x) (∇ ζ x)) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hvuK : IntegrableOn (fun x => |W1p.value u x - m|) K :=
    ((((Lp.memLp (W1p.value u)).mono_measure
      (Measure.restrict_mono hKΩ le_rfl)).integrable one_le_two).sub (integrable_const m)).abs
  refine integrable_of_forall_notMem_eq_zero_of_norm_le hK.measurableSet
    ((((Lp.aestronglyMeasurable (W1p.value u)).mono_measure
      (Measure.restrict_mono_set volume hKΩ)).sub aestronglyMeasurable_const).mul
        (aestronglyMeasurable_matrixBilinearForm_apply
          (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).restrict
          (measurable_gradient φ).aestronglyMeasurable
          (measurable_gradient ζ).aestronglyMeasurable)) (hvuK.mul_const (Lam * M * M))
    (fun x hx => by simp [hgζ0 x hx]) fun x hx => ?_
  rw [norm_mul, Real.norm_eq_abs (W1p.value u x - m)]
  exact mul_le_mul_of_nonneg_left
    ((matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hbd x) (hgφM x hx) (hgζM x hx))
    (abs_nonneg _)

/-- The terms of the equation of a cutoff solution that involve the datum `G` are integrable. -/
private theorem integrable_cutoff_terms_datum
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {B K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K)
    (hKB : K ⊆ B) (hG : IntegrableOn G B) {ζ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hζ : Continuous ζ) (hφ : Continuous φ) {M : ℝ} (hζM : ∀ x ∈ K, |ζ x| ≤ M)
    (hgζM : ∀ x ∈ K, ‖∇ ζ x‖ ≤ M) (hφM : ∀ x ∈ K, |φ x| ≤ M) (hgφM : ∀ x ∈ K, ‖∇ φ x‖ ≤ M)
    (hζ0 : ∀ x ∉ K, ζ x = 0) (hgζ0 : ∀ x ∉ K, ∇ ζ x = 0) :
    Integrable (fun x => ζ x * ⟪G x, ∇ φ x⟫_ℝ) ∧ Integrable (fun x => ⟪G x, ∇ ζ x⟫_ℝ * φ x) := by
  have hGK : IntegrableOn (fun x => ‖G x‖) K := (hG.mono_set hKB).norm
  refine ⟨integrable_of_forall_notMem_eq_zero_of_norm_le hK.measurableSet
    ((hζ.aestronglyMeasurable.mul
      (hG.aestronglyMeasurable.inner (measurable_gradient φ).aestronglyMeasurable)).mono_set hKB)
    (hGK.const_mul (M * M)) (fun x hx => by simp [hζ0 x hx]) fun x hx => ?_,
    integrable_of_forall_notMem_eq_zero_of_norm_le hK.measurableSet
    (((hG.aestronglyMeasurable.inner (measurable_gradient ζ).aestronglyMeasurable).mul
      hφ.aestronglyMeasurable).mono_set hKB)
    (hGK.const_mul (M * M)) (fun x hx => by simp [hgζ0 x hx]) fun x hx => ?_⟩
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hζM x hx)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |ζ x| * |⟪G x, ∇ φ x⟫_ℝ| ≤ M * (‖G x‖ * ‖∇ φ x‖) :=
          mul_le_mul (hζM x hx) (abs_real_inner_le_norm _ _) (abs_nonneg _) hM0
      _ ≤ M * (‖G x‖ * M) := by gcongr; exact hgφM x hx
      _ = M * M * ‖G x‖ := by ring
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hφM x hx)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |⟪G x, ∇ ζ x⟫_ℝ| * |φ x| ≤ (‖G x‖ * ‖∇ ζ x‖) * M :=
          mul_le_mul (abs_real_inner_le_norm _ _) (hφM x hx) (abs_nonneg _) (by positivity)
      _ ≤ (‖G x‖ * M) * M := by gcongr; exact hgζM x hx
      _ = M * M * ‖G x‖ := by ring

/-- The Leibniz rule `∇(ζ φ) = ζ ∇φ + φ ∇ζ` for smooth real functions. -/
private theorem gradient_mul_eq_smul_add_smul {ζ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ∇ (fun y => ζ y * φ y) x = ζ x • ∇ φ x + φ x • ∇ ζ x := by
  simpa only [conj_trivial] using
    gradient_fun_mul (hζ.differentiable (by simp) x) (hφ.differentiable (by simp) x)

/-- **The equation tested with `ζ φ`.** For a smooth cutoff `ζ` with compact support in `Ω` and a
smooth `φ`, the product `ζ φ` is a test function on `Ω`, so a weak solution `u` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` satisfies `∫ ⟪∇(ζ φ), a ∇u⟫ = ∫ ζ ⟪G, ∇φ⟫ + ∫ ⟪G, ∇ζ⟫ φ`. -/
private theorem integral_matrixBilinearForm_gradient_mul_eq
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Ω 2)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ)
    (hζΩ : tsupport ζ ⊆ Ω) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i4 : Integrable (fun x => ζ x * ⟪G x, ∇ φ x⟫_ℝ))
    (i5 : Integrable (fun x => ⟪G x, ∇ ζ x⟫_ℝ * φ x)) :
    ∫ x, matrixBilinearForm (a x) (∇ (fun y => ζ y * φ y) x) (W1p.gradient u x) =
      (∫ x, ζ x * ⟪G x, ∇ φ x⟫_ℝ) + ∫ x, ⟪G x, ∇ ζ x⟫_ℝ * φ x := by
  set ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => ζ x * φ x
  have hψK : tsupport ψ ⊆ tsupport ζ := tsupport_mul_subset_left
  let ψΩ : 𝓓(Ω, ℝ) := ⟨ψ, hζ.mul hφ, hζc.mul_right, hψK.trans hζΩ⟩
  have hcoe : (ψΩ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) = ψ := TestFunction.coe_mk
  have hgψ0 : ∀ x ∉ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∇ ψ x = 0 := fun x hx =>
    gradient_of_notMem_tsupport fun h => hx (hζΩ (hψK h))
  have h1 : ∫ x, matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) =
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 ψΩ) := by
    rw [energyFormH1_zero_zero_eq_setIntegral, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => by simp [hgψ0 x hx]]
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 ψΩ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx, hcoe]
  rw [h1, hu ψΩ, hcoe, ← integral_add i4 i5,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hgψ0 x hx]]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ψ, gradient_mul_eq_smul_add_smul hζ hφ x, inner_add_right, real_inner_smul_right]
  ring

/-- **The equation of a cutoff solution.** Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in
`Ω`, let `G` be integrable on a set `B ⊆ Ω`, and let `ζ` be a smooth cutoff with compact support in
`B`. For every constant `m` and every smooth `φ`, the field `ζ ∇u + (u - m) ∇ζ`, the gradient of
`ζ (u - m)`, satisfies

`∫ ⟪∇φ, a (ζ ∇u + (u - m) ∇ζ)⟫ = ∫ (ζ ⟪G, ∇φ⟫ + (u - m) ⟪∇φ, a ∇ζ⟫) + ∫ (⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫) φ`.

So `ζ (u - m)` solves an equation of the same form, with divergence datum `ζ G + (u - m) a ∇ζ` and
the additional scalar datum `⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫`, which is supported where `∇ζ` is. The first
integrand on the right is integrable. -/
private theorem integral_matrixBilinearForm_cutoff_eq
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
    (ha : AEStronglyMeasurable a volume) (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hLam : 0 ≤ Lam)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Ω 2)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {B : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hBΩ : B ⊆ Ω)
    (hG : IntegrableOn G B)
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζB : tsupport ζ ⊆ B)
    (m : ℝ) {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Integrable (fun x => ζ x * ⟪G x, ∇ φ x⟫_ℝ +
        (W1p.value u x - m) * matrixBilinearForm (a x) (∇ φ x) (∇ ζ x)) ∧
      ∫ x, matrixBilinearForm (a x) (∇ φ x)
          (ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x) =
        (∫ x, (ζ x * ⟪G x, ∇ φ x⟫_ℝ +
            (W1p.value u x - m) * matrixBilinearForm (a x) (∇ φ x) (∇ ζ x))) +
          ∫ x, (⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) * φ x := by
  set K := tsupport ζ
  have hKΩ : K ⊆ Ω := hζB.trans hBΩ
  set gu : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => ζ x * φ x
  obtain ⟨M, hζM, hgζM, hφM, hgφM, hgψM⟩ :=
    exists_forall_mem_abs_le_and_norm_gradient_le hζ hφ (hζ.mul hφ) (K := K) hζc.isCompact
  have hζ0 : ∀ x ∉ K, ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hgζ0 : ∀ x ∉ K, ∇ ζ x = 0 := fun x hx => gradient_of_notMem_tsupport hx
  have hgψ0 : ∀ x ∉ K, ∇ ψ x = 0 := fun x hx =>
    gradient_of_notMem_tsupport fun h => hx (tsupport_mul_subset_left h)
  obtain ⟨i1, i2⟩ := integrable_cutoff_terms_gradient ha hbd hLam u hζc.isCompact hKΩ
    hφ.continuous hgζM hφM hgψM hgζ0 hgψ0
  have i3 := integrable_cutoff_term_value ha hbd u hζc.isCompact hKΩ hgζM hgφM hgζ0 m
  obtain ⟨i4, i5⟩ := integrable_cutoff_terms_datum hζc.isCompact hζB hG hζ.continuous
    hφ.continuous hζM hgζM hφM hgφM hζ0 hgζ0
  have e3 := integral_matrixBilinearForm_gradient_mul_eq u hu hζ hζc hKΩ hφ i4 i5
  have e1 : ∫ x, matrixBilinearForm (a x) (∇ φ x) (ζ x • gu x + (W1p.value u x - m) • ∇ ζ x) =
      (∫ x, matrixBilinearForm (a x) (∇ ψ x) (gu x)) -
        (∫ x, matrixBilinearForm (a x) (∇ ζ x) (gu x) * φ x) +
          ∫ x, (W1p.value u x - m) * matrixBilinearForm (a x) (∇ φ x) (∇ ζ x) := by
    rw [← integral_sub i1 i2, ← integral_add (f := fun x =>
      matrixBilinearForm (a x) (∇ ψ x) (gu x) - matrixBilinearForm (a x) (∇ ζ x) (gu x) * φ x)
      (i1.sub i2) i3]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ψ, gradient_mul_eq_smul_add_smul hζ hφ x, map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul]
    ring
  have e2 : ∫ x, (⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (gu x)) * φ x =
      (∫ x, ⟪G x, ∇ ζ x⟫_ℝ * φ x) - ∫ x, matrixBilinearForm (a x) (∇ ζ x) (gu x) * φ x := by
    rw [← integral_sub i5 i2]
    simp only [sub_mul, gu]
  refine ⟨i4.add i3, ?_⟩
  rw [e1, e2, integral_add i4 i3, e3]
  ring

/-- The vector `a ∇ζ`, representing `η ↦ ⟪η, a ∇ζ⟫`, the divergence datum that a cutoff `ζ`
contributes to the equation of `ζ (u - m)`, is a.e. strongly measurable. -/
private theorem aestronglyMeasurable_toDual_symm_transpose
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) (ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :
    AEStronglyMeasurable (fun x => (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
      (matrixBilinearForm (a x).transpose (∇ ζ x))) volume := by
  have hBa : AEStronglyMeasurable (fun x => matrixBilinearForm (a x).transpose) volume :=
    continuous_matrixBilinearForm.comp_aestronglyMeasurable
      ((continuous_id.matrix_transpose).comp_aestronglyMeasurable ha)
  have hc : Continuous fun q : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) × EuclideanSpace ℝ (Fin (n + 1)) =>
        (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm (q.1 q.2) :=
    (toDual ℝ _).symm.continuous.comp (continuous_fst.clm_apply continuous_snd)
  exact hc.comp_aestronglyMeasurable (hBa.prodMk (measurable_gradient ζ).aestronglyMeasurable)

/-- **The equation of a cutoff solution on the whole space.** In the setting of
`integral_matrixBilinearForm_cutoff_eq`, let `v ∈ H¹(ℝⁿ)` have weak gradient
`ζ ∇u + (u - m) ∇ζ`, and let `H` be a locally integrable field whose divergence is minus the scalar
datum `⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫`. Then `v` solves `-∂ᵢ(aⁱʲ ∂ⱼv) = -div G'` on the whole space, with
`G' = ζ G + (u - m) a ∇ζ + H`; the vector `a ∇ζ` represents `η ↦ ⟪η, a ∇ζ⟫`. -/
private theorem energyFormH1_eq_integral_inner_of_cutoff
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
    (ha : AEStronglyMeasurable a volume) (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (hLam : 0 ≤ Lam)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Ω 2)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {B : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hBΩ : B ⊆ Ω) (hG : IntegrableOn G B)
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζB : tsupport ζ ⊆ B) (m : ℝ)
    {v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hv : ∀ᵐ x, W1p.gradient v x = ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x)
    {H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hH : LocallyIntegrable H volume)
    (hHh : ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∫ x, ⟪H x, ∇ φ x⟫_ℝ = ∫ x, (⟪G x, ∇ ζ x⟫_ℝ -
        matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) * φ x)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    energyFormH1 a 0 0 v (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x, ⟪ζ x • G x + (W1p.value u x - m) • (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
        (matrixBilinearForm (a x).transpose (∇ ζ x)) + H x,
          ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  obtain ⟨hint, heq⟩ := integral_matrixBilinearForm_cutoff_eq ha hbd hLam u hBΩ hG hu hζ hζc hζB
    m φ.contDiff
  have hφ1 : ContDiff ℝ 1 (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    φ.contDiff.of_le (by exact_mod_cast le_top)
  have hHi : Integrable fun x => ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
    refine (hH.integrable_smul_left_of_hasCompactSupport
      (hφ1.continuous_gradient one_ne_zero).norm φ.hasCompactSupport.gradient.norm).norm.mono'
      (hH.aestronglyMeasurable.inner (measurable_gradient _).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, norm_smul, norm_norm, mul_comm]
    exact abs_real_inner_le_norm _ _
  rw [energyFormH1_zero_zero_eq_setIntegral]
  simp only [Opens.coe_top, Measure.restrict_univ]
  have hae : ∀ᵐ x, matrixBilinearForm (a x) (W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 2 φ) x)
      (W1p.gradient v x) = matrixBilinearForm (a x) (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
        (ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x) := by
    filter_upwards [hv, W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ]
      with x h1 h2
    rw [h1, h2]
  rw [integral_congr_ae hae, heq, ← hHh _ hφ1 φ.hasCompactSupport, ← integral_add hint hHi]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [inner_add_left, real_inner_smul_left, toDual_symm_apply,
    matrixBilinearForm_transpose_apply]

/-- The exponent `q` with `1 / q = 1 / p + 1 / (n + 1)` lies strictly between `1` and `p` when
`p > 2` and `n ≥ 1`. -/
private theorem one_lt_and_le_of_inv_eq_inv_add_inv (hn : n ≠ 0) {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ + ((n : ℝ) + 1)⁻¹) : 1 < q ∧ q ≤ p := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn)
  have hn0 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hq0 : (0 : ℝ) < q := by
    refine lt_of_le_of_ne q.coe_nonneg fun h => ?_
    rw [← h, inv_zero] at hpq
    linarith [inv_pos.2 hp0]
  have hp2 : (p : ℝ)⁻¹ < 2⁻¹ := inv_strictAnti₀ two_pos (by exact_mod_cast hp)
  have hn2 : ((n : ℝ) + 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ two_pos (by linarith)
  refine ⟨?_, ?_⟩
  · have hq1 : (q : ℝ)⁻¹ < 1 := by linarith
    exact_mod_cast (inv_lt_one₀ hq0).1 hq1
  · have : (p : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by linarith
    exact_mod_cast (inv_le_inv₀ hp0 hq0).1 this

/-- **Hölder's inequality on a ball.** When `1 / q = 1 / p + 1 / (n + 1)`, the `L^q` norm on
`B(x₀, R)` is at most `R V` times the `Lᵖ` norm there, with `V = |B(0, 1)|^(1/(n + 1))`. -/
private theorem ofReal_inv_mul_eLpNorm_ball_le {p q : ℝ≥0}
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ + ((n : ℝ) + 1)⁻¹) (hqp : (q : ℝ≥0∞) ≤ p)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 < R) {F : Type*} [NormedAddCommGroup F]
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hG : AEStronglyMeasurable G (volume.restrict (ball x₀ R))) :
    ENNReal.ofReal R⁻¹ * eLpNorm G q (volume.restrict (ball x₀ R)) ≤
      (((volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toNNReal ^ ((n : ℝ) + 1)⁻¹ :
        ℝ≥0) : ℝ≥0∞) * eLpNorm G p (volume.restrict (ball x₀ R)) := by
  set V : ℝ≥0 :=
    (volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toNNReal ^ ((n : ℝ) + 1)⁻¹
  have hq0 : (0 : ℝ) < q := inv_pos.1 (hpq ▸ by positivity)
  have hexp : 1 / (q : ℝ) - 1 / p = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [one_div, one_div, hpq]; push_cast; ring
  have hfac : (R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ^ (1 / (q : ℝ) - 1 / p) =
      R * V := by
    rw [finrank_euclideanSpace_fin, hexp, Real.mul_rpow (by positivity) measureReal_nonneg,
      Real.pow_rpow_inv_natCast hR.le n.succ_ne_zero]
    simp [V, measureReal_def, ENNReal.coe_toNNReal_eq_toReal]
  have hH := Measure.eLpNorm_ball_le_mul_rpow volume (x₀ := x₀) (p := p) hq0
    (by exact_mod_cast hqp) hG
  rw [hfac, ENNReal.ofReal_mul hR.le] at hH
  simp only [ENNReal.ofReal_coe_nnreal] at hH
  calc ENNReal.ofReal R⁻¹ * eLpNorm G q (volume.restrict (ball x₀ R))
      ≤ ENNReal.ofReal R⁻¹ * (eLpNorm G p (volume.restrict (ball x₀ R)) *
          (ENNReal.ofReal R * V)) := by gcongr
    _ = ENNReal.ofReal (R⁻¹ * R) * V * eLpNorm G p (volume.restrict (ball x₀ R)) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hR.le)]; ring
    _ = V * eLpNorm G p (volume.restrict (ball x₀ R)) := by
        rw [inv_mul_cancel₀ hR.ne', ENNReal.ofReal_one, one_mul]

/-- The bookkeeping of constants in the interior estimate, with `k = c₀ / R` and `R⁻¹ Z ≤ V X`. -/
private theorem mul_add_mul_add_le_mul_add {CW CD V : ℝ≥0} {c₀ Lam R : ℝ} (hc₀ : 0 ≤ c₀)
    (hLam : 0 ≤ Lam) {X Y Z W : ℝ≥0∞} (hZ : ENNReal.ofReal R⁻¹ * Z ≤ V * X) :
    (CW : ℝ≥0∞) * ((ENNReal.ofReal 1 * X + ENNReal.ofReal (Lam * (c₀ * R⁻¹)) * Y) +
      CD * (ENNReal.ofReal (c₀ * R⁻¹) * Z + ENNReal.ofReal (Lam * (c₀ * R⁻¹)) * W)) ≤
      ((CW * (1 + c₀.toNNReal * (Lam.toNNReal + CD + CD * Lam.toNNReal)) * (1 + V) : ℝ≥0) :
          ℝ≥0∞) * (X + ENNReal.ofReal R⁻¹ * (Y + W)) := by
  set κ := c₀.toNNReal
  set L := Lam.toNNReal
  set ρ := ENNReal.ofReal R⁻¹
  have hk : ENNReal.ofReal (c₀ * R⁻¹) = κ * ρ := ENNReal.ofReal_mul hc₀
  have hk' : ENNReal.ofReal (Lam * (c₀ * R⁻¹)) = L * (κ * ρ) := by
    rw [ENNReal.ofReal_mul hLam, hk, ← ENNReal.ofNNReal_toNNReal]
  have h1 : (1 : ℝ≥0) ≤ 1 + κ * (L + CD + CD * L) := le_self_add
  have hκ {t : ℝ≥0} (ht : t ≤ L + CD + CD * L) : t * κ ≤ 1 + κ * (L + CD + CD * L) := by
    rw [mul_comm]; exact (by gcongr : κ * t ≤ κ * _).trans le_add_self
  have h2 := hκ (le_self_add.trans le_self_add : L ≤ _)
  have h3 := hκ (le_add_self.trans le_self_add : CD ≤ _)
  have h4 := hκ (le_add_self : CD * L ≤ _)
  set K : ℝ≥0 := 1 + κ * (L + CD + CD * L)
  rw [hk, hk', ENNReal.ofReal_one]
  calc (CW : ℝ≥0∞) * ((1 * X + L * (κ * ρ) * Y) + CD * (κ * ρ * Z + L * (κ * ρ) * W))
      = CW * (1 * X + ((L * κ : ℝ≥0) : ℝ≥0∞) * ρ * Y + ((CD * κ : ℝ≥0) : ℝ≥0∞) * ρ * Z +
          ((CD * L * κ : ℝ≥0) : ℝ≥0∞) * ρ * W) := by push_cast; ring
    _ ≤ CW * ((K : ℝ≥0∞) * X + K * ρ * Y + K * ρ * Z + K * ρ * W) := by
        gcongr
        exact_mod_cast h1
    _ = ((CW * K : ℝ≥0) : ℝ≥0∞) * (X + ρ * Z + ρ * (Y + W)) := by push_cast; ring
    _ ≤ ((CW * K : ℝ≥0) : ℝ≥0∞) * (X + V * X + ρ * (Y + W) + V * (ρ * (Y + W))) := by
        gcongr ((CW * K : ℝ≥0) : ℝ≥0∞) * ?_
        exact (by gcongr : X + ρ * Z + ρ * (Y + W) ≤ X + V * X + ρ * (Y + W)).trans le_self_add
    _ = ((CW * K * (1 + V) : ℝ≥0) : ℝ≥0∞) * (X + ρ * (Y + W)) := by push_cast; ring

/-- A smooth cutoff for the ball `B(x₀, R)`: equal to one, with vanishing gradient, on
`B(x₀, R/2)`, with values in `[0, 1]`, compact support in `B(x₀, R)` and gradient bounded by
`c₀ / R`, for a constant `c₀` depending only on the dimension. -/
private theorem exists_cutoff_ball :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1)))
      {R : ℝ}, 0 < R → ∃ ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ ball x₀ R ∧
        (∀ x, |ζ x| ≤ 1) ∧ (∀ x ∈ ball x₀ (R / 2), ζ x = 1 ∧ ∇ ζ x = 0) ∧
          ∀ x, ‖∇ ζ x‖ ≤ c₀ * R⁻¹ := by
  obtain ⟨c, hc, hcut⟩ := exists_forall_contDiff_cutoff_closedBall
      (E := EuclideanSpace ℝ (Fin (n + 1)))
  refine ⟨4 * c, by positivity, fun x₀ R hR => ?_⟩
  obtain ⟨ζ, hζ, hζ01, hζ1, hζsupp, hgζ, -⟩ :=
    hcut x₀ (r := R / 2) (R := 3 * R / 4) (by positivity) (by linarith)
  refine ⟨ζ, hζ, (isCompact_closedBall x₀ _).of_isClosed_subset (isClosed_tsupport ζ) hζsupp,
    hζsupp.trans (closedBall_subset_ball (by linarith)), fun x => ?_, fun x hx => ?_,
    fun x => (hgζ x).trans_eq (by field_simp; ring)⟩
  · obtain ⟨h0, h1⟩ := hζ01 ⟨x, rfl⟩
    rwa [abs_of_nonneg h0]
  · have hev : ζ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := Filter.mem_of_superset
      (isOpen_ball.mem_nhds hx) fun y hy => hζ1 (ball_subset_closedBall hy)
    exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const _ _)⟩

/-- The pointwise bound `‖ζ X + c W‖ ≤ ‖X‖ + k |c|` when `|ζ| ≤ 1` and `‖W‖ ≤ k`. -/
private theorem norm_smul_add_smul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ζ c k : ℝ} {X W : F} (hζ : |ζ| ≤ 1) (hW : ‖W‖ ≤ k) :
    ‖ζ • X + c • W‖ ≤ 1 * ‖X‖ + k * ‖c‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right hW (norm_nonneg _)

/-- The scalar datum `⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫` of a cutoff solution lies in `L^q`, with norm at most
`k (‖G‖_{q,B} + Λ ‖∇u‖_{q,B})` when `‖∇ζ‖ ≤ k` and `ζ` is supported in `B`. -/
private theorem memLp_and_eLpNorm_le_scalarDatum
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
      (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hLam : 0 ≤ Lam)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      (u : W1p volume Ω 2) {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {B : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hB : MeasurableSet B) {q : ℝ≥0∞} (hq : 1 ≤ q)
      {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hgζk : ∀ x, ‖∇ ζ x‖ ≤ k) (hgζ0 : ∀ x ∉ B, ∇ ζ x = 0)
    (hgq : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) q
      (volume.restrict B))
    (hGq : MemLp G q (volume.restrict B)) :
    MemLp (fun x => ⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) q
        volume ∧
      eLpNorm (fun x => ⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) q
        volume ≤ ENNReal.ofReal k * eLpNorm G q (volume.restrict B) +
          ENNReal.ofReal (Lam * k) * eLpNorm
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) q
            (volume.restrict B) := by
  refine memLp_and_eLpNorm_le_of_norm_le_add (f := fun x =>
      ⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) hB hq hk
    (mul_nonneg hLam hk)
    ((hGq.aestronglyMeasurable.inner (measurable_gradient ζ).aestronglyMeasurable).sub
      (aestronglyMeasurable_matrixBilinearForm_apply
        (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).restrict
        (measurable_gradient ζ).aestronglyMeasurable hgq.aestronglyMeasurable))
    (fun x hx => by simp [hgζ0 x hx]) hGq hgq fun x _ => ?_
  refine (norm_sub_le _ _).trans (add_le_add ((abs_real_inner_le_norm _ _).trans ?_)
    ((matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le (hbd x) (hgζk x) le_rfl))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hgζk x) (norm_nonneg _)

/-- The divergence datum `ζ G + (u - m) a ∇ζ` of a cutoff solution lies in `Lᵖ`, with norm at
most `‖G‖_{p,B} + Λ k ‖u - m‖_{p,B}` when `|ζ| ≤ 1`, `‖∇ζ‖ ≤ k` and `ζ` is supported in `B`. -/
private theorem memLp_and_eLpNorm_le_divergenceDatum
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ}
      (ha : AEStronglyMeasurable a volume)
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hLam : 0 ≤ Lam)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      (u : W1p volume Ω 2) {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {B : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hB : MeasurableSet B) {p : ℝ≥0∞} (hp : 1 ≤ p)
      {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hζ : Continuous ζ) (hζle : ∀ x, |ζ x| ≤ 1) {k : ℝ} (hk : 0 ≤ k) (hgζk : ∀ x, ‖∇ ζ x‖ ≤ k)
    (hζ0 : ∀ x ∉ B, ζ x = 0) (hgζ0 : ∀ x ∉ B, ∇ ζ x = 0) (m : ℝ)
    (hvum : MemLp (fun x => W1p.value u x - m) p (volume.restrict B))
    (hGp : MemLp G p (volume.restrict B)) :
    MemLp
      (fun x => ζ x • G x + (W1p.value u x - m) • (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
        (matrixBilinearForm (a x).transpose (∇ ζ x))) p volume ∧
      eLpNorm
        (fun x => ζ x • G x + (W1p.value u x - m) • (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
        (matrixBilinearForm (a x).transpose (∇ ζ x))) p volume ≤
          ENNReal.ofReal 1 * eLpNorm G p (volume.restrict B) +
            ENNReal.ofReal (Lam * k) * eLpNorm (fun x => W1p.value u x - m) p
              (volume.restrict B) := by
  have hwle : ∀ x, ‖(toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
      (matrixBilinearForm (a x).transpose (∇ ζ x))‖ ≤ Lam * k := fun x => by
    rw [LinearIsometryEquiv.norm_map]
    exact (matrixBilinearForm (a x).transpose).le_of_opNorm_le_of_le
      ((norm_matrixBilinearForm_transpose (a x)).trans_le (hbd x)) (hgζk x)
  refine memLp_and_eLpNorm_le_of_norm_le_add (f := fun x => ζ x • G x + (W1p.value u x - m) •
      (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm (matrixBilinearForm (a x).transpose (∇ ζ x)))
    hB hp zero_le_one (mul_nonneg hLam hk)
    ((hζ.aestronglyMeasurable.smul hGp.aestronglyMeasurable).add
      (hvum.aestronglyMeasurable.smul (aestronglyMeasurable_toDual_symm_transpose ha ζ).restrict))
    (fun x hx => by simp [hζ0 x hx, hgζ0 x hx]) hGp hvum fun x _ =>
      norm_smul_add_smul_le (hζle x) (hwle x)

/-- The gradient `ζ ∇u + (u - m) ∇ζ` of a cutoff solution lies in `Lᵖ` when `|ζ| ≤ 1`, `‖∇ζ‖ ≤ k`,
`ζ` is supported in `B` and `∇u, u ∈ Lᵖ(B)`. -/
private theorem memLp_cutoff_gradient {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Ω 2) {B : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hB : MeasurableSet B) {p : ℝ≥0∞} (hp : 1 ≤ p) {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      (hζ : Continuous ζ)
    (hζle : ∀ x, |ζ x| ≤ 1) {k : ℝ} (hk : 0 ≤ k) (hgζk : ∀ x, ‖∇ ζ x‖ ≤ k)
    (hζ0 : ∀ x ∉ B, ζ x = 0) (hgζ0 : ∀ x ∉ B, ∇ ζ x = 0) (m : ℝ)
    (hgp : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) p
      (volume.restrict B))
    (hvum : MemLp (fun x => W1p.value u x - m) p (volume.restrict B)) :
    MemLp (fun x => ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x) p volume := by
  refine (memLp_and_eLpNorm_le_of_norm_le_add
    (f := fun x => ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x) hB hp zero_le_one hk
    ((hζ.aestronglyMeasurable.smul hgp.aestronglyMeasurable).add
      (hvum.aestronglyMeasurable.smul (measurable_gradient ζ).aestronglyMeasurable))
    (fun x hx => by simp [hζ0 x hx, hgζ0 x hx]) hgp hvum fun x _ =>
      norm_smul_add_smul_le (hζle x) (hgζk x)).1

/-- Where the cutoff `ζ` is one with vanishing gradient, the gradient `ζ ∇u + (u - m) ∇ζ` of
`ζ (u - m)` is `∇u`, so the `Lᵖ` norm of `∇u` there is at most that of the whole gradient. -/
private theorem eLpNorm_gradient_le_of_ae_eq_cutoff {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Ω 2) {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : MeasurableSet S)
    {v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {m : ℝ}
    (hv : ∀ᵐ x, W1p.gradient v x = ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x)
    (hζ1 : ∀ x ∈ S, ζ x = 1 ∧ ∇ ζ x = 0) (p : ℝ≥0∞) :
    eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) p
      (volume.restrict S) ≤ eLpNorm (⇑(W1p.gradient v)) p volume := by
  refine (eLpNorm_congr_ae ?_).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem hS] with x hx hxS
  rw [hx, (hζ1 x hxS).1, (hζ1 x hxS).2, one_smul, smul_zero, add_zero]

/-- The gradient `ζ ∇u + (u - m) ∇ζ` of a cutoff `ζ` supported in `B(x₀, R)` vanishes almost
everywhere outside `B(x₀, r₀ / 4)` when `4 R ≤ r₀`. -/
private theorem ae_gradient_eq_zero_of_cutoff {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Ω 2) {v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {m : ℝ}
    (hv : ∀ᵐ x, W1p.gradient v x = ζ x • W1p.gradient u x + (W1p.value u x - m) • ∇ ζ x)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R r₀ : ℝ} (hRr₀ : 4 * R ≤ r₀)
    (hζ0 : ∀ x ∉ ball x₀ R, ζ x = 0) (hgζ0 : ∀ x ∉ ball x₀ R, ∇ ζ x = 0) :
    ∀ᵐ x, x ∉ ball x₀ (r₀ / 4) → W1p.gradient v x = 0 := by
  filter_upwards [hv] with x hx hxr
  have hxB : x ∉ ball x₀ R := fun hxB => hxr (ball_subset_ball (by linarith) hxB)
  rw [hx, hζ0 x hxB, hgζ0 x hxB, zero_smul, smul_zero, add_zero]

/-- **The interior `W^{1,p}` estimate for coefficients of small mean oscillation below a radius.**
Let `ℝ^{n+1}` have dimension at least two, let `2 < p < ∞` and `1 / q = 1 / p + 1 / (n + 1)`, and
let `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with
the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}` bounded by `Λ`,
such that on every ball of radius at most `r₀` some constant matrix, uniformly elliptic with
constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in an open set `Ω`, and let `B(x₀, R) ⊆ Ω` with `4R ≤ r₀`. If `u`,
`∇u` and `G` lie in `Lᵖ(B(x₀, R))`, then for every constant `m`

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B)} + R⁻¹ (‖u - m‖_{Lᵖ(B)} + ‖∇u‖_{L^q(B)}))`,

with `B = B(x₀, R)`. Both sides scale in the same way under dilations, since `q` is the Sobolev
exponent below `p`. The constants depend neither on `r₀`, `R`, `x₀` nor on `Ω`; the radius enters
only through the smallness of the mean oscillation of `a` on balls of radius at most `r₀`, as for
coefficients of vanishing mean oscillation. The gradient on the right is measured in the weaker
`L^q` norm. -/
theorem exists_eLpNorm_gradient_ball_le_of_setAverage_le (hn : n ≠ 0) {p q : ℝ≥0} (hp : 2 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ + ((n : ℝ) + 1)⁻¹) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) (m : ℝ)
          (x₀ : EuclideanSpace ℝ (Fin (n + 1))) {R : ℝ}, 0 < R → 4 * R ≤ r₀ →
          ball x₀ R ⊆ Ω →
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p (volume.restrict (ball x₀ R)) →
          MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p
            (volume.restrict (ball x₀ R)) →
          MemLp G p (volume.restrict (ball x₀ R)) →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1))) p (volume.restrict (ball x₀ (R / 2))) ≤
            C * (eLpNorm G p (volume.restrict (ball x₀ R)) + ENNReal.ofReal R⁻¹ *
              (eLpNorm (fun x => W1p.value u x - m) p (volume.restrict (ball x₀ R)) +
                eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
                  EuclideanSpace ℝ (Fin (n + 1))) q (volume.restrict (ball x₀ R)))) := by
  obtain ⟨hq1, hqp⟩ := one_lt_and_le_of_inv_eq_inv_add_inv hn hp hpq
  have hpq' : (p : ℝ)⁻¹ = (q : ℝ)⁻¹ - 1 / Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin, Nat.cast_add_one, hpq, one_div, add_sub_cancel_right]
  obtain ⟨CW, δ, hδ, hW⟩ := exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero
    (n := n) (p := (p : ℝ≥0∞)) (by exact_mod_cast hp) ENNReal.coe_ne_top lam Lam
  obtain ⟨CD, hD⟩ := exists_eLpNorm_le_and_integral_inner_gradient_eq volume hq1 hpq'
  obtain ⟨c₀, hc₀, hcut⟩ := exists_cutoff_ball (n := n)
  refine ⟨CW * (1 + c₀.toNNReal * (Lam.toNNReal + CD + CD * Lam.toNNReal)) *
    (1 + (volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toNNReal ^ ((n : ℝ) + 1)⁻¹), δ, hδ,
    fun {a r₀} ha hbd hosc Ω u G m x₀ R hR hRr₀ hball hu hgp hvp hGp => ?_⟩
  have : IsFiniteMeasure (volume.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast one_le_two.trans hp.le
  have hqp' : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp
  have hLam : 0 ≤ Lam := (norm_nonneg (matrixBilinearForm (a 0))).trans (hbd 0)
  obtain ⟨ζ, hζ, hζc, hζB, hζle, hζ1, hgζk⟩ := hcut x₀ hR
  have hζ0 : ∀ x ∉ ball x₀ R, ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hζB h)
  have hgζ0 : ∀ x ∉ ball x₀ R, ∇ ζ x = 0 := fun x hx =>
    gradient_of_notMem_tsupport fun h => hx (hζB h)
  have hvum := hvp.sub (memLp_const m)
  -- The scalar datum, in `L^q`, is minus the divergence of a field `H ∈ Lᵖ`.
  obtain ⟨hhq, hhle⟩ := memLp_and_eLpNorm_le_scalarDatum ha hbd hLam u measurableSet_ball
    (by exact_mod_cast hq1.le) (by positivity) hgζk hgζ0 (hgp.mono_exponent hqp')
    (hGp.mono_exponent hqp')
  obtain ⟨H, -, hHle, hHh⟩ := hD _ hhq (HasCompactSupport.intro hζc fun x hx => by
    simp [gradient_of_notMem_tsupport hx])
  have hHp : MemLp H p volume :=
    hHle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hhq.eLpNorm_lt_top)
  obtain ⟨hG₁p, hG₁le⟩ := memLp_and_eLpNorm_le_divergenceDatum ha hbd hLam u (G := G)
    measurableSet_ball hp1 hζ.continuous hζle (by positivity) hgζk hζ0 hgζ0 m hvum hGp
  -- The whole-space estimate for the cutoff `ζ (u - m)`.
  obtain ⟨v, -, hv⟩ := W1p.exists_top_value_gradient_ae_eq_mul_sub_const (by norm_num) u hζ
    hζc (hζB.trans hball) m
  have hvgp := memLp_cutoff_gradient u measurableSet_ball hp1 hζ.continuous hζle (by positivity)
    hgζk hζ0 hgζ0 m hgp hvum
  have hWv := hW ha hbd hosc x₀ v _ (ae_gradient_eq_zero_of_cutoff u hv hRr₀ hζ0 hgζ0)
    (energyFormH1_eq_integral_inner_of_cutoff ha hbd hLam u hball (hGp.integrable hp1) hu hζ hζc
      hζB m hv (hHp.locallyIntegrable hp1) hHh)
    (hvgp.ae_eq (hv.mono fun x hx => hx.symm)) (hG₁p.add hHp)
  -- On `B(x₀, R/2)` the cutoff is one, so the gradient there is `∇u`.
  refine ((eLpNorm_gradient_le_of_ae_eq_cutoff u measurableSet_ball hv hζ1 p).trans
    (hWv.trans (mul_le_mul_right (eLpNorm_add_le hp1) _))).trans
    (le_trans ?_ (mul_add_mul_add_le_mul_add hc₀ hLam
      (ofReal_inv_mul_eLpNorm_ball_le hpq hqp' hR hGp.aestronglyMeasurable)))
  gcongr
  exact hHle.trans (by gcongr)

end Interior

end PDE

end TauCeti
