/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.MeanOscillation
import TauCeti.Analysis.PDE.Regularity.SharpFunctionMethod
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.SmallMeanOscillation
import TauCeti.MeasureTheory.Integral.Average

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

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`: the
  `W^{1,p}` estimate for coefficients of small mean oscillation, `2 < p < ∞`.
* `TauCeti.PDE.exists_eqOn_ball_and_forall_setAverage_le`: a coefficient field of small mean
  oscillation below a radius `r₀` agrees on a ball `B(x₀, R)`, `4R ≤ r₀`, with a field of small
  mean oscillation at every scale.
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
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le (n := n)
    (E := EuclideanSpace ℝ (Fin (n + 1))) (F := EuclideanSpace ℝ (Fin (n + 1))) hp hp_top
    (decayConst n lam Lam) (forcingConst n lam Lam) (forcingConst n lam Lam) (2 * Lam)
  refine ⟨C, δ, hδ, fun {a} ha hbd hosc u G hu hint hgp hGp =>
    h hint hgp hGp fun q q' hq hqp c ρ κ hρ hκ => ?_⟩
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
    exact energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero hba 0 0 (ae_restrict_of_ae hsupp) _

end Localization

end PDE

end TauCeti
