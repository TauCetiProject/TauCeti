/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Monic.Reciprocal
public import TauCeti.Analysis.Polynomial.Puiseux.Monic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Puiseux splitting in reciprocal root coordinates

A complex polynomial family whose formal discriminant is a distinguished-coordinate power
times an analytic unit splits in normalized reciprocal coordinates after a power substitution
on a full disc. Translate to a nonroot of the central fiber, reverse at the formal degree,
and apply analytic monic normalization followed by monic Puiseux splitting. No condition on
the order of the original leading coefficient is needed.

The original fibers may drop degree. The factorization retains the extra zero roots of the
formal reversal at such points. Recovering the original finite roots uses reciprocal
coordinates and the existing root equation for integral normalization.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), Sections 2–3 (reciprocal coordinates in the discriminant theorem).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4 (parameterized splitting).
-/

public section

open Metric Polynomial Set

namespace Polynomial

variable {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A nonnullified complex polynomial family with formal discriminant a power times an
analytic unit has a full-disc analytic splitting in normalized reciprocal coordinates.
The translation center `τ` need only avoid the central fiber's roots. The original fibers
may drop degree. Reversal is taken before specialization, at the original formal degree. -/
theorem exists_analyticOnNhd_reciprocal_prod_X_sub_C_of_discr_eq_pow_mul
    (p : Polynomial (MvPolynomial σ ℂ)) {Φ : E × ℂ → σ → ℂ}
    {U : Set E} {x₀ : E} {R : ℝ} (τ : ℂ)
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hR : 0 < R)
    (hΦ : ∀ i, AnalyticOnNhd ℂ (fun b ↦ Φ b i) (U ×ˢ ball 0 R))
    (hτ : (p.map (MvPolynomial.eval (Φ (x₀, 0)))).eval τ ≠ 0)
    {a : ℕ} {u : E × ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hdiscr : ∀ b ∈ U ×ˢ ball 0 R,
      MvPolynomial.eval (Φ b) p.discr = b.2 ^ a * u b) :
    ∃ ρ > (0 : ℝ), ball x₀ ρ ⊆ U ∧ ∃ R' > (0 : ℝ),
      R' ^ p.natDegree.factorial ≤ R ∧
      ∃ r : Fin p.natDegree → E × ℂ → ℂ,
        (∀ i, AnalyticOnNhd ℂ (r i) (ball x₀ ρ ×ˢ ball 0 R')) ∧
        (∀ b ∈ ball x₀ ρ ×ˢ ball 0 R',
          ((p.comp (X + C (MvPolynomial.C τ))).reverse.map
            (MvPolynomial.eval (Φ (b.1, b.2 ^ p.natDegree.factorial)))).integralNormalization =
              ∏ i, (X - C (r i b))) ∧
        ∀ b ∈ ball x₀ ρ ×ˢ (ball 0 R' \ {0}), Function.Injective (fun i ↦ r i b) := by
  obtain ⟨ε, hε, hεS, Q, hQA, hQ⟩ := p.exists_analytic_monic_reciprocal_normalization (Φ := Φ)
    (S := U ×ˢ ball 0 R) (x₀ := (x₀, 0)) τ (hU.prod isOpen_ball) ⟨hx₀, mem_ball_self hR⟩ hΦ hτ
  -- Shrink to a product of balls inside the nonroot neighborhood.
  let ρ := min ε R
  have hρ : 0 < ρ := lt_min hε hR
  have hball : ball x₀ ρ ×ˢ ball (0 : ℂ) ρ ⊆ ball (x₀, 0) ε := by
    rw [ball_prod_same x₀ (0 : ℂ) ρ]
    exact ball_subset_ball (min_le_left ε R)
  have hS : ball x₀ ρ ×ˢ ball (0 : ℂ) ρ ⊆ U ×ˢ ball 0 R := hball.trans hεS
  have hbase : ball x₀ ρ ⊆ U := fun x hx ↦ (hS (a := (x, 0)) ⟨hx, mem_ball_self hρ⟩).1
  have hv : AnalyticOnNhd ℂ
      (fun b ↦ (p.map (MvPolynomial.eval (Φ b))).eval τ) (ball x₀ ρ ×ˢ ball 0 ρ) := by
    have h := AnalyticOnNhd.aeval_mvPolynomial hΦ (p.eval (MvPolynomial.C τ))
    have heq (b) : MvPolynomial.eval (Φ b) (p.eval (MvPolynomial.C τ)) =
        (p.map (MvPolynomial.eval (Φ b))).eval τ := by
      rw [← eval₂_at_apply, eval_map]
      simp
    simpa only [MvPolynomial.aeval_eq_eval, heq] using h.mono hS
  -- The normalization factor is an analytic unit, preserving the discriminant exponent.
  let v := fun b ↦ (p.map (MvPolynomial.eval (Φ b))).eval τ ^
    ((p.natDegree - 1) * (p.natDegree - 2)) * u b
  have hvA : AnalyticOnNhd ℂ v (ball x₀ ρ ×ˢ ball 0 ρ) :=
    (hv.pow _).mul (hu.mono hS)
  have hv0 : ∀ b ∈ ball x₀ ρ ×ˢ ball 0 ρ, v b ≠ 0 := fun b hb ↦
    mul_ne_zero (pow_ne_zero _ (hQ b (hball hb)).1) (hu0 b (hS hb))
  have hQdiscr : ∀ b ∈ ball x₀ ρ ×ˢ ball 0 ρ, (Q b).discr = b.2 ^ a * v b := by
    intro b hb
    rw [(hQ b (hball hb)).2.2.2.2, hdiscr b (hS hb)]
    dsimp only [v]
    ring
  -- A parameter ball is simply connected, so the existing monic splitting applies.
  let : ContractibleSpace (ball x₀ ρ) :=
    (convex_ball x₀ ρ).contractibleSpace ⟨x₀, mem_ball_self hρ⟩
  let : SimplyConnectedSpace (ball x₀ ρ) := SimplyConnectedSpace.ofContractible _
  obtain ⟨R', hR', hfit, r, hr, hfac, hinj, _⟩ :=
    TauCeti.Polynomial.exists_analyticOnNhd_prod_X_sub_C_of_discr_eq_pow_mul
      isOpen_ball hρ (fun i _ ↦ (hQA i).mono hball)
      (fun b hb ↦ (hQ b (hball hb)).2.1)
      (fun b hb ↦ (hQ b (hball hb)).2.2.1) hvA hv0 hQdiscr
  refine ⟨ρ, hρ, hbase, R', hR', hfit.trans (min_le_right ε R), r, hr, ?_, hinj⟩
  intro b hb
  have hsub : (b.1, b.2 ^ p.natDegree.factorial) ∈ ball x₀ ρ ×ˢ ball 0 ρ := by
    refine ⟨hb.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hb.2) (norm_nonneg _)
      p.natDegree.factorial_ne_zero).trans_le hfit
  rw [← (hQ _ (hball hsub)).2.2.2.1]
  exact hfac b hb

end Polynomial
