/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Lazard.Complexification
public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Factorization
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Puiseux Laurent branches along Lazard monomial deformations

Let a real polynomial in a distinguished variable have leading coefficient, constant
coefficient, and formal discriminant with locally constant finite Lazard valuations along
real analytic centers. A common evaluator gives monomial deformations of a complexification
of the centers. Along these deformations, construct a complete distinct Puiseux splitting
and analytic extensions of the branches after removing their poles. Near each parameter
point the branches have Laurent-power forms with analytic units. The integer exponent of each
global branch label is constant throughout the parameter ball.
Ordinary specialization at the centers may be nullified.

The evaluator can also separate any prescribed finite set of base exponents, so it can be
chosen for the removed base exponents of the polynomial being lifted. The complex centers
respect conjugation. The conclusion constructs the root labels; neither a splitting nor
complex valuation constancy is assumed. Discriminants are compared with the formal
coefficient polynomial only away from the exceptional hyperplane, where the leading
coefficient guarantees preservation of degree.

The construction uses `TauCeti.exists_complexification_isLazardEvaluator_analytic_units`
and `TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_laurent`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), §5.2, application of
  Corollary 4.2 to the monomial deformation.
-/

public section

open Filter Finsupp Function Metric Set Topology

namespace Polynomial

variable {σ ι : Type*} [LinearOrder σ] [Fintype σ] [Fintype ι]

/-- Locally constant finite Lazard valuations of the formal leading coefficient, constant
coefficient, and discriminant along real analytic centers construct Puiseux Laurent branches
of the monomial deformation. The centers have one conjugation-compatible complex extension,
and the evaluator also separates the prescribed finite set `V`. After the factorial power
substitution, the same distinct root labels have analytic pole-removed extensions and
Laurent-power forms whose exponents are constant on the parameter ball and bounded below by the
negative substituted leading-coefficient weight. The analytic leading-coefficient unit is retained
for the same deformation, before the factorial substitution. Nullified ordinary fibers
are allowed; degree zero is included. -/
theorem exists_complexification_isLazardEvaluator_nonmonic_laurent
    (p : Polynomial (MvPolynomial σ ℝ)) {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ}
    (hφ : AnalyticAt ℝ φ a) (vLead vConst vDiscr : σ →₀ ℕ)
    (hlead : ∀ᶠ x in 𝓝 a, p.leadingCoeff.lazardValuation (φ x) = toLex vLead)
    (hconst : ∀ᶠ x in 𝓝 a, (p.coeff 0).lazardValuation (φ x) = toLex vConst)
    (hdiscr : ∀ᶠ x in 𝓝 a, p.discr.lazardValuation (φ x) = toLex vDiscr)
    {V : Set (σ →₀ ℕ)} (hV : V.Finite) :
    ∃ ρ > (0 : ℝ), ∃ Φ : (ι → ℂ) → σ → ℂ, ∃ c : σ → ℕ,
      TauCeti.IsLazardEvaluator ({vLead, vConst, vDiscr} ∪ V) c ∧
      AnalyticOnNhd ℂ Φ (ball (fun j ↦ (a j : ℂ)) ρ) ∧
      (∀ x ∈ ball a ρ, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) ∧
      (∀ z, Φ (star z) = star (Φ z)) ∧
      ∃ u : (ι → ℂ) × ℂ → ℂ,
        AnalyticOnNhd ℂ u (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) ∧
        (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, u b ≠ 0 ∧
          MvPolynomial.eval₂ Complex.ofRealHom
            (fun j ↦ Φ b.1 j + b.2 ^ c j) p.leadingCoeff =
              b.2 ^ Finsupp.weight c vLead * u b) ∧
      ∃ R > (0 : ℝ), R ^ p.natDegree.factorial ≤ ρ ∧
        ∃ r g : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ,
          (∀ i, AnalyticOnNhd ℂ (r i)
            (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}))) ∧
          (∀ i, AnalyticOnNhd ℂ (g i)
              (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 R) ∧
            EqOn (g i) (fun b ↦ b.2 ^ (p.natDegree.factorial *
              Finsupp.weight c vLead) * r i b)
              (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}))) ∧
          (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}),
            Injective (fun i ↦ r i b) ∧
            p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
                (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j))) =
              C (MvPolynomial.eval₂ Complex.ofRealHom
                (fun j ↦ Φ b.1 j + b.2 ^ (p.natDegree.factorial * c j)) p.leadingCoeff) *
                ∏ i, (X - C (r i b))) ∧
          ∃ e : Fin p.natDegree → ℤ,
            ∀ x ∈ ball (fun j ↦ (a j : ℂ)) ρ,
              ∃ w : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ,
              (∀ i, -(p.natDegree.factorial * Finsupp.weight c vLead : ℤ) ≤ e i) ∧
              (∀ i, AnalyticAt ℂ (w i) (x, 0)) ∧ (∀ i, w i (x, 0) ≠ 0) ∧
              ∀ᶠ b in 𝓝 (x, (0 : ℂ)), (∀ i, w i b ≠ 0) ∧
                (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * w i b) := by
  classical
  -- Prepare all three formal coefficient polynomials with the same centers and evaluator.
  let P : Fin 3 → MvPolynomial σ ℝ := ![p.leadingCoeff, p.coeff 0, p.discr]
  let v : Fin 3 → σ →₀ ℕ := ![vLead, vConst, vDiscr]
  have hval (i : Fin 3) : ∀ᶠ x in 𝓝 a, (P i).lazardValuation (φ x) = toLex (v i) := by
    fin_cases i
    · simpa [P, v] using hlead
    · simpa [P, v] using hconst
    · simpa [P, v] using hdiscr
  have hrange : Set.range v = {vLead, vConst, vDiscr} := by
    dsimp only [v]
    rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]
  obtain ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, hu, hforms, _⟩ :=
    TauCeti.exists_complexification_isLazardEvaluator_analytic_units P hφ v hval hV
  let F : (ι → ℂ) × ℂ → ℂ[X] := fun b ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun j ↦ Φ b.1 j + b.2 ^ c j))
  have hcoeff (b : (ι → ℂ) × ℂ) (i : ℕ) : (F b).coeff i =
      MvPolynomial.eval (fun j ↦ Φ b.1 j + b.2 ^ c j)
        ((p.coeff i).map Complex.ofRealHom) := by
    simp only [F, coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  have hFA (i : ℕ) : AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i)
      (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) := by
    intro b hb
    simp only [hcoeff]
    have h := AnalyticAt.aeval_mvPolynomial
      (f := fun b : (ι → ℂ) × ℂ ↦ fun j ↦ Φ b.1 j + b.2 ^ c j)
      (fun j ↦ ((analyticAt_pi_iff.1 (hΦ b.1 hb.1)) j).comp analyticAt_fst |>.add
        (analyticAt_snd.pow (c j))) ((p.coeff i).map Complex.ofRealHom)
    simpa only [MvPolynomial.aeval_eq_eval] using h
  have hL (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) :
      (F b).coeff p.natDegree = b.2 ^ Finsupp.weight c vLead * u 0 b := by
    simpa [hcoeff, P, v] using
      (hforms b hb 0).2
  have hC (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) :
      (F b).coeff 0 = b.2 ^ Finsupp.weight c vConst * u 1 b := by
    simpa [hcoeff, P, v] using (hforms b hb 1).2
  -- Nonzero leading coefficient preserves the formal degree off the hyperplane.
  have hdeg (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 ρ \ {0})) :
      (F b).natDegree = p.natDegree := by
    apply natDegree_map_of_leadingCoeff_ne_zero
    have h := hL b ⟨hb.1, hb.2.1⟩
    rw [hcoeff, coeff_natDegree] at h
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map, h]
    exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hforms b ⟨hb.1, hb.2.1⟩ 0).1
  have hD (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 ρ \ {0})) :
      (F b).discr ≠ 0 := by
    -- The degree-preserving discriminant map theorem is used only on this punctured set.
    rw [discr_map_of_natDegree_eq _ (hdeg b hb)]
    have h := (hforms b ⟨hb.1, hb.2.1⟩ 2).2
    simp only [P, v, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map, h]
    exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hforms b ⟨hb.1, hb.2.1⟩ 2).1
  -- A complex parameter ball is simply connected, allowing the constructed Laurent splitting.
  let : ContractibleSpace (ball (fun j ↦ (a j : ℂ)) ρ) :=
    (convex_ball _ ρ).contractibleSpace ⟨_, mem_ball_self hρ⟩
  let : SimplyConnectedSpace (ball (fun j ↦ (a j : ℂ)) ρ) :=
    SimplyConnectedSpace.ofContractible _
  obtain ⟨R, hR, hfit, r, g, hr, hg, hfac, hLaurent⟩ :=
    TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_laurent isOpen_ball hρ
      (fun i _ ↦ hFA i) hdeg hD (hu 0) (fun b hb ↦ (hforms b hb 0).1)
      (hu 1) (fun b hb ↦ (hforms b hb 1).1) hL hC
  refine ⟨ρ, hρ, Φ, c, hrange ▸ hc, hΦ, hreal, hstar,
    u 0, hu 0, ?_, R, hR, hfit, r, g, hr, hg, ?_, hLaurent⟩
  · intro b hb
    simpa only [P, v, Matrix.cons_val_zero, MvPolynomial.eval₂_eq_eval_map] using hforms b hb 0
  intro b hb
  refine ⟨(hfac b hb).1, ?_⟩
  simpa only [F, coeff_map, MvPolynomial.coe_eval₂Hom, coeff_natDegree, ← pow_mul]
    using (hfac b hb).2

end Polynomial
