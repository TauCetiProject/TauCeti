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
and analytic extensions of the branches after removing their poles. The Laurent exponents
and nowhere-zero analytic units are global on the parameter product.
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

/-- A statement eventually true along a filter for each of the three indices of `Fin 3`. -/
private lemma eventually_forall_fin_three {α : Type*} {l : Filter α} {q : Fin 3 → α → Prop}
    (h0 : ∀ᶠ x in l, q 0 x) (h1 : ∀ᶠ x in l, q 1 x) (h2 : ∀ᶠ x in l, q 2 x) :
    ∀ i, ∀ᶠ x in l, q i x := fun i ↦ by
  fin_cases i <;> assumption

/-- The coefficients of a real multivariate polynomial pushed to `ℂ` and evaluated at `x`. -/
private lemma coeff_map_eval₂Hom {σ : Type*} (p : Polynomial (MvPolynomial σ ℝ)) (x : σ → ℂ)
    (i : ℕ) :
    (p.map (MvPolynomial.eval₂Hom Complex.ofRealHom x)).coeff i =
      MvPolynomial.eval x ((p.coeff i).map Complex.ofRealHom) := by
  simp only [coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]

/-- The coefficients of the complexified polynomial evaluated along the monomial deformation
`b ↦ Φ b.1 + b.2 ^ c` are analytic in `b`. -/
private lemma analyticOnNhd_coeff_map_eval₂Hom {σ ι : Type*} [Fintype σ] [Fintype ι]
    (p : Polynomial (MvPolynomial σ ℝ)) {Φ : (ι → ℂ) → σ → ℂ} (c : σ → ℕ)
    {S : Set (ι → ℂ)} {T : Set ℂ} (hΦ : AnalyticOnNhd ℂ Φ S) (i : ℕ) :
    AnalyticOnNhd ℂ (fun b : (ι → ℂ) × ℂ ↦
      (p.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun j ↦ Φ b.1 j + b.2 ^ c j))).coeff i)
      (S ×ˢ T) := by
  intro b hb
  simp only [coeff_map_eval₂Hom]
  have h := AnalyticAt.aeval_mvPolynomial
    (f := fun b : (ι → ℂ) × ℂ ↦ fun j ↦ Φ b.1 j + b.2 ^ c j)
    (fun j ↦ ((analyticAt_pi_iff.1 (hΦ b.1 hb.1)) j).comp analyticAt_fst |>.add
      (analyticAt_snd.pow (c j))) ((p.coeff i).map Complex.ofRealHom)
  simpa only [MvPolynomial.aeval_eq_eval] using h

/-- If the leading coefficient and the discriminant of `p` do not vanish at `x`, neither does
the discriminant of the complexified polynomial. -/
private lemma discr_map_eval₂Hom_ne_zero {σ : Type*} (p : Polynomial (MvPolynomial σ ℝ))
    {x : σ → ℂ} (hl : MvPolynomial.eval₂ Complex.ofRealHom x p.leadingCoeff ≠ 0)
    (hd : MvPolynomial.eval₂ Complex.ofRealHom x p.discr ≠ 0) :
    (p.map (MvPolynomial.eval₂Hom Complex.ofRealHom x)).discr ≠ 0 := by
  rw [discr_map_of_natDegree_eq _ (natDegree_map_of_leadingCoeff_ne_zero _ hl)]
  exact hd

variable {σ ι : Type*} [LinearOrder σ] [Fintype σ] [Fintype ι]

/-- Locally constant finite Lazard valuations of the formal leading coefficient, constant
coefficient, and discriminant along real analytic centers construct Puiseux Laurent branches
of the monomial deformation. The centers have one conjugation-compatible complex extension,
and the evaluator also separates the prescribed finite set `V`. After the factorial power
substitution, the same distinct root labels have analytic pole-removed extensions and
Laurent-power forms whose exponents are constant on the parameter ball and bounded below by the
negative substituted leading-coefficient weight. Their analytic units are nowhere zero on the
whole parameter product, including its distinguished hyperplane. The analytic leading-coefficient
and formal-discriminant units are retained for the same deformation, before the factorial
substitution. Nullified ordinary fibers are allowed; degree zero is included. -/
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
      ∃ u v : (ι → ℂ) × ℂ → ℂ,
        AnalyticOnNhd ℂ u (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) ∧
        (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, u b ≠ 0 ∧
          MvPolynomial.eval₂ Complex.ofRealHom
            (fun j ↦ Φ b.1 j + b.2 ^ c j) p.leadingCoeff =
              b.2 ^ Finsupp.weight c vLead * u b) ∧
        AnalyticOnNhd ℂ v (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) ∧
        (∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ, v b ≠ 0 ∧
          MvPolynomial.eval₂ Complex.ofRealHom
            (fun j ↦ Φ b.1 j + b.2 ^ c j) p.discr =
              b.2 ^ Finsupp.weight c vDiscr * v b) ∧
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
            ∃ w : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ,
              (∀ i, -(p.natDegree.factorial * Finsupp.weight c vLead : ℤ) ≤ e i) ∧
              (∀ i, AnalyticOnNhd ℂ (w i)
                (ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 R)) ∧
              (∀ i, ∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 R, w i b ≠ 0) ∧
              ∀ b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 R \ {0}),
                ∀ i, r i b = b.2 ^ e i * w i b := by
  classical
  -- Prepare all three formal coefficient polynomials with the same centers and evaluator.
  let P : Fin 3 → MvPolynomial σ ℝ := ![p.leadingCoeff, p.coeff 0, p.discr]
  let v : Fin 3 → σ →₀ ℕ := ![vLead, vConst, vDiscr]
  have hval : ∀ i : Fin 3, ∀ᶠ x in 𝓝 a, (P i).lazardValuation (φ x) = toLex (v i) :=
    eventually_forall_fin_three hlead hconst hdiscr
  have hrange : Set.range v = {vLead, vConst, vDiscr} := by
    rw [show v = ![vLead, vConst, vDiscr] from rfl, Matrix.range_cons,
      Matrix.range_cons_cons_empty, Set.singleton_union]
  obtain ⟨ρ, hρ, Φ, c, hc, hΦ, hreal, hstar, u, hu, hforms, _⟩ :=
    TauCeti.exists_complexification_isLazardEvaluator_analytic_units P hφ v hval hV
  let F : (ι → ℂ) × ℂ → ℂ[X] := fun b ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun j ↦ Φ b.1 j + b.2 ^ c j))
  have hL (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) :
      (F b).coeff p.natDegree = b.2 ^ Finsupp.weight c vLead * u 0 b := by
    simpa [F, coeff_map_eval₂Hom, P, v] using (hforms b hb 0).2
  have hC (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ ball 0 ρ) :
      (F b).coeff 0 = b.2 ^ Finsupp.weight c vConst * u 1 b := by
    simpa [F, coeff_map_eval₂Hom, P, v] using (hforms b hb 1).2
  -- Nonzero leading coefficient preserves the formal degree off the hyperplane.
  have hnz (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 ρ \ {0})) (k : Fin 3) :
      MvPolynomial.eval₂ Complex.ofRealHom
        (fun j ↦ Φ b.1 j + b.2 ^ c j) (P k) ≠ 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map, (hforms b ⟨hb.1, hb.2.1⟩ k).2]
    exact mul_ne_zero (pow_ne_zero _ hb.2.2) (hforms b ⟨hb.1, hb.2.1⟩ k).1
  have hdeg (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 ρ \ {0})) :
      (F b).natDegree = p.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ (hnz b hb 0)
  have hD (b) (hb : b ∈ ball (fun j ↦ (a j : ℂ)) ρ ×ˢ (ball 0 ρ \ {0})) :
      (F b).discr ≠ 0 :=
    discr_map_eval₂Hom_ne_zero p (hnz b hb 0) (hnz b hb 2)
  -- A complex parameter ball is simply connected, allowing the constructed Laurent splitting.
  let : ContractibleSpace (ball (fun j ↦ (a j : ℂ)) ρ) :=
    (convex_ball _ ρ).contractibleSpace ⟨_, mem_ball_self hρ⟩
  let : SimplyConnectedSpace (ball (fun j ↦ (a j : ℂ)) ρ) :=
    SimplyConnectedSpace.ofContractible _
  obtain ⟨R, hR, hfit, r, g, hr, hg, hfac, e, w, he, hw, hw0, hform⟩ :=
    TauCeti.Polynomial.exists_analyticOnNhd_nonmonic_laurent isOpen_ball hρ
      (fun i _ ↦ analyticOnNhd_coeff_map_eval₂Hom p c hΦ i) hdeg hD (hu 0)
      (fun b hb ↦ (hforms b hb 0).1)
      (hu 1) (fun b hb ↦ (hforms b hb 1).1) hL hC
  refine ⟨ρ, hρ, Φ, c, hrange ▸ hc, hΦ, hreal, hstar,
    u 0, u 2, hu 0, ?_, hu 2, ?_, R, hR, hfit, r, g, hr, hg, ?_, e, w, he, hw, hw0, hform⟩
  · intro b hb
    simpa only [P, v, Matrix.cons_val_zero, MvPolynomial.eval₂_eq_eval_map] using hforms b hb 0
  · intro b hb
    simpa only [P, v, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      MvPolynomial.eval₂_eq_eval_map] using hforms b hb 2
  · intro b hb
    refine ⟨(hfac b hb).1, ?_⟩
    simpa only [F, coeff_map, MvPolynomial.coe_eval₂Hom, coeff_natDegree, ← pow_mul]
      using (hfac b hb).2

end Polynomial
