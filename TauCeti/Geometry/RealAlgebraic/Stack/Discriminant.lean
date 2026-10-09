/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Discriminant
public import TauCeti.Geometry.RealAlgebraic.Stack.Puiseux

/-!
# Local monic delineability from constant discriminant order

A monic polynomial with real polynomial coefficients has a local delineation along an
analytic parametrization on which its formal discriminant has constant finite ambient order.
The sections extend to real analytic functions, have constant positive root multiplicities,
and account for all real roots; signs are constant on every section and sector.

The construction starts with the real discriminant-order condition, not a supplied complex
splitting or a hypothesis of constant root multiplicities. Multiple roots at the center,
constant polynomials and families without real roots are included. This is the monic local
analytic delineability conclusion, not a theorem about ambient order on the root sections.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Metric Polynomial Topology

namespace TauCeti

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

/-- A monic polynomial family along a real analytic parametrization has a delineation on
some positive-radius ball if the formal discriminant has constant finite ambient order.
All root sections admit analytic extensions to that ball. No distinct-root-count or
multiplicity-invariance hypothesis is required. -/
theorem _root_.Polynomial.exists_delineation_of_monic_of_orderAt_discr_eq
    (p : Polynomial (MvPolynomial σ ℝ)) (hp : p.Monic)
    {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m) :
    ∃ ε > 0, ∃ D : Delineation (fun (_ : Unit) (x : ball a ε) ↦
      p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))),
      ∀ i, ∃ s : (ι → ℝ) → ℝ, AnalyticOnNhd ℝ s (ball a ε) ∧
        ∀ x : ball a ε, D.root i x = s x := by
  obtain ⟨Φ, v, r, u, -, hreal, hr, hu, hu0, hsplit⟩ :=
    p.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq hp hφ hm
  let P : (ι → ℂ) × ℂ → ℂ[X] := fun z ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
      (Φ z.1 + z.2 ^ p.natDegree.factorial • (fun i ↦ (v i : ℂ))))
  let ψ : (ι → ℝ) → ι → ℂ := fun x i ↦ (x i : ℂ)
  have hψ : AnalyticAt ℝ ψ a := by
    apply analyticAt_pi_iff.2
    intro i
    exact Complex.ofRealCLM.analyticAt _ |>.comp
      ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).analyticAt a)
  have hP : ∀ᶠ x in 𝓝 a, P (ψ x, 0) =
      (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).map (algebraMap ℝ ℂ) := by
    filter_upwards [hreal] with x hx
    simp only [P, ψ, zero_pow p.natDegree.factorial_ne_zero, zero_smul, add_zero, hx,
      Polynomial.map_map]
    congr 1
    rw [MvPolynomial.comp_eval₂Hom]
    rfl
  exact exists_delineation_on_hyperplane hr
    (hsplit.mono fun _ hz ↦ hz.1) hu hu0 (hsplit.mono fun _ hz ↦ hz.2) hψ hP

end TauCeti
