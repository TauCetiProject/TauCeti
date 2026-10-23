/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Discriminant
public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation

/-!
# Local delineability from constant discriminant order

A polynomial with real polynomial coefficients has a local delineation along an analytic
parametrization on which its fibers are nonzero of constant degree and its formal discriminant
has constant finite ambient order. The sections extend to real analytic functions, have constant
positive root multiplicities, and account for all real roots; signs are constant on every section
and sector.

The formal leading coefficient may vanish along the parametrization, so the fiber degree may be
smaller than the formal degree at which the discriminant is taken; monic polynomials are a
special case. The construction starts with the real discriminant-order condition, not a supplied
complex splitting or a hypothesis of constant root multiplicities. Multiple roots at the center,
constant polynomials and families without real roots are included. This is the local analytic
delineability conclusion, not a theorem about ambient order on the root sections.

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

/-- **Local delineability from constant discriminant order.** Let `p` be a polynomial whose
coefficients are real polynomials, specialized along a real analytic parametrization `φ`. If the
fiber at `a` is nonzero, the fibers near `a` have constant degree, and the formal discriminant of
`p` has constant finite ambient order near `a`, then the fibers have a delineation on some
positive-radius ball around `a`, and all root sections admit analytic extensions to that ball.

The formal leading coefficient of `p` may vanish at `a`, so the constant degree of the fibers can
be smaller than the formal degree at which the discriminant is taken. -/
theorem _root_.Polynomial.exists_delineation_of_orderAt_discr_eq
    (p : Polynomial (MvPolynomial σ ℝ)) {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {d m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hp : p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ a)) ≠ 0)
    (hd : ∀ᶠ x in 𝓝 a, (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).natDegree = d)
    (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m) :
    ∃ ε > 0, ∃ D : Delineation (fun (_ : Unit) (x : ball a ε) ↦
      p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))),
      ∀ i, ∃ s : (ι → ℝ) → ℝ, AnalyticOnNhd ℝ s (ball a ε) ∧
        ∀ x : ball a ε, D.root i x = s x := by
  obtain ⟨k, s, U, hU, haU, hs, hmono, hroots, -, hmult⟩ :=
    p.exists_analyticOnNhd_ordered_roots_of_orderAt_discr_eq hφ hp hd hm
  -- The coefficients of the fibers are polynomial functions of `φ`.
  have hcoeff : ∀ᶠ x in 𝓝 a, ∀ j,
      ContinuousAt (fun x ↦ (p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x))).coeff j) x := by
    filter_upwards [hφ.eventually_analyticAt] with x hx j
    simpa only [coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.aeval_eq_eval₂Hom,
      Algebra.algebraMap_self] using
      (AnalyticAt.aeval_mvPolynomial (fun i ↦ analyticAt_pi_iff.1 hx i) (p.coeff j)).continuousAt
  have hlc := leadingCoeff_ne_zero.2 hp
  have hF : ∀ᶠ x in 𝓝 a, p.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (φ x)) ≠ 0 := by
    filter_upwards [hcoeff.self_of_nhds _ |>.eventually_ne hlc] with x hx h
    exact hx (by rw [h, coeff_zero])
  obtain ⟨ε, hε, hεU, D, hD⟩ := exists_delineation_ball_of_isRoot_iff hcoeff hF hd
    (hU.mem_nhds haU) (fun i ↦ (hs i).continuousOn) hmono hroots hmult
  refine ⟨ε, hε, D, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := hD i
  exact ⟨s j, (hs j).mono hεU, hj⟩

end TauCeti
