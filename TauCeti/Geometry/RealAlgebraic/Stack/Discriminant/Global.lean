/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Discriminant.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Chart
public import TauCeti.Geometry.RealAlgebraic.Stack.Analytic

/-!
# Analytic delineability from constant discriminant order

A real polynomial family with nonzero fibers of constant degree over a connected analytic
submanifold has a global analytic delineation when its nonzero formal discriminant has constant
ambient order on the base. The ordered real root functions are intrinsically analytic, their
positive multiplicities are constant, and the polynomial has constant sign on every section
and sector. The formal leading coefficient may vanish on the base, so the fiber degree need
not equal the formal degree. Constant polynomials and families without real roots are included.

The construction combines the local discriminant-order theorem
`Polynomial.exists_delineation_of_orderAt_discr_eq` with chart globalization and the intrinsic
analytic root-section API. Constancy of ambient order of the original multivariate polynomial
along the sections is not asserted: it is distinct from constancy of fiber root multiplicity.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), 242–268, Sections 2–3.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti

variable {n d : ℕ} {S : Set (Fin n → ℝ)} {p : Polynomial (MvPolynomial (Fin n) ℝ)}

/-- **Analytic delineability from constant discriminant order.** A polynomial with nonzero
fibers of constant degree over a preconnected analytic submanifold, whose nonzero formal
discriminant has constant ambient order on the base, has a global delineation with intrinsically
analytic root functions. Each root function is represented by an ambient function whose values
off the base are immaterial.

No preservation of the formal degree or nonvanishing of the discriminant values is required.
Multiple roots are allowed, and their fiber multiplicities are constant. This does not assert
constant ambient order of the polynomial along its root sections. -/
theorem exists_analytic_delineation_of_orderAt_discr_eq
    (hS : IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hp : ∀ x ∈ S, p.map (MvPolynomial.eval x) ≠ 0)
    (hdegree : ∀ x ∈ S, ∀ y ∈ S,
      (p.map (MvPolynomial.eval x)).natDegree = (p.map (MvPolynomial.eval y)).natDegree)
    (hdiscr : p.discr ≠ 0)
    (horder : ∀ x ∈ S, ∀ y ∈ S, p.discr.orderAt x = p.discr.orderAt y) :
    ∃ D : Delineation (fun (_ : Unit) (x : S) ↦ p.map (MvPolynomial.eval x.1)),
      ∀ i, ∃ r : (Fin n → ℝ) → ℝ, AnalyticOnSubmanifold d r S ∧
        ∀ x : S, r x = D.root i x := by
  classical
  -- Construct the local stacks in the free coordinates of each analytic chart.
  have hlocal : ∀ x ∈ S,
      ∃ e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
        IsAnalyticChart d S e ∧ x ∈ e.source ∧
          ∃ V : Set (Fin d → ℝ), IsOpen V ∧ firstCoords ℝ n d (e x) ∈ V ∧
            ∃ D : Delineation (fun (_ : Unit) (u : V) ↦
              p.map (MvPolynomial.eval (e.symm (firstCoords ℝ d n u)))),
              ∀ i, ∀ u v : V,
                (p.map (MvPolynomial.eval (e.symm (firstCoords ℝ d n u)))).rootMultiplicity
                    (D.root i u) =
                  (p.map (MvPolynomial.eval (e.symm (firstCoords ℝ d n v)))).rootMultiplicity
                    (D.root i v) := by
    intro x hx
    obtain ⟨e, hxe, he⟩ := hS.exists_isAnalyticChart x hx
    let a := firstCoords ℝ n d (e x)
    let φ := fun u ↦ e.symm (firstCoords ℝ d n u)
    have hφ : AnalyticAt ℝ φ a := he.analyticAt_symm_firstCoords hxe hx
    have hφx : φ a = x := he.symm_firstCoords_firstCoords_apply hxe hx
    have hφS : ∀ᶠ u in 𝓝 a, φ u ∈ S :=
      (he.eventually_symm_firstCoords_mem hxe hx).mono fun _ hu ↦ hu.2
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1
      (MvPolynomial.orderAt_eq_top_iff.not.2 hdiscr : p.discr.orderAt x ≠ ⊤)
    have hdeg : ∀ᶠ u in 𝓝 a,
        (p.map (MvPolynomial.eval (φ u))).natDegree =
          (p.map (MvPolynomial.eval x)).natDegree :=
      hφS.mono fun u hu ↦ hdegree (φ u) hu x hx
    have hord : ∀ᶠ u in 𝓝 a, p.discr.orderAt (φ u) = m :=
      hφS.mono fun u hu ↦ (horder (φ u) hu x hx).trans hm.symm
    obtain ⟨ε, hε, D, -⟩ := p.exists_delineation_of_orderAt_discr_eq hφ
      (by simpa only [MvPolynomial.eval, hφx] using hp x hx) hdeg hord
    -- Give the transported family an explicit type: the local constructor uses `eval₂Hom id`,
    -- whereas chart gluing uses `eval`, its definitionally equal specialization.
    let D' : Delineation (fun (_ : Unit) (u : ball a ε) ↦
      p.map (MvPolynomial.eval (e.symm (firstCoords ℝ d n u)))) := D
    refine ⟨e, he, hxe, ball a ε, isOpen_ball, mem_ball_self hε, D', ?_⟩
    intro i u v
    rw [D'.rootMultiplicity_root () i u, D'.rootMultiplicity_root () i v]
  -- Ordered root lists glue without any choice of a global complex-root labelling.
  obtain ⟨D, -⟩ := exists_delineation_of_locally_chart
    (P := fun (_ : Unit) x ↦ p.map (MvPolynomial.eval x))
    (q := fun x t ↦ (p.map (MvPolynomial.eval x)).rootMultiplicity t) hconn hlocal
  -- Polynomial coefficients are intrinsically analytic, so the glued real roots are too.
  have hcoeff (k : Unit) (j : ℕ) : AnalyticOnSubmanifold d
      (fun x ↦ (p.map (MvPolynomial.eval x)).coeff j) S :=
    hS.analyticOnSubmanifold_coeff_map_eval p j
  refine ⟨D, fun i ↦ ?_⟩
  let r := Function.extend Subtype.val (D.root i) (fun _ ↦ 0)
  have hr (x : S) : r x = D.root i x := Subtype.val_injective.extend_apply _ _ x
  exact ⟨r, D.analyticOnSubmanifold_root hS hcoeff i hr, hr⟩

end TauCeti
