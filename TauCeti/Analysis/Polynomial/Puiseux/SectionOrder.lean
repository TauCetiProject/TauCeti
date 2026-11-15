/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Contact
public import TauCeti.Analysis.Polynomial.Puiseux.Order
import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Constant plane order on Puiseux root sections

A family of plane polynomials admits a ramified analytic splitting near the
distinguished hyperplane. If its discriminant is a power of the ramification
parameter times an analytic unit, the ambient order of each plane polynomial
at each labelled root section is locally constant in the family parameter.
On a preconnected parameter set these orders are constant everywhere, assuming
the splitting and discriminant hypotheses as germs at each point.

These are orders in both coordinates of the plane polynomial, rather than
multiplicities in its vertical fiber. The plane polynomials may themselves be
transverse restrictions of polynomials in more variables; identifying their
orders with those of the original polynomials requires order-detecting slices.
Root labels may collide on the distinguished hyperplane.

The results combine `TauCeti.eventually_min_analyticOrderAt_root_sub_eq` with
`MvPolynomial.orderAt_mul_eq_sum_min_of_puiseux`.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Metric Polynomial Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {p : E → MvPolynomial (Fin 2) ℂ} {c : E → ℂ}
  {N n a : ℕ} {r : Fin n → E × ℂ → ℂ} {u : E × ℂ → ℂ}

/-- In a ramified analytic splitting with power-times-unit discriminant, the
ambient orders of the plane polynomials at all labelled root sections are
locally constant on one common parameter neighborhood. Collisions of root
labels on the hyperplane are allowed. -/
theorem eventually_orderAt_root_eq_of_puiseux {x₀ : E} (hN : 0 < N)
    (hr : ∀ i, AnalyticAt ℂ (r i) (x₀, 0))
    (hsplit : ∀ᶠ b in 𝓝 (x₀, (0 : ℂ)),
      MvPolynomial.aeval ![C (c b.1 + b.2 ^ N), X] (p b.1) =
        ∏ i, (X - C (r i b)))
    (hu : AnalyticAt ℂ u (x₀, 0)) (hu0 : u (x₀, 0) ≠ 0)
    (hdiscr : ∀ᶠ b in 𝓝 (x₀, (0 : ℂ)),
      (MvPolynomial.aeval ![C (c b.1 + b.2 ^ N), X] (p b.1)).discr =
        b.2 ^ a * u b) :
    ∀ᶠ x in 𝓝 x₀, ∀ i,
      (p x).orderAt ![c x, r i (x, 0)] =
        (p x₀).orderAt ![c x₀, r i (x₀, 0)] := by
  let P : E × ℂ → ℂ[X] := fun b ↦
    MvPolynomial.aeval ![C (c b.1 + b.2), X] (p b.1)
  have hcontact := eventually_min_analyticOrderAt_root_sub_eq
    (P := P) hr hsplit hu hu0 hdiscr
  have hdata := (eventually_all.2 fun i ↦ (hr i).eventually_analyticAt).and hsplit
  rw [nhds_prod_eq] at hdata
  have hslice := hdata.curry
  have horder (x : E) (hx : ∀ᶠ t in 𝓝 (0 : ℂ),
      (∀ i, AnalyticAt ℂ (r i) (x, t)) ∧
      MvPolynomial.aeval ![C (c x + t ^ N), X] (p x) =
        ∏ i, (X - C (r i (x, t)))) (i : Fin n) :
      (p x).orderAt ![c x, r i (x, 0)] * N =
        ∑ j, min (N : ℕ∞) (analyticOrderAt (fun t ↦ r j (x, t) - r i (x, 0)) 0) := by
    apply MvPolynomial.orderAt_mul_eq_sum_min_of_puiseux _ _ hN
      (fun j ↦ (hx.self_of_nhds.1 j).curry_right) analyticAt_const one_ne_zero
    filter_upwards [hx] with t ht z
    have heval := congrArg (Polynomial.aeval z) ht.2
    have hcoords : (fun j ↦ Polynomial.aeval z (![C (c x + t ^ N), X] j)) =
        ![c x + t ^ N, z] := by
      ext j
      fin_cases j <;> simp
    simpa only [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval,
      hcoords, Polynomial.aeval_C, Polynomial.aeval_X, map_prod, map_sub,
      Algebra.algebraMap_self, RingHom.id_apply, Matrix.cons_val_zero, one_mul] using heval
  filter_upwards [hslice, hcontact] with x hx hc i
  apply (ENat.mul_left_strictMono (a := (N : ℕ∞)) (by simpa using hN.ne')
    (by simp)).injective
  exact (horder x hx i).trans ((Finset.sum_congr rfl fun j _ ↦ hc i j).trans
    (horder x₀ hslice.self_of_nhds i).symm)

/-- On a preconnected parameter set, a ramified analytic splitting with
power-times-unit discriminant has constant ambient plane order on every
labelled root section. Analyticity, splitting, and the discriminant identity
are only required as germs at each point of the distinguished hyperplane.
The discriminant exponent may depend on the parameter point.
The order can differ between sections. -/
theorem orderAt_root_eq_of_puiseux {U : Set E}
    (hUc : IsPreconnected U) (hN : 0 < N)
    (hr : ∀ x ∈ U, ∀ i, AnalyticAt ℂ (r i) (x, 0))
    (hsplit : ∀ x ∈ U, ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
      MvPolynomial.aeval ![C (c b.1 + b.2 ^ N), X] (p b.1) =
        ∏ i, (X - C (r i b)))
    (hu : ∀ x ∈ U, AnalyticAt ℂ u (x, 0))
    (hu0 : ∀ x ∈ U, u (x, 0) ≠ 0)
    (hdiscr : ∀ x ∈ U, ∃ a : ℕ, ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
      (MvPolynomial.aeval ![C (c b.1 + b.2 ^ N), X] (p b.1)).discr =
        b.2 ^ a * u b)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (i : Fin n) :
    (p x).orderAt ![c x, r i (x, 0)] = (p y).orderAt ![c y, r i (y, 0)] := by
  apply hUc.apply_eq_of_eventually_eq _ hx hy
  intro z hz
  obtain ⟨a, hdiscr⟩ := hdiscr z hz
  exact ((eventually_orderAt_root_eq_of_puiseux hN
    (hr z hz) (hsplit z hz) (hu z hz) (hu0 z hz)
    hdiscr).mono fun _ h ↦ h i).filter_mono nhdsWithin_le_nhds

end TauCeti
