/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import TauCeti.Geometry.RealAlgebraic.Projection.Delineability

/-!
# Analytic projection families for delineation

A finite family of polynomials with real analytic coefficients and bounded degrees admits a
finite family of real analytic base functions whose constant zero pattern guarantees
delineability on each preconnected base set. The degrees may drop and members may vanish
identically on such a set. Repeated roots and common factors are allowed.

The base functions are obtained by substituting the analytic coefficient tuple into the Collins
projection of a universal polynomial family. Thus they include the coefficient and subresultant
conditions needed for constant degrees, root counts and pairwise gcd degrees, without requiring
the original coefficients to be polynomial functions of the base coordinates. This is the
projection step in constructing local sign-invariant decompositions for analytic functions.

The local version chooses one common open neighborhood inside any prescribed neighborhood.
Neither finite-dimensionality nor completeness of the real parameter space is required.

## References

* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Section 5.1 and Chapter 11.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]
  {F : ι → E → ℝ[X]} {U : Set E} {d : ι → ℕ}

/-- A bounded-degree analytic polynomial family has a finite analytic projection family.
On every preconnected subset of the domain where the projection functions have a constant zero
pattern, the original family has a delineation. No fixed-degree, squarefree or nonvanishing
assumptions are imposed on the original family. -/
theorem exists_analyticOnNhd_projection_delineation
    (hF : ∀ i j, j ≤ d i → AnalyticOnNhd ℝ (fun x ↦ (F i x).coeff j) U)
    (hdeg : ∀ i x, x ∈ U → (F i x).natDegree ≤ d i) :
    ∃ g : Finset (E → ℝ), (∀ a ∈ g, AnalyticOnNhd ℝ a U) ∧
      ∀ S ⊆ U, IsPreconnected S →
        (∀ a ∈ g, ∀ x ∈ S, ∀ y ∈ S, a x = 0 ↔ a y = 0) →
        Nonempty (Delineation fun i (x : S) ↦ F i x) := by
  classical
  let := Fintype.ofFinite ι
  -- Each coefficient gets its own universal variable; specialization recovers every fiber.
  let σ := Σ i, Fin (d i + 1)
  let c : E → σ → ℝ := fun x a ↦ (F a.1 x).coeff a.2
  let P : ι → (MvPolynomial σ ℝ)[X] := fun i ↦
    ∑ j : Fin (d i + 1), monomial (j : ℕ) (MvPolynomial.X ⟨i, j⟩)
  let φ : E → MvPolynomial σ ℝ →+* ℝ := fun x ↦ MvPolynomial.eval (c x)
  have hP (i) {x : E} (hx : x ∈ U) : (P i).map (φ x) = F i x := by
    simp only [P, φ, Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X, c]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ monomial j ((F i x).coeff j))]
    exact ((F i x).as_sum_range' (d i + 1) (by have := hdeg i x hx; omega)).symm
  let Q := (Finset.univ.image P).collinsProjection
  let g : Finset (E → ℝ) := Q.image fun q x ↦ φ x q
  have hg : ∀ a ∈ g, AnalyticOnNhd ℝ a U := by
    rintro a ha
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 ha
    simpa only [φ, MvPolynomial.aeval_eq_eval] using
      AnalyticOnNhd.aeval_mvPolynomial (fun a : σ ↦ hF a.1 a.2 (by omega)) q
  refine ⟨g, hg, fun S hSU hS hzero ↦ ?_⟩
  let := isPreconnected_iff_preconnectedSpace.1 hS
  -- Apply the ring-theoretic projection theorem and then recover the original labels.
  obtain ⟨D⟩ := nonempty_delineation_of_collinsProjection (fun x : S ↦ φ x)
    (fun q hq ↦ continuousOn_iff_continuous_domRestrict.1
      ((hg _ (Finset.mem_image_of_mem _ hq)).continuousOn.mono hSU))
    (fun q hq x y ↦ hzero _ (Finset.mem_image_of_mem _ hq) x x.2 y y.2)
  let f : ι → ↥(Finset.univ.image P) := fun i ↦
    ⟨P i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hf : Function.Surjective f := by
    rintro ⟨p, hp⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨i, rfl⟩
  have hfamily : (fun i (x : S) ↦ (P i).map (φ x)) = fun i (x : S) ↦ F i x :=
    funext fun i ↦ funext fun x ↦ hP i (hSU x.2)
  rw [← hfamily]
  exact ⟨D.reindex f fun i ↦ hf.exists.1 (D.exists_multiplicity_pos i)⟩

/-- Analytic polynomial germs of locally bounded degree admit one finite analytic projection
family on a common open neighborhood inside any prescribed neighborhood. Its constant zero
pattern on a preconnected base set suffices for a delineation of all the original fibers. -/
theorem exists_analytic_projection_delineation_nhds {x₀ : E} {V : Set E}
    (hF : ∀ i j, j ≤ d i → AnalyticAt ℝ (fun x ↦ (F i x).coeff j) x₀)
    (hdeg : ∀ i, ∀ᶠ x in 𝓝 x₀, (F i x).natDegree ≤ d i) (hV : V ∈ 𝓝 x₀) :
    ∃ U ⊆ V, IsOpen U ∧ x₀ ∈ U ∧ ∃ g : Finset (E → ℝ),
      (∀ a ∈ g, AnalyticOnNhd ℝ a U) ∧
      ∀ S ⊆ U, IsPreconnected S →
        (∀ a ∈ g, ∀ x ∈ S, ∀ y ∈ S, a x = 0 ↔ a y = 0) →
        Nonempty (Delineation fun i (x : S) ↦ F i x) := by
  have ha : ∀ᶠ x in 𝓝 x₀, ∀ i, ∀ j : Fin (d i + 1),
      AnalyticAt ℝ (fun y ↦ (F i y).coeff j) x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
      (hF i j (by omega)).eventually_analyticAt
  have hd : ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x).natDegree ≤ d i := eventually_all.2 hdeg
  obtain ⟨U, hU, hUo, hx₀⟩ := eventually_nhds_iff.1 (inter_mem hV (ha.and hd))
  refine ⟨U, fun x hx ↦ (hU x hx).1, hUo, hx₀,
    exists_analyticOnNhd_projection_delineation (d := d) ?_ ?_⟩
  · intro i j hj x hx
    exact (hU x hx).2.1 i ⟨j, by omega⟩
  · exact fun i x hx ↦ (hU x hx).2.2 i

end TauCeti
