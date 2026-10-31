/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Connected

/-!
# A single polynomial relation for a Nash function

A Nash germ satisfies a nonzero polynomial relation `P (y, f y) = 0` near its point, and both
the relation and the neighbourhood may change from point to point. This file shows that a
function which is a Nash germ at every point of a semialgebraic set satisfies one nonzero
relation on the whole set. Such a global relation is where the classical proof that a Nash
function on an open semialgebraic set has a semialgebraic graph begins.

* `AnalyticOnNhd.eval_map_eval_eq_zero_of_isPreconnected`: by analytic continuation, a relation
  satisfied near one point of a preconnected set on which `f` is analytic holds on the whole set.
* `IsPreconnected.exists_ne_zero_polynomial_relation_of_isNashAt`: a function that is a Nash
  germ at every point of a preconnected set satisfies a single nonzero relation on that set.
* `Set.Finite.exists_ne_zero_polynomial_relation_of_isNashAt_of_sUnion`: the same on a union of
  finitely many preconnected sets, with the product of the relations of the pieces.
* `TauCeti.IsSemialgebraic.exists_ne_zero_polynomial_relation_of_isNashAt`: the same on a
  semialgebraic set, which is a finite union of connected semialgebraic sets.

The set need not be open: being a Nash germ at a point already involves a whole neighbourhood
of it.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
-/

public section

open Filter Polynomial Set Topology

section Analytic

variable {𝕜 σ : Type*} [NontriviallyNormedField 𝕜] [Fintype σ] {f : (σ → 𝕜) → 𝕜}
  {s : Set (σ → 𝕜)}

/-- Substituting an analytic function into a polynomial with polynomial coefficients gives an
analytic function. -/
theorem AnalyticOnNhd.eval_map_eval (hf : AnalyticOnNhd 𝕜 f s) (P : (MvPolynomial σ 𝕜)[X]) :
    AnalyticOnNhd 𝕜 (fun y ↦ (P.map (MvPolynomial.eval y)).eval (f y)) s := by
  have hcoeff (p : MvPolynomial σ 𝕜) : AnalyticOnNhd 𝕜 (fun y ↦ MvPolynomial.eval y p) s :=
    (AnalyticOnNhd.eval_continuousLinearMap (.id 𝕜 (σ → 𝕜)) p).mono (subset_univ s)
  simp_rw [eval_map, eval₂_eq_sum_range]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ ↦ (hcoeff (P.coeff i)).mul (hf.pow i)

/-- **Analytic continuation of a polynomial relation.** If `f` is analytic on a preconnected set
`s` and satisfies the relation `P (y, f y) = 0` near one point of `s`, it satisfies this relation
at every point of `s`. -/
theorem AnalyticOnNhd.eval_map_eval_eq_zero_of_isPreconnected (hf : AnalyticOnNhd 𝕜 f s)
    (hs : IsPreconnected s) {P : (MvPolynomial σ 𝕜)[X]} {x : σ → 𝕜} (hx : x ∈ s)
    (hP : ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).eval (f y) = 0) :
    ∀ y ∈ s, (P.map (MvPolynomial.eval y)).eval (f y) = 0 :=
  fun _ hy ↦ (hf.eval_map_eval P).eqOn_zero_of_preconnected_of_eventuallyEq_zero hs hx hP hy

end Analytic

variable {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {s : Set (σ → ℝ)}

/-- A function that is a Nash germ at every point of a preconnected set satisfies a single
nonzero polynomial relation `P (y, f y) = 0` at every point of the set. -/
theorem IsPreconnected.exists_ne_zero_polynomial_relation_of_isNashAt (hs : IsPreconnected s)
    (hf : ∀ x ∈ s, TauCeti.IsNashAt f x) :
    ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧ ∀ y ∈ s, (P.map (MvPolynomial.eval y)).eval (f y) = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨1, one_ne_zero, fun _ hy ↦ hy.elim⟩
  obtain ⟨-, P, hP0, hP⟩ := TauCeti.isNashAt_iff.1 (hf x hx)
  have hfa : AnalyticOnNhd ℝ f s := fun y hy ↦ (hf y hy).analyticAt
  exact ⟨P, hP0, hfa.eval_map_eval_eq_zero_of_isPreconnected hs hx hP⟩

/-- A function that is a Nash germ at every point of a union of finitely many preconnected sets
satisfies a single nonzero polynomial relation `P (y, f y) = 0` on the union. -/
theorem Set.Finite.exists_ne_zero_polynomial_relation_of_isNashAt_of_sUnion
    {𝒞 : Set (Set (σ → ℝ))} (h𝒞 : 𝒞.Finite) (hc : ∀ t ∈ 𝒞, IsPreconnected t)
    (hf : ∀ x ∈ ⋃₀ 𝒞, TauCeti.IsNashAt f x) :
    ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧
      ∀ y ∈ ⋃₀ 𝒞, (P.map (MvPolynomial.eval y)).eval (f y) = 0 := by
  choose! Q hQ0 hQ using fun t (ht : t ∈ 𝒞) ↦
    (hc t ht).exists_ne_zero_polynomial_relation_of_isNashAt fun x hx ↦ hf x ⟨t, ht, hx⟩
  -- the product of the relations of the pieces is a relation on their union
  refine ⟨∏ t ∈ h𝒞.toFinset, Q t, Finset.prod_ne_zero_iff.2 fun t ht ↦ hQ0 t (by simpa using ht),
    fun y ⟨t, ht, hy⟩ ↦ ?_⟩
  rw [Polynomial.map_prod, eval_prod]
  exact Finset.prod_eq_zero (h𝒞.mem_toFinset.2 ht) (hQ t ht y hy)

namespace TauCeti

/-- A function that is a Nash germ at every point of a semialgebraic set satisfies a single
nonzero polynomial relation `P (y, f y) = 0` at every point of the set. In particular, a Nash
function on an open semialgebraic set satisfies one nonzero polynomial relation on all of it. -/
theorem IsSemialgebraic.exists_ne_zero_polynomial_relation_of_isNashAt (hs : IsSemialgebraic s)
    (hf : ∀ x ∈ s, IsNashAt f x) :
    ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧ ∀ y ∈ s, (P.map (MvPolynomial.eval y)).eval (f y) = 0 := by
  obtain ⟨𝒞, h𝒞, -, hc, rfl⟩ := hs.exists_finite_isConnected_partition
  exact h𝒞.exists_ne_zero_polynomial_relation_of_isNashAt_of_sUnion
    (fun t ht ↦ (hc t ht).1.isPreconnected) hf

end TauCeti
