/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.CommonRoots
public import TauCeti.Analysis.Polynomial.RealRoots.Ordered

import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.Topology.Algebra.Polynomial.RootMultiplicity

/-!
# Common ordered real roots of a finite family of real polynomials

Let `F k x`, for `k` in a finite index type, be real polynomials of fixed degrees whose
coefficients depend continuously on a parameter `x`. Suppose that the number of distinct complex
roots of each member is locally nonincreasing and that the degree of the gcd of every pair of
distinct members is locally constant. The family matching lemma
`Polynomial.eventually_exists_bijOn_biUnion_roots_toFinset` then shows that the product of the
members has a locally constant number of distinct complex roots, so the results of
`TauCeti/Analysis/Polynomial/RealRoots/Ordered.lean` apply to the product.

On a nonempty preconnected base this gives a single finite list of continuous, strictly increasing
functions enumerating, at every parameter, the real roots of all the members together, such that
the multiplicity of each listed root in each member is the same at every parameter. In particular
membership of a listed root in the root set of each member does not depend on the parameter. This
is the common ordered list of real roots over which a delineable family is stacked.

## Main results

* `Polynomial.eventually_card_aroots_prod_eq`: the product of the members has locally constant
  number of distinct complex roots.
* `Polynomial.exists_continuous_ordered_common_roots_of_preconnectedSpace`: the common ordered list
  of real roots with constant multiplicities in every member.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots and delineability).
-/

public section

open Filter Metric Topology TauCeti

namespace Polynomial

variable {B : Type*} [TopologicalSpace B] {ι : Type*} [Fintype ι] {F : ι → B → ℝ[X]}
  {d : ι → ℕ}

/-- **Family matching lemma for real polynomials.** Let `F k x` be real polynomials of degree
`d k` near `x₀`, for `k` in a finite index type, whose coefficients of index at most `d k` are
continuous at `x₀`. Suppose that near `x₀` no member has more distinct complex roots than at `x₀`,
and that the degree of the gcd of every pair of distinct members is the same as at `x₀`. Then for
`x` near `x₀` there is a single bijection `e` from the distinct complex roots of all the `F k x₀`
onto those of all the `F k x` that moves each root by less than `ε` and preserves its multiplicity
in every member. -/
theorem eventually_exists_bijOn_biUnion_aroots_toFinset {x₀ : B}
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀,
      ((F k x).aroots ℂ).toFinset.card ≤ ((F k x₀).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : ℂ → ℂ,
      Set.BijOn e (Finset.univ.biUnion fun k => ((F k x₀).aroots ℂ).toFinset)
        (Finset.univ.biUnion fun k => ((F k x).aroots ℂ).toFinset) ∧
      ∀ z ∈ Finset.univ.biUnion (fun k => ((F k x₀).aroots ℂ).toFinset), ‖e z - z‖ < ε ∧
        ∀ k, ((F k x).map (algebraMap ℝ ℂ)).rootMultiplicity (e z) =
          ((F k x₀).map (algebraMap ℝ ℂ)).rootMultiplicity z := by
  simp only [aroots_def] at hcard ⊢
  refine eventually_exists_bijOn_biUnion_roots_toFinset (fun k i hi => ?_)
    (fun k => (hdeg k).mono fun x hx => by rw [degree_map, hx]) hcard
    (fun k l hkl => (hgcd hkl).mono fun x hx => by rw [gcd_map, gcd_map, natDegree_map,
      natDegree_map, hx]) hε
  simpa only [coeff_map, Complex.coe_algebraMap, Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.comp (hF k i hi)

/-- **Distinct complex roots of the product of a family.** Under the hypotheses of the family
matching lemma for real polynomials, the product of the members has, near `x₀`, as many distinct
complex roots as at `x₀`. -/
theorem eventually_card_aroots_prod_eq {x₀ : B}
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀,
      ((F k x).aroots ℂ).toFinset.card ≤ ((F k x₀).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∀ᶠ x in 𝓝 x₀,
      ((∏ k, F k x).aroots ℂ).toFinset.card = ((∏ k, F k x₀).aroots ℂ).toFinset.card := by
  have hne {x : B} (hx : ∀ k, (F k x).degree = d k) (k : ι) (_ : k ∈ Finset.univ) :
      (F k x).map (algebraMap ℝ ℂ) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective]
    rintro h
    simpa [h] using hx k
  filter_upwards [eventually_exists_bijOn_biUnion_aroots_toFinset hF hdeg hcard hgcd one_pos,
    eventually_all.2 hdeg] with x ⟨e, he, _⟩ hx
  rw [aroots_prod_toFinset _ _ (hne hx),
    aroots_prod_toFinset _ _ (hne fun k => (hdeg k).self_of_nhds)]
  exact (Finset.card_nbij e he.mapsTo he.injOn he.surjOn).symm

omit [Fintype ι] in
/-- **Common ordered real roots.** Let `F k x` be real polynomials of degree `d k`, for `k` in a
finite index type, whose coefficients depend continuously on a parameter in a nonempty
preconnected space. Suppose that the number of distinct complex roots of each member is locally
nonincreasing, and the degree of the gcd of every pair of distinct members is locally constant.
Then there are finitely many continuous functions `r x 0 < ⋯ < r x (n - 1)` whose values at each
`x` are exactly the real roots of the members `F k x` together, and the multiplicity of `r x i` as
a root of each member `F k x` does not depend on `x`. -/
theorem exists_continuous_ordered_common_roots_of_preconnectedSpace [Finite ι]
    [PreconnectedSpace B] [Nonempty B] (hF : ∀ k, ∀ i ≤ d k, Continuous (fun x => (F k x).coeff i))
    (hdeg : ∀ k x, (F k x).degree = d k)
    (hcard : ∀ k x₀, ∀ᶠ x in 𝓝 x₀,
      ((F k x).aroots ℂ).toFinset.card ≤ ((F k x₀).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l => ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∃ n : ℕ, ∃ r : B → Fin n → ℝ,
      (∀ i, Continuous (fun x => r x i)) ∧ (∀ x, StrictMono (r x)) ∧
      (∀ x t, (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t) ∧
      (∀ k i x y, (F k x).rootMultiplicity (r x i) = (F k y).rootMultiplicity (r y i)) := by
  cases nonempty_fintype ι
  have hne (k : ι) (x : B) : F k x ≠ 0 := by
    rintro h
    simpa [h] using hdeg k x
  -- every coefficient of every member, not only those up to its degree, is continuous
  have hF' (k : ι) (i : ℕ) : Continuous fun x => (F k x).coeff i := by
    by_cases hi : i ≤ d k
    · exact hF k i hi
    · refine continuous_const.congr fun x => (coeff_eq_zero_of_degree_lt ?_).symm
      rw [hdeg k x]
      exact_mod_cast Nat.lt_of_not_le hi
  -- the results on ordered real roots apply to the product of the members
  obtain ⟨n, r, hrc, hrm, hroots, hmult⟩ :=
    exists_continuous_ordered_roots_of_preconnectedSpace (F := fun x => ∏ k, F k x)
      (d := ∑ k, d k)
      (fun i _ => continuous_iff_continuousAt.2 fun x =>
        continuousAt_coeff_prod _ (fun k _ i => (hF' k i).continuousAt) i)
      (fun x => by rw [degree_prod, Nat.cast_sum]; exact Finset.sum_congr rfl fun k _ => hdeg k x)
      (fun x₀ => (eventually_card_aroots_prod_eq (fun k i hi => (hF k i hi).continuousAt)
        (fun k => Eventually.of_forall (hdeg k)) (fun k => hcard k x₀)
        fun k l hkl => hgcd hkl x₀).mono fun x hx => hx.le)
  have hroot (x : B) (t : ℝ) : (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t := by
    rw [← hroots x t, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, IsRoot.def]
  refine ⟨n, r, hrc, hrm, hroot, fun k i => ?_⟩
  -- Constant product multiplicity forces every factor multiplicity to be locally constant.
  suffices h : IsLocallyConstant fun x => (F k x).rootMultiplicity (r x i) from
    h.apply_eq_of_preconnectedSpace
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
  exact (eventually_rootMultiplicity_eq_of_prod Finset.univ
    (fun k _ j hj => (hF k j hj).continuousAt)
    (fun k _ => .of_forall fun x => (natDegree_eq_of_degree_eq_some (hdeg k x)).le)
    (hrc i).continuousAt (fun k _ => hne k x₀)
    (.of_forall fun x => hmult i x x₀)).mono fun _ hx => hx k (Finset.mem_univ k)

end Polynomial
