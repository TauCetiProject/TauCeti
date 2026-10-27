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

The hypothesis on distinct complex roots follows from gcd data: the number of distinct complex
roots of a nonzero real polynomial is its degree minus the degree of its gcd with its derivative.
So both results also hold when each member has locally constant degree of its gcd with its
derivative. By the subresultant gcd criterion, this is what fixed vanishing of principal
subresultant coefficients provides.

The underlying topological gluing argument is provided separately for any local continuous,
strictly increasing enumerations of an intrinsic set of real roots. It does not require the
coefficient hypotheses used to construct such enumerations.

## Main results

* `TauCeti.exists_roots_of_locally`: glue local ordered real-root enumerations over a nonempty
  preconnected base.
* `Polynomial.eventually_card_aroots_prod_eq`: the product of the members has locally constant
  number of distinct complex roots.
* `Polynomial.exists_continuous_ordered_common_roots_of_preconnectedSpace`: the common ordered list
  of real roots with constant multiplicities in every member.
* `Polynomial.eventually_exists_bijOn_biUnion_aroots_toFinset_of_natDegree_gcd_derivative`: the
  family matching lemma with locally constant degrees of the gcds of the members with their
  derivatives in place of the hypothesis on distinct complex roots.
* `Polynomial.exists_continuous_ordered_common_roots_of_natDegree_gcd_derivative`: the common
  ordered list of real roots under the same gcd hypotheses.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots and delineability).
-/

public section

open Filter Function Metric Polynomial Set Topology TauCeti

namespace TauCeti

variable {X ι : Type*} [TopologicalSpace X] {P : ι → X → ℝ[X]}

/-- Local continuous strictly increasing enumerations `θ a` of an intrinsic set `Z y ⊆ ℝ` on
open neighborhoods `U a` glue over a nonempty preconnected base. The local counts are globally
constant, the glued root functions are continuous, strictly increasing and enumerate `Z`, and
they agree with every local enumeration. If every local enumeration has constant root
multiplicities in a family `P`, so do the glued roots. -/
theorem exists_roots_of_locally [PreconnectedSpace X] [Nonempty X] {Z : X → Set ℝ}
    {U : X → Set X} (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x) {c : X → ℕ}
    {θ : ∀ a, Fin (c a) → U a → ℝ} {μ : ∀ a, ι → Fin (c a) → ℕ}
    (hθc : ∀ a i, Continuous (θ a i)) (hθmono : ∀ a (y : U a), StrictMono fun i ↦ θ a i y)
    (hθrange : ∀ a (y : U a), range (fun i ↦ θ a i y) = Z y)
    (hθmult : ∀ a k i (y : U a), (P k y).rootMultiplicity (θ a i y) = μ a k i) :
    ∃ (n : ℕ) (hc : ∀ x, c x = n) (r : Fin n → X → ℝ) (m : ι → Fin n → ℕ),
      (∀ i, Continuous (r i)) ∧ (∀ x, StrictMono fun i ↦ r i x) ∧
      (∀ x, range (fun i ↦ r i x) = Z x) ∧
      (∀ k i x, (P k x).rootMultiplicity (r i x) = m k i) ∧
      ∀ a (y : U a) i, r i y = θ a (Fin.cast (hc a).symm i) y := by
  classical
  let a₀ : X := Classical.arbitrary X
  have hcard (a : X) (y : U a) : Nat.card (Z y) = c a := by
    rw [← hθrange a y, Nat.card_range_of_injective (hθmono a y).injective]
    simp
  -- The number of roots is locally constant, hence globally constant.
  have hclocal : IsLocallyConstant fun x ↦ Nat.card (Z x) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
    filter_upwards [(hU a).mem_nhds (hxU a)] with y hy
    exact (hcard a ⟨y, hy⟩).trans (hcard a ⟨a, hxU a⟩).symm
  let n := Nat.card (Z a₀)
  have hc (a : X) : c a = n :=
    (hcard a ⟨a, hxU a⟩).symm.trans (hclocal.apply_eq_of_preconnectedSpace a a₀)
  let r (i : Fin n) (x : X) := θ x (Fin.cast (hc x).symm i) ⟨x, hxU x⟩
  have hrmono (x : X) : StrictMono fun i ↦ r i x :=
    (hθmono x ⟨x, hxU x⟩).comp (Fin.cast_strictMono (hc x).symm)
  have hrrange (x : X) : range (fun i ↦ r i x) = Z x := by
    exact ((Fin.castOrderIso (hc x).symm).surjective.range_comp _).trans
      (hθrange x ⟨x, hxU x⟩)
  -- Increasing complete lists agree on overlaps. This identifies the pointwise
  -- choice with each local continuous root function, including its multiplicity.
  have hrU (a : X) (y : U a) (i : Fin n) : r i y = θ a (Fin.cast (hc a).symm i) y := by
    have hmono := (hθmono a y).comp (Fin.cast_strictMono (hc a).symm)
    apply congrFun (((hrmono y).range_inj_of_wellFoundedLT hmono).1 ?_) i
    exact (hrrange y).trans (((Fin.castOrderIso (hc a).symm).surjective.range_comp _).trans
      (hθrange a y)).symm
  have hrc (i : Fin n) : Continuous (r i) := by
    refine continuous_iff_continuousAt.2 fun a ↦ ?_
    have hcont : ContinuousOn (r i) (U a) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (hθc a _).congr fun y ↦ (hrU a y i).symm
    exact (hU a).continuousOn_iff.mp hcont (hxU a)
  let m (k : ι) (i : Fin n) := (P k a₀).rootMultiplicity (r i a₀)
  have hm (k : ι) (i : Fin n) (x : X) : (P k x).rootMultiplicity (r i x) = m k i := by
    have hmult : IsLocallyConstant fun y ↦ (P k y).rootMultiplicity (r i y) := by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun a ↦ ?_
      filter_upwards [(hU a).mem_nhds (hxU a)] with y hy
      rw [hrU a ⟨y, hy⟩ i, hrU a ⟨a, hxU a⟩ i, hθmult, hθmult]
    exact hmult.apply_eq_of_preconnectedSpace x a₀
  exact ⟨n, hc, r, m, hrc, hrmono, hrrange, hm, hrU⟩

end TauCeti

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

/-- **Family matching lemma for real polynomials, gcd form.** Let `F k x` be real polynomials of
degree `d k` near `x₀`, for `k` in a finite index type, whose coefficients of index at most `d k`
are continuous at `x₀`. Suppose that near `x₀` the degree of the gcd of each member with its
derivative, and the degree of the gcd of every pair of distinct members, are the same as at
`x₀`. Then for `x` near `x₀` there is a single bijection `e` from the distinct complex roots of
all the `F k x₀` onto those of all the `F k x` that moves each root by less than `ε` and preserves
its multiplicity in every member. -/
theorem eventually_exists_bijOn_biUnion_aroots_toFinset_of_natDegree_gcd_derivative {x₀ : B}
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hder : ∀ k, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F k x).derivative).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F k x₀).derivative).natDegree)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : ℂ → ℂ,
      Set.BijOn e (Finset.univ.biUnion fun k => ((F k x₀).aroots ℂ).toFinset)
        (Finset.univ.biUnion fun k => ((F k x).aroots ℂ).toFinset) ∧
      ∀ z ∈ Finset.univ.biUnion (fun k => ((F k x₀).aroots ℂ).toFinset), ‖e z - z‖ < ε ∧
        ∀ k, ((F k x).map (algebraMap ℝ ℂ)).rootMultiplicity (e z) =
          ((F k x₀).map (algebraMap ℝ ℂ)).rootMultiplicity z :=
  eventually_exists_bijOn_biUnion_aroots_toFinset hF hdeg
    (fun k => (eventually_card_aroots_toFinset_eq_of_natDegree_gcd_derivative (K := ℂ) (hdeg k)
      (hder k)).mono fun _ hx => hx.le) hgcd hε

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
        continuousAt_coeff_prod _ (fun k _ i _ => (hF' k i).continuousAt))
      (fun x => by rw [degree_prod, Nat.cast_sum]; exact Finset.sum_congr rfl fun k _ => hdeg k x)
      (fun x₀ => (eventually_card_aroots_prod_eq (fun k i hi => (hF k i hi).continuousAt)
        (fun k => Eventually.of_forall (hdeg k)) (fun k => hcard k x₀)
        fun k l hkl => hgcd hkl x₀).mono fun x hx => hx.le)
  have hroot (x : B) (t : ℝ) : (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t := by
    rw [← hroots x t, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, IsRoot.def]
  exact ⟨n, r, hrc, hrm, hroot, fun k i =>
    TauCeti.Polynomial.rootMultiplicity_eq_of_prod Finset.univ
      (fun k _ j hj => hF k j hj)
      (fun k _ x => (natDegree_eq_of_degree_eq_some (hdeg k x)).le)
      (hrc i) (fun k _ => hne k) (hmult i) k (Finset.mem_univ k)⟩

omit [Fintype ι] in
/-- **Common ordered real roots, gcd form.** Let `F k x` be real polynomials of degree `d k`, for
`k` in a finite index type, whose coefficients depend continuously on a parameter in a nonempty
preconnected space. Suppose that the degree of the gcd of each member with its derivative, and
the degree of the gcd of every pair of distinct members, are locally constant. Then there are
finitely many continuous functions `r x 0 < ⋯ < r x (n - 1)` whose values at each `x` are exactly
the real roots of the members `F k x` together, and the multiplicity of `r x i` as a root of each
member `F k x` does not depend on `x`. -/
theorem exists_continuous_ordered_common_roots_of_natDegree_gcd_derivative
    [Finite ι] [PreconnectedSpace B] [Nonempty B]
    (hF : ∀ k, ∀ i ≤ d k, Continuous (fun x => (F k x).coeff i))
    (hdeg : ∀ k x, (F k x).degree = d k)
    (hder : ∀ k x₀, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F k x).derivative).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F k x₀).derivative).natDegree)
    (hgcd : Pairwise fun k l => ∀ x₀, ∀ᶠ x in 𝓝 x₀,
      (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
        (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∃ n : ℕ, ∃ r : B → Fin n → ℝ,
      (∀ i, Continuous (fun x => r x i)) ∧ (∀ x, StrictMono (r x)) ∧
      (∀ x t, (∃ k, (F k x).IsRoot t) ↔ ∃ i, r x i = t) ∧
      (∀ k i x y, (F k x).rootMultiplicity (r x i) = (F k y).rootMultiplicity (r y i)) :=
  exists_continuous_ordered_common_roots_of_preconnectedSpace hF hdeg
    (fun k x₀ => (eventually_card_aroots_toFinset_eq_of_natDegree_gcd_derivative (K := ℂ)
      (Eventually.of_forall (hdeg k)) (hder k x₀)).mono fun _ hx => hx.le) hgcd

end Polynomial
