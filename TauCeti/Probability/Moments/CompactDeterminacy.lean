/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Group.Submonoid.Finsupp
import TauCeti.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Multivariate moment determinacy on a compact set

Two finite measures on a compact subset of `ι → ℝ` (`ι` finite) that agree on every mixed monomial
`x ↦ ∏ i, x i ^ n i` are equal.

This complements the univariate mechanism in `TauCeti/Probability/Moments/Determinacy.lean`, which
determines a finite measure on `ℝ` from its polynomial moments under a finite-exponential-moment
hypothesis. Here the hypothesis is compact support instead, and the conclusion is multivariate. The
two are genuinely different routes: that one is analytic (the moment generating function is
analytic on a strip), this one is approximation-theoretic (Stone–Weierstrass).

It supplies the determinacy input consumed by `mixedIID_mixingLaw_unique`
(`TauCetiRoadmap/Exchangeability/README.md`, *Layer 6 — directing measures and de Finetti
representation*), where the mixed monomials arise as the finite-dimensional moments of a mixture of
i.i.d. laws on a compact box.

## Main results

* `Measure.ext_of_forall_integral_monomial_eq` — the compact-subtype form.
* `Measure.ext_of_forall_integral_monomial_eq_of_support` — the ambient form on `ι → ℝ`, for
  measures supported on a common compact set.

## Scope

Mixed monomials are finite products of coordinate powers. On a compact subset of a finite real
product, their integrals determine a finite measure. The ambient version applies to two finite
measures when both are supported on the same compact set.
-/

public section

noncomputable section

open MeasureTheory Set BoundedContinuousFunction

namespace TauCeti

variable {ι : Type*} {K : Set (ι → ℝ)}

/-- The `i`-th coordinate, as a continuous function on a subset of `ι → ℝ`. -/
private def coordFun (K : Set (ι → ℝ)) (i : ι) : C(K, ℝ) :=
  ⟨fun x => (x : ι → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩

/-- The `i`-th coordinate as a bounded continuous function, using compactness of `K`. -/
private def coordBCF (K : Set (ι → ℝ)) [CompactSpace K] (i : ι) : K →ᵇ ℝ :=
  mkOfCompact (coordFun K i)

@[simp]
private theorem coordBCF_apply [CompactSpace K] (i : ι) (x : K) :
    coordBCF K i x = (x : ι → ℝ) i :=
  rfl

/-- Every element of the multiplicative closure of the coordinate functions is a mixed monomial.
`Submonoid.exists_of_mem_closure_range` supplies the exponent vector; this only transports the
resulting equation of bounded continuous functions to its pointwise form. -/
private theorem exists_monomial_of_mem_closure [Fintype ι] [CompactSpace K] {g : K →ᵇ ℝ}
    (hg : g ∈ Submonoid.closure (Set.range (coordBCF K))) :
    ∃ n : ι → ℕ, ∀ x : K, g x = ∏ i, (x : ι → ℝ) i ^ n i := by
  obtain ⟨n, rfl⟩ := Submonoid.exists_of_mem_closure_range (coordBCF K) g hg
  exact ⟨n, fun x => by
    simp only [BoundedContinuousFunction.prod_apply, BoundedContinuousFunction.pow_apply,
      coordBCF_apply]⟩

/-- **Multivariate moment determinacy on a compact set.** Two finite Borel measures on a compact
subset `K` of `ι → ℝ` that assign the same integral to every mixed monomial
`x ↦ ∏ i, x i ^ n i` are equal.

Compactness is what makes the monomials suffice: it bounds the coordinates, so the polynomial
functions are dense in `C(K, ℝ)` by Stone–Weierstrass. Without it the conclusion fails, as the
classical lognormal counterexample on `ℝ` shows. -/
theorem Measure.ext_of_forall_integral_monomial_eq [Fintype ι] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] {μ ν : Measure K} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmom : ∀ n : ι → ℕ, ∫ x, ∏ i, (x : ι → ℝ) i ^ n i ∂μ
      = ∫ x, ∏ i, (x : ι → ℝ) i ^ n i ∂ν) :
    μ = ν := by
  have : PolishSpace K :=
    (isCompact_iff_compactSpace.mpr ‹CompactSpace K›).isClosed.polishSpace
  refine MeasureTheory.ext_of_forall_mem_submonoid_integral_eq_of_polish
    (S := Submonoid.closure (Set.range (coordBCF K))) (fun x y hxy => ?_) fun g hg => ?_
  · -- Distinct points of `K` differ in some coordinate.
    obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h => hxy (Subtype.ext h)
    exact ⟨coordBCF K i, Submonoid.subset_closure (Set.mem_range_self i), hi⟩
  · obtain ⟨n, hn⟩ := exists_monomial_of_mem_closure hg
    simpa only [hn] using hmom n

/-- **Multivariate moment determinacy, ambient form.** Two finite Borel measures on `ι → ℝ`
that are both supported on a common compact set `K` and assign the same integral to every mixed
monomial are equal.

Both support hypotheses are required *by this proof*, which restricts to the compact subtype: that
route establishes only `μ.restrict K = ν.restrict K`, and each support hypothesis is what identifies
one restriction with the original measure.

`hν` cannot simply be dropped. Classically, a compactly supported finite measure is
moment-determinate among all finite measures *whose moments exist*. But `hmom` is stated with
Bochner integrals, and `MeasureTheory.integral_undef` makes `∫ f ∂ν = 0` when `f` is not
`ν`-integrable, so `hmom` asserts nothing where `ν`'s moments diverge. Taking `μ` a Dirac mass and
`ν` a Cauchy measure satisfies every hypothesis with `hν` deleted, since each side of `hmom` is `0`
for `n ≠ 0` — on the left because `0 ^ n = 0`, on the right because the integral is undefined. So
`hν` is what forces `ν`'s moments to exist at all.

The strengthening that *is* available replaces `hν` by moment-integrability of `ν`, which compact
support implies: with genuine moments, a Markov bound on `x i ^ (2 * m)` confines `ν` to the same
box. That is left to a follow-up; the Layer 6 consumer already has both mixing laws on a common
compact box. -/
theorem Measure.ext_of_forall_integral_monomial_eq_of_support [Fintype ι] (hK : IsCompact K)
    {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ Kᶜ = 0) (hν : ν Kᶜ = 0)
    (hmom : ∀ n : ι → ℕ, ∫ x, ∏ i, x i ^ n i ∂μ = ∫ x, ∏ i, x i ^ n i ∂ν) :
    μ = ν := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKm : MeasurableSet K := hK.measurableSet
  have hμr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)
  have hνr : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)
  have hfin : ∀ (ρ : Measure (ι → ℝ)) [IsFiniteMeasure ρ],
      IsFiniteMeasure (Measure.comap Subtype.val ρ : Measure K) := by
    intro ρ _
    constructor
    rw [comap_subtype_coe_apply hKm]
    exact measure_lt_top ρ _
  have := hfin μ
  have := hfin ν
  have hmom' : ∀ n : ι → ℕ,
      ∫ x : K, ∏ i, (x : ι → ℝ) i ^ n i ∂(Measure.comap Subtype.val μ)
        = ∫ x : K, ∏ i, (x : ι → ℝ) i ^ n i ∂(Measure.comap Subtype.val ν) := by
    intro n
    rw [integral_subtype_comap hKm fun x => ∏ i, x i ^ n i,
      integral_subtype_comap hKm fun x => ∏ i, x i ^ n i, hμr, hνr]
    exact hmom n
  have hmap := congrArg (Measure.map (Subtype.val : K → (ι → ℝ)))
    (Measure.ext_of_forall_integral_monomial_eq hmom')
  rwa [map_comap_subtype_coe hKm, map_comap_subtype_coe hKm, hμr, hνr] at hmap

end TauCeti
