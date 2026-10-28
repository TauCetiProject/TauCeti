/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.AnalyticBelyiPair
public import TauCeti.Combinatorics.PermutationTriple.Examples

/-!
# Analytic Belyi pairs unramified over `1`

An analytic Belyi pair is determined up to isomorphism by the isomorphism class of its monodromy
triple (`TauCeti.AnalyticBelyiPair.nonempty_iso_iff_isoClass_monodromyTriple_eq`), and the
components of that triple that are the identity are exactly the points of `{0, 1, ∞}` over which
the Belyi map is unramified (`TauCeti.AnalyticBelyiPair.monodromyTriple_σ1_eq_one_iff` and its
analogues over `0` and `∞`). This file treats the pairs whose Belyi map is unramified over `1`,
and the pairs with at most one branch value.

* A pair unramified over `1` is isomorphic to the power map `z ↦ z ^ n` of the Riemann sphere,
  where `n` is its degree (`TauCeti.AnalyticBelyiPair.nonempty_iso_pow_iff`). Indeed `σ1 = 1`
  in its monodromy triple, so `σ0` alone generates a transitive group and the triple is
  isomorphic to the cyclic triple `TauCeti.PermutationTriple.cyclicTriple n`
  (`TauCeti.AnalyticBelyiPair.isoClass_monodromyTriple_eq_cyclicTriple_iff`), as is the triple of
  `z ↦ z ^ n`. In particular the surface of such a pair is the Riemann sphere.
* A pair with at most one branch value has degree one
  (`TauCeti.AnalyticBelyiPair.degree_β_eq_one_of_branchValues_subset_singleton`): two of the
  components of its triple are the identity, so the third is too, and a connected triple with
  trivial monodromy has a single sheet.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Theorem 2.61 (covers with the same branch values are isomorphic exactly when their monodromies
  are conjugate), applied here to the covers with at most two branch values.
-/

public section

namespace TauCeti

open RiemannSurface ThricePuncturedSphere PermutationTriple

open scoped OnePoint

namespace AnalyticBelyiPair

/-- **The monodromy triple of a pair is isomorphic to the cyclic triple exactly when the Belyi map
is unramified over `1`**, for any numbering of the fibre over `1/2`. -/
theorem isoClass_monodromyTriple_eq_cyclicTriple_iff {P : AnalyticBelyiPair.{0}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    IsoClass.mk (P.isCoveringMap_restrict.monodromyTriple ν) = IsoClass.mk (cyclicTriple n) ↔
      ((1 : ℂ) : OnePoint ℂ) ∉ P.β.branchValues := by
  rw [IsoClass.mk_eq_mk_iff,
    equivalent_cyclicTriple_iff (P.isCoveringMap_restrict.isConnected_monodromyTriple ν),
    P.monodromyTriple_σ1_eq_one_iff]

/-- **The analytic Belyi pairs unramified over `1` are the power maps.** A pair is isomorphic to
the Riemann sphere with the power map `z ↦ z ^ n` exactly when it has degree `n` and its Belyi map
is unramified over `1`. -/
theorem nonempty_iso_pow_iff {P : AnalyticBelyiPair.{0}} {n : ℕ} (hn : n ≠ 0) :
    Nonempty (P.Iso (pow hn)) ↔ degree P.β = n ∧ ((1 : ℂ) : OnePoint ℂ) ∉ P.β.branchValues := by
  obtain ⟨ν⟩ := P.nonempty_restrict_preimage_singleton_equiv basePt
  obtain ⟨ν'⟩ := (pow hn).nonempty_restrict_preimage_singleton_equiv basePt
  have hpow := ((pow hn).isoClass_monodromyTriple_eq_cyclicTriple_iff
    (ν'.trans (finCongr (degree_β_pow hn)))).2 (one_notMem_branchValues_β_pow hn)
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨hdeg, h⟩ ↦ ?_⟩
  · have hdeg : degree P.β = n := e.degree_eq.trans (degree_β_pow hn)
    refine ⟨hdeg, (P.isoClass_monodromyTriple_eq_cyclicTriple_iff (ν.trans (finCongr hdeg))).1 ?_⟩
    rw [← e.isoClass_monodromyTriple_eq, hpow]
  · rw [nonempty_iso_iff_isoClass_monodromyTriple_eq (ν.trans (finCongr hdeg)), hpow,
      (P.isoClass_monodromyTriple_eq_cyclicTriple_iff _).2 h]

/-- **An analytic Belyi pair with at most one branch value has degree one**, so it is trivial
(`TauCeti.AnalyticBelyiPair.degree_β_eq_one_iff_nonempty_iso`). -/
theorem degree_β_eq_one_of_branchValues_subset_singleton (P : AnalyticBelyiPair.{0})
    {q : OnePoint ℂ} (hq : P.β.branchValues ⊆ {q}) : degree P.β = 1 := by
  obtain ⟨ν⟩ := P.nonempty_restrict_preimage_singleton_equiv basePt
  set t := P.isCoveringMap_restrict.monodromyTriple ν
  have hne {y : OnePoint ℂ} (hy : y ≠ q) : y ∉ P.β.branchValues := fun h ↦ hy (hq h)
  have h0 := P.monodromyTriple_σ0_eq_one_iff ν
  have h1 := P.monodromyTriple_σ1_eq_one_iff ν
  have hinf := P.monodromyTriple_σinf_eq_one_iff ν
  -- The Belyi map is unramified over two of the three points, so two of the components are the
  -- identity, and the product relation gives the third. The connected trivial triple has one sheet.
  have ht : t = 1 := by
    by_cases hq0 : ((0 : ℂ) : OnePoint ℂ) = q
    · subst hq0
      exact eq_one_of_σ1_eq_one_of_σinf_eq_one (h1.2 (hne (by simp))) (hinf.2 (hne (by simp)))
    by_cases hq1 : ((1 : ℂ) : OnePoint ℂ) = q
    · subst hq1
      exact eq_one_of_σ0_eq_one_of_σinf_eq_one (h0.2 (hne (by simp))) (hinf.2 (hne (by simp)))
    · exact ext_of_two (h0.2 (hne hq0)) (h1.2 (hne hq1))
  exact isConnected_one_iff.1 (ht ▸ P.isCoveringMap_restrict.isConnected_monodromyTriple ν)

end AnalyticBelyiPair

end TauCeti
