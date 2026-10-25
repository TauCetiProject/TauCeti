/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Eisenstein
import TauCeti.RingTheory.DiscreteValuationRing.RootPartition
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly

/-!
# Counting roots of an Eisenstein polynomial in balls

Let `L / K` be a finite separable extension of nonarchimedean local fields and `g` an Eisenstein
polynomial over `𝒪[K]` of degree `[L : K]`. Every root `z` of `g` in `𝒪[L]` generates `L` over
`K`, so it is a uniformizer of `L`, and the order of `g'(z)` is the different exponent `d` of
`L / K`. Consequently, if the uniformizers of `L` are covered by a finite family of pairwise
disjoint balls of order `r > d`, each ball contains at most one root of `g`, and the number of
roots of `g` in `𝒪[L]` is the number of balls containing a root. Such a family of balls exists
for every order `r ≥ 2`, by `TauCeti.exists_finset_addVal_eq_biUnion`.

The point of this count is that the family of balls is fixed once and for all, independently of
`g`: the root count of every Eisenstein polynomial of degree `[L : K]` becomes a finite sum of
indicators of the same balls. Integrating the root count over the Eisenstein polynomials thus
reduces to measuring, for each ball, the polynomials having a root in it.

## Main results

* `TauCeti.adjoin_eq_top_of_eisenstein_of_natDegree_eq_finrank`: a root in `𝒪[L]` of an
  Eisenstein polynomial of degree `[L : K]` generates `L` over `K`.
* `TauCeti.card_roots_map_eq_sum_ite_of_eisenstein`: the number of roots in `𝒪[L]` of an
  Eisenstein polynomial of degree `[L : K]` is the number of balls of a disjoint cover of the
  uniformizers by balls of order larger than the different exponent that contain a root.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- A root in `𝒪[L]` of an Eisenstein polynomial over `𝒪[K]` of degree `[L : K]` generates `L`
over `K`. -/
theorem adjoin_eq_top_of_eisenstein_of_natDegree_eq_finrank {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = Module.finrank K L) {ξ : 𝒪[L]}
    (hroot : (f.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ) : K⟮(ξ : L)⟯ = ⊤ := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have hassoc : Associated (minpoly 𝒪[K] ξ) f :=
    associated_minpoly_of_eisenstein_isRoot ξ f hf hroot
  -- The minimal polynomial of `ξ` over `K` comes from that over `𝒪[K]`, of degree `deg f`.
  have hminpoly : minpoly K (ξ : L) = (minpoly 𝒪[K] ξ).map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.adjoin.finrank (.of_finite K (ξ : L)), hminpoly,
    (minpoly.monic hint).natDegree_map, natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated hassoc), hdeg, IntermediateField.finrank_top']

variable [Algebra.IsSeparable K L]

open Classical in
/-- **Root counts of Eisenstein polynomials as sums over balls.** Let `g` be an Eisenstein
polynomial over `𝒪[K]` of degree `[L : K]`, and let `C` index a family of pairwise disjoint balls
`v_L(x - c) ≥ r` covering the uniformizers of `L`, of order `r` larger than the different exponent
of `L / K`. Then the number of roots of `g` in `𝒪[L]`, counted with multiplicity, is the number of
these balls that contain a root of `g`. -/
theorem card_roots_map_eq_sum_ite_of_eisenstein {g : 𝒪[K][X]} (hg : g.IsEisensteinAt 𝓂[K])
    (hdeg : g.natDegree = Module.finrank K L) {r : ℕ} (hr : differentExponent K L < r)
    (C : Finset 𝒪[L])
    (hcover : {x : 𝒪[L] | addVal 𝒪[L] x = 1} ⊆
      ⋃ c ∈ C, {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)})
    (hdisj : (C : Set 𝒪[L]).PairwiseDisjoint
      fun c ↦ {x : 𝒪[L] | (r : ℕ∞) ≤ addVal 𝒪[L] (x - c)}) :
    (g.map (algebraMap 𝒪[K] 𝒪[L])).roots.card =
      ∑ c ∈ C, if ∃ z : 𝒪[L], aeval z g = 0 ∧ (r : ℕ∞) ≤ addVal 𝒪[L] (z - c) then 1 else 0 := by
  set F := g.map (algebraMap 𝒪[K] 𝒪[L])
  have hF : F ≠ 0 := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective _ _)).2
    fun h ↦ hg.leading (by simp [h])
  have hmem (z : 𝒪[L]) : z ∈ F.roots ↔ aeval z g = 0 := by
    rw [mem_roots hF, IsRoot, eval_map_algebraMap]
  -- Every root generates `L`, so it is a uniformizer and `g'` has order `d(L / K)` there.
  have hgen {z : 𝒪[L]} (hz : z ∈ F.roots) : K⟮(z : L)⟯ = ⊤ :=
    adjoin_eq_top_of_eisenstein_of_natDegree_eq_finrank hg hdeg (isRoot_of_mem_roots hz)
  rw [F.card_roots_eq_sum_ite_of_addVal_lt C (fun z hz ↦ ?_) hdisj fun z hz ↦ ?_]
  · refine Finset.sum_congr rfl fun c _ ↦ if_congr ?_ rfl rfl
    simp only [hmem]
  · have hz1 : addVal 𝒪[L] z = 1 :=
      addVal_uniformizer (irreducible_of_eisenstein_adjoin_eq_top g hg z
        (isRoot_of_mem_roots hz) (hgen hz))
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hcover hz1
  · rw [derivative_map, eval_map_algebraMap,
      ← natCast_differentExponent_eq_addVal_aeval_derivative_of_eisenstein_adjoin_eq_top g hg z
        (isRoot_of_mem_roots hz) (hgen hz)]
    exact_mod_cast hr

end TauCeti
