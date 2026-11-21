/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Excision
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Compl

/-!
# Relative classes supported on two disjoint closed sets

Let `S` and `T` be disjoint closed subsets of a topological space `X`, and write `Hⁿ(-)` for
relative singular cohomology. A class of `Hⁿ(X, X ∖ (S ∪ T))` is supported near `S ∪ T`; since `S`
and `T` are disjoint, it splits as the sum of a class supported near `S` and a class supported near
`T`. This file proves the splitting in the form in which it is used to add up local
contributions: if `c ∈ Hⁿ(X, X ∖ (S ∪ T))`, `a ∈ Hⁿ(X, X ∖ S)` and `b ∈ Hⁿ(X, X ∖ T)` agree on the
open set `X ∖ T` around `S`, and on the open set `X ∖ S` around `T`, then `c` is the sum of the
restrictions of `a` and `b`
(`TopCat.eq_singularCohomologyComplRestrict_add_of_disjoint`).

Here `c` and `a` *agree on `X ∖ T`* when they have the same pull-back to the pair
`(X ∖ T, (X ∖ T) ∖ S)`, along the inclusions into `(X, X ∖ (S ∪ T))`
(`TopPair.interPairMapOfSubset`) and into `(X, X ∖ S)` (`TopPair.excisionMap`).

The proof combines two exact sequences. Since `S ∩ T` is empty, `Hⁿ⁺¹(X, X ∖ (S ∩ T))` vanishes,
so by the Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)`
(`TopCat.exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero`) the difference
`c - a - b` is a difference of restrictions of classes `a'` and `b'`, so `c` is the sum of the
restrictions of `a + a'` and `b - b'`. Restricted to `(X ∖ T, (X ∖ T) ∖ S)`, every class of
`Hⁿ(X, X ∖ T)` vanishes, as the inclusion factors through `X ∖ T`
(`TopCat.singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_add`); so
`a + a'` and `a` have the same restriction there, and `a' = 0` by excision of `T`
(`TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset`). Symmetrically
`b' = 0`.

## Main results

* `TopCat.eq_singularCohomologyComplRestrict_add_of_disjoint`: the splitting of a relative class
  supported on two disjoint closed sets.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the Mayer–Vietoris sequence of the pairs `(X, X ∖ K)` and `(X, X ∖ L)` in the proof
  of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C} {X : TopCat.{w}} {S T : Set X}

/-- Let `S, T ⊆ U`. On the pair `(X ∖ T, (X ∖ T) ∖ S)`, the restriction to `Hⁿ(X, X ∖ U)` of
`a ∈ Hⁿ(X, X ∖ S)` plus that of `b ∈ Hⁿ(X, X ∖ T)` only sees `a`: the pair lies in `X ∖ T`, so `b`
restricts to zero there. -/
lemma singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_add {U : Set X}
    (hSU : S ⊆ U) (hTU : T ⊆ U) (h : Tᶜ ∩ Sᶜ ⊆ Uᶜ) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n)
    (b : (TopPair.ofSubset Tᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset h) n
        (singularCohomologyComplRestrict R k M hSU n a +
          singularCohomologyComplRestrict R k M hTU n b) =
      TopPair.singularCohomologyMap (TopPair.excisionMap Tᶜ Sᶜ) n a := by
  rw [map_add,
    singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero hTU h
      subset_rfl, add_zero,
    singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict,
    TopPair.interPairMapOfSubset_eq_excisionMap]

/-- **A relative class supported on two disjoint closed sets is a sum.** Let `S` and `T` be
disjoint closed subsets of `X`. If `c ∈ Hⁿ(X, X ∖ (S ∪ T))` has the same restriction as
`a ∈ Hⁿ(X, X ∖ S)` to the pair `(X ∖ T, (X ∖ T) ∖ S)`, and the same restriction as
`b ∈ Hⁿ(X, X ∖ T)` to the pair `(X ∖ S, (X ∖ S) ∖ T)`, then `c` is the sum of the restrictions of
`a` and `b` to `Hⁿ(X, X ∖ (S ∪ T))`. -/
theorem eq_singularCohomologyComplRestrict_add_of_disjoint (hS : IsClosed S) (hT : IsClosed T)
    (hST : Disjoint S T) {n : ℕ} (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n)
    (b : (TopPair.ofSubset Tᶜ).singularCohomology R k M n)
    (c : (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n)
    (ha : TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (TopPair.interPairMapOfSubset
        ((Set.inter_comm Tᶜ Sᶜ).trans (Set.compl_union S T).symm).subset) n c =
      TopPair.singularCohomologyMap (TopPair.excisionMap Tᶜ Sᶜ) n a)
    (hb : TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (TopPair.interPairMapOfSubset
        (Set.compl_union S T).symm.subset) n c =
      TopPair.singularCohomologyMap (TopPair.excisionMap Sᶜ Tᶜ) n b) :
    c = singularCohomologyComplRestrict R k M Set.subset_union_left n a +
      singularCohomologyComplRestrict R k M Set.subset_union_right n b := by
  -- The class `c - a - b` is killed by the connecting morphism, whose target vanishes, so it is a
  -- difference of restrictions of classes `a'` and `b'`.
  have hzero : IsZero ((TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M (n + 1)) :=
    TopPair.isZero_singularCohomology_of_surjective_map (R := R) (k := k) (M := M)
      (P := TopPair.ofSubset (S ∩ T)ᶜ) (fun x ↦
        ⟨⟨x, fun hx ↦ Set.disjoint_left.1 hST hx.1 hx.2⟩,
        -- The subspace map of `ofSubset` is `Subtype.val`, by definition.
        by rw [TopPair.ofSubset_map]; rfl⟩) _
  obtain ⟨a', b', hd⟩ := exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero hS hT rfl
    (c - singularCohomologyComplRestrict R k M Set.subset_union_left n a -
      singularCohomologyComplRestrict R k M Set.subset_union_right n b)
    (by rw [hzero.eq_of_tgt (singularCohomologyComplMayerVietorisδ R k M hS hT n (n + 1)) 0]
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply])
  -- So `c` is the sum of the restrictions of `a + a'` and `b - b'`.
  have hc : c = singularCohomologyComplRestrict R k M Set.subset_union_left n (a + a') +
      singularCohomologyComplRestrict R k M Set.subset_union_right n (b - b') := by
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq] at hd
    rw [map_add, map_sub, ← hd]
    abel
  -- On `(X ∖ T, (X ∖ T) ∖ S)` the class `c` restricts as `a + a'` and as `a`, so `a' = 0` by
  -- excision of `T`; symmetrically `b' = 0`.
  rw [hc, singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_add] at ha
  rw [hc, add_comm,
    singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_add] at hb
  have ha' : a' = 0 := by
    simpa using TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset
      hT.isOpen_compl hS (Set.subset_compl_iff_disjoint_right.2 hST) n ha
  have hb' : b' = 0 := by
    simpa using TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset
      hS.isOpen_compl hT (Set.subset_compl_iff_disjoint_left.2 hST) n hb
  rw [hc, ha', hb', add_zero, sub_zero]

end TopCat
