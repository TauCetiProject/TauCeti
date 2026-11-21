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
`c - a - b` is a difference of restrictions of classes `a'` and `b'`. Restricted to
`(X ∖ T, (X ∖ T) ∖ S)`, every class of `Hⁿ(X, X ∖ T)` vanishes, as the inclusion factors through
`X ∖ T`; so `a'` restricts to zero there, and `a' = 0` by excision of `T`
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

namespace TopPair

variable {X : TopCat.{w}} {A B B' : Set X}
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

/-- If `A ⊆ B''`, the inclusion `(A, A ∩ B) ⟶ (X, B')` followed by the restriction
`(X, B') ⟶ (X, B'')` factors through the subspace `B''`, so it induces zero on relative
cohomology. -/
lemma singularCohomologyMap_interPairMapOfSubset_comp_eq_zero {B'' : Set X} (h : A ∩ B ⊆ B')
    (hB : Set.MapsTo (𝟙 X) B' B'') (hA : A ⊆ B'') (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (interPairMapOfSubset h ≫ ofSubsetMap (𝟙 X) hB) n = 0 :=
  singularCohomologyMap_eq_zero_of_fac R k M _
    (TopCat.ofHom ⟨fun x : A ↦ (⟨x.val, Set.mem_of_subset_of_mem hA x.property⟩ : B''),
      by fun_prop⟩)
    -- Both sides are `Subtype.val : A → X`; the `rfl` unfolds the composite of `TopCat.ofHom`s.
    (by rw [interPairMapOfSubset_comp_ofSubsetMap_id, interPairMapOfSubset_fst, ofSubset_map]; rfl)
    n

end TopPair

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C} {X : TopCat.{w}} {S T : Set X}

/-- Restricting a class of `Hⁿ(X, X ∖ S)` to `Hⁿ(X, X ∖ T)`, `S ⊆ T`, and then to a pair
`(A, A ∩ B)` with `A ∩ B ⊆ X ∖ T` is restricting it to `(A, A ∩ B)` directly. -/
lemma singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict (hST : S ⊆ T)
    {A B : Set X} (h : A ∩ B ⊆ Tᶜ) {n : ℕ}
    (x : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset h) n
        (singularCohomologyComplRestrict R k M hST n x) =
      TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset
        (h.trans (Set.compl_subset_compl.2 hST))) n x := by
  dsimp only [singularCohomologyComplRestrict]
  rw [← TopPair.singularCohomologyMap_comp_apply, TopPair.interPairMapOfSubset_comp_ofSubsetMap_id]

/-- If moreover `A ⊆ X ∖ S`, that restriction vanishes: the inclusion of `(A, A ∩ B)` into
`(X, X ∖ S)` factors through the subspace `X ∖ S`. -/
lemma singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero
    (hST : S ⊆ T) {A B : Set X} (h : A ∩ B ⊆ Tᶜ) (hA : A ⊆ Sᶜ) {n : ℕ}
    (x : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset h) n
        (singularCohomologyComplRestrict R k M hST n x) = 0 := by
  dsimp only [singularCohomologyComplRestrict]
  rw [← TopPair.singularCohomologyMap_comp_apply,
    TopPair.singularCohomologyMap_interPairMapOfSubset_comp_eq_zero h _ hA]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

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
  set hTS : (Tᶜ ∩ Sᶜ : Set X) ⊆ (S ∪ T)ᶜ :=
    ((Set.inter_comm Tᶜ Sᶜ).trans (Set.compl_union S T).symm).subset
  set hST' : (Sᶜ ∩ Tᶜ : Set X) ⊆ (S ∪ T)ᶜ := (Set.compl_union S T).symm.subset
  -- The class `d = c - a - b` is killed by the connecting morphism, whose target vanishes, so it
  -- is a difference of restrictions of classes `a'` and `b'`.
  set d := c - singularCohomologyComplRestrict R k M Set.subset_union_left n a -
    singularCohomologyComplRestrict R k M Set.subset_union_right n b
  have hzero : IsZero ((TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M (n + 1)) :=
    TopPair.isZero_singularCohomology_of_surjective_map (R := R) (k := k) (M := M)
      (P := TopPair.ofSubset (S ∩ T)ᶜ) (fun x ↦
        ⟨⟨x, fun hx ↦ Set.disjoint_left.1 hST hx.1 hx.2⟩,
        -- The subspace map of `ofSubset` is `Subtype.val`, by definition.
        by rw [TopPair.ofSubset_map]; rfl⟩) _
  obtain ⟨a', b', hd⟩ := exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero hS hT rfl d
    (by rw [hzero.eq_of_tgt (singularCohomologyComplMayerVietorisδ R k M hS hT n (n + 1)) 0]
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply])
  -- On `(X ∖ T, (X ∖ T) ∖ S)` the class `d` vanishes, and so does every class of `Hⁿ(X, X ∖ T)`.
  have hdT : TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset hTS) n d = 0 := by
    simp only [d, map_sub, ha,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero _ _
        subset_rfl, TopPair.interPairMapOfSubset_eq_excisionMap, sub_self]
  have hdS : TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset hST') n d = 0 := by
    simp only [d, map_sub, hb,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero _ _
        subset_rfl, TopPair.interPairMapOfSubset_eq_excisionMap, sub_self, sub_zero]
  -- Hence `a'` and `b'` restrict to zero there, and vanish by excision.
  have ha' : a' = 0 := by
    refine (map_eq_zero_iff _
      (TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset hT.isOpen_compl hS
        (Set.subset_compl_iff_disjoint_right.2 hST) n)).1 ?_
    have h := congrArg (TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset hTS) n) hd
    rwa [hdT, map_sub,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero _ _
        subset_rfl, sub_zero,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict,
      TopPair.interPairMapOfSubset_eq_excisionMap] at h
  have hb' : b' = 0 := by
    refine (map_eq_zero_iff _
      (TopPair.injective_singularCohomologyMap_excisionMap_of_isClosed_subset hS.isOpen_compl hT
        (Set.subset_compl_iff_disjoint_left.2 hST) n)).1 ?_
    have h := congrArg (TopPair.singularCohomologyMap (TopPair.interPairMapOfSubset hST') n) hd
    rwa [hdS, map_sub,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict_eq_zero _ _
        subset_rfl, zero_sub,
      singularCohomologyMap_interPairMapOfSubset_singularCohomologyComplRestrict,
      TopPair.interPairMapOfSubset_eq_excisionMap, neg_eq_zero] at h
  rw [ha', hb', map_zero, map_zero, sub_zero] at hd
  rw [← sub_eq_zero, ← sub_sub, hd]

end TopCat
