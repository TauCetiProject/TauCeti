/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Topology.Compactness.Compact

/-!
# Isomorphisms over finite unions of open sets, by Mayer–Vietoris induction

Let `B` be a topological space and `H` a family of objects of an abelian category indexed by the
subsets of `B`, with restriction maps `H W ⟶ H W'` for `W ⊆ W'` that compose. Let `A` be a functor
on the subsets of `B` and `ψ W : A(W) ⟶ H W` maps commuting with the restrictions. Suppose that for
open sets `U` and `V` the map `A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism, and that the
Mayer–Vietoris sequence `H (U ∩ V) ⟶ H U ⊞ H V ⟶ H (U ∪ V)` (`TauCeti.subsetMayerVietoris`) is
exact with surjective last map. If `ψ U` and `ψ V` are isomorphisms and `ψ (U ∩ V)` is an
epimorphism, then `ψ (U ∪ V)` is an isomorphism (`TauCeti.isIso_union_of_subsetMayerVietoris`).
So if `ψ` is an isomorphism over the empty set and over every subset with a property `P` inherited
by subsets, and the Mayer–Vietoris sequences are exact with surjective last map whenever `U`
satisfies `P`, then `ψ` is an isomorphism over every finite union of open sets satisfying `P`
(`TauCeti.isIso_biUnion_of_subsetMayerVietoris`), and so over the whole space when it is compact
and covered by open sets satisfying `P` (`TauCeti.isIso_univ_of_subsetMayerVietoris`).

This is the induction of Milnor and Stasheff's proof of the Thom isomorphism: for a real vector
bundle of rank `r`, `A(W)` is the zeroth homology of `W`, possibly with twisted coefficients,
`H W` is the homology in degree `r` of the Thom pair over `W`, with constant or twisted
coefficients, `P` says that `W` lies in the base set of a trivialization, and the last map of the
Mayer–Vietoris sequence is an epimorphism because that homology vanishes in degree `r - 1` over a
trivializing set.

The inverse over `U ∪ V` is built on the middle term of the Mayer–Vietoris sequence from the
inverses over `U` and over `V`. It vanishes on the image of `H (U ∩ V)` because `ψ` is natural and
surjective over `U ∩ V`, so it descends to the cokernel `H (U ∪ V)`; it inverts `ψ` on the images
of `A(U)` and of `A(V)`, which generate `A(U ∪ V)`.

## Main definitions

* `TauCeti.subsetMayerVietoris`: the Mayer–Vietoris short complex of a family indexed by subsets.

## Main results

* `TauCeti.isIso_union_of_subsetMayerVietoris`: the Mayer–Vietoris step.
* `TauCeti.isIso_biUnion_of_subsetMayerVietoris`: `ψ` is an isomorphism over finite unions of
  open sets satisfying `P`.
* `TauCeti.isIso_univ_of_subsetMayerVietoris`: `ψ` is an isomorphism over a compact space covered
  by open sets satisfying `P`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over unions of
  trivializing open sets).
-/

public noncomputable section

open CategoryTheory Limits Set

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] {B : Type w} {H : Set B → C}
  (res : ∀ {W W' : Set B}, W ⊆ W' → (H W ⟶ H W'))
  (hres : ∀ {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W''), res h ≫ res h' = res (h.trans h'))

/-- The **Mayer–Vietoris short complex** `H (U ∩ V) ⟶ H U ⊞ H V ⟶ H (U ∪ V)` of a family of objects
indexed by the subsets of `B`, with restriction maps `res`: the first map is the difference of the
restrictions and the second their sum. -/
abbrev subsetMayerVietoris (U V : Set B) : ShortComplex C :=
  ShortComplex.mk (biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
      (-res (inter_subset_right : U ∩ V ⊆ V)))
    (biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)))
    (by simp [hres])

variable {A : Set B ⥤ C} {ψ : ∀ W, A.obj W ⟶ H W}
  (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), A.map (homOfLE h) ≫ ψ W' = ψ W ≫ res h)

include hψ

/-- **The Mayer–Vietoris step**: if `ψ U` and `ψ V` are isomorphisms, `ψ (U ∩ V)` is an
epimorphism, `A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism, and the Mayer–Vietoris sequence is exact
with surjective last map, then `ψ (U ∪ V)` is an isomorphism. -/
theorem isIso_union_of_subsetMayerVietoris {U V : Set B}
    (hA : Epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
      (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V)))))
    [IsIso (ψ U)] [IsIso (ψ V)] [Epi (ψ (U ∩ V))] (hS : (subsetMayerVietoris res hres U V).Exact)
    [Epi (subsetMayerVietoris res hres U V).g] :
    IsIso (ψ (U ∪ V)) := by
  let S := subsetMayerVietoris res hres U V
  -- The candidate inverse on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ A.obj (U ∪ V) :=
    biprod.desc (inv (ψ U) ≫ A.map (homOfLE subset_union_left))
      (inv (ψ V) ≫ A.map (homOfLE subset_union_right))
  have hres' {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W')] :
      ψ W ≫ res h ≫ inv (ψ W') = A.map (homOfLE h) := by
    rw [← Category.assoc, ← hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- It vanishes on the image of the first map: both restrictions from `U ∩ V` to `U ∪ V` agree.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, φ, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, reassoc_of% (hres' inter_subset_left),
      reassoc_of% (hres' inter_subset_right), ← Functor.map_comp, add_neg_eq_zero]
    -- Both composites are morphisms `U ∩ V ⟶ U ∪ V` of the preorder of subsets.
    exact congrArg A.map (Subsingleton.elim _ _)
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  have e₁ : res subset_union_left = biprod.inl ≫ S.g := (biprod.inl_desc _ _).symm
  have e₂ : res subset_union_right = biprod.inr ≫ S.g := (biprod.inr_desc _ _).symm
  refine ⟨Φ, (cancel_epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
    (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V))))).1 (biprod.hom_ext' _ _ ?_ ?_),
    (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · rw [biprod.inl_desc_assoc, reassoc_of% (hψ subset_union_left), Category.comp_id,
      biprod.inl_desc, e₁, Category.assoc, hgΦ, biprod.inl_desc, IsIso.hom_inv_id_assoc]
  · rw [biprod.inr_desc_assoc, reassoc_of% (hψ subset_union_right), Category.comp_id,
      biprod.inr_desc, e₂, Category.assoc, hgΦ, biprod.inr_desc, IsIso.hom_inv_id_assoc]
  · rw [reassoc_of% hgΦ, Category.comp_id, biprod.inl_desc_assoc, Category.assoc, hψ,
      IsIso.inv_hom_id_assoc, e₁]
  · rw [reassoc_of% hgΦ, Category.comp_id, biprod.inr_desc_assoc, Category.assoc, hψ,
      IsIso.inv_hom_id_assoc, e₂]

variable [TopologicalSpace B] {P : Set B → Prop} (hP : ∀ {W W' : Set B}, W ⊆ W' → P W' → P W)
  (hPψ : ∀ W, P W → IsIso (ψ W)) (hempty : IsIso (ψ ∅))
  (hA : ∀ {U V : Set B}, IsOpen U → IsOpen V →
    Epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
      (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V)))))
  (hMV : ∀ {U V : Set B}, IsOpen U → IsOpen V → P U →
    (subsetMayerVietoris res hres U V).Exact ∧ Epi (subsetMayerVietoris res hres U V).g)

include hP hPψ hempty hA hMV

/-- **Finite unions**: if `ψ` is an isomorphism over the empty set and over every subset with a
property `P` inherited by subsets, `A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism for open `U` and
`V`, and the Mayer–Vietoris sequence of open sets `U` and `V` with `U` satisfying `P` is exact with
surjective last map, then `ψ` is an isomorphism over every finite
union of open sets satisfying `P`. -/
theorem isIso_biUnion_of_subsetMayerVietoris {κ : Type*} (s : Finset κ) {W : κ → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i)) (hWP : ∀ i ∈ s, P (W i)) :
    IsIso (ψ (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset κ), W i) = ∅ by simp]
    exact hempty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hao := hWo a (Finset.mem_insert_self a s)
    have haP := hWP a (Finset.mem_insert_self a s)
    have : IsIso (ψ (W a)) := hPψ _ haP
    have : IsIso (ψ (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWP i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the open sets `W a ∩ W i`, `i ∈ s`, satisfying `P`.
    have : IsIso (ψ (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      exact ih (fun i hi ↦ hao.inter (hWo i (Finset.mem_insert_of_mem hi)))
        fun _ _ ↦ hP inter_subset_left haP
    have hVo := isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi)
    obtain ⟨hS, hg⟩ := hMV hao hVo haP
    exact isIso_union_of_subsetMayerVietoris res hres hψ (hA hao hVo) hS

/-- **Compact spaces**: under the hypotheses of `TauCeti.isIso_biUnion_of_subsetMayerVietoris`, if
`B` is compact and every point has an open neighbourhood satisfying `P`, then `ψ` is an
isomorphism over the whole space. -/
theorem isIso_univ_of_subsetMayerVietoris [CompactSpace B]
    (hcover : ∀ b : B, ∃ U, IsOpen U ∧ b ∈ U ∧ P U) :
    IsIso (ψ univ) := by
  choose U hUo hbU hUP using hcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    fun b _ ↦ mem_iUnion.2 ⟨b, hbU b⟩
  have h := isIso_biUnion_of_subsetMayerVietoris res hres hψ hP hPψ hempty hA hMV t
    (fun b _ ↦ hUo b) fun b _ ↦ hUP b
  rwa [univ_subset_iff.1 ht] at h

end TauCeti
