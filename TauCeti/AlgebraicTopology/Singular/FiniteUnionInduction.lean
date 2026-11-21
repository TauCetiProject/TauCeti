/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Isomorphisms out of zeroth homology over finite unions of open sets

Let `B` be a topological space and `H` a family of objects of an abelian category indexed by the
subsets of `B`, with restriction maps `H W ⟶ H W'` for `W ⊆ W'` that compose. Suppose that maps
`ψ W : H₀(W; M) ⟶ H W` are given, natural in `W`, which are isomorphisms over every subset with a
property `P` inherited by subsets. If for open sets `U` and `V` with `U` satisfying `P` the
Mayer–Vietoris sequence `H (U ∩ V) ⟶ H U ⊞ H V ⟶ H (U ∪ V)` (`TauCeti.subsetMayerVietoris`) is
exact and its last map is an epimorphism, then `ψ` is an isomorphism over every finite union of
open sets satisfying `P` (`TauCeti.isIso_biUnion_of_subsetMayerVietoris`), and so over the whole
space when it is compact and covered by open sets satisfying `P`
(`TauCeti.isIso_univ_of_subsetMayerVietoris`).

This is the induction of Milnor and Stasheff's proof of the Thom isomorphism: for a real vector
bundle of rank `r`, `H W` is the homology in degree `r` of the Thom pair over `W`, with constant or
twisted coefficients, `P` says that `W` lies in the base set of a trivialization, and the last map
of the Mayer–Vietoris sequence is an epimorphism because that homology vanishes in degree `r - 1`
over a trivializing set.

The inverse over `U ∪ V` is built on the middle term of the Mayer–Vietoris sequence from the
inverses over `U` and over `V`. It vanishes on the image of `H (U ∩ V)` because `ψ` is natural and
surjective over `U ∩ V`, so it descends to the cokernel `H (U ∪ V)`; it inverts `ψ` on the classes
of points, which lie in `U` or in `V`.

## Main definitions

* `TauCeti.subsetMayerVietoris`: the Mayer–Vietoris short complex of a family indexed by subsets.

## Main results

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

open CategoryTheory Limits Set AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] {B : Type w}
  [TopologicalSpace B] {H : Set B → C} (res : ∀ {W W' : Set B}, W ⊆ W' → (H W ⟶ H W'))
  (hres : ∀ {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W''), res h ≫ res h' = res (h.trans h'))

/-- The **Mayer–Vietoris short complex** `H (U ∩ V) ⟶ H U ⊞ H V ⟶ H (U ∪ V)` of a family of objects
indexed by the subsets of `B`, with restriction maps `res`: the first map is the difference of the
restrictions and the second their sum. -/
abbrev subsetMayerVietoris (U V : Set B) : ShortComplex C :=
  ShortComplex.mk (biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
      (-res (inter_subset_right : U ∩ V ⊆ V)))
    (biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)))
    (by simp [hres])

variable (M : C) {ψ : ∀ W : Set B, ((singularHomologyFunctor C 0).obj M).obj (TopCat.of W) ⟶ H W}
  (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), ((singularHomologyFunctor C 0).obj M).map
    (TopCat.ofHom (ContinuousMap.inclusion h)) ≫ ψ W' = ψ W ≫ res h)

include hψ

/-- On a point of `W ⊆ W'`, a candidate inverse `Φ` of `ψ W'` which on the image of `H W` is the
inverse of `ψ W` followed by the inclusion inverts `ψ W'`. -/
private theorem singularHomology₀Section_comp_comp_of_comp_eq {W W' : Set B} (h : W ⊆ W')
    [IsIso (ψ W)] {Φ : H W' ⟶ ((singularHomologyFunctor C 0).obj M).obj (TopCat.of W')}
    (hΦ : res h ≫ Φ = inv (ψ W) ≫ ((singularHomologyFunctor C 0).obj M).map
      (TopCat.ofHom (ContinuousMap.inclusion h))) (x : W) :
    singularHomology₀Section M (X := TopCat.of W') (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        ψ W' ≫ Φ =
      singularHomology₀Section M (X := TopCat.of W')
        (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc, reassoc_of% (hψ h), hΦ,
    IsIso.hom_inv_id_assoc]

/-- **The Mayer–Vietoris step**: if `ψ` is an isomorphism over the open sets `U` and `V` and
surjective over `U ∩ V`, and the Mayer–Vietoris sequence is exact with surjective last map, then
`ψ` is an isomorphism over `U ∪ V`. -/
private theorem isIso_union_of_subsetMayerVietoris {U V : Set B} [IsIso (ψ U)] [IsIso (ψ V)]
    [Epi (ψ (U ∩ V))] (hS : (subsetMayerVietoris res hres U V).Exact)
    [Epi (subsetMayerVietoris res hres U V).g] :
    IsIso (ψ (U ∪ V)) := by
  let H₀ := (singularHomologyFunctor C 0).obj M
  let S := subsetMayerVietoris res hres U V
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ H₀.obj (TopCat.of ↥(U ∪ V)) :=
    biprod.desc (inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)))
      (inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)))
  -- It vanishes on the image of the first map, since both restrictions of a class over `U ∩ V`
  -- give the same class over `U ∪ V`.
  have hφ : S.f ≫ φ = 0 := by
    have hres' {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W')] :
        ψ W ≫ res h ≫ inv (ψ W') = H₀.map (TopCat.ofHom (ContinuousMap.inclusion h)) := by
      rw [← Category.assoc, ← hψ h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, φ, H₀, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, reassoc_of% hres', ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.inclusion_comp_inclusion, add_neg_eq_zero]
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the image of `H U` and of `H V`, `Φ` is the inverse of `ψ U` or `ψ V`.
  have hΦU : res subset_union_left ≫ Φ =
      inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)) := by
    rw [← biprod.inl_desc (res subset_union_left) (res subset_union_right), Category.assoc]
    exact (congrArg (biprod.inl ≫ ·) hgΦ).trans (biprod.inl_desc _ _)
  have hΦV : res subset_union_right ≫ Φ =
      inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)) := by
    rw [← biprod.inr_desc (res subset_union_left) (res subset_union_right), Category.assoc]
    exact (congrArg (biprod.inr ≫ ·) hgΦ).trans (biprod.inr_desc _ _)
  refine ⟨Φ, singularHomology₀_hom_ext _ fun x ↦ ?_,
    (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    rw [Category.comp_id]
    obtain ⟨x, hx | hx⟩ := x
    · exact singularHomology₀Section_comp_comp_of_comp_eq res M hψ _ hΦU ⟨x, hx⟩
    · exact singularHomology₀Section_comp_comp_of_comp_eq res M hψ _ hΦV ⟨x, hx⟩
  -- The second map of the Mayer–Vietoris sequence is an epimorphism.
  · have e₁ : biprod.inl ≫ S.g = res subset_union_left := biprod.inl_desc _ _
    rw [Category.comp_id, reassoc_of% e₁, reassoc_of% hΦU, hψ, IsIso.inv_hom_id_assoc, e₁]
  · have e₂ : biprod.inr ≫ S.g = res subset_union_right := biprod.inr_desc _ _
    rw [Category.comp_id, reassoc_of% e₂, reassoc_of% hΦV, hψ, IsIso.inv_hom_id_assoc, e₂]

variable {P : Set B → Prop} (hP : ∀ {W W' : Set B}, W ⊆ W' → P W' → P W)
  (hPψ : ∀ W, P W → IsIso (ψ W)) (hempty : IsIso (ψ ∅))
  (hMV : ∀ {U V : Set B}, IsOpen U → IsOpen V → P U →
    (subsetMayerVietoris res hres U V).Exact ∧ Epi (subsetMayerVietoris res hres U V).g)

include hP hPψ hempty hMV

/-- **Finite unions**: if `ψ` is an isomorphism over every subset with a property `P` inherited by
subsets, and the Mayer–Vietoris sequence of open sets `U` and `V` with `U` satisfying `P` is exact
with surjective last map, then `ψ` is an isomorphism over every finite union of open sets
satisfying `P`. -/
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
    obtain ⟨hS, hg⟩ := hMV hao
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi)) haP
    exact isIso_union_of_subsetMayerVietoris res hres M hψ hS

/-- **Compact spaces**: under the hypotheses of `TauCeti.isIso_biUnion_of_subsetMayerVietoris`, if
`B` is compact and every point has an open neighbourhood satisfying `P`, then `ψ` is an
isomorphism over the whole space. -/
theorem isIso_univ_of_subsetMayerVietoris [CompactSpace B]
    (hcover : ∀ b : B, ∃ U, IsOpen U ∧ b ∈ U ∧ P U) :
    IsIso (ψ univ) := by
  choose U hUo hbU hUP using hcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    fun b _ ↦ mem_iUnion.2 ⟨b, hbU b⟩
  have h := isIso_biUnion_of_subsetMayerVietoris res hres M hψ hP hPψ hempty hMV t
    (fun b _ ↦ hUo b) fun b _ ↦ hUP b
  rwa [univ_subset_iff.1 ht] at h

end TauCeti
