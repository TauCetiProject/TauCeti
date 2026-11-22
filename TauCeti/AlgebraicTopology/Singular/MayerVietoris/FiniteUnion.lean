/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Basic

/-!
# Isomorphisms glued over finite unions by Mayer–Vietoris

Let `A` be a functor on the subsets of a space `B` with values in an abelian category, let `M`
assign to each subset `W` of `B` an object `M W`, with restriction maps `M W ⟶ M W'` for
`W ⊆ W'`, and let `ψ W : A(W) ⟶ M W` be maps commuting with the restrictions. Suppose that for
open sets `U` and `V` the map `A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism and the restrictions form
an exact Mayer–Vietoris sequence

`M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V)`

whose second map is an epimorphism. If `ψ U` and `ψ V` are isomorphisms and `ψ (U ∩ V)` is an
epimorphism, then `ψ (U ∪ V)` is an isomorphism (`TauCeti.isIso_union_of_mayerVietoris`): its
inverse is glued on the middle term of the sequence from the inverses over `U` and over `V`. By
induction on their number, `ψ` is an isomorphism over every finite union of open sets from a family
closed under subsets on which it is an isomorphism and the sequence is exact on the right
(`TauCeti.isIso_biUnion_of_mayerVietoris`).

This is the gluing step in the computations of the homology of the Thom pair of a vector bundle in
the rank degree: there `M W` is that homology over `W`, with constant or local coefficients, the
sequence is exact on the right over a trivializing set since the homology vanishes below the rank,
and `A(W)` is a group computed from `W`, such as `H₀(W)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets).
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] {B : Type w}
  {A : Set B ⥤ C} {M : Set B → C} (res : ∀ ⦃W W' : Set B⦄, W ⊆ W' → (M W ⟶ M W'))
  (ψ : ∀ W : Set B, A.obj W ⟶ M W)

/-- **The Mayer–Vietoris step**: if `A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism, the restrictions
form an exact sequence `M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V)` whose second map is an epimorphism,
`ψ U` and `ψ V` are isomorphisms and `ψ (U ∩ V)` is an epimorphism, then `ψ (U ∪ V)` is an
isomorphism. -/
theorem isIso_union_of_mayerVietoris
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'), A.map (homOfLE h) ≫ ψ W' = ψ W ≫ res h)
    {U V : Set B}
    (hA : Epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
      (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V)))))
    (hw : biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
        (-res (inter_subset_right : U ∩ V ⊆ V)) ≫
      biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)) =
        0)
    (hS : (ShortComplex.mk _ _ hw).Exact)
    (hg : Epi (biprod.desc (res (subset_union_left : U ⊆ U ∪ V))
      (res (subset_union_right : V ⊆ U ∪ V))))
    [IsIso (ψ U)] [IsIso (ψ V)] [Epi (ψ (U ∩ V))] :
    IsIso (ψ (U ∪ V)) := by
  let S := ShortComplex.mk _ _ hw
  have : Epi S.g := hg
  -- The candidate inverse on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ A.obj (U ∪ V) :=
    biprod.desc (inv (ψ U) ≫ A.map (homOfLE subset_union_left))
      (inv (ψ V) ≫ A.map (homOfLE subset_union_right))
  have hres {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W')] :
      ψ W ≫ res h ≫ inv (ψ W') = A.map (homOfLE h) := by
    rw [← Category.assoc, ← hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- It vanishes on the image of the first map: both restrictions from `U ∩ V` to `U ∪ V` agree.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, φ, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, reassoc_of% (hres inter_subset_left),
      reassoc_of% (hres inter_subset_right), ← Functor.map_comp, add_neg_eq_zero]
    -- Both composites are morphisms `U ∩ V ⟶ U ∪ V` of the preorder of subsets.
    exact congrArg A.map (Subsingleton.elim _ _)
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  refine ⟨Φ, (cancel_epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
    (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V))))).1 (biprod.hom_ext' _ _ ?_ ?_),
    (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · rw [biprod.inl_desc_assoc, reassoc_of% (hψ subset_union_left), Category.comp_id,
      biprod.inl_desc]
    have : res (subset_union_left : U ⊆ U ∪ V) = biprod.inl ≫ S.g := (biprod.inl_desc _ _).symm
    rw [this, Category.assoc, hgΦ, biprod.inl_desc, IsIso.hom_inv_id_assoc]
  · rw [biprod.inr_desc_assoc, reassoc_of% (hψ subset_union_right), Category.comp_id,
      biprod.inr_desc]
    have : res (subset_union_right : V ⊆ U ∪ V) = biprod.inr ≫ S.g := (biprod.inr_desc _ _).symm
    rw [this, Category.assoc, hgΦ, biprod.inr_desc, IsIso.hom_inv_id_assoc]
  · rw [reassoc_of% hgΦ, Category.comp_id, biprod.inl_desc_assoc, Category.assoc, hψ,
      IsIso.inv_hom_id_assoc]
    exact (biprod.inl_desc _ _).symm
  · rw [reassoc_of% hgΦ, Category.comp_id, biprod.inr_desc_assoc, Category.assoc, hψ,
      IsIso.inv_hom_id_assoc]
    exact (biprod.inr_desc _ _).symm

/-- **Finite unions**: let `P` be a property of subsets of `B`, inherited by subsets, such that `ψ`
is an isomorphism over every set with `P`, and over the empty set. If over any two open sets
`A(U) ⊞ A(V) ⟶ A(U ∪ V)` is an epimorphism and the restrictions form an exact Mayer–Vietoris
sequence, whose second map is an epimorphism when the first set has `P`, then `ψ` is an isomorphism
over every finite union of open sets with `P`. -/
theorem isIso_biUnion_of_mayerVietoris [TopologicalSpace B]
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'), A.map (homOfLE h) ≫ ψ W' = ψ W ≫ res h)
    (hA : ∀ U V : Set B, IsOpen U → IsOpen V →
      Epi (biprod.desc (A.map (homOfLE (subset_union_left : U ⊆ U ∪ V)))
        (A.map (homOfLE (subset_union_right : V ⊆ U ∪ V)))))
    (P : Set B → Prop) (hP : ∀ ⦃W W' : Set B⦄, W ⊆ W' → P W' → P W)
    (hψP : ∀ W, P W → IsIso (ψ W)) (hψ_empty : IsIso (ψ ∅))
    (hw : ∀ U V : Set B, biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
        (-res (inter_subset_right : U ∩ V ⊆ V)) ≫
      biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)) =
        0)
    (hS : ∀ U V : Set B, IsOpen U → IsOpen V → (ShortComplex.mk _ _ (hw U V)).Exact)
    (hg : ∀ U V : Set B, IsOpen U → IsOpen V → P U →
      Epi (biprod.desc (res (subset_union_left : U ⊆ U ∪ V))
        (res (subset_union_right : V ⊆ U ∪ V))))
    {κ : Type*} (s : Finset κ) {W : κ → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWP : ∀ i ∈ s, P (W i)) :
    IsIso (ψ (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset κ), W i) = ∅ by simp]
    exact hψ_empty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hUo := hWo a (Finset.mem_insert_self a s)
    have hUP := hWP a (Finset.mem_insert_self a s)
    have hVo : IsOpen (⋃ i ∈ s, W i) :=
      isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi)
    have : IsIso (ψ (W a)) := hψP _ hUP
    have : IsIso (ψ (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWP i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the open sets `W a ∩ W i`, `i ∈ s`, which have `P`.
    have : IsIso (ψ (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      exact ih (fun i hi ↦ hUo.inter (hWo i (Finset.mem_insert_of_mem hi)))
        fun i hi ↦ hP inter_subset_right (hWP i (Finset.mem_insert_of_mem hi))
    exact isIso_union_of_mayerVietoris res ψ hψ (hA _ _ hUo hVo) (hw _ _) (hS _ _ hUo hVo)
      (hg _ _ hUo hVo hUP)

end TauCeti
