/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Maps out of zeroth homology over finite unions

Let `M` assign to each subset `W` of a space `B` an object `M W` of an abelian category, with
restriction maps `M W ⟶ M W'` for `W ⊆ W'`, and let `ψ W : H₀(W; R) ⟶ M W` be maps commuting with
the restrictions and the maps induced by the inclusions. Suppose that for open sets `U` and `V` the
restrictions form an exact Mayer–Vietoris sequence

`M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V)`

whose second map is an epimorphism. If `ψ U` and `ψ V` are isomorphisms and `ψ (U ∩ V)` is an
epimorphism, then `ψ (U ∪ V)` is an isomorphism (`TauCeti.isIso_union_of_mayerVietoris`): its
inverse is glued on the middle term of the sequence from the inverses over `U` and over `V`. By
induction on their number, `ψ` is an isomorphism over every finite union of open sets from a family
closed under subsets on which it is an isomorphism and the sequence is exact on the right
(`TauCeti.isIso_biUnion_of_mayerVietoris`).

This is the gluing step in the computation of the homology of the Thom pair of a vector bundle in
the rank degree: there `M W` is that homology over `W`, the sequence is exact on the right over a
trivializing set since the homology vanishes below the rank, and `ψ` sends the class of a point to
the fibre class over it.

`TauCeti.isIso_thomPairOver_union_of_isIso` is the same step with the roles exchanged: there the
target is fixed to the homology of the Thom pair with constant coefficients and the source is any
functor. Here the source is fixed to `H₀` and the target is any family with an exact
Mayer–Vietoris sequence, such as the homology of the Thom pair with local coefficients.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the induction over finite unions
  of trivializing open sets).
-/

public section

noncomputable section

open CategoryTheory Limits Set AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C) {B : Type w}
  [TopologicalSpace B] {M : Set B → C} (res : ∀ ⦃W W' : Set B⦄, W ⊆ W' → (M W ⟶ M W'))
  (ψ : ∀ W : Set B, ((singularHomologyFunctor C 0).obj R).obj (TopCat.of W) ⟶ M W)

/-- Over `W ⊆ W'`, with `ψ W'` an isomorphism, the restriction from `W` to `W'` read through `ψ W`
and `ψ W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem comp_res_comp_inv
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'),
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        ψ W' = ψ W ≫ res h)
    {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W')] :
    ψ W ≫ res h ≫ inv (ψ W') =
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← reassoc_of% (hψ h), IsIso.hom_inv_id, Category.comp_id]

/-- A candidate inverse `Φ` of `ψ W'` which on the image of the restriction from `W` is the inverse
of `ψ W` followed by the inclusion inverts `ψ W'` on the classes of points of `W`. -/
private theorem singularHomology₀Section_comp_comp_of_res_comp_eq
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'),
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        ψ W' = ψ W ≫ res h)
    {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W)]
    {Φ : M W' ⟶ ((singularHomologyFunctor C 0).obj R).obj (TopCat.of W')}
    (hΦ : res h ≫ Φ = inv (ψ W) ≫
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)))
    (x : W) :
    singularHomology₀Section R (X := TopCat.of W') (TopCat.ofHom (ContinuousMap.inclusion h) x) ≫
        ψ W' ≫ Φ =
      singularHomology₀Section R (TopCat.ofHom (ContinuousMap.inclusion h) x) := by
  rw [← singularHomology₀Section_naturality, Category.assoc, reassoc_of% (hψ h), hΦ,
    IsIso.hom_inv_id_assoc]

/-- Such a `Φ` also inverts `ψ W'` on the image of the restriction from `W`. -/
private theorem res_comp_comp_of_res_comp_eq
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'),
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        ψ W' = ψ W ≫ res h)
    {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W)]
    {Φ : M W' ⟶ ((singularHomologyFunctor C 0).obj R).obj (TopCat.of W')}
    (hΦ : res h ≫ Φ = inv (ψ W) ≫
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h))) :
    res h ≫ Φ ≫ ψ W' = res h := by
  rw [reassoc_of% hΦ, hψ, IsIso.inv_hom_id_assoc]

/-- **The Mayer–Vietoris step**: if the restrictions form an exact sequence
`M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V)` whose second map is an epimorphism, `ψ U` and `ψ V` are
isomorphisms and `ψ (U ∩ V)` is an epimorphism, then `ψ (U ∪ V)` is an isomorphism. -/
theorem isIso_union_of_mayerVietoris
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'),
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        ψ W' = ψ W ≫ res h)
    {U V : Set B}
    (hw : biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
        (-res (inter_subset_right : U ∩ V ⊆ V)) ≫
      biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)) =
        0)
    (hS : (ShortComplex.mk _ _ hw).Exact)
    (hg : Epi (biprod.desc (res (subset_union_left : U ⊆ U ∪ V))
      (res (subset_union_right : V ⊆ U ∪ V))))
    [IsIso (ψ U)] [IsIso (ψ V)] [Epi (ψ (U ∩ V))] :
    IsIso (ψ (U ∪ V)) := by
  let H₀ := (singularHomologyFunctor C 0).obj R
  let S := ShortComplex.mk _ _ hw
  have : Epi S.g := hg
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : S.X₂ ⟶ H₀.obj (TopCat.of ↥(U ∪ V)) :=
    biprod.desc (inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)))
      (inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)))
  -- It vanishes on the image of the first map, since both restrictions of a class over `U ∩ V`
  -- give the same class over `U ∪ V`.
  have hφ : S.f ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [S, φ, H₀, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, comp_res_comp_inv_assoc R res ψ hψ,
      ← Functor.map_comp, ← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion,
      add_neg_eq_zero]
  let Φ := (hS.gIsCokernel).desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : S.g ≫ Φ = φ := (hS.gIsCokernel).fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the image of the restrictions from `U` and from `V`, `Φ` is the inverse of `ψ U` or `ψ V`
  -- followed by the inclusion.
  have hΦ {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (ψ W)] (j : M W ⟶ S.X₂) (hj : j ≫ S.g = res hW)
      (hjφ : j ≫ φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW))) :
      res hW ≫ Φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW)) := by
    rw [← hj, Category.assoc, hgΦ, hjφ]
  have hΦU := hΦ subset_union_left biprod.inl (biprod.inl_desc _ _) (biprod.inl_desc _ _)
  have hΦV := hΦ subset_union_right biprod.inr (biprod.inr_desc _ _) (biprod.inr_desc _ _)
  refine ⟨Φ, singularHomology₀_hom_ext _ fun x ↦ ?_, (cancel_epi S.g).1 (biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    rw [Category.comp_id]
    obtain ⟨x, hx | hx⟩ := x
    · exact singularHomology₀Section_comp_comp_of_res_comp_eq R res ψ hψ _ hΦU ⟨x, hx⟩
    · exact singularHomology₀Section_comp_comp_of_res_comp_eq R res ψ hψ _ hΦV ⟨x, hx⟩
  · simpa [S] using res_comp_comp_of_res_comp_eq R res ψ hψ _ hΦU
  · simpa [S] using res_comp_comp_of_res_comp_eq R res ψ hψ _ hΦV

/-- **Finite unions**: let `P` be a property of subsets of `B`, inherited by subsets, such that `ψ`
is an isomorphism over every set with `P`, and over the empty set. If the restrictions form an exact
Mayer–Vietoris sequence over any two open sets, whose second map is an epimorphism when the first
set has `P`, then `ψ` is an isomorphism over every finite union of open sets with `P`. -/
theorem isIso_biUnion_of_mayerVietoris
    (hψ : ∀ ⦃W W' : Set B⦄ (h : W ⊆ W'),
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        ψ W' = ψ W ≫ res h)
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
    exact isIso_union_of_mayerVietoris R res ψ hψ (hw _ _) (hS _ _ hUo hVo) (hg _ _ hUo hVo hUP)

end TauCeti
