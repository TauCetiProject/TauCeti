/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.Singular.Basic

/-!
# Maps out of `H₀` over finite unions of open sets

Let `B` be a topological space, `R` a ring, and `W ↦ M W` a family of `R`-modules indexed by the
subsets of `B`, with restriction maps `M W ⟶ M W'` for `W ⊆ W'`, whose Mayer–Vietoris sequences
`M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V)` are exact for open `U` and `V`. Let `ψ W : H₀(W; R) ⟶ M W` be
maps commuting with the restrictions. If `ψ W` is an isomorphism for every `W` in a family of
"good" sets closed under passing to subsets, `M ∅` vanishes, and the second map of the
Mayer–Vietoris sequence is onto whenever `U` is good, then `ψ` is an isomorphism over every finite
union of good open sets (`TauCeti.isIso_biUnion_of_mayerVietoris`).

This is the induction over finite unions of trivializing open sets in the computation of the
homology of the Thom pair of a vector bundle in the rank degree, both with constant coefficients
(`TauCeti.Topology.VectorBundle.Thom.RankDegreeHomology`) and with coefficients in the orientation
system (`TauCeti.Topology.VectorBundle.Thom.TwistedRankDegreeHomology`). There `M W` is the
homology of the Thom pair over `W` in the rank degree, the good sets are the subsets of the base
sets of trivializations, and the surjectivity in the Mayer–Vietoris sequence comes from the
vanishing of that homology below the rank.

## Main results

* `TauCeti.isIso_biUnion_of_mayerVietoris`: `ψ` is an isomorphism over a finite union of good open
  sets.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4.
-/

public section

open CategoryTheory Limits Set AlgebraicTopology

universe w

namespace TauCeti

variable {R : Type w} [Ring R] {B : Type w} [TopologicalSpace B] {M : Set B → ModuleCat.{w} R}
  (res : ∀ {W W' : Set B}, W ⊆ W' → (M W ⟶ M W'))
  (ψ : ∀ W : Set B, ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).obj
    (TopCat.of W) ⟶ M W)

/-- Over `W ⊆ W'`, with `ψ W'` an isomorphism, the restriction from `W` to `W'` read through `ψ W`
and `ψ W'` is the map induced by the inclusion. -/
@[reassoc]
private theorem comp_res_comp_inv
    (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫ ψ W' = ψ W ≫ res h)
    {W W' : Set B} (h : W ⊆ W') [IsIso (ψ W')] :
    ψ W ≫ res h ≫ inv (ψ W') =
      ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)).map
        (TopCat.ofHom (ContinuousMap.inclusion h)) := by
  rw [← Category.assoc, ← hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The Mayer–Vietoris step**: if `ψ U` and `ψ V` are isomorphisms, `ψ (U ∩ V)` is onto, and the
Mayer–Vietoris sequence `M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V) ⟶ 0` is exact, then `ψ (U ∪ V)` is an
isomorphism. -/
private theorem isIso_union_of_mayerVietoris
    (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫ ψ W' = ψ W ≫ res h)
    (hres : ∀ {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W''), res h ≫ res h' = res (h.trans h'))
    {U V : Set B}
    (hS : (ShortComplex.mk (biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
      (-res (inter_subset_right : U ∩ V ⊆ V)))
      (biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)))
      (by rw [biprod.lift_desc, Preadditive.neg_comp, hres, hres, add_neg_cancel])).Exact)
    [Epi (biprod.desc (res (subset_union_left : U ⊆ U ∪ V))
      (res (subset_union_right : V ⊆ U ∪ V)))]
    [IsIso (ψ U)] [IsIso (ψ V)] [Epi (ψ (U ∩ V))] :
    IsIso (ψ (U ∪ V)) := by
  let H₀ := (singularHomologyFunctor (ModuleCat.{w} R) 0).obj (ModuleCat.of R R)
  -- The inverse map, on the middle term of the Mayer–Vietoris sequence.
  let φ : M U ⊞ M V ⟶ H₀.obj (TopCat.of ↥(U ∪ V)) :=
    biprod.desc (inv (ψ U) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_left)))
      (inv (ψ V) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion subset_union_right)))
  -- It vanishes on the image of the first map, since both restrictions of a class over `U ∩ V`
  -- give the same class over `U ∪ V`.
  have hφ : biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
      (-res (inter_subset_right : U ∩ V ⊆ V)) ≫ φ = 0 := by
    rw [← cancel_epi (ψ (U ∩ V)), comp_zero]
    simp only [φ, H₀, biprod.lift_desc, Preadditive.neg_comp, Preadditive.comp_add,
      Preadditive.comp_neg, comp_res_comp_inv_assoc res ψ hψ, ← Functor.map_comp,
      ← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion, add_neg_eq_zero]
  let Φ := hS.gIsCokernel.desc (CokernelCofork.ofπ φ hφ)
  have hgΦ : biprod.desc (res (subset_union_left : U ⊆ U ∪ V))
      (res (subset_union_right : V ⊆ U ∪ V)) ≫ Φ = φ :=
    hS.gIsCokernel.fac (CokernelCofork.ofπ φ hφ) WalkingParallelPair.one
  -- On the classes over `U` and over `V`, `Φ` is the inverse of `ψ U` or `ψ V` followed by the
  -- inclusion.
  have hΦ {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (ψ W)] (j : M W ⟶ M U ⊞ M V)
      (hj : j ≫ biprod.desc (res subset_union_left) (res subset_union_right) = res hW)
      (hjφ : j ≫ φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW))) :
      res hW ≫ Φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW)) := by
    rw [← hj, Category.assoc, hgΦ, hjφ]
  have hΦU := hΦ subset_union_left biprod.inl (biprod.inl_desc _ _) (biprod.inl_desc _ _)
  have hΦV := hΦ subset_union_right biprod.inr (biprod.inr_desc _ _) (biprod.inr_desc _ _)
  -- Such a restriction inverts `ψ (U ∪ V)` on the classes of points of `W`, and on `M W`.
  have hpt {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (ψ W)]
      (hΦW : res hW ≫ Φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW)))
      (x : W) :
      singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of ↥(U ∪ V))
          (TopCat.ofHom (ContinuousMap.inclusion hW) x) ≫ ψ (U ∪ V) ≫ Φ =
        singularHomology₀Section (ModuleCat.of R R) (X := TopCat.of ↥(U ∪ V))
          (TopCat.ofHom (ContinuousMap.inclusion hW) x) := by
    rw [← singularHomology₀Section_naturality, Category.assoc, reassoc_of% (hψ hW), hΦW,
      IsIso.hom_inv_id_assoc]
  have hres' {W : Set B} (hW : W ⊆ U ∪ V) [IsIso (ψ W)]
      (hΦW : res hW ≫ Φ = inv (ψ W) ≫ H₀.map (TopCat.ofHom (ContinuousMap.inclusion hW))) :
      res hW ≫ Φ ≫ ψ (U ∪ V) = res hW := by
    rw [reassoc_of% hΦW, hψ, IsIso.inv_hom_id_assoc]
  refine ⟨Φ, singularHomology₀_hom_ext _ fun x ↦ ?_,
    (cancel_epi (biprod.desc (res subset_union_left) (res subset_union_right))).1
      (biprod.hom_ext' _ _ ?_ ?_)⟩
  · -- A point of `U ∪ V` lies in `U` or in `V`, where the composite is computed.
    obtain ⟨x, hx | hx⟩ := x <;> rw [Category.comp_id]
    exacts [hpt _ hΦU ⟨x, hx⟩, hpt _ hΦV ⟨x, hx⟩]
  -- On `M U ⊞ M V`, which maps onto `M (U ∪ V)`, the composite is computed summand by summand.
  · simpa using hres' _ hΦU
  · simpa using hres' _ hΦV

/-- **Isomorphisms out of `H₀` over finite unions of open sets.** Let `M` be a family of modules
over the subsets of `B` with restriction maps `res`, and `ψ W : H₀(W; R) ⟶ M W` maps commuting with
the restrictions. Suppose that `ψ W` is an isomorphism for every set `W` satisfying a property `G`
inherited by subsets, that `M ∅` vanishes, that for open `U` and `V` the Mayer–Vietoris sequence
`M (U ∩ V) ⟶ M U ⊞ M V ⟶ M (U ∪ V)` is exact, and that its second map is onto when `U` satisfies
`G`. Then `ψ` is an isomorphism over every finite union of open sets satisfying `G`. -/
theorem isIso_biUnion_of_mayerVietoris
    (hψ : ∀ {W W' : Set B} (h : W ⊆ W'), ((singularHomologyFunctor (ModuleCat.{w} R) 0).obj
      (ModuleCat.of R R)).map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫ ψ W' = ψ W ≫ res h)
    (hres : ∀ {W W' W'' : Set B} (h : W ⊆ W') (h' : W' ⊆ W''), res h ≫ res h' = res (h.trans h'))
    (G : Set B → Prop) (hG : ∀ {W W' : Set B}, W ⊆ W' → G W' → G W)
    (hiso : ∀ W, G W → IsIso (ψ W)) (hempty : IsZero (M ∅))
    (hexact : ∀ {U V : Set B}, IsOpen U → IsOpen V →
      (ShortComplex.mk (biprod.lift (res (inter_subset_left : U ∩ V ⊆ U))
        (-res (inter_subset_right : U ∩ V ⊆ V)))
        (biprod.desc (res (subset_union_left : U ⊆ U ∪ V)) (res (subset_union_right : V ⊆ U ∪ V)))
        (by rw [biprod.lift_desc, Preadditive.neg_comp, hres, hres, add_neg_cancel])).Exact)
    (hepi : ∀ {U V : Set B}, IsOpen U → IsOpen V → G U →
      Epi (biprod.desc (res (subset_union_left : U ⊆ U ∪ V))
        (res (subset_union_right : V ⊆ U ∪ V))))
    {ι : Type*} (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWG : ∀ i ∈ s, G (W i)) :
    IsIso (ψ (⋃ i ∈ s, W i)) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact isIso_of_source_target_iso_zero _
      (isZero_singularHomology_of_isEmpty _ (TopCat.of (∅ : Set B)) _).isoZero hempty.isoZero
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have ha := Finset.mem_insert_self a s
    have : IsIso (ψ (W a)) := hiso _ (hWG a ha)
    have : IsIso (ψ (⋃ i ∈ s, W i)) :=
      ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWG i (Finset.mem_insert_of_mem hi))
    -- `W a ∩ ⋃ i ∈ s, W i` is the union of the open sets `W a ∩ W i`, `i ∈ s`, satisfying `G`.
    have : IsIso (ψ (W a ∩ ⋃ i ∈ s, W i)) := by
      rw [inter_iUnion₂]
      exact ih (fun i hi ↦ (hWo a ha).inter (hWo i (Finset.mem_insert_of_mem hi)))
        fun i hi ↦ hG inter_subset_right (hWG i (Finset.mem_insert_of_mem hi))
    have hU := hWo a ha
    have hV : IsOpen (⋃ i ∈ s, W i) :=
      isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi)
    have := hepi hU hV (hWG a ha)
    exact isIso_union_of_mayerVietoris res ψ hψ hres (hexact hU hV)

end TauCeti
