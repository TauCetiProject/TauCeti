/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Transfer.Degree

/-!
# The transfer of a finite covering on relative singular chains

Let `p : E ⟶ B` be a covering map whose fibres are finite, and let `A ⊆ B`. The transfer
`C(B; R) ⟶ C(E; R)` sends a singular simplex of `B` to the sum of its lifts
(`IsCoveringMap.singularTransfer`). The lifts of a simplex lying in `A` lie in `p⁻¹ A`, so the
transfer carries the chains of `A` into those of `p⁻¹ A` and descends to the **relative transfer**

`C(B, A; R) ⟶ C(E, p⁻¹ A; R)`

on relative singular chains (`IsCoveringMap.singularPairTransfer`), characterized by its
composite with the quotient map from absolute chains
(`IsCoveringMap.singularChainComplexπ_comp_singularPairTransfer`). The formulas of the absolute
transfer descend with it:

* a bijective self-map `f` of `E` over `B`, such as a deck transformation, permutes the lifts of
  each simplex, so `f_* ∘ transfer = transfer` on relative chains
  (`IsCoveringMap.singularPairTransfer_comp_singularChainComplexMap_of_comp_eq`);
* when every fibre has `d` points, `p_* ∘ transfer = d • id` on relative chains
  (`IsCoveringMap.singularPairTransfer_comp_singularChainComplexMap`);
* for the quotient covering of a free action of a finite group `G`,
  `transfer ∘ p_* = ∑_{g ∈ G} g_*` on relative chains
  (`IsQuotientCoveringMap.singularChainComplexMap_comp_singularPairTransfer`).

The first two also hold on relative singular homology. Together these are the relative form of the
identities from which the homology of the base of a finite quotient covering is the object of
invariants of the homology of the total space when `|G|` is invertible in the coefficients
(`IsQuotientCoveringMap.isLimitHomologyMapConePairTransferCone`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G, for the transfer of a finite covering and Proposition 3G.1.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti.TopCat

universe w v u

namespace IsCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B} (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))
  (A : Set B) {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)

/-- The transfer carries the singular chains of a space `X` mapping to `B` into those of a subspace
`Y` of `E` containing every point over the image of `X`: if a chain map `φ` out of the chains of
`E` vanishes on the chains of `Y`, then the transfer followed by `φ` vanishes on the chains of
`X`. -/
private theorem chainComplexMap_comp_singularTransfer_comp_eq_zero {X Y : TopCat.{w}} (i : X ⟶ B)
    {j : Y ⟶ E} (hj : Topology.IsInducing j) (hij : ∀ e, p e ∈ Set.range i → e ∈ Set.range j)
    {K : ChainComplex C ℕ} {φ : (TopCat.toSSet.obj E).chainComplex R ⟶ K}
    (hφ : SSet.chainComplexMap (TopCat.toSSet.map j) R ≫ φ = 0) :
    SSet.chainComplexMap (TopCat.toSSet.map i) R ≫ hp.singularTransfer hfin R ≫ φ = 0 := by
  ext n σ
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, comp_zero,
    SSet.ι_chainComplexMap_f_assoc, ιChainComplex_singularTransfer_f_assoc, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun τ hτ ↦ ?_
  -- A lift `τ` of a simplex of `X` takes values in the range of `j`, so it comes from `Y`.
  have hτ : (TopCat.toSSet.map p).app _ τ = (TopCat.toSSet.map i).app _ σ :=
    (Set.Finite.mem_toFinset _).mp hτ
  have hmem (z) : simplexMap τ z ∈ Set.range j := by
    refine hij _ ⟨simplexMap σ z, ?_⟩
    simpa using (congrArg (fun s ↦ simplexMap s z) hτ).symm
  obtain ⟨τ', rfl⟩ := (hj.mem_range_toSSet_map_app_iff _ τ).2 fun _ ⟨z, hz⟩ ↦ hz ▸ hmem ⟨z⟩
  rw [← SSet.ι_chainComplexMap_f_assoc, ← HomologicalComplex.comp_f, hφ,
    HomologicalComplex.zero_f, comp_zero]

/-- **The relative transfer** `C(B, A; R) ⟶ C(E, p⁻¹ A; R)` of a covering map `p : E ⟶ B` with
finite fibres and a subset `A ⊆ B`: the chain map on relative singular chains induced by the
transfer, which sends a singular simplex of `B` to the sum of its lifts to `E`. -/
def singularPairTransfer :
    (TopPair.ofSubset A).singularChainComplex R ⟶
      (TopPair.ofSubset (p ⁻¹' A)).singularChainComplex R :=
  Cofork.IsColimit.desc (TopPair.isColimitCokernelCoforkSingularChainComplex _ R)
    (hp.singularTransfer hfin R ≫ (TopPair.ofSubset (p ⁻¹' A)).singularChainComplexπ R)
    ((chainComplexMap_comp_singularTransfer_comp_eq_zero hp hfin R (TopPair.ofSubset A).map
      (TopPair.ofSubset (p ⁻¹' A)).isEmbedding_map.isInducing
      (fun e ⟨y, hy⟩ ↦ ⟨⟨e, by rw [Set.mem_preimage, ← hy]; exact y.property⟩, rfl⟩)
      (TopPair.chainComplexMap_comp_singularChainComplexπ _ R)).trans zero_comp.symm)

/-- The relative transfer is induced by the transfer: on the image of an absolute chain of `B`,
it is the image of the transfer of that chain. -/
@[simp]
theorem singularChainComplexπ_comp_singularPairTransfer :
    (TopPair.ofSubset A).singularChainComplexπ R ≫ hp.singularPairTransfer hfin A R =
      hp.singularTransfer hfin R ≫ (TopPair.ofSubset (p ⁻¹' A)).singularChainComplexπ R :=
  Cofork.IsColimit.π_desc' (TopPair.isColimitCokernelCoforkSingularChainComplex _ R) _ _

/-- `singularChainComplexπ_comp_singularPairTransfer` followed by a further map `h` out of the
relative chains of `p⁻¹ A`. -/
-- Stated by hand rather than by `reassoc`: the domain of `singularChainComplexπ` agrees with the
-- codomain of the transfer only up to unfolding `TopPair.toSSetPair`, so `reassoc` cannot
-- reassociate the right-hand side. Elaborating `singularChainComplexπ R ≫ h` on its own keeps its
-- source in the form that `TopPair.singularChainComplexπ_ofSubsetMap_naturality` rewrites.
@[simp]
theorem singularChainComplexπ_comp_singularPairTransfer_assoc {K : ChainComplex C ℕ}
    (h : (TopPair.ofSubset (p ⁻¹' A)).singularChainComplex R ⟶ K) :
    (TopPair.ofSubset A).singularChainComplexπ R ≫ hp.singularPairTransfer hfin A R ≫ h =
      hp.singularTransfer hfin R ≫ ((TopPair.ofSubset (p ⁻¹' A)).singularChainComplexπ R ≫ h :) :=
  (Category.assoc _ _ _).symm.trans
    ((eq_whisker (singularChainComplexπ_comp_singularPairTransfer hp hfin A R) h).trans
      (Category.assoc _ _ _))

/-- **The relative transfer is invariant under deck transformations**: `f_* ∘ transfer = transfer`
on relative singular chains for every bijective self-map `f` of `E` over `B`. -/
theorem singularPairTransfer_comp_singularChainComplexMap_of_comp_eq {f : E ⟶ E}
    (hf : Function.Bijective f) (hfp : f ≫ p = p) :
    hp.singularPairTransfer hfin A R ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hfp A)) R =
      hp.singularPairTransfer hfin A R := by
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R)).1 ?_
  rw [singularChainComplexπ_comp_singularPairTransfer_assoc,
    ← TopPair.singularChainComplexπ_ofSubsetMap_naturality,
    singularChainComplexπ_comp_singularPairTransfer]
  -- The two forms of the chains of `E` meet here, so the last step is closed by `exact`.
  exact (reassoc_of% singularTransfer_comp_chainComplexMap_of_comp_eq hp hfin R hf hfp) _

/-- **The relative transfer formula** `p_* ∘ transfer = d • id` on relative singular chains, for a
covering map whose fibres all have `d` points. -/
theorem singularPairTransfer_comp_singularChainComplexMap {d : ℕ}
    (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) :
    hp.singularPairTransfer hfin A R ≫
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap p (Set.mapsTo_preimage p A)) R =
      d • 𝟙 _ := by
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R)).1 ?_
  rw [singularChainComplexπ_comp_singularPairTransfer_assoc,
    ← TopPair.singularChainComplexπ_ofSubsetMap_naturality, Preadditive.comp_nsmul,
    Category.comp_id]
  -- As above, the two forms of the chains of `E` meet here.
  exact ((reassoc_of% singularTransfer_comp_chainComplexMap hp hfin R hd) _).trans
    ((Preadditive.nsmul_comp _ _ _).trans (congrArg (d • ·) (Category.id_comp _)))

variable [CategoryWithHomology C] (n : ℕ)

/-- **The relative transfer is invariant under deck transformations**: `f_* ∘ transfer = transfer`
on relative singular homology for every bijective self-map `f` of `E` over `B`. -/
theorem homologyMap_singularPairTransfer_comp_singularHomologyMap_of_comp_eq {f : E ⟶ E}
    (hf : Function.Bijective f) (hfp : f ≫ p = p) :
    HomologicalComplex.homologyMap (hp.singularPairTransfer hfin A R) n ≫
        (TopPair.ofSubset (p ⁻¹' A)).singularHomologyMap
          (TopPair.ofSubsetMap f (f.mapsTo_preimage_of_comp_eq hfp A)) R n =
      HomologicalComplex.homologyMap (hp.singularPairTransfer hfin A R) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <| congrArg
    (HomologicalComplex.homologyMap · n)
    (hp.singularPairTransfer_comp_singularChainComplexMap_of_comp_eq hfin A R hf hfp)

/-- **The relative transfer formula** `p_* ∘ transfer = d • id` on relative singular homology, for a
covering map whose fibres all have `d` points. -/
theorem homologyMap_singularPairTransfer_comp_singularHomologyMap {d : ℕ}
    (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) :
    HomologicalComplex.homologyMap (hp.singularPairTransfer hfin A R) n ≫
        (TopPair.ofSubset (p ⁻¹' A)).singularHomologyMap
          (TopPair.ofSubsetMap p (Set.mapsTo_preimage p A)) R n =
      d • 𝟙 _ := by
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [singularPairTransfer_comp_singularChainComplexMap hp hfin A R hd]
  exact (HomologicalComplex.homologyFunctor C _ n).map_nsmul.trans
    (congrArg (d • ·) ((HomologicalComplex.homologyFunctor C _ n).map_id _))

end IsCoveringMap

namespace IsQuotientCoveringMap

variable {E B : TopCat.{w}} {p : E ⟶ B} {G : Type*} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (A : Set B)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C) [Fintype G]

/-- **The deck-transformation formula** `transfer ∘ p_* = ∑_{g ∈ G} g_*` on relative singular
chains, for the quotient covering map `p` of an action of a finite group `G` and a subset `A` of
the base. -/
theorem singularChainComplexMap_comp_singularPairTransfer :
    TopPair.singularChainComplexMap (TopPair.ofSubsetMap p (Set.mapsTo_preimage p A)) R ≫
        hG.isCoveringMap.singularPairTransfer hG.finite_fiber A R =
      ∑ g : G, TopPair.singularChainComplexMap (TopPair.ofSubsetMap
        (TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩) (hG.mapsTo_smul_preimage A g)) R := by
  refine (cancel_epi ((TopPair.ofSubset (p ⁻¹' A)).singularChainComplexπ R)).1 ?_
  rw [← TopPair.singularChainComplexπ_ofSubsetMap_naturality_assoc,
    IsCoveringMap.singularChainComplexπ_comp_singularPairTransfer, Preadditive.comp_sum]
  -- As in `IsCoveringMap.singularPairTransfer_comp_singularChainComplexMap_of_comp_eq`, the two
  -- forms of the chains of `E` meet here, so the remaining steps are composed by terms.
  refine ((reassoc_of% hG.chainComplexMap_comp_singularTransfer R) _).trans
    ((Preadditive.sum_comp _ _ _).trans ?_)
  exact Finset.sum_congr rfl fun g _ ↦ TopPair.singularChainComplexπ_ofSubsetMap_naturality _ _ R

end IsQuotientCoveringMap
