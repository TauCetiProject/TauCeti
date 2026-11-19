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
  choose g hg using hmem
  have hgc : Continuous g := hj.continuous_iff.mpr (by
    convert (simplexMap τ).continuous using 1
    exact funext hg)
  obtain ⟨τ', hτ'⟩ := simplexMap_surjective ⟨g, hgc⟩
  have hττ' : (TopCat.toSSet.map j).app _ τ' = τ :=
    simplexMap_injective (by ext z; simp [hτ', hg])
  rw [← hττ', ← SSet.ι_chainComplexMap_f_assoc, ← HomologicalComplex.comp_f, hφ,
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
      (fun e ⟨y, hy⟩ ↦ ⟨⟨e, by rw [Set.mem_preimage, ← hy]; exact y.2⟩, rfl⟩)
      (TopPair.chainComplexMap_comp_singularChainComplexπ _ R)).trans zero_comp.symm)

/-- The relative transfer is induced by the transfer: on the image of an absolute chain of `B`,
it is the image of the transfer of that chain. -/
@[reassoc (attr := simp)]
theorem singularChainComplexπ_comp_singularPairTransfer :
    (TopPair.ofSubset A).singularChainComplexπ R ≫ hp.singularPairTransfer hfin A R =
      hp.singularTransfer hfin R ≫ (TopPair.ofSubset (p ⁻¹' A)).singularChainComplexπ R :=
  Cofork.IsColimit.π_desc' (TopPair.isColimitCokernelCoforkSingularChainComplex _ R) _ _

/-- **The relative transfer is invariant under deck transformations**: `f_* ∘ transfer = transfer`
on relative singular chains for every bijective self-map `f` of `E` over `B`. -/
theorem singularPairTransfer_comp_singularChainComplexMap_of_comp_eq {f : E ⟶ E}
    (hf : Function.Bijective f) (hfp : f ≫ p = p) (hfA : Set.MapsTo f (p ⁻¹' A) (p ⁻¹' A)) :
    hp.singularPairTransfer hfin A R ≫
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hfA) R =
      hp.singularPairTransfer hfin A R := by
  -- Compare after the quotient map from absolute chains. The ambient chains of a pair appear in
  -- two forms that only agree up to unfolding `TopPair.toSSetPair`, so `rw [Category.assoc]`
  -- fails and the composites are reassociated by explicit terms.
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R)).1 ?_
  refine ((Category.assoc _ _ _).symm.trans
    (eq_whisker (singularChainComplexπ_comp_singularPairTransfer hp hfin A R) _)).trans ?_
  refine ((Category.assoc _ _ _).trans ((whisker_eq _
    (TopPair.singularChainComplexπ_ofSubsetMap_naturality f hfA R).symm).trans
      (Category.assoc _ _ _).symm)).trans ?_
  exact (eq_whisker (singularTransfer_comp_chainComplexMap_of_comp_eq hp hfin R hf hfp) _).trans
    (singularChainComplexπ_comp_singularPairTransfer hp hfin A R).symm

/-- **The relative transfer formula** `p_* ∘ transfer = d • id` on relative singular chains, for a
covering map whose fibres all have `d` points. -/
theorem singularPairTransfer_comp_singularChainComplexMap {d : ℕ}
    (hd : ∀ b, Nat.card (p ⁻¹' {b}) = d) :
    hp.singularPairTransfer hfin A R ≫
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap p (Set.mapsTo_preimage p A)) R =
      d • 𝟙 _ := by
  -- As in `singularPairTransfer_comp_singularChainComplexMap_of_comp_eq`, the composites are
  -- reassociated by explicit terms.
  refine (cancel_epi ((TopPair.ofSubset A).singularChainComplexπ R)).1 ?_
  refine ((Category.assoc _ _ _).symm.trans
    (eq_whisker (singularChainComplexπ_comp_singularPairTransfer hp hfin A R) _)).trans ?_
  refine ((Category.assoc _ _ _).trans ((whisker_eq _
    (TopPair.singularChainComplexπ_ofSubsetMap_naturality p (Set.mapsTo_preimage p A) R).symm).trans
      (Category.assoc _ _ _).symm)).trans ?_
  exact (eq_whisker (singularTransfer_comp_chainComplexMap hp hfin R hd) _).trans
    ((Preadditive.nsmul_comp _ _ _).trans ((congrArg (d • ·)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
        (Preadditive.comp_nsmul _ _ _).symm))

variable [CategoryWithHomology C] (n : ℕ)

/-- **The relative transfer is invariant under deck transformations**: `f_* ∘ transfer = transfer`
on relative singular homology for every bijective self-map `f` of `E` over `B`. -/
theorem homologyMap_singularPairTransfer_comp_singularHomologyMap_of_comp_eq {f : E ⟶ E}
    (hf : Function.Bijective f) (hfp : f ≫ p = p) (hfA : Set.MapsTo f (p ⁻¹' A) (p ⁻¹' A)) :
    HomologicalComplex.homologyMap (hp.singularPairTransfer hfin A R) n ≫
        (TopPair.ofSubset (p ⁻¹' A)).singularHomologyMap (TopPair.ofSubsetMap f hfA) R n =
      HomologicalComplex.homologyMap (hp.singularPairTransfer hfin A R) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <| congrArg
    (HomologicalComplex.homologyMap · n)
    (hp.singularPairTransfer_comp_singularChainComplexMap_of_comp_eq hfin A R hf hfp hfA)

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

include hG in
/-- For the quotient covering map `p : E ⟶ B` of an action of `G`, the preimage `p⁻¹ A` of a subset
of the base is invariant under the action. -/
theorem mapsTo_smul_preimage (g : G) : Set.MapsTo (g • ·) (p ⁻¹' A) (p ⁻¹' A) :=
  fun e he ↦ by rwa [Set.mem_preimage, hG.map_smul]

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C) [Fintype G]

/-- **The deck-transformation formula** `transfer ∘ p_* = ∑_{g ∈ G} g_*` on relative singular
chains, for the quotient covering map `p` of an action of a finite group `G` and a subset `A` of
the base. -/
theorem singularChainComplexMap_comp_singularPairTransfer :
    TopPair.singularChainComplexMap (TopPair.ofSubsetMap p (Set.mapsTo_preimage p A)) R ≫
        hG.isCoveringMap.singularPairTransfer hG.finite_fiber A R =
      ∑ g : G, TopPair.singularChainComplexMap (TopPair.ofSubsetMap
        (TopCat.ofHom ⟨(g • ·), hG.continuous_const_smul g⟩) (hG.mapsTo_smul_preimage A g)) R := by
  -- Compare after the quotient map from absolute chains, reassociating by explicit terms as in
  -- `IsCoveringMap.singularPairTransfer_comp_singularChainComplexMap_of_comp_eq`.
  refine (cancel_epi ((TopPair.ofSubset (p ⁻¹' A)).singularChainComplexπ R)).1 ?_
  refine ((Category.assoc _ _ _).symm.trans (eq_whisker
    (TopPair.singularChainComplexπ_ofSubsetMap_naturality p (Set.mapsTo_preimage p A) R).symm
      _)).trans ?_
  refine ((Category.assoc _ _ _).trans (whisker_eq _
    (IsCoveringMap.singularChainComplexπ_comp_singularPairTransfer _ _ A R))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans
    (eq_whisker (hG.chainComplexMap_comp_singularTransfer R) _)).trans ?_
  exact (Preadditive.sum_comp _ _ _).trans ((Finset.sum_congr rfl fun g _ ↦
    TopPair.singularChainComplexπ_ofSubsetMap_naturality _ _ R).trans
      (Preadditive.comp_sum _ _ _).symm)

end IsQuotientCoveringMap
