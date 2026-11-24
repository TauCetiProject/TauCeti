/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Opens
public import TauCeti.AlgebraicTopology.Cohomology.Cap.MayerVietoris.Local
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Compl
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Basic

/-! # Poincaré duality and the signed Mayer–Vietoris connecting square

`HomologicalOrientation.dualityMap_mayerVietorisδ` intertwines the compact-support cohomology
and singular-homology connecting maps with sign `(-1)^(p+1)` when `p+(q+1)=dim M`.
The equality takes place in the homology of the original intersection, for integral module
coefficients, including torsion and zero coefficients.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial Topology TopologicalSpace

namespace TauCeti
namespace CapMayerVietoris

open _root_.TopCat TopPair

local notation "ℤₘ" => ModuleCat.of ℤ (ULift ℤ : Type)

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {X : TopCat.{0}} (L : ModuleCat.{0} ℤ)

private def supportCover (U V : Opens X) (K N : Set X) : Fin 3 → Set X :=
  ![(U : Set X) ∩ V, (U : Set X) \ N, (V : Set X) \ K]

private lemma supportCover_isOpen (U V : Opens X) {K N : Set X}
    (hK : IsClosed K) (hN : IsClosed N) (i : Fin 3) :
    IsOpen (supportCover U V K N i) := by
  fin_cases i
  · exact U.isOpen.inter V.isOpen
  · exact IsOpen.sdiff U.isOpen hN
  · exact IsOpen.sdiff V.isOpen hK

private lemma supportCover_iUnion (U V : Opens X) {K N : Set X}
    (hKN : K ⊆ U) (hNV : N ⊆ V) (hUV : U ⊔ V = ⊤) :
    ⋃ i, supportCover U V K N i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hu : x ∈ U
  · by_cases hv : x ∈ V
    · exact Set.mem_iUnion.mpr ⟨0, hu, hv⟩
    · exact Set.mem_iUnion.mpr ⟨1, hu, fun hn ↦ hv (hNV hn)⟩
  · have hv : x ∈ V := by
      have hx : x ∈ U ⊔ V := hUV ▸ Set.mem_univ x
      exact hx.resolve_left hu
    exact Set.mem_iUnion.mpr ⟨2, hv, fun hk ↦ hu (hKN hk)⟩

private lemma supportCover_subordinate (U V : Opens X) (K N : Set X) (m : ℕ)
    (σ : (X.smallSingularSubcomplex (supportCover U V K N) : SSet) _⦋m⦌) :
    (Set.range (X.toSSetObjEquiv _ σ.val) ⊆ U ∨
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ Kᶜ) ∧
    (Set.range (X.toSSetObjEquiv _ σ.val) ⊆ V ∨
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ Nᶜ) ∧
    (Set.range (X.toSSetObjEquiv _ σ.val) ⊆ (U ⊓ V : Opens X) ∨
      Set.range (X.toSSetObjEquiv _ σ.val) ⊆ (K ∩ N)ᶜ) := by
  obtain ⟨i, hi⟩ :=
    (TopCat.mem_smallSingularSubcomplex_iff X (supportCover U V K N) σ.val).1 σ.property
  fin_cases i
  · exact ⟨Or.inl (hi.trans Set.inter_subset_left), Or.inl (hi.trans Set.inter_subset_right),
      Or.inl hi⟩
  · exact ⟨Or.inl (hi.trans Set.sdiff_subset), Or.inr (hi.trans (Set.sdiff_subset_compl _ _)),
      Or.inr fun x hx hkn ↦ (hi hx).2 hkn.2⟩
  · exact ⟨Or.inr (hi.trans (Set.sdiff_subset_compl _ _)), Or.inl (hi.trans Set.sdiff_subset),
      Or.inr fun x hx hkn ↦ (hi hx).2 hkn.1⟩

section Manifold

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {d : ℕ} (o : HomologicalOrientation M E d) (hn : Module.finrank ℝ E = d)

local notation "Mₜ" => TopCat.of M

private def openFundamentalClass (W : Opens Mₜ)
    (K : Compacts Mₜ) (hKW : (K : Set Mₜ) ⊆ W) :
    ((openSubspacePair W (K : Set Mₜ)ᶜ).singularChainComplex
      ℤₘ).homology d :=
  -- By `openSubspacePair_compl` (rfl), this is `localHomology` along
  -- `Opens.inclusion' W ⁻¹' K`. Native category/compact-carrier ascriptions
  -- avoid the stock 200000-heartbeat timeout in this carrier identification.
  (show localHomology (A := ModuleCat.{0} ℤ) ℤₘ (Opens.inclusion' W ⁻¹' (K : Set Mₜ)) d from
    (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding).fundamentalClassOn hn
      (show IsCompact (Opens.inclusion' W ⁻¹' (K : Set Mₜ)) from
        W.isOpenEmbedding.isInducing.isCompact_preimage' K.isCompact
        (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)))

private lemma fundamentalClassOn_open_preimage (W : Opens Mₜ)
    (K : Compacts Mₜ) (hKW : (K : Set Mₜ) ⊆ W) :
    TopPair.singularHomologyMap
      (openSubspaceInclusion W (K : Set Mₜ)ᶜ) ℤₘ d
      (openFundamentalClass o hn W K hKW) = o.fundamentalClassOn hn K.isCompact := by
  have hy := HomologicalOrientation.eq_localHomologyMap_fundamentalClassOn
    (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding) hn W.isOpenEmbedding
      (W.isOpenEmbedding.isInducing.isCompact_preimage' K.isCompact
        (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)) rfl K.isCompact.isClosed
      (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)
      (γ := o.fundamentalClassOn hn K.isCompact) (by
        intro x hx
        rw [o.localHomologyRestriction_fundamentalClassOn hn K.isCompact hx,
          ← IsOpenEmbedding.coe_localOrientationEquiv,
          HomologicalOrientation.localOrientationEquiv_comap_apply])
  erw [localHomologyMap_def] at hy
  convert hy.symm using 1
  -- Both native pair maps have the open inclusion as their ambient component.
  congr 2

private lemma localized_cap_fundamentalClass (W : Opens Mₜ) (K : Compacts Mₜ)
    (hKW : (K : Set Mₜ) ⊆ W) {ι : Type}
    (F : ι → Set Mₜ) (hF : ∀ i, IsOpen (F i)) (hcov : ⋃ i, F i = Set.univ)
    (hSW : ∀ m (σ : ((Mₜ).smallSingularSubcomplex F : SSet) _⦋m⦌),
      Set.range ((Mₜ).toSSetObjEquiv _ σ.val) ⊆ W ∨
        Set.range ((Mₜ).toSSetObjEquiv _ σ.val) ⊆ (K : Set Mₜ)ᶜ)
    (p q : ℕ) (h : p + q = d)
    (ζ : ((TopPair.ofSubset (K : Set Mₜ)ᶜ).singularCochainComplex ℤₘ ℤ L).cycles p)
    (z : (((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrict
      ((Mₜ).smallSingularSubcomplex F)).chainComplex ℤₘ).homology d)
    (hz : SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrictι
          ((Mₜ).smallSingularSubcomplex F)) ℤₘ d z =
      o.fundamentalClassOn hn K.isCompact) :
    capIntoHomology L ((Mₜ).smallSingularSubcomplex F) W
        ⟨(K : Set Mₜ)ᶜ, K.isCompact.isClosed.isOpen_compl⟩ hSW p q d h ζ z =
      (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding).capFundamentalClassOn
        hn L (W.isOpenEmbedding.isInducing.isCompact_preimage' K.isCompact
        (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)) p q h (TopPair.singularCohomologyMap
          (openSubspaceInclusion W (K : Set Mₜ)ᶜ) p
          (((TopPair.ofSubset (K : Set Mₜ)ᶜ).singularCochainComplex ℤₘ ℤ L).homologyπ
            p ζ)) := by
  let D : Opens Mₜ := ⟨(K : Set Mₜ)ᶜ, K.isCompact.isClosed.isOpen_compl⟩
  let S := (Mₜ).smallSingularSubcomplex F
  let P := openSubspacePair W D
  let f := openSubspaceInclusion W D
  let T := P.smallSingularSubcomplex (fun i ↦ TopPair.Hom.fst f ⁻¹' F i)
  have hT : T ≤ S.preimage (TopPair.toSSetPair.map f).right := by
    have ht := TopPair.smallSingularSubcomplex_le_preimage f F
    erw [TopPair.smallSingularSubcomplex_eq (TopPair.ofSubset (D : Set Mₜ)) F] at ht
    exact ht
  have : IsIso (SSetPair.homologyMap
      ((TopPair.toSSetPair.obj (TopPair.ofSubset (D : Set Mₜ))).restrictι S) ℤₘ d) :=
    TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex_ofSubset
      ℤₘ (D : Set Mₜ) F hF hcov d
  have : IsIso (SSetPair.homologyMap ((TopPair.toSSetPair.obj P).restrictι T) ℤₘ d) :=
    TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex
      ℤₘ P (fun i ↦ TopPair.Hom.fst f ⁻¹' F i)
      (fun i ↦ (hF i).preimage (TopPair.Hom.fst f).hom.continuous)
      (by erw [← Set.preimage_iUnion, hcov, Set.preimage_univ]) d
  have hy := fundamentalClassOn_open_preimage o hn W K hKW
  have hc := capIntoHomology_apply_eq_singularCap L S W D T hT hSW p q d h ζ z
    (openFundamentalClass o hn W K hKW) (hz.trans hy.symm)
  erw [HomologicalOrientation.capFundamentalClassOn_apply]
  erw [HomologicalComplex.moduleCat_homologyMap_homologyπ]
  -- The cap-fundamental-class map uses the homology of this literal relative pair.
  convert hc using 1
  rfl

omit [T2Space M] in
private lemma support_excision_preimage (W : Opens Mₜ)
    (K : Compacts Mₜ) (hKW : (K : Set Mₜ) ⊆ W) (p : ℕ) :
    TopCat.singularCohomologyComplRestrict ℤₘ ℤ L (W.isOpenEmbedding.subset_map_preimageCompacts
      K.isCompact
      (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)) p ≫
      TopCat.singularCohomologyComplCompactsMap W.isOpenEmbedding.injective
        (W.isOpenEmbedding.preimageCompacts K.isCompact (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)) p =
      TopPair.singularCohomologyMap
        (R := ℤₘ) (k := ℤ) (M := L)
        (openSubspaceInclusion W (K : Set Mₜ)ᶜ) p := by
  -- Complement restriction and excision are defined by these native maps of pairs.
  change TopPair.singularCohomologyMap _ p ≫ TopPair.singularCohomologyMap _ p = _
  erw [← TopPair.singularCohomologyMap_comp]
  apply congrArg (fun f ↦ TopPair.singularCohomologyMap
    (R := ℤₘ) (k := ℤ) (M := L) f p)
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.comp_id _)

private lemma exists_small_fundamentalCycle (K : Compacts Mₜ) {ι : Type}
    (F : ι → Set Mₜ) (hF : ∀ i, IsOpen (F i)) (hcov : ⋃ i, F i = Set.univ) :
    ∃ z : (((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrict
        ((Mₜ).smallSingularSubcomplex F)).chainComplex ℤₘ).cycles d,
      SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrictι
          ((Mₜ).smallSingularSubcomplex F)) ℤₘ d
        (((((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrict
          ((Mₜ).smallSingularSubcomplex F)).chainComplex ℤₘ).homologyπ d) z) =
        o.fundamentalClassOn hn K.isCompact := by
  let P := TopPair.ofSubset (K : Set Mₜ)ᶜ
  let S := (Mₜ).smallSingularSubcomplex F
  let Q := (TopPair.toSSetPair.obj P).restrict S
  let j := SSetPair.homologyMap ((TopPair.toSSetPair.obj P).restrictι S) ℤₘ d
  have : IsIso j := TopPair.isIso_homologyMap_restrictι_smallSingularSubcomplex_ofSubset
    ℤₘ (K : Set Mₜ)ᶜ F hF hcov d
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso j).surjective
    (o.fundamentalClassOn hn K.isCompact)
  obtain ⟨z, hz⟩ :=
    (Q.chainComplex ℤₘ).moduleCat_homologyπ_surjective d y
  exact ⟨z, (congrArg j hz).trans hy⟩

private lemma restriction_small_fundamentalClass (S : (TopCat.toSSet.obj Mₜ).Subcomplex)
    (K K' : Compacts Mₜ) (hKK' : K ≤ K')
    (z : (((TopPair.toSSetPair.obj
        (TopPair.ofSubset (K' : Set Mₜ)ᶜ)).restrict S).chainComplex ℤₘ).homology d)
    (hz : SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (K' : Set Mₜ)ᶜ)).restrictι S)
        ℤₘ d z = o.fundamentalClassOn hn K'.isCompact) :
    SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrictι S) ℤₘ d
      (HomologicalComplex.homologyMap
        (SSetPair.chainComplexMap (restrictSubsetMap S (Set.compl_subset_compl.mpr hKK'))
          ℤₘ) d z) = o.fundamentalClassOn hn K.isCompact := by
  have hc := congrArg (fun f ↦ HomologicalComplex.homologyMap f d)
    (chainComplexMap_restrictSubsetMap_comp_restrictι (R := ℤₘ) S
      (Set.compl_subset_compl.mpr hKK'))
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have hv := ConcreteCategory.congr_hom hc z
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hz] at hv
  have hr := o.localHomologyRestriction_fundamentalClassOn_of_subset hn
    K'.isCompact K.isCompact hKK'
  erw [localHomologyRestriction_def] at hr
  exact hv.trans hr

private lemma cap_fundamentalCycle (S : (TopCat.toSSet.obj Mₜ).Subcomplex)
    (K : Compacts Mₜ) (p q : ℕ) (h : p + q = d)
    (α : ((TopPair.ofSubset (K : Set Mₜ)ᶜ).singularCochainComplex ℤₘ ℤ L).cycles p)
    (z : (((TopPair.toSSetPair.obj
        (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrict S).chainComplex ℤₘ).cycles d)
    (hz : SSetPair.homologyMap
        ((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrictι S) ℤₘ d
        (((((TopPair.toSSetPair.obj
        (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrict S).chainComplex ℤₘ).homologyπ d) z) =
      o.fundamentalClassOn hn K.isCompact) :
    (((TopCat.toSSet.obj Mₜ).chainComplex L).homologyπ q).hom
      ((ChainComplex.capCycles ℤ
          ((TopPair.ofSubset (K : Set Mₜ)ᶜ).alexanderWhitneyDiagonal (ρ_ ℤₘ).inv)
          ((TopCat.toSSet.obj Mₜ).chainComplexPairing (ρ_ L).hom) p q d h α).hom
        (HomologicalComplex.cyclesMap
          (SSetPair.chainComplexMap
            ((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrictι S) ℤₘ) d z)) =
      o.capFundamentalClassOn hn L K.isCompact p q h
        (((TopPair.ofSubset (K : Set Mₜ)ᶜ).singularCochainComplex ℤₘ ℤ L).homologyπ p α) := by
  have hc := ConcreteCategory.congr_hom
    (TopPair.singularCap_homologyπ (TopPair.ofSubset (K : Set Mₜ)ᶜ) ℤ
      (ρ_ ℤₘ).inv (ρ_ L).hom p q d h α)
    (HomologicalComplex.cyclesMap (SSetPair.chainComplexMap
      ((TopPair.toSSetPair.obj (TopPair.ofSubset (K : Set Mₜ)ᶜ)).restrictι S) ℤₘ) d z)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← HomologicalComplex.moduleCat_homologyMap_homologyπ, hz] at hc
  rw [HomologicalOrientation.capFundamentalClassOn_apply]
  exact hc.symm

private lemma duality_excision_preimage (W : Opens Mₜ)
    (K : Compacts Mₜ) (hKW : (K : Set Mₜ) ⊆ W)
    (p q : ℕ) (h : p + q = d)
    (a : (TopPair.ofSubset (K : Set Mₜ)ᶜ).singularCohomology ℤₘ ℤ L p) :
    let NW := W.isOpenEmbedding.preimageCompacts K.isCompact (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)
    let hKI := W.isOpenEmbedding.subset_map_preimageCompacts K.isCompact
      (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)
    (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding).dualityMap hn L p q h
        (TopCat.compactSupportCohomologyι p NW
          (TopCat.singularCohomologyComplCompactsMap W.isOpenEmbedding.injective NW p
            (TopCat.singularCohomologyComplRestrict ℤₘ ℤ L hKI p a))) =
      (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding).capFundamentalClassOn
        hn L (W.isOpenEmbedding.isInducing.isCompact_preimage' K.isCompact
        (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)) p q h (TopPair.singularCohomologyMap
          (openSubspaceInclusion W (K : Set Mₜ)ᶜ)
          p a) := by
  intro NW hKI
  have hc := ConcreteCategory.congr_hom (support_excision_preimage L W K hKW p) a
  erw [ConcreteCategory.comp_apply] at hc
  have hd := HomologicalOrientation.dualityMap_compactSupportCohomologyι_apply
    (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding) hn L p q h NW
      (TopCat.singularCohomologyComplCompactsMap W.isOpenEmbedding.injective NW p
        (TopCat.singularCohomologyComplRestrict ℤₘ ℤ L hKI p a))
  erw [hc] at hd
  erw [hc]
  erw [HomologicalOrientation.capFundamentalClassOn_apply]
  -- The native complement-preimage pair and its inclusion are the open-subspace pair/map.
  convert hd using 1
  rfl

private lemma localized_duality_compact_union (U V : Opens Mₜ)
    (hUV : U ⊔ V = ⊤) (K N : Compacts Mₜ)
    (hKU : (K : Set Mₜ) ⊆ U) (hNV : (N : Set Mₜ) ⊆ V)
    {ι : Type} (F : ι → Set Mₜ) (hF : ∀ i, IsOpen (F i))
    (hcov : ⋃ i, F i = Set.univ)
    (hSW : ∀ m (σ : ((Mₜ).smallSingularSubcomplex F : SSet) _⦋m⦌),
      Set.range ((Mₜ).toSSetObjEquiv _ σ.val) ⊆ (U ⊓ V : Opens Mₜ) ∨
        Set.range ((Mₜ).toSSetObjEquiv _ σ.val) ⊆
          ((K ⊓ N : Compacts Mₜ) : Set Mₜ)ᶜ)
    (p q : ℕ) (h : p + (q + 1) = d)
    (a : (TopPair.ofSubset ((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ).singularCohomology ℤₘ ℤ L p)
    (ζ : ((TopPair.ofSubset ((K ⊓ N : Compacts Mₜ) : Set Mₜ)ᶜ).singularCochainComplex
       ℤₘ ℤ L).cycles (p + 1))
    (hζ : ((TopPair.ofSubset ((K ⊓ N : Compacts Mₜ) : Set Mₜ)ᶜ).singularCochainComplex
         ℤₘ ℤ L).homologyπ (p + 1) ζ =
      TopCat.singularCohomologyComplMayerVietorisδ ℤₘ ℤ L
        K.isCompact.isClosed N.isCompact.isClosed p (p + 1) rfl a)
    (z : (((TopPair.toSSetPair.obj (TopPair.ofSubset
      ((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ)).restrict
        ((Mₜ).smallSingularSubcomplex F)).chainComplex ℤₘ).cycles d)
    (hz : SSetPair.homologyMap
      ((TopPair.toSSetPair.obj (TopPair.ofSubset
        ((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ)).restrictι
          ((Mₜ).smallSingularSubcomplex F)) ℤₘ d
        ((((TopPair.toSSetPair.obj (TopPair.ofSubset
          ((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ)).restrict
            ((Mₜ).smallSingularSubcomplex F)).chainComplex ℤₘ).homologyπ d z) =
      o.fundamentalClassOn hn (K ⊔ N).isCompact) :
    let W := U ⊓ V
    let D : Opens Mₜ :=
      ⟨((K ⊓ N : Compacts Mₜ) : Set Mₜ)ᶜ,
        (K ⊓ N).isCompact.isClosed.isOpen_compl⟩
    (HomologicalComplex.cyclesMap (SSetPair.chainComplexMap
        (restrictSubsetMap ((Mₜ).smallSingularSubcomplex F)
          (Set.compl_subset_compl.mpr inf_le_sup)) ℤₘ) d ≫
      capIntoCycles L ((Mₜ).smallSingularSubcomplex F) W D hSW
        (p + 1) q d (by omega) ζ ≫
      ((TopCat.toSSet.obj ((Opens.toTopCat Mₜ).obj W)).chainComplex L).homologyπ q).hom
        z =
      (o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding).dualityMap hn L
        (p + 1) q (by omega)
        (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p (p + 1) rfl
          (TopCat.compactSupportCohomologyι p (K ⊔ N) a)) := by
  let W := U ⊓ V
  let C : Opens Mₜ :=
    ⟨((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ,
      (K ⊔ N).isCompact.isClosed.isOpen_compl⟩
  let D : Opens Mₜ :=
    ⟨((K ⊓ N : Compacts Mₜ) : Set Mₜ)ᶜ,
      (K ⊓ N).isCompact.isClosed.isOpen_compl⟩
  let S := (Mₜ).smallSingularSubcomplex F
  let R := ((TopPair.toSSetPair.obj (TopPair.ofSubset (C : Set Mₜ))).restrict S).chainComplex ℤₘ
  have hCD : C ≤ D := Set.compl_subset_compl.mpr inf_le_sup
  let qD := SSetPair.chainComplexMap (restrictSubsetMap S hCD) ℤₘ
  have hμD : SSetPair.homologyMap
      ((TopPair.toSSetPair.obj (TopPair.ofSubset (D : Set Mₜ))).restrictι S) ℤₘ d
      (HomologicalComplex.homologyMap qD d (R.homologyπ d z)) =
      o.fundamentalClassOn hn (K ⊓ N).isCompact :=
    restriction_small_fundamentalClass o hn S (K ⊓ N) (K ⊔ N) inf_le_sup _ hz
  have hKW : ((K ⊓ N : Compacts Mₜ) : Set Mₜ) ⊆ W :=
    Set.inter_subset_inter hKU hNV
  have hright₀ := ConcreteCategory.congr_hom
    (homologyπ_capIntoHomology L S W D hSW (p + 1) q d (by omega) ζ)
    (HomologicalComplex.cyclesMap qD d z)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← HomologicalComplex.moduleCat_homologyMap_homologyπ] at hright₀
  have hright := hright₀.symm.trans (localized_cap_fundamentalClass L o hn W (K ⊓ N)
    hKW F hF hcov hSW (p + 1) q (by omega) ζ _ hμD)
  erw [hζ] at hright
  let NW : Compacts ((Opens.toTopCat Mₜ).obj W) :=
    W.isOpenEmbedding.preimageCompacts (K ⊓ N).isCompact (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)
  have hN := W.isOpenEmbedding.subset_map_preimageCompacts (K ⊓ N).isCompact
    (fun x hx ↦ ⟨⟨x, hKW hx⟩, rfl⟩)
  have hδc := ConcreteCategory.congr_hom
    (TopCat.compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV (K ⊔ N)
      K.isCompact N.isCompact hKU hNV (by exact Set.Subset.rfl) NW hN p (p + 1) rfl) a
  simp only [ConcreteCategory.comp_apply, TopCat.singularCohomologyComplRestrict,
    TopPair.ofSubsetMap_id, TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply] at hδc
  have hdex := duality_excision_preimage L o hn W (K ⊓ N) hKW (p + 1) q (by omega)
    (TopCat.singularCohomologyComplMayerVietorisδ ℤₘ ℤ L
      K.isCompact.isClosed N.isCompact.isClosed p (p + 1) rfl a)
  have hd := (congrArg
    ((o.comap (j := (Opens.inclusion' W).hom) W.isOpenEmbedding).dualityMap hn L
      (p + 1) q (by omega)) hδc).trans hdex
  have hr := hright.trans hd.symm
  -- Evaluation of the native composite is the evaluation used in the preceding cap identity.
  change (capIntoCycles L S W D hSW (p + 1) q d (by omega) ζ ≫
    ((TopCat.toSSet.obj ((Opens.toTopCat Mₜ).obj W)).chainComplex L).homologyπ q).hom
      (HomologicalComplex.cyclesMap qD d z) = _
  exact hr

private lemma signed_duality_on_compact_union (U V : Opens Mₜ)
    (hUV : U ⊔ V = ⊤) (K N : Compacts Mₜ)
    (hKU : (K : Set Mₜ) ⊆ U) (hNV : (N : Set Mₜ) ⊆ V)
    (p q : ℕ) (h : p + (q + 1) = d)
    (a : (TopPair.ofSubset
      ((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ).singularCohomology ℤₘ ℤ L p) :
    (TopCat.mayerVietorisδ L U.isOpen V.isOpen
        (congrArg (fun W : Opens Mₜ ↦ (W : Set Mₜ)) hUV)
        (q + 1) q rfl).hom
      (o.capFundamentalClassOn hn L (K ⊔ N).isCompact p (q + 1) h a) =
      ((-1 : ℤ) ^ (p + 1)) •
        ((o.comap (j := (Opens.inclusion' (U ⊓ V)).hom) (U ⊓ V).isOpenEmbedding).dualityMap
           hn L (p + 1) q (by omega)
          (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p (p + 1) rfl
            (TopCat.compactSupportCohomologyι p (K ⊔ N) a))) := by
  obtain rfl : d = p + q + 1 := by omega
  let A : Opens Mₜ := ⟨(K : Set Mₜ)ᶜ, K.isCompact.isClosed.isOpen_compl⟩
  let B : Opens Mₜ := ⟨(N : Set Mₜ)ᶜ, N.isCompact.isClosed.isOpen_compl⟩
  let C : Opens Mₜ :=
    ⟨((K ⊔ N : Compacts Mₜ) : Set Mₜ)ᶜ,
      (K ⊔ N).isCompact.isClosed.isOpen_compl⟩
  let D : Opens Mₜ :=
    ⟨((K ⊓ N : Compacts Mₜ) : Set Mₜ)ᶜ,
      (K ⊓ N).isCompact.isClosed.isOpen_compl⟩
  let F := supportCover U V (K : Set Mₜ) (N : Set Mₜ)
  let S := (Mₜ).smallSingularSubcomplex F
  have hCA : C ≤ A := Set.compl_subset_compl.mpr Set.subset_union_left
  have hCB : C ≤ B := Set.compl_subset_compl.mpr Set.subset_union_right
  have hAD : A ≤ D := Set.compl_subset_compl.mpr Set.inter_subset_left
  have hBD : B ≤ D := Set.compl_subset_compl.mpr Set.inter_subset_right
  have hS := supportCover_subordinate U V (K : Set Mₜ) (N : Set Mₜ)
  have hSU := fun m σ ↦ (hS m σ).1
  have hSV := fun m σ ↦ (hS m σ).2.1
  have hSW := fun m σ ↦ (hS m σ).2.2
  have hF := supportCover_isOpen U V K.isCompact.isClosed N.isCompact.isClosed
  have hcov := supportCover_iUnion U V hKU hNV hUV
  obtain ⟨ζ, hζ⟩ := ((TopPair.ofSubset (D : Set Mₜ)).singularCochainComplex
    ℤₘ ℤ L).moduleCat_homologyπ_surjective (p + 1)
      (TopCat.singularCohomologyComplMayerVietorisδ ℤₘ ℤ L
        K.isCompact.isClosed N.isCompact.isClosed p (p + 1) rfl a)
  obtain ⟨φ, ψ, α, hφ, hψ, hα, ha⟩ :=
    TopCat.exists_singularCohomologyComplMayerVietorisδ_representatives ℤₘ ℤ L
    K.isCompact.isClosed N.isCompact.isClosed p a ζ hζ
  erw [ChainComplex.linearYonedaObj_d_apply, TopPair.singularCochainComplexMap_f_apply] at hφ hψ
  simp only [TopPair.singularCochainComplexMap_f_apply] at hα
  obtain ⟨z, hz⟩ := exists_small_fundamentalCycle o hn (K ⊔ N) F hF hcov
  have hs := ConcreteCategory.congr_hom
    (capCycles_homologyπ_mayerVietorisδ L S U V A B C D hUV hCA hCB hAD hBD hSU hSV hSW
      p q (p + q) rfl φ ψ α ζ hφ hψ hα) z
  have hleft := cap_fundamentalCycle L o hn S (K ⊔ N) p (q + 1) h α z hz
  erw [ha] at hleft
  have hr := localized_duality_compact_union L o hn U V hUV K N hKU hNV
    F hF hcov hSW p q h a ζ hζ z hz
  let Q := (TopCat.toSSet.obj ((Opens.toTopCat Mₜ).obj (U ⊓ V))).homology L q
  let ev := LinearMap.evalAddMonoidHom (σ₁₂ := RingHom.id ℤ) (M₂ := Q) z
  erw [congrArg ev (ModuleCat.hom_zsmul _ _), map_zsmul ev _ _] at hs
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  erw [hleft, hr] at hs
  exact hs

/-- The native duality maps intertwine the two Mayer–Vietoris connecting maps with sign
`(-1)^(p+1)`, as an equality in the actual homology of the intersection. -/
lemma _root_.TauCeti.HomologicalOrientation.dualityMap_mayerVietorisδ
    (U V : Opens Mₜ) (hUV : U ⊔ V = ⊤)
    (p q : ℕ) (h : p + (q + 1) = d) :
    o.dualityMap hn L p (q + 1) h ≫
        TopCat.mayerVietorisδ L U.isOpen V.isOpen
          (congrArg (fun W : Opens Mₜ ↦ (W : Set Mₜ)) hUV)
          (q + 1) q rfl =
      ((-1 : ℤ) ^ (p + 1)) •
        (TopCat.compactSupportCohomologyMayerVietorisδ ℤₘ ℤ L U V hUV p (p + 1) rfl ≫
          (o.comap (j := (Opens.inclusion' (U ⊓ V)).hom) (U ⊓ V).isOpenEmbedding).dualityMap
             hn L (p + 1) q (by omega)) := by
  apply TopCat.compactSupportCohomology_hom_ext
  intro C
  have hcover : (C : Set Mₜ) ⊆ (U : Set Mₜ) ∪ V := by
    simpa only [← Opens.coe_sup, hUV, Opens.coe_top] using Set.subset_univ (C : Set Mₜ)
  obtain ⟨k, n, hk, hn', hku, hnv, heq⟩ :=
    C.isCompact.binary_compact_cover U.isOpen V.isOpen hcover
  let K : Compacts Mₜ := ⟨k, hk⟩
  let N : Compacts Mₜ := ⟨n, hn'⟩
  have hC : C = K ⊔ N := SetLike.coe_injective heq
  subst C
  conv_lhs =>
    erw [← Category.assoc, o.compactSupportCohomologyι_dualityMap hn L p (q + 1) h (K ⊔ N)]
  erw [Preadditive.comp_zsmul]
  ext a
  erw [ModuleCat.hom_zsmul]
  simp only [← LinearMap.evalAddMonoidHom_apply, map_zsmul]
  -- Concrete evaluation and the bundled composite have the same native ModuleCat map.
  erw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact signed_duality_on_compact_union L o hn U V hUV K N hku hnv p q h a

end Manifold

end CapMayerVietoris
end TauCeti
