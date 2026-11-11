/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# Mayer–Vietoris for the cup product with a pulled-back relative class

For a topological pair `P = (X, A)`, a map `g : X ⟶ Z` and a relative class `u ∈ Hⁿ(X, A; K)`,
`TopPair.pullbackCup` is the map `Hᵖ(Z; M) ⟶ Hᵐ(X, A; M)`, `a ↦ g^*a ⌣ u`, `p + n = m`. For the Thom
pair `(E, E₀)` of a vector bundle, `g` its projection and `u` a Thom class, it is the Thom map
(`TauCeti.thomMap`), which the Thom isomorphism asserts to be bijective.

This file proves the inductive step of the proof of that isomorphism by Mayer–Vietoris over
trivializing open sets (Milnor and Stasheff, proof of Theorem 10.4). Let `π : X ⟶ Y` be a map, let
`U` and `V` be open sets covering `Y`, and let `U'` and `V'` be open sets covering `X` with
`π(U') ⊆ U` and `π(V') ⊆ V` (for instance their preimages). Let `A ⊆ U'` and `B ⊆ V'` be open in
`A ∪ B`, and `u` a class of the pair `(U' ∪ V', A ∪ B)`. Restricting `u` and `π` gives such maps
over `U`, over `V` and over `U ∩ V`, with values in the cohomology of the pairs `(U', A)`,
`(V', B)` and `(U' ∩ V', A ∩ B)`. If these three maps are bijective in every degree, and
`Hⁿ⁻¹(U' ∩ V', A ∩ B; M) = 0`, then the map over `Y` is bijective in every degree
(`TopPair.bijective_pullbackCup_union`).

The proof compares the Mayer–Vietoris sequence of the cover `{U, V}` of `Y`
(`TopCat.singularCohomologyMayerVietorisδ`) with that of the pairs `(U', A)` and `(V', B)`
(`TopCat.singularCohomologyPairMayerVietorisδ`). The maps above commute with the restrictions by
naturality of the cup product, and with the connecting morphisms because the connecting morphism
of the pairs satisfies `δ (a ⌣ b|) = δ a ⌣ b`
(`TopCat.singularCohomologyPairMayerVietorisδ_singularCup`) and the absolute connecting morphism
is natural (`TopCat.singularCohomologyMayerVietorisδ_naturality`). In positive degrees the five
lemma (`LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`) concludes. In
degree `0` the sequence of `Y` starts with an injective map, and the vanishing of
`Hⁿ⁻¹(U' ∩ V', A ∩ B; M)` replaces the missing terms.

## Main results

* `TopPair.bijective_pullbackCup_union`: the Mayer–Vietoris step.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, proof of Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set TopCat

universe w

namespace TopPair

/-! ### The Mayer–Vietoris step -/

section MayerVietoris

variable {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

variable {X Y : TopCat.{w}} (π : X ⟶ Y) {U' V' : Set X} {A B : Set X} (hAU : A ⊆ U')
  (hBV : B ⊆ V') {U V : Set Y} (hπU : MapsTo π U' U) (hπV : MapsTo π V' V)

/-- The restriction `U' ⟶ U` of `π`. -/
private abbrev restrictLeft : (TopPair.ofInclusion hAU).fst ⟶ TopCat.of U :=
  TopCat.ofHom ⟨hπU.restrict, π.hom.continuous.restrict hπU⟩

/-- The restriction `V' ⟶ V` of `π`. -/
private abbrev restrictRight : (TopPair.ofInclusion hBV).fst ⟶ TopCat.of V :=
  TopCat.ofHom ⟨hπV.restrict, π.hom.continuous.restrict hπV⟩

/-- The restriction `U' ∩ V' ⟶ U ∩ V` of `π`. -/
private abbrev restrictInter :
    (TopPair.ofInclusion (inter_subset_inter hAU hBV)).fst ⟶ TopCat.of ↥(U ∩ V) :=
  TopCat.ofHom ⟨(hπU.inter_inter hπV).restrict, π.hom.continuous.restrict (hπU.inter_inter hπV)⟩

/-- The restriction `U' ∪ V' ⟶ Y` of `π`. -/
private abbrev restrictUnion : (TopPair.ofInclusion (union_subset_union hAU hBV)).fst ⟶ Y :=
  TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V')) ≫ π

/-- The map of pairs `(U', A) ⟶ (U' ∪ V', A ∪ B)` induced by the inclusion. -/
private abbrev leftToUnion :
    TopPair.ofInclusion hAU ⟶ TopPair.ofInclusion (union_subset_union hAU hBV) :=
  TopPair.ofInclusionMap hAU (union_subset_union hAU hBV)
    (ContinuousMap.inclusion subset_union_left) fun _ hx ↦ subset_union_left hx

/-- The map of pairs `(V', B) ⟶ (U' ∪ V', A ∪ B)` induced by the inclusion. -/
private abbrev rightToUnion :
    TopPair.ofInclusion hBV ⟶ TopPair.ofInclusion (union_subset_union hAU hBV) :=
  TopPair.ofInclusionMap hBV (union_subset_union hAU hBV)
    (ContinuousMap.inclusion subset_union_right) fun _ hx ↦ subset_union_right hx

/-- The map of pairs `(U' ∩ V', A ∩ B) ⟶ (U', A)` induced by the inclusion. -/
private abbrev interToLeft :
    TopPair.ofInclusion (inter_subset_inter hAU hBV) ⟶ TopPair.ofInclusion hAU :=
  TopPair.ofInclusionMap (inter_subset_inter hAU hBV) hAU
    (ContinuousMap.inclusion inter_subset_left) fun _ hx ↦ inter_subset_left hx

/-- The map of pairs `(U' ∩ V', A ∩ B) ⟶ (V', B)` induced by the inclusion. -/
private abbrev interToRight :
    TopPair.ofInclusion (inter_subset_inter hAU hBV) ⟶ TopPair.ofInclusion hBV :=
  TopPair.ofInclusionMap (inter_subset_inter hAU hBV) hBV
    (ContinuousMap.inclusion inter_subset_right) fun _ hx ↦ inter_subset_right hx

variable {n : ℕ}
  (u : (TopPair.ofInclusion (union_subset_union hAU hBV)).singularCohomology (ModuleCat.of K K) K
    (ModuleCat.of K K) n)

/-- The map `a ↦ π^*a ⌣ u` over `Y`, as a morphism of modules. -/
private abbrev Φ (p m : ℕ) (h : p + n = m) :=
  ModuleCat.ofHom ((TopPair.ofInclusion (union_subset_union hAU hBV)).pullbackCup M
    (restrictUnion π hAU hBV) n p m h u)

/-- The map `a ↦ π^*a ⌣ u` over `U`, as a morphism of modules. -/
private abbrev ΦU (p m : ℕ) (h : p + n = m) :=
  ModuleCat.ofHom ((TopPair.ofInclusion hAU).pullbackCup M (restrictLeft π hAU hπU) n p m h
    (TopPair.singularCohomologyMap (leftToUnion hAU hBV) n u))

/-- The map `a ↦ π^*a ⌣ u` over `V`, as a morphism of modules. -/
private abbrev ΦV (p m : ℕ) (h : p + n = m) :=
  ModuleCat.ofHom ((TopPair.ofInclusion hBV).pullbackCup M (restrictRight π hBV hπV) n p m h
    (TopPair.singularCohomologyMap (rightToUnion hAU hBV) n u))

/-- The map `a ↦ π^*a ⌣ u` over `U ∩ V`, as a morphism of modules. -/
private abbrev ΦI (p m : ℕ) (h : p + n = m) :=
  ModuleCat.ofHom ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).pullbackCup M
    (restrictInter π hAU hBV hπU hπV) n p m h
    (TopPair.singularCohomologyMap (interToUnionMap hAU hBV) n u))

omit [CommRing K] in
private lemma fst_ofInclusionMap {X Y : TopCat.{w}} {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t)
    (hst' : s' ⊆ t') (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s') :
    Hom.fst (TopPair.ofInclusionMap hst hst' g hg) = TopCat.ofHom g := by
  ext x
  exact TopPair.ofInclusionMap_fst_apply g hg x

omit [CommRing K] in
private lemma interToLeft_comp_leftToUnion :
    interToLeft hAU hBV ≫ leftToUnion hAU hBV = interToUnionMap hAU hBV := by
  rw [← TopPair.ofInclusionMap_comp]
  rfl

omit [CommRing K] in
private lemma interToRight_comp_rightToUnion :
    interToRight hAU hBV ≫ rightToUnion hAU hBV = interToUnionMap hAU hBV := by
  rw [← TopPair.ofInclusionMap_comp]
  rfl

/-- The maps over `Y` and over `U` and `V` commute with the restrictions. -/
private lemma toBiprod_comm (p m : ℕ) (h : p + n = m) :
    singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M U V p ≫
        biprod.map (ΦU π hAU hBV hπU u p m h) (ΦV π hAU hBV hπV u p m h) =
      Φ π hAU hBV u p m h ≫
        singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hAU hBV m := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, biprod.map_fst,
      singularCohomologyPairMayerVietorisToBiprod_fst,
      singularCohomologyMayerVietorisToBiprod_fst_assoc]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact pullbackCup_naturality (leftToUnion hAU hBV) (restrictLeft π hAU hπU)
      (restrictUnion π hAU hBV) (TopCat.ofHom (ContinuousMap.subtypeVal U))
      (by rw [fst_ofInclusionMap]; rfl) h u a
  · rw [Category.assoc, Category.assoc, biprod.map_snd,
      singularCohomologyPairMayerVietorisToBiprod_snd,
      singularCohomologyMayerVietorisToBiprod_snd_assoc]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact pullbackCup_naturality (rightToUnion hAU hBV) (restrictRight π hBV hπV)
      (restrictUnion π hAU hBV) (TopCat.ofHom (ContinuousMap.subtypeVal V))
      (by rw [fst_ofInclusionMap]; rfl) h u a

/-- The maps over `U`, `V` and `U ∩ V` commute with the differences of restrictions. -/
private lemma fromBiprod_comm (p m : ℕ) (h : p + n = m) :
    singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M U V p ≫
        ΦI π hAU hBV hπU hπV u p m h =
      biprod.map (ΦU π hAU hBV hπU u p m h) (ΦV π hAU hBV hπV u p m h) ≫
        singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M hAU hBV m := by
  apply biprod.hom_ext'
  · rw [inl_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inl_map_assoc,
      inl_singularCohomologyPairMayerVietorisFromBiprod]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [← interToLeft_comp_leftToUnion, TopPair.singularCohomologyMap_comp, ModuleCat.comp_apply]
    exact pullbackCup_naturality (interToLeft hAU hBV) (restrictInter π hAU hBV hπU hπV)
      (restrictLeft π hAU hπU) (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left))
      (by rw [fst_ofInclusionMap]; rfl) h _ a
  · rw [inr_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inr_map_assoc,
      inr_singularCohomologyPairMayerVietorisFromBiprod, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_inj]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [← interToRight_comp_rightToUnion, TopPair.singularCohomologyMap_comp, ModuleCat.comp_apply]
    exact pullbackCup_naturality (interToRight hAU hBV) (restrictInter π hAU hBV hπU hπV)
      (restrictRight π hBV hπV) (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right))
      (by rw [fst_ofInclusionMap]; rfl) h _ a

variable (hU' : IsOpen U') (hV' : IsOpen V') (hUV' : U' ∪ V' = univ)
  (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))
  (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)

include hUV' in
/-- The maps over `U ∩ V` and over `Y` commute with the connecting morphisms. -/
private lemma δ_comm (q mq m : ℕ) (hq : q + n = mq) (hm : mq + 1 = m) (h : q + 1 + n = m) :
    ΦI π hAU hBV hπU hπV u q mq hq ≫
        singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M hAU hBV
          (hU'.preimage continuous_subtype_val) (hV'.preimage continuous_subtype_val) hA hB mq m
          hm =
      singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl ≫
        Φ π hAU hBV u (q + 1) m h := by
  ext a
  refine (singularCohomologyPairMayerVietorisδ_singularCup K hU' hV' hUV' hAU hBV hA hB
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom hq rfl hm h
    (TopCat.singularCohomologyMap (restrictInter π hAU hBV hπU hπV) q a) u).trans ?_
  refine congrArg (fun x ↦ (TopPair.ofInclusion (union_subset_union hAU hBV)).singularCup K
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (q + 1) n m h x u) ?_
  have e₁ := ConcreteCategory.congr_hom (singularCohomologyMayerVietorisδ_naturality
    (ModuleCat.of K K) K M hU' hV' hUV' hU hV hUV π hπU hπV q (q + 1) rfl) a
  have e₂ := ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp
    (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V'))) π (q + 1))
    (singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl a)
  simp only [ConcreteCategory.comp_apply] at e₁ e₂
  exact (congrArg (TopCat.singularCohomologyMap
    (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V'))) (q + 1)) e₁).symm.trans e₂.symm

omit [CommRing K] in
private lemma bijective_biprod_map {K : Type w} [Ring K] {P Q P' Q' : ModuleCat.{w} K}
    (f : P ⟶ P') (g : Q ⟶ Q') (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (biprod.map f g) := by
  have := (ConcreteCategory.isIso_iff_bijective f).2 hf
  have := (ConcreteCategory.isIso_iff_bijective g).2 hg
  exact (ConcreteCategory.isIso_iff_bijective _).1 (biprod.mapIso (asIso f) (asIso g)).isIso_hom

include hU' hV' hUV' hA hB hU hV hUV in
/-- **The Mayer–Vietoris step for `a ↦ π^*a ⌣ u`.** Let `π : X ⟶ Y` carry the members of an open
cover `{U', V'}` of `X` into those of an open cover `{U, V}` of `Y`, let `A ⊆ U'` and `B ⊆ V'` be
open in `A ∪ B`, and let `u ∈ Hⁿ(U' ∪ V', A ∪ B; K)`. Suppose that the maps `a ↦ π^*a ⌣ u` over `U`,
`V` and `U ∩ V`, with values in the cohomology of `(U', A)`, `(V', B)` and `(U' ∩ V', A ∩ B)` and
the restrictions of `π` and `u`, are bijective in every degree, and that
`Hⁿ⁻¹(U' ∩ V', A ∩ B; M) = 0`. Then `a ↦ π^*a ⌣ u` is bijective from `Hᵖ(Y; M)` to
`Hᵖ⁺ⁿ(U' ∪ V', A ∪ B; M)` in every degree `p`. -/
theorem bijective_pullbackCup_union
    (hI₀ : ∀ q, q + 1 = n → IsZero
      ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).singularCohomology (ModuleCat.of K K) K
        M q))
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective ((TopPair.ofInclusion hAU).pullbackCup M
      (TopCat.ofHom ⟨hπU.restrict, π.hom.continuous.restrict hπU⟩) n p m h
      (TopPair.singularCohomologyMap (TopPair.ofInclusionMap hAU (union_subset_union hAU hBV)
        (ContinuousMap.inclusion subset_union_left) fun _ hx ↦ subset_union_left hx) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective ((TopPair.ofInclusion hBV).pullbackCup M
      (TopCat.ofHom ⟨hπV.restrict, π.hom.continuous.restrict hπV⟩) n p m h
      (TopPair.singularCohomologyMap (TopPair.ofInclusionMap hBV (union_subset_union hAU hBV)
        (ContinuousMap.inclusion subset_union_right) fun _ hx ↦ subset_union_right hx) n u)))
    (hΦI : ∀ p m (h : p + n = m), Function.Bijective
      ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).pullbackCup M
        (TopCat.ofHom ⟨(hπU.inter_inter hπV).restrict,
          π.hom.continuous.restrict (hπU.inter_inter hπV)⟩) n p m h
        (TopPair.singularCohomologyMap (interToUnionMap hAU hBV) n u)))
    {p m : ℕ} (h : p + n = m) :
    Function.Bijective ((TopPair.ofInclusion (union_subset_union hAU hBV)).pullbackCup M
      (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V')) ≫ π) n p m h u) := by
  have hU'' := hU'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  have hV'' := hV'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  have hbiprod : ∀ p m (h : p + n = m), Function.Bijective
      (biprod.map (ΦU π hAU hBV hπU u p m h) (ΦV π hAU hBV hπV u p m h)) := fun p m h ↦
    bijective_biprod_map _ _ (hΦU p m h) (hΦV p m h)
  cases p with
  | zero =>
    have hT := (ModuleCat.mono_iff_injective _).1
      (mono_singularCohomologyMayerVietorisToBiprod_zero (ModuleCat.of K K) K M hU hV hUV)
    refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ hT ?_, fun y ↦ ?_⟩
    · refine (hbiprod 0 m h).1 ?_
      rw [map_zero, ← ConcreteCategory.comp_apply, toBiprod_comm, ConcreteCategory.comp_apply]
      simp only [ConcreteCategory.hom_ofHom]
      rw [ha, map_zero, map_zero]
    obtain ⟨z, hz⟩ := (hbiprod 0 m h).2
      (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hAU hBV m y)
    obtain ⟨a, rfl⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M hU hV hUV 0) z).1 <| by
      refine (hΦI 0 m h).1 ((ConcreteCategory.congr_hom
        (fromBiprod_comm π hAU hBV hπU hπV u 0 m h) z).trans ?_)
      rw [map_zero, ConcreteCategory.comp_apply, hz, ← ConcreteCategory.comp_apply,
        singularCohomologyPairMayerVietorisToBiprod_fromBiprod]
      rfl
    have hy : singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hAU hBV m
        (y - Φ π hAU hBV u 0 m h a) = 0 := by
      rw [map_sub, ← hz, sub_eq_zero]
      exact ConcreteCategory.congr_hom (toBiprod_comm π hAU hBV hπU hπV u 0 m h) a
    refine ⟨a, (sub_eq_zero.1 ?_).symm⟩
    cases n with
    | zero =>
      obtain rfl : m = 0 := by lia
      exact (ModuleCat.mono_iff_injective _).1
        (mono_singularCohomologyPairMayerVietorisToBiprod_zero (ModuleCat.of K K) K M hAU hBV
          hU'' hV'' hA hB) (hy.trans (map_zero _).symm)
    | succ n =>
      obtain ⟨w, hw⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₁ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          n m (by lia)) _).1 hy
      have := ModuleCat.isZero_iff_subsingleton.1 (hI₀ n rfl)
      rw [Subsingleton.elim w 0, map_zero] at hw
      exact hw.symm
  | succ q =>
    have hq : q + n + 1 = m := by lia
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
      _ _ _ _ _
      (congrArg ModuleCat.Hom.hom (fromBiprod_comm π hAU hBV hπU hπV u q (q + n) rfl)).symm
      (congrArg ModuleCat.Hom.hom (δ_comm π hAU hBV hπU hπV u hU' hV' hUV' hA hB hU hV hUV q
        (q + n) m rfl hq h))
      (congrArg ModuleCat.Hom.hom (toBiprod_comm π hAU hBV hπU hπV u (q + 1) m h)).symm
      (congrArg ModuleCat.Hom.hom (fromBiprod_comm π hAU hBV hπU hπV u (q + 1) m h)).symm
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyMayerVietoris_exact₃ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyMayerVietoris_exact₁ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M hU hV hUV (q + 1)))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₃ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          (q + n) m hq))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₁ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          (q + n) m hq))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₂ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          m))
      (hbiprod q (q + n) rfl).2 (hΦI q (q + n) rfl) (hbiprod (q + 1) m h) ((hΦI (q + 1) m h).1)

end MayerVietoris

end TopPair
