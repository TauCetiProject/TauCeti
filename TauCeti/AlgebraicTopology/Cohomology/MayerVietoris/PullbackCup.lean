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
`(V', B)` and `(U' ∩ V', A ∩ B)`. If these three maps are bijective in degrees `q ≤ p`, and
`Hⁿ⁻¹(U' ∩ V', A ∩ B; M) = 0`, then the map over `Y` is bijective in degree `p`
(`TopPair.bijective_pullbackCup_union`).

For the induction over finite unions of trivializing open sets the step is restated for the maps
`TopCat.pullbackCupRestrict` over subsets of the base of a fixed map `π : X ⟶ Y` and pair `(X, Z)`:
if the maps over open sets `U`, `V` and `U ∩ V` are bijective in degrees `q ≤ p` and
`Hⁿ⁻¹(π⁻¹(U ∩ V), π⁻¹(U ∩ V) ∩ Z; M) = 0`, then the map over `U ∪ V` is bijective in degree `p`
(`TopCat.bijective_pullbackCupRestrict_union`).

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
* `TopCat.bijective_pullbackCup_of_union_eq_univ`: the step for the pair `(X, Z)` and an open
  cover of the base by two sets.
* `TopCat.bijective_pullbackCupRestrict_union`: the step over the union of two open sets of the
  base.

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
    (TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) n u))

/-- The map `a ↦ π^*a ⌣ u` over `V`, as a morphism of modules. -/
private abbrev ΦV (p m : ℕ) (h : p + n = m) :=
  ModuleCat.ofHom ((TopPair.ofInclusion hBV).pullbackCup M (restrictRight π hBV hπV) n p m h
    (TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) n u))

/-- The map `a ↦ π^*a ⌣ u` over `U ∩ V`, as a morphism of modules. -/
private abbrev ΦI (p m : ℕ) (h : p + n = m) :=
  ModuleCat.ofHom ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).pullbackCup M
    (restrictInter π hAU hBV hπU hπV) n p m h
    (TopPair.singularCohomologyMap (interToUnionMap hAU hBV) n u))

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
    -- In the side condition both maps `U' ⟶ Y` are the restriction of `π`, so `rfl` closes it.
    exact pullbackCup_naturality (leftToUnionMap hAU hBV) (restrictLeft π hAU hπU)
      (restrictUnion π hAU hBV) (TopCat.ofHom (ContinuousMap.subtypeVal U))
      (by rw [ofInclusionMap_fst]; rfl) h u a
  · rw [Category.assoc, Category.assoc, biprod.map_snd,
      singularCohomologyPairMayerVietorisToBiprod_snd,
      singularCohomologyMayerVietorisToBiprod_snd_assoc]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    -- In the side condition both maps `V' ⟶ Y` are the restriction of `π`, so `rfl` closes it.
    exact pullbackCup_naturality (rightToUnionMap hAU hBV) (restrictRight π hBV hπV)
      (restrictUnion π hAU hBV) (TopCat.ofHom (ContinuousMap.subtypeVal V))
      (by rw [ofInclusionMap_fst]; rfl) h u a

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
    rw [← interToLeftMap_comp_leftToUnionMap, TopPair.singularCohomologyMap_comp,
      ModuleCat.comp_apply]
    -- In the side condition both maps `U' ∩ V' ⟶ U` are the restriction of `π`, so `rfl` closes it.
    exact pullbackCup_naturality (interToLeftMap hAU hBV) (restrictInter π hAU hBV hπU hπV)
      (restrictLeft π hAU hπU) (TopCat.ofHom (ContinuousMap.inclusion inter_subset_left))
      (by rw [ofInclusionMap_fst]; rfl) h _ a
  · rw [inr_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inr_map_assoc,
      inr_singularCohomologyPairMayerVietorisFromBiprod, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_inj]
    ext a
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [← interToRightMap_comp_rightToUnionMap, TopPair.singularCohomologyMap_comp,
      ModuleCat.comp_apply]
    -- In the side condition both maps `U' ∩ V' ⟶ V` are the restriction of `π`, so `rfl` closes it.
    exact pullbackCup_naturality (interToRightMap hAU hBV) (restrictInter π hAU hBV hπU hπV)
      (restrictRight π hBV hπV) (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right))
      (by rw [ofInclusionMap_fst]; rfl) h _ a

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
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, pullbackCup_apply]
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

include hU' hV' hA hB hU hV hUV in
/-- The Mayer–Vietoris step in degree `0`. The sequence of `Y` starts with the injective
restriction `H⁰(Y; M) ⟶ H⁰(U; M) ⊞ H⁰(V; M)`, and the vanishing of `Hⁿ⁻¹(U' ∩ V', A ∩ B; M)`
replaces the missing terms of the sequence of the pairs. -/
private lemma bijective_pullbackCup_union_zero
    (hI₀ : ∀ q, q + 1 = n → IsZero
      ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).singularCohomology (ModuleCat.of K K) K
        M q))
    {m : ℕ} (h : 0 + n = m)
    (hbiprod : Function.Bijective
      (biprod.map (ΦU (M := M) π hAU hBV hπU u 0 m h) (ΦV (M := M) π hAU hBV hπV u 0 m h)))
    (hΦI : Function.Injective (ΦI (M := M) π hAU hBV hπU hπV u 0 m h)) :
    Function.Bijective (Φ (M := M) π hAU hBV u 0 m h) := by
  have hU'' := hU'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  have hV'' := hV'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
  -- Injectivity: if `Φ a = 0`, the maps over `U` and `V` send the restriction of `a` to
  -- `H⁰(U) ⊞ H⁰(V)` to the restriction of `Φ a = 0`. They are injective, so the restriction of
  -- `a` vanishes, and the restriction `H⁰(Y) ⟶ H⁰(U) ⊞ H⁰(V)` is injective.
  have hT := (ModuleCat.mono_iff_injective _).1
    (mono_singularCohomologyMayerVietorisToBiprod_zero (ModuleCat.of K K) K M hU hV hUV)
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha ↦ hT ?_, fun y ↦ ?_⟩
  · refine hbiprod.1 ?_
    rw [map_zero, ← ConcreteCategory.comp_apply, toBiprod_comm, ConcreteCategory.comp_apply]
    simp only [ConcreteCategory.hom_ofHom] at ha ⊢
    rw [ha, map_zero, map_zero]
  -- Surjectivity: lift the restriction of `y` to `z ∈ H⁰(U) ⊞ H⁰(V)`. Its difference of
  -- restrictions is sent to `0` by the injective map over `U ∩ V`, so it vanishes and, by
  -- exactness at `H⁰(U) ⊞ H⁰(V)`, `z` is the restriction of some `a ∈ H⁰(Y)`.
  obtain ⟨z, hz⟩ := hbiprod.2
    (singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hAU hBV m y)
  obtain ⟨a, rfl⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M hU hV hUV 0) z).1 <| by
    refine hΦI ((ConcreteCategory.congr_hom
      (fromBiprod_comm π hAU hBV hπU hπV u 0 m h) z).trans ?_)
    rw [map_zero, ConcreteCategory.comp_apply, hz, ← ConcreteCategory.comp_apply,
      singularCohomologyPairMayerVietorisToBiprod_fromBiprod]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  have hy : singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M hAU hBV m
      (y - Φ π hAU hBV u 0 m h a) = 0 := by
    rw [map_sub, ← hz, sub_eq_zero]
    exact ConcreteCategory.congr_hom (toBiprod_comm π hAU hBV hπU hπV u 0 m h) a
  -- Then `y - Φ a` restricts to `0`; it remains to see that the restriction to
  -- `Hᵐ(U', A) ⊞ Hᵐ(V', B)` is injective.
  refine ⟨a, (sub_eq_zero.1 ?_).symm⟩
  cases n with
  | zero =>
    -- In degree `0` the restriction is injective at the start of the sequence of the pairs.
    obtain rfl : m = 0 := by lia
    exact (ModuleCat.mono_iff_injective _).1
      (mono_singularCohomologyPairMayerVietorisToBiprod_zero (ModuleCat.of K K) K M hAU hBV
        hU'' hV'' hA hB) (hy.trans (map_zero _).symm)
  | succ n =>
    -- Otherwise `y - Φ a` is in the image of the connecting morphism from the cohomology of
    -- `(U' ∩ V', A ∩ B)` in degree `m - 1`, which vanishes by `hI₀`.
    obtain ⟨w, hw⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (singularCohomologyPairMayerVietoris_exact₁ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
        n m (by lia)) _).1 hy
    have := ModuleCat.isZero_iff_subsingleton.1 (hI₀ n rfl)
    rw [Subsingleton.elim w 0, map_zero] at hw
    exact hw.symm

include hU' hV' hUV' hA hB hU hV hUV in
/-- **The Mayer–Vietoris step for `a ↦ π^*a ⌣ u`.** Let `π : X ⟶ Y` carry the members of an open
cover `{U', V'}` of `X` into those of an open cover `{U, V}` of `Y`, let `A ⊆ U'` and `B ⊆ V'` be
open in `A ∪ B`, and let `u ∈ Hⁿ(U' ∪ V', A ∪ B; K)`. Suppose that the maps `a ↦ π^*a ⌣ u` over `U`,
`V` and `U ∩ V`, with values in the cohomology of `(U', A)`, `(V', B)` and `(U' ∩ V', A ∩ B)` and
the restrictions of `π` and `u`, are bijective in degrees `q ≤ p`, and that
`Hⁿ⁻¹(U' ∩ V', A ∩ B; M) = 0`. Then `a ↦ π^*a ⌣ u` is bijective from `Hᵖ(Y; M)` to
`Hᵖ⁺ⁿ(U' ∪ V', A ∪ B; M)`. -/
theorem bijective_pullbackCup_union {p m : ℕ}
    (hI₀ : ∀ q, q + 1 = n → IsZero
      ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).singularCohomology (ModuleCat.of K K) K
        M q))
    (hΦU : ∀ q ≤ p, Function.Bijective ((TopPair.ofInclusion hAU).pullbackCup M
      (TopCat.ofHom ⟨hπU.restrict, π.hom.continuous.restrict hπU⟩) n q (q + n) rfl
      (TopPair.singularCohomologyMap (leftToUnionMap hAU hBV) n u)))
    (hΦV : ∀ q ≤ p, Function.Bijective ((TopPair.ofInclusion hBV).pullbackCup M
      (TopCat.ofHom ⟨hπV.restrict, π.hom.continuous.restrict hπV⟩) n q (q + n) rfl
      (TopPair.singularCohomologyMap (rightToUnionMap hAU hBV) n u)))
    (hΦI : ∀ q ≤ p, Function.Bijective
      ((TopPair.ofInclusion (inter_subset_inter hAU hBV)).pullbackCup M
        (TopCat.ofHom ⟨(hπU.inter_inter hπV).restrict,
          π.hom.continuous.restrict (hπU.inter_inter hπV)⟩) n q (q + n) rfl
        (TopPair.singularCohomologyMap (interToUnionMap hAU hBV) n u)))
    (h : p + n = m) :
    Function.Bijective ((TopPair.ofInclusion (union_subset_union hAU hBV)).pullbackCup M
      (TopCat.ofHom (ContinuousMap.subtypeVal (U' ∪ V')) ≫ π) n p m h u) := by
  subst h
  have hbiprod : ∀ q ≤ p, Function.Bijective
      (biprod.map (ΦU π hAU hBV hπU u q (q + n) rfl) (ΦV π hAU hBV hπV u q (q + n) rfl)) :=
    fun q hq ↦ ModuleCat.bijective_biprod_map _ _ (hΦU q hq) (hΦV q hq)
  cases p with
  | zero =>
    exact bijective_pullbackCup_union_zero π hAU hBV hπU hπV u hU' hV' hA hB hU hV hUV hI₀ rfl
      (hbiprod 0 le_rfl) (hΦI 0 le_rfl).1
  | succ q =>
    -- In positive degrees the five lemma applies to the two Mayer–Vietoris sequences.
    have hU'' := hU'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
    have hV'' := hV'.preimage (continuous_subtype_val (p := (· ∈ U' ∪ V')))
    have hq : q + n + 1 = q + 1 + n := by lia
    have hq' : q ≤ q + 1 := by lia
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective _ _ _ _ _ _ _ _
      _ _ _ _ _
      (congrArg ModuleCat.Hom.hom (fromBiprod_comm π hAU hBV hπU hπV u q (q + n) rfl)).symm
      (congrArg ModuleCat.Hom.hom (δ_comm π hAU hBV hπU hπV u hU' hV' hUV' hA hB hU hV hUV q
        (q + n) (q + 1 + n) rfl hq rfl))
      (congrArg ModuleCat.Hom.hom (toBiprod_comm π hAU hBV hπU hπV u (q + 1) _ rfl)).symm
      (congrArg ModuleCat.Hom.hom (fromBiprod_comm π hAU hBV hπU hπV u (q + 1) _ rfl)).symm
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyMayerVietoris_exact₃ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyMayerVietoris_exact₁ (ModuleCat.of K K) K M hU hV hUV q (q + 1) rfl))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M hU hV hUV (q + 1)))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₃ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          (q + n) _ hq))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₁ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          (q + n) _ hq))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (singularCohomologyPairMayerVietoris_exact₂ (ModuleCat.of K K) K M hAU hBV hU'' hV'' hA hB
          (q + 1 + n)))
      (hbiprod q hq').2 (hΦI q hq') (hbiprod (q + 1) le_rfl) (hΦI (q + 1) le_rfl).1

end MayerVietoris

end TopPair

namespace TopCat

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)

/-! ### The Mayer–Vietoris step for an open cover of the base -/

section Cover

variable {U V : Set Y}

variable (M : ModuleCat.{w} K)

/-- The restriction of `π` to a map `π⁻¹ S ⟶ S` carrying `π⁻¹ S` into `S` is
`π.hom.restrictPreimage S`. -/
private theorem ofHom_restrict_mapsTo_preimage (S : Set Y) :
    ofHom ⟨(mapsTo_preimage π S).restrict, π.hom.continuous.restrict (mapsTo_preimage π S)⟩ =
      ofHom (π.hom.restrictPreimage S) :=
  TopCat.ext fun _ ↦ rfl

/-- A map of pairs `φ` into the union of the pairs over `U` and `V`, followed by the inclusion of
that union into `(X, Z)`, is a map of pairs `ψ` into the pair over `S` followed by the inclusion
of the pair over `S`, when `φ` and `ψ` agree on the points of `X`. -/
private theorem comp_restrictPreimagePairUnionIso_hom_comp_restrictPreimagePairMap
    {P : TopPair.{w}} {S : Set Y}
    (φ : P ⟶ TopPair.ofInclusion (union_subset_union
      (inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)))
    (ψ : P ⟶ TopPair.ofInclusion (inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S))
    (hφψ : ∀ x, (TopPair.Hom.fst φ x).1 = (TopPair.Hom.fst ψ x).1) :
    φ ≫ (restrictPreimagePairUnionIso π Z U V).hom ≫ restrictPreimagePairMap π Z (U ∪ V) =
      ψ ≫ restrictPreimagePairMap π Z S :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
    ((restrictPreimagePairMap_fst_apply π Z (U ∪ V) _).trans
      (restrictPreimagePairUnionIso_hom_fst_apply π Z U V _)).trans
      ((hφψ x).trans (restrictPreimagePairMap_fst_apply π Z S _).symm))

/-- **The Mayer–Vietoris step for the pair `(X, Z)` and an open cover of the base.** Let
`π : X ⟶ Y` be a map, `Z ⊆ X`, `u ∈ Hⁿ(X, Z; K)`, and let `U` and `V` be open sets covering `Y`.
Suppose that the maps `TopCat.pullbackCupRestrict` of `u` over `U`, `V` and `U ∩ V` are bijective
in degrees `q ≤ p`, and that `Hⁿ⁻¹(π⁻¹(U ∩ V), π⁻¹(U ∩ V) ∩ Z; M)` vanishes. Then
`Hᵖ(Y; M) ⟶ Hᵖ⁺ⁿ(X, Z; M)`, `a ↦ π^*a ⌣ u`, is bijective. -/
theorem bijective_pullbackCup_of_union_eq_univ (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n p m : ℕ}
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hU' : ∀ q ≤ p, Function.Bijective (pullbackCupRestrict π Z M U n q (q + n) rfl u))
    (hV' : ∀ q ≤ p, Function.Bijective (pullbackCupRestrict π Z M V n q (q + n) rfl u))
    (hUV' : ∀ q ≤ p, Function.Bijective (pullbackCupRestrict π Z M (U ∩ V) n q (q + n) rfl u))
    (hUV₀ : ∀ j, j + 1 = n → IsZero ((TopPair.ofInclusion (inter_subset_left :
      π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V))).singularCohomology (ModuleCat.of K K) K M j))
    (h : p + n = m) :
    Function.Bijective ((TopPair.ofSubset Z).pullbackCup M π n p m h u) := by
  have hUV'' : π ⁻¹' U ∪ π ⁻¹' V = univ := by rw [← preimage_union, hUV, preimage_univ]
  have := isIso_restrictPreimagePairMap π Z (S := U ∪ V) fun _ ↦ hUV ▸ mem_univ _
  have hZ : π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z ⊆ Z := union_subset inter_subset_right inter_subset_right
  have hZ' {W : Set Y} (hW : IsOpen W) :
      IsOpen (((↑) : ↥(π ⁻¹' U ∩ Z ∪ π ⁻¹' V ∩ Z) → X) ⁻¹' (π ⁻¹' W ∩ Z)) := by
    rw [preimage_inter, preimage_val_eq_univ_of_subset hZ, inter_univ]
    exact (hW.preimage π.hom.continuous).preimage continuous_subtype_val
  refine (TopPair.bijective_pullbackCup_iff_of_isIso
    ((restrictPreimagePairUnionIso π Z U V).hom ≫ restrictPreimagePairMap π Z (U ∪ V)) (𝟙 Y)
    (g := ofHom (ContinuousMap.subtypeVal _) ≫ π) (by
      rw [TopPair.Hom.fst_comp, restrictPreimagePairUnionIso_hom_fst, restrictPreimagePairMap_fst]
      exact TopCat.ext fun _ ↦ rfl) h u).1 ?_
  refine TopPair.bijective_pullbackCup_union π (inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
    (inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V) (mapsTo_preimage π U) (mapsTo_preimage π V) _
    (hU.preimage π.hom.continuous) (hV.preimage π.hom.continuous) hUV''
    (hZ' hU) (hZ' hV) hU hV hUV
    (fun j hj ↦ ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M j).mapIso
      (restrictPreimagePairInterIso π Z U V).op).isZero_iff.1 (hUV₀ j hj)) ?_ ?_ ?_ h
  · intro q hq
    rw [ofHom_restrict_mapsTo_preimage, ← TopPair.singularCohomologyMap_comp_apply,
      comp_restrictPreimagePairUnionIso_hom_comp_restrictPreimagePairMap π Z _ (𝟙 _)
        fun x ↦ congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x), Category.id_comp,
      ← pullbackCupRestrict_apply]
    exact hU' q hq
  · intro q hq
    rw [ofHom_restrict_mapsTo_preimage, ← TopPair.singularCohomologyMap_comp_apply,
      comp_restrictPreimagePairUnionIso_hom_comp_restrictPreimagePairMap π Z _ (𝟙 _)
        fun x ↦ congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x), Category.id_comp,
      ← pullbackCupRestrict_apply]
    exact hV' q hq
  · intro q hq
    rw [← TopPair.singularCohomologyMap_comp_apply,
      comp_restrictPreimagePairUnionIso_hom_comp_restrictPreimagePairMap π Z _
        (restrictPreimagePairInterIso π Z U V).hom
        fun x ↦ (congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
          (restrictPreimagePairInterIso_hom_fst_apply π Z U V x).symm,
      TopPair.singularCohomologyMap_comp_apply]
    exact (TopPair.bijective_pullbackCup_iff_of_isIso (restrictPreimagePairInterIso π Z U V).hom
      (𝟙 (of ↥(U ∩ V))) (g' := ofHom (π.hom.restrictPreimage (U ∩ V)))
      (by
        rw [restrictPreimagePairInterIso_hom_fst]
        exact TopCat.ext fun _ ↦ rfl) rfl _).2
      (by rw [← pullbackCupRestrict_apply π Z M (U ∩ V) rfl u]; exact hUV' q hq)

end Cover

/-! ### The Mayer–Vietoris step over a union -/

section Union

variable {W S : Set Y}

variable (W) in
/-- The restriction of `u` to the pair over `W`, as a class of the pair formed by `π⁻¹ W` and its
points lying in `Z`. -/
private abbrev restrictClass {n : ℕ}
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (TopPair.ofSubset (X := of ↥(π ⁻¹' W)) ((↑) ⁻¹' (π ⁻¹' W ∩ Z))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) n :=
  TopPair.singularCohomologyMap (TopPair.ofSubsetPreimageValIso
      (inter_subset_left : π ⁻¹' W ∩ Z ⊆ π ⁻¹' W)).hom n
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z W) n u)

variable (M : ModuleCat.{w} K)

/-- For `S ⊆ W`, the map over `S` agrees with the map over the preimage of `S` in `W` of the
restriction of `π` over `W`, up to homeomorphisms; so the two are bijective together. -/
private theorem bijective_pullbackCupRestrict_restrict_iff (hSW : S ⊆ W) {n p m : ℕ}
    (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (pullbackCupRestrict (ofHom (π.hom.restrictPreimage W))
      ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) M ((↑) ⁻¹' S) n p m h (restrictClass π Z W u)) ↔
      Function.Bijective (pullbackCupRestrict π Z M S n p m h u) := by
  have hu : TopPair.singularCohomologyMap (restrictPreimagePairMap
      (ofHom (π.hom.restrictPreimage W)) ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) ((↑) ⁻¹' S)) n
      (restrictClass π Z W u) =
      TopPair.singularCohomologyMap (restrictPreimagePairRestrictPreimageIso π Z hSW).hom n
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n u) := by
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      ← TopPair.singularCohomologyMap_comp_apply]
    exact congrArg (fun f ↦ TopPair.singularCohomologyMap f n u)
      (TopPair.hom_ext_of_fst _ (by
        simp only [TopPair.Hom.fst_comp, TopPair.ofSubsetPreimageValIso_hom_fst,
          restrictPreimagePairRestrictPreimageIso_hom_fst, restrictPreimagePairMap_fst]
        exact TopCat.ext fun _ ↦ rfl))
  rw [pullbackCupRestrict_apply, pullbackCupRestrict_apply π Z M S h u, hu]
  have hS : S ⊆ range ((↑) : W → Y) := by rwa [Subtype.range_coe]
  let g := isoOfHomeo (X := of ↥((↑) ⁻¹' S : Set ↥W)) (Y := of ↥S)
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hS)
  exact TopPair.bijective_pullbackCup_iff_of_isIso
    (restrictPreimagePairRestrictPreimageIso π Z hSW).hom g.hom
    (by
      rw [restrictPreimagePairRestrictPreimageIso_hom_fst]
      exact TopCat.ext fun _ ↦ Subtype.ext rfl) h _

/-- **The Mayer–Vietoris step over a union.** Let `π : X ⟶ Y` be a map, `Z ⊆ X`,
`u ∈ Hⁿ(X, Z; K)`, and let `U` and `V` be open sets of `Y`. Suppose that the maps
`TopCat.pullbackCupRestrict` of `u` over `U`, `V` and `U ∩ V` are bijective in degrees `q ≤ p`, and
that `Hⁿ⁻¹(π⁻¹(U ∩ V), π⁻¹(U ∩ V) ∩ Z; M)` vanishes. Then the map of `u` over `U ∪ V` is bijective
in degree `p`. -/
theorem bijective_pullbackCupRestrict_union {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V)
    {n p m : ℕ}
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hU' : ∀ q ≤ p, Function.Bijective (pullbackCupRestrict π Z M U n q (q + n) rfl u))
    (hV' : ∀ q ≤ p, Function.Bijective (pullbackCupRestrict π Z M V n q (q + n) rfl u))
    (hUV' : ∀ q ≤ p, Function.Bijective (pullbackCupRestrict π Z M (U ∩ V) n q (q + n) rfl u))
    (hUV₀ : ∀ j, j + 1 = n → IsZero ((TopPair.ofInclusion (inter_subset_left :
      π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V))).singularCohomology (ModuleCat.of K K) K M j))
    (h : p + n = m) :
    Function.Bijective (pullbackCupRestrict π Z M (U ∪ V) n p m h u) := by
  have hUVW : U ∩ V ⊆ U ∪ V := inter_subset_left.trans subset_union_left
  -- The cover case, for the restriction of `π` over `U ∪ V` and the cover of `U ∪ V` by the
  -- preimages of `U` and `V`, whose hypotheses are those over `U`, `V` and `U ∩ V`.
  have key := bijective_pullbackCup_of_union_eq_univ (X := of ↥(π ⁻¹' (U ∪ V)))
    (ofHom (π.hom.restrictPreimage (U ∪ V))) ((↑) ⁻¹' (π ⁻¹' (U ∪ V) ∩ Z)) M
    (U := ((↑) : ↥(U ∪ V) → Y) ⁻¹' U) (V := ((↑) : ↥(U ∪ V) → Y) ⁻¹' V)
    (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
    (eq_univ_of_forall fun x ↦ x.2) (n := n) (p := p) (m := m)
  replace key := key (restrictClass π Z (U ∪ V) u)
    (fun q hq ↦ (bijective_pullbackCupRestrict_restrict_iff π Z M subset_union_left rfl u).2
      (hU' q hq))
    (fun q hq ↦ (bijective_pullbackCupRestrict_restrict_iff π Z M subset_union_right rfl u).2
      (hV' q hq))
    (fun q hq ↦ (bijective_pullbackCupRestrict_restrict_iff π Z M hUVW rfl u).2 (hUV' q hq))
    fun j hj ↦ by
      have := (hUV₀ j hj).of_iso ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M
        j).mapIso (restrictPreimagePairRestrictPreimageIso π Z hUVW).op).symm
      rwa [preimage_inter (s := U) (t := V)] at this
  rw [pullbackCupRestrict_apply π Z M (U ∪ V) h u]
  exact (TopPair.bijective_pullbackCup_iff_of_isIso (TopPair.ofSubsetPreimageValIso
    (inter_subset_left : π ⁻¹' (U ∪ V) ∩ Z ⊆ π ⁻¹' (U ∪ V))).hom (𝟙 _)
    (g := ofHom (π.hom.restrictPreimage (U ∪ V)))
    (by rw [TopPair.ofSubsetPreimageValIso_hom_fst]; exact TopCat.ext fun _ ↦ rfl) h
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z (U ∪ V)) n u)).1 (key h)

end Union

end TopCat
