/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for a product bundle

Let `B` be a space and `F` a real vector space of dimension `r = d + 2 ≥ 2`, given with a
continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²`, and let `K` be a commutative ring. For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` of the Thom pair of the product bundle (`TauCeti.prodThomPair`),
the Thom map

`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^*a ⌣ u`,

is `TopPair.pullbackCup` of the pair and of the projection `π : B × F → B`. This file proves that
it is bijective in every degree `p` and for every `K`-module `M` as soon as `u` restricts, on the
fibre pair `(F, F ∖ {0})` over each point of `B`, to a generator of `Hʳ(F, F ∖ {0}; K)`
(`TauCeti.bijective_pullbackCup_prodThomPair`): this is the Thom isomorphism for product bundles of
rank at least `2`.

The argument starts from the class `δ σ`, where `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); K)` is pulled back from
the sphere (`TauCeti.prodThomPairPuncturedClass`) and `δ` is the connecting morphism of the pair.
The connecting morphism is linear over the cohomology of `B × F` up to the Koszul sign
(`TopPair.singularCohomologyδ_singularCup`), so with graded commutativity of the cup product
`π^*a ⌣ δ σ = (-1)^(p r) δ (σ ⌣ π^*a)`
(`TauCeti.pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass`). Up to this sign the Thom map
of `δ σ` is the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv`, so it is bijective
(`TauCeti.bijective_pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass`). In degree `0`,
every class `u` is then `π^*ε ⌣ δ σ` for some `ε ∈ H⁰(B; K)`, and by associativity the Thom map
of `u` sends `a` to `π^*(a ⌣ ε) ⌣ δ σ`. On the fibre over `b`, `u` restricts to `ε(b)` times the
restriction of `δ σ`, which corresponds to the unit of the cohomology of a point. So if `u`
generates on every fibre, the values of `ε` are units, and the cup product with `ε` is bijective
(`TauCeti.bijective_singularCup_right_of_isUnit`).

The ranks `0` and `1`, where `F ∖ {0}` is empty or has two contractible components, are not
treated here, as in `TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere`.

## Main results

* `TauCeti.pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass`: the Thom map of `δ σ` is
  `(-1)^(p r)` times `TauCeti.prodThomPairSingularCohomologySphereEquiv`.
* `TauCeti.bijective_pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass`: it is bijective.
* `TauCeti.singularCohomologyMap_prodThomPairMap_singularCohomologyδ_prodThomPairPuncturedClass`:
  the class `δ σ` is natural in the base.
* `TauCeti.bijective_pullbackCup_prodThomPair`: the Thom isomorphism for product bundles.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof (the Thom isomorphism, first for a trivial
  bundle).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] {d : ℕ}

/-- **The Thom map of `δ σ` on a product bundle.** For `F` of dimension `r = d + 2` and
`a ∈ Hᵖ(B; M)`, `π^*a ⌣ δ σ = (-1)^(p r) δ (σ ⌣ π^*a)`, where `σ` is
`TauCeti.prodThomPairPuncturedClass` and `δ` the connecting morphism of the Thom pair of `B × F`:
up to sign, the Thom map of `δ σ` is `TauCeti.prodThomPairSingularCohomologySphereEquiv`. -/
theorem pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) {p m : ℕ} (h : p + (d + 2) = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e)) a =
      ((-1 : ℤ) ^ (p * (d + 2))) • prodThomPairSingularCohomologySphereEquiv M B e p m h a := by
  have hδ := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (q := d + 1) (n := d + 1 + p) (by omega) rfl
    (by omega) h (TopCat.singularCohomologyMap (prodThomPairProj B F) p a)
    (prodThomPairPuncturedClass K B e)
  have hc := TopCat.singularCup_gradedComm (prodThomPair B F).snd K
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) ?_ ?_ (n := d + 1 + p) (by omega)
    (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)
    (prodThomPairPuncturedClass K B e)
  · -- `δ (π^*a|_{E₀} ⌣ σ) = (-1)ᵖ π^*a ⌣ δ σ` and `σ ⌣ π^*a = (-1)^(p (d + 1)) π^*a|_{E₀} ⌣ σ`.
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      map_comp_prodThomPairProj] at hδ
    rw [TopPair.pullbackCup_apply, prodThomPairSingularCohomologySphereEquiv_apply, hc, map_zsmul,
      hδ, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Even.neg_one_pow (n := p * (d + 2) + p * (d + 1) + p) ⟨p * (d + 2), by ring⟩, one_smul]
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal]
  · exact braiding_leftUnitor _

/-- **The Thom isomorphism for `δ σ` on a product bundle.** For `F` of dimension `r = d + 2`, the
Thom map `a ↦ π^*a ⌣ δ σ`, `Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`, is bijective, where `σ` is
`TauCeti.prodThomPairPuncturedClass` and `δ` the connecting morphism of the Thom pair. -/
theorem bijective_pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) {p m : ℕ} (h : p + (d + 2) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) := by
  have hf := pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass M e (B := B) h
  have hc : ((-1 : ℤ) ^ (p * (d + 2))) * (-1) ^ (p * (d + 2)) = 1 := by rw [← mul_pow]; norm_num
  generalize (-1 : ℤ) ^ (p * (d + 2)) = c at hf hc
  set L := prodThomPairSingularCohomologySphereEquiv M B e p m h
  refine ⟨fun a a' haa' ↦ L.injective ?_, fun y ↦ ⟨c • L.symm y, ?_⟩⟩
  · simpa [hf, smul_smul, hc] using congrArg (c • ·) haa'
  · rw [hf, map_zsmul, L.apply_symm_apply, smul_smul, hc, one_smul]

/-- **Naturality of `δ σ`**: the map of Thom pairs of product bundles induced by a map
`g : B' → B` of the bases pulls the class `δ σ` of `B × F` back to the class `δ σ` of `B' × F`. -/
@[simp]
theorem singularCohomologyMap_prodThomPairMap_singularCohomologyδ_prodThomPairPuncturedClass
    {B' : Type w} [TopologicalSpace B'] (g : C(B', B))
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    TopPair.singularCohomologyMap (prodThomPairMap F g) (d + 2)
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e)) =
      ((prodThomPair B' F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2)) (prodThomPairPuncturedClass K B' e) := by
  rw [← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) (d + 1) (d + 2),
    ConcreteCategory.comp_apply,
    singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]

/-- If the class `π^*ε ⌣ δ σ` restricts to a generator on the fibre over `b`, then the value of
`ε ∈ H⁰(B; K)` at `b` is a unit: the restriction is `ε(b)` times the image of the unit of the
cohomology of a point under the Thom map of `δ σ` over the point, which is bijective. -/
private theorem isUnit_singularCohomologyZeroEval_of_span_eq_top
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (ε : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0) (b : B)
    (hb : Submodule.span K {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (d + 2)
      ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) (d + 2) 0 (d + 2)
        (zero_add _) (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
          (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e)) ε))} = ⊤) :
    IsUnit (singularCohomologyZeroEval b ε) := by
  let φ := prodThomPairFiberMap F b
  let g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).fst ⟶ TopCat.of PUnit.{w + 1} :=
    TopCat.const PUnit.unit
  have hφ : φ = (complZeroPairIsoProdThomPair F).hom ≫
      prodThomPairMap F (ContinuousMap.const PUnit.{w + 1} b) := by
    rw [complZeroPairIsoProdThomPair_hom, prodThomPairFiberMap_comp_prodThomPairMap,
      ContinuousMap.const_apply]
  -- On the fibre over `b`, `T : x ↦ g^*x ⌣ φ^*(δ σ)` is bijective, as it is over a point.
  set T := (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).pullbackCup (ModuleCat.of K K) g
    (d + 2) 0 (d + 2) (zero_add _) (TopPair.singularCohomologyMap φ (d + 2)
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) with hT_def
  have hT : Function.Bijective T := by
    rw [hT_def, hφ, TopPair.singularCohomologyMap_comp_apply,
      singularCohomologyMap_prodThomPairMap_singularCohomologyδ_prodThomPairPuncturedClass,
      TopPair.bijective_pullbackCup_iff_of_isIso (complZeroPairIsoProdThomPair F).hom (g := g)
        (g' := prodThomPairProj PUnit.{w + 1} F) (𝟙 _) (TopCat.ext fun _ ↦ Subsingleton.elim _ _)]
    exact bijective_pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass _ e _
  -- The restriction of `π^*ε ⌣ δ σ` to the fibre is `T (ε(b) • 1)`.
  have hg : TopPair.Hom.fst φ ≫ prodThomPairProj B F = g ≫ TopCat.const b :=
    TopCat.ext fun x ↦ (prodThomPairProj_apply F _).trans
      (congrArg Prod.fst (prodThomPairFiberMap_fst_apply F b x))
  rw [← TopPair.pullbackCup_naturality φ g (prodThomPairProj B F) (TopCat.const b) hg,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul] at hb
  -- So `T 1 = a • T (ε(b) • 1) = T ((a ε(b)) • 1)` for some `a`, and `a ε(b) = 1`.
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (hb ▸ Submodule.mem_top (x := T (TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne))
  rw [← map_smul, smul_smul] at ha
  have := congrArg (singularCohomologyZeroEval PUnit.unit) (hT.1 ha)
  simp only [map_smul, singularCohomologyZeroEval_singularCohomologyZeroOne, smul_eq_mul,
    mul_one] at this
  exact IsUnit.of_mul_eq_one_right a this

/-- **The Thom isomorphism for a product bundle.** Let `F` have dimension `r = d + 2 ≥ 2`, and let
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restrict, on the fibre pair `(F, F ∖ {0})` over every point of
`B`, to a generator of `Hʳ(F, F ∖ {0}; K)`. Then for every `K`-module `M` and every degree `p`, the
Thom map `a ↦ π^*a ⌣ u`, `Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`, is bijective. -/
theorem bijective_pullbackCup_prodThomPair (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (d + 2))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (d + 2) u} = ⊤)
    {p m : ℕ} (h : p + (d + 2) = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u) := by
  -- Write `u = π^*ε ⌣ δ σ` for a class `ε ∈ H⁰(B; K)`; its values are units.
  obtain ⟨ε, rfl⟩ := (bijective_pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass
    (ModuleCat.of K K) e (B := B) (zero_add (d + 2))).2 u
  have hε := bijective_singularCup_right_of_isUnit M p ε
    fun b ↦ isUnit_singularCohomologyZeroEval_of_span_eq_top e ε b (hu b)
  -- `a ↦ π^*a ⌣ (π^*ε ⌣ δ σ)` is `a ↦ π^*(a ⌣ ε) ⌣ δ σ`.
  convert (bijective_pullbackCup_singularCohomologyδ_prodThomPairPuncturedClass M e h).comp hε
    using 1
  funext a
  rw [Function.comp_apply, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
    TopPair.pullbackCup_apply, ← TopCat.singularCup_naturality]
  exact (TopPair.singularCup_assoc K (prodThomPair B F) (by monoidal) (by monoidal) (add_zero p)
    h (zero_add _) h _ _ _).symm

end TauCeti
