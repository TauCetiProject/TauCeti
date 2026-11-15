/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space and `F` a real vector space of finite dimension `r ≥ 2`. For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` of the Thom pair of the product bundle (`TauCeti.prodThomPair`),
with coefficients in a commutative ring `K`, the *Thom map* `a ↦ π^*a ⌣ u` from `Hᵖ(B; M)` to
`Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)` is `TopPair.pullbackCup` of the pair and the projection
`π : B × F → B`. This file proves that it is bijective in every degree, for every `K`-module `M`,
as soon as the restriction of `u` to the fibre pair `(F, F ∖ {0})` over every point of `B`
generates `Hʳ(F, F ∖ {0}; K)` (`TauCeti.bijective_pullbackCup_prodThomPair`). This is the case of a
single trivializing open set in the proof of the Thom isomorphism by Mayer–Vietoris over unions of
trivializing open sets.

First take for `u` the class `δ σ`, the image under the connecting morphism `δ` of the pair of the
class `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); K)` pulled back from the generator of the cohomology of the sphere
`Sʳ⁻¹` (`TauCeti.prodThomPairPuncturedClass`). The connecting morphism is linear over the cohomology
of `B × F` up to sign (`TopPair.singularCohomologyδ_singularCup`), and the cup product is graded
commutative (`TopCat.singularCup_gradedComm`), so
`π^*a ⌣ δ σ = (-1)^(p r) δ (σ ⌣ π^*a)`
(`TauCeti.pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedClass`). The map
`a ↦ δ (σ ⌣ π^*a)` is the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv`, so the
Thom map of `δ σ` is bijective.

A general class `u` is then the image `π^*ε ⌣ δ σ` of a degree-zero class `ε ∈ H⁰(B; K)`. On the
fibre over `b` this reads `u_b = ε(b) • (δ σ)_b`, and both `u_b` and `(δ σ)_b` generate the fibre
cohomology, which is a free `K`-module of rank one, so every value `ε(b)` is a unit. Hence `ε` is a
unit for the cup product (`TauCeti.exists_singularCup_eq_one`), and by associativity the Thom map of
`u` is that of `δ σ` composed with the bijective map `a ↦ a ⌣ ε`.

The ranks `0` and `1`, where `F ∖ {0}` is empty or has two contractible components, are not
treated here.

## Main results

* `TauCeti.pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedClass`: the Thom map
  of `δ σ` is `(-1)^(p r)` times `TauCeti.prodThomPairSingularCohomologySphereEquiv`, so it is
  bijective.
* `TauCeti.bijective_pullbackCup_prodThomPair`: **the Thom isomorphism for a product bundle**, for
  any class whose restrictions to the fibres generate.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle and then by Mayer–Vietoris).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]

section Sphere

variable {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] {d : ℕ}

/-- **The Thom map of the class `δ σ` of a product bundle.** For `e : F ≃L[ℝ] ℝᵈ⁺²`, let
`σ ∈ Hᵈ⁺¹(B × (F ∖ {0}); K)` be `TauCeti.prodThomPairPuncturedClass` and `δ` the connecting
morphism of the Thom pair `(B × F, B × (F ∖ {0}))`. Then
`π^*c ⌣ δ σ = (-1)^(p (d + 2)) δ (σ ⌣ π^*c)` for `c ∈ Hᵖ(B; M)`, where `c ↦ δ (σ ⌣ π^*c)` is the
equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv`. -/
theorem pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (p m : ℕ) (h : p + (d + 2) = m)
    (c : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e)) c =
      ((-1 : ℤ) ^ (p * (d + 2))) • prodThomPairSingularCohomologySphereEquiv M B e p m h c := by
  rw [TopPair.pullbackCup_apply, prodThomPairSingularCohomologySphereEquiv_apply,
    ← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  have h1 := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (p := p) (q := d + 1) (n := d + 1 + p)
    (q' := d + 2) (by omega) rfl (by omega) h
    (TopCat.singularCohomologyMap (prodThomPairProj B F) p c) (prodThomPairPuncturedClass K B e)
  have h2 := TopCat.singularCup_gradedComm (prodThomPair B F).snd K
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
    (μ := (λ_ M).hom) (μ' := (ρ_ M).hom) (braiding_rightUnitor M) (p := d + 1) (q := p)
    (n := d + 1 + p) rfl (prodThomPairPuncturedClass K B e)
    (TopCat.singularCohomologyMap (prodThomPair B F).map p
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p c))
  rw [h2, map_zsmul] at h1
  have hs : ((-1 : ℤ) ^ p) * (-1) ^ p = 1 := by rw [← mul_pow]; norm_num
  replace h1 := congrArg (((-1 : ℤ) ^ p) • ·) h1
  simp only [smul_smul, hs, one_smul, ← pow_add] at h1
  rw [← h1]
  congr 2
  ring

/-- The Thom map of the product bundle for the class `δ σ` is bijective in every degree. -/
private theorem bijective_pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (p m : ℕ) (h : p + (d + 2) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) := by
  have hinv : Function.Involutive fun x :
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m ↦
      ((-1 : ℤ) ^ (p * (d + 2))) • x := fun x ↦ by
    simp only [smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
  have hf : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) =
      (fun x ↦ ((-1 : ℤ) ^ (p * (d + 2))) • x) ∘
        prodThomPairSingularCohomologySphereEquiv M B e p m h :=
    funext (pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedClass M e p m h)
  rw [hf]
  exact hinv.bijective.comp (LinearEquiv.bijective _)

omit [Module ℝ F] in
/-- On the fibre over `b`, the Thom map of a class `u` sends a degree-zero class `ε` of the base to
the restriction of `u` multiplied by the value `ε(b)`. -/
private theorem singularCohomologyMap_prodThomPairFiberMap_pullbackCup_zero {n : ℕ}
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (ε : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (b : B) :
    TopPair.singularCohomologyMap (prodThomPairFiberMap F b) n
        ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) n 0 n
          (zero_add n) u ε) =
      singularCohomologyZeroEval b ε •
        TopPair.singularCohomologyMap (prodThomPairFiberMap F b) n u := by
  have hg : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
      TopCat.const (Y := TopCat.of PUnit.{w + 1}) PUnit.unit ≫
        TopCat.const (X := TopCat.of PUnit.{w + 1}) b := by
    ext x
    exact (prodThomPairProj_apply F _).trans
      (congrArg Prod.fst (prodThomPairFiberMap_fst_apply F b x))
  rw [← TopPair.pullbackCup_naturality (K := K) _ _ _ _ hg,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul]
  congr 1
  rw [TopCat.singularCohomologyZeroOne_def]
  exact TopPair.pullbackCup_one (K := K) _ _ _ _

/-- The restriction to a fibre of the class `δ σ`, the image of the unit under
`TauCeti.prodThomPairSingularCohomologySphereEquiv`, has trivial annihilator. -/
private theorem eq_zero_of_smul_singularCohomologyMap_prodThomPairFiberMap_eq_zero
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (b : B) {t : K}
    (ht : t • TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (d + 2)
      ((prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} K)) B e 0 (d + 2))
        (TopCat.of B).singularCohomologyZeroOne) = 0) : t = 0 := by
  have hb := prodThomPairFiberMap_comp_prodThomPairMap F PUnit.unit
    (ContinuousMap.const PUnit.{w + 1} b)
  rw [ContinuousMap.const_apply] at hb
  rw [← hb, TopPair.singularCohomologyMap_comp_apply,
    prodThomPairSingularCohomologySphereEquiv_naturality (𝟙_ (ModuleCat.{w} K))
      (ContinuousMap.const PUnit.{w + 1} b) e 0 (d + 2),
    singularCohomologyMap_singularCohomologyZeroOne, ← map_smul, ← map_smul] at ht
  -- Over a point, the projection to the fibre is a left inverse of the fibre inclusion.
  have h1 := congrArg (TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
    (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd PUnit.{w + 1} F) (d + 2)) ht
  rw [← TopPair.singularCohomologyMap_comp_apply, prodThomPairSnd_comp_prodThomPairFiberMap,
    TopPair.singularCohomologyMap_id, ModuleCat.id_apply, map_zero] at h1
  have h2 := congrArg (singularCohomologyZeroEval PUnit.unit)
    ((LinearEquiv.map_eq_zero_iff _).1 h1)
  simpa using h2

/-- The Thom map of a class `u` whose restriction to every fibre generates, for a fibre with a
linear equivalence to `ℝᵈ⁺²`. -/
private theorem bijective_pullbackCup_prodThomPair_of_continuousLinearEquiv
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) {n : ℕ} (hn : d + 2 = n)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) n u} = ⊤)
    {p m : ℕ} (h : p + n = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) n p m h u) := by
  subst hn
  set u₀ := (prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} K)) B e 0 (d + 2))
    (TopCat.of B).singularCohomologyZeroOne with hu₀
  have hA (N : ModuleCat.{w} K) (q r : ℕ) (hqr : q + (d + 2) = r) :
      Function.Bijective ((prodThomPair B F).pullbackCup N (prodThomPairProj B F) (d + 2) q r hqr
        u₀) := by
    rw [hu₀, TopCat.singularCohomologyZeroOne_def,
      prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle]
    exact bijective_pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedClass N e q r
      hqr
  -- Write `u` as the Thom map of `u₀` applied to a degree-zero class `ε` of the base.
  obtain ⟨ε, hε⟩ := (hA (ModuleCat.of K K) 0 (d + 2) (zero_add _)).2 u
  -- The values of `ε` are units, since `u` and `u₀` both restrict to generators of the fibres.
  have hunit (b : B) : IsUnit (singularCohomologyZeroEval b ε) := by
    have hb := hu b
    rw [← hε, singularCohomologyMap_prodThomPairFiberMap_pullbackCup_zero] at hb
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1
      (hb.symm ▸ Submodule.mem_top :
        TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (d + 2) u₀ ∈ Submodule.span K
          {singularCohomologyZeroEval b ε •
            TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (d + 2) u₀})
    refine IsUnit.of_mul_eq_one s (mul_comm s _ ▸ sub_eq_zero.1
      (eq_zero_of_smul_singularCohomologyMap_prodThomPairFiberMap_eq_zero e b ?_))
    rw [sub_smul, mul_smul, one_smul, sub_eq_zero]
    exact hs
  -- So the Thom map of `u` is that of `u₀` after the bijective cup product with `ε`.
  have hfac : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p rfl
          a ε := by
    funext a
    rw [← hε, Function.comp_apply, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
      TopPair.pullbackCup_apply, ← TopCat.singularCup_naturality]
    exact ((prodThomPair B F).singularCup_assoc K (u₁₂ := (λ_ _).inv) (u := (λ_ _).inv)
      (u₂₃ := (λ_ _).inv) (u' := (λ_ _).inv) (by monoidal) (μ₁₂ := (ρ_ M).hom)
      (μ := (ρ_ M).hom) (μ₂₃ := (ρ_ (ModuleCat.of K K)).hom) (μ' := (ρ_ M).hom) (by monoidal)
      rfl h (zero_add _) h _ _ _).symm
  rw [hfac]
  exact (hA M p m h).comp (bijective_singularCup_right_of_isUnit M ε hunit p)

end Sphere

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The Thom isomorphism for a product bundle.** Let `F` be a real vector space of finite
dimension `r ≥ 2`, and let `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` be a class whose restriction to the
fibre pair `(F, F ∖ {0})` over every point of `B` generates `Hʳ(F, F ∖ {0}; K)`. Then the Thom map
`a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`, for every degree
`p` and every `K`-module `M`. -/
theorem bijective_pullbackCup_prodThomPair (hF : 2 ≤ finrank ℝ F)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨d, hd⟩ : ∃ d, d + 2 = finrank ℝ F := ⟨finrank ℝ F - 2, by omega⟩
  exact bijective_pullbackCup_prodThomPair_of_continuousLinearEquiv M
    (ContinuousLinearEquiv.ofFinrankEq (by simp [hd])) hd u hu h

end TauCeti
