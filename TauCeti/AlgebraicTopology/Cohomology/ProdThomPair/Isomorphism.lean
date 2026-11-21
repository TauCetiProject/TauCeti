/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Line
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space and `F` a finite-dimensional real normed space of dimension
`r = finrank ℝ F ≥ 0`. The product bundle `B × F → B` has Thom pair `(B × F, B × (F ∖ {0}))`
(`TauCeti.prodThomPair`) and projection `π : B × F → B` (`TauCeti.prodThomPairProj`). For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` with coefficients in a commutative ring `K`, the map

`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^*a ⌣ u`

(`TopPair.pullbackCup`) is the Thom map of `u`. This file proves that it is bijective in every
degree and for every module of coefficients `M` as soon as `u` restricts on the fibre pair
`(F, F ∖ {0})` over every point to a generator of `Hʳ(F, F ∖ {0}; K) ≅ K`
(`TauCeti.bijective_pullbackCup_prodThomPair`), bundled as the `K`-linear equivalence
`TauCeti.prodThomPairPullbackCupEquiv`. This is the Thom isomorphism over a single trivializing
open set, the case that the Mayer–Vietoris step `TopCat.bijective_pullbackCupRestrict_union`
extends to unions of trivializing open sets.

For positive rank `r = d + 1 ≥ 1`, the proof first treats the class `δ σ`, where
`σ ∈ Hᵈ(B × (F ∖ {0}); K)` is pulled back from the standard top class of `Sᵈ`
(`TauCeti.prodThomPairPuncturedClass`) and `δ` is the connecting morphism of the pair. The
connecting morphism is linear over the cohomology of `B × F` up to sign
(`TopPair.singularCohomologyδ_singularCup`), and the cup product is graded commutative
(`TopCat.singularCup_gradedComm`), so

`π^*a ⌣ δ σ = (-1)^(p r) δ (σ ⌣ π^*a)`

for `a` of degree `p`, and for a class `σ` of any degree
(`TauCeti.pullbackCup_prodThomPair_singularCohomologyδ`). The right-hand side is, up to that sign,
the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` computed from the cohomology of
`Sᵈ × B`, so the Thom map of `δ σ` is bijective. The same identity applies in rank one to the class
`σ ∈ H⁰(B × (F ∖ {0}); K)` of the positive side (`TauCeti.prodThomPairPuncturedLineClass`), and
identifies its Thom map with the equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv`
computed from the two sides
(`TauCeti.pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedLineClass`). For rank
`0` (`Subsingleton F`), `B × (F ∖ {0})` is empty and the projection `π : B × F → B` is a
homeomorphism, so the preimage of `1 ∈ H⁰(B × F; K)` has bijective Thom map
(`TopPair.bijective_pullbackCup_of_isEmpty`).

A general class `u` is then `π^*c ⌣ v` for a unique `c ∈ H⁰(B; K)` and our model class `v`.
Restricted to the fibre over `b`, it is the value `c(b)` times the restriction of `v`; since
`Hʳ(F, F ∖ {0}; K)` is one copy of `K`, it can only generate if `c(b)` is a unit. A degree-zero
class whose values are units is a unit for the cup product (`TauCeti.exists_singularCup_eq_one`),
and the Thom map of `u` is that of `v` composed with the cup product by `c`, which is then
bijective (`TauCeti.bijective_singularCup_left_of_singularCup_eq_one`).

## Main definitions and results

* `TauCeti.pullbackCup_prodThomPair_singularCohomologyδ`: the Thom map of `δ σ` is, up to the sign
  `(-1)^(p r)`, the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` (all positive
  ranks `r = d + 1 ≥ 1`).
* `TauCeti.pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedLineClass`: in rank
  one, the Thom map of `δ σ` for the class `σ` of the positive side is, up to the sign `(-1)^p`, the
  equivalence `TauCeti.prodThomPairSingularCohomologyLineEquiv`.
* `TauCeti.bijective_pullbackCup_prodThomPair`: **the Thom isomorphism for a product bundle** of
  arbitrary finite rank `r ≥ 0`.
* `TauCeti.bijective_pullbackCup_prodThomPair_snd`: `a ↦ π^*a ⌣ pr₂^* g` is bijective for any
  generator `g` of `Hʳ(F, F ∖ {0}; K)`.
* `TauCeti.prodThomPairPullbackCupEquiv`: the `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)` given by `a ↦ π^*a ⌣ u`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The Thom map of `δ σ` -/

omit [NormedSpace ℝ F] in
/-- For any class `σ ∈ H^q(B × (F ∖ {0}); K)` with `q + 1 = r`, the Thom map `a ↦ π^*a ⌣ δ σ` of
the product bundle sends `a ∈ Hᵖ(B; M)` to `(-1)^(p r) δ (σ ⌣ π^*a)`: the connecting morphism moves
the cup product with `π^*a` past `δ`, and graded commutativity exchanges `π^*a` and `σ`. -/
private theorem pullbackCup_prodThomPair_singularCohomologyδ_eq_smul {q r : ℕ} (hq : q + 1 = r)
    {p n m : ℕ} (hn : q + p = n) (h : p + r = m)
    (σ : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) q)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          q r hq) σ) a =
      ((-1 : ℤ) ^ (p * r)) •
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m (by lia))
          ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
            q p n hn σ (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)) := by
  subst hq
  -- The connecting morphism moves the cup product with `π^*a` past `δ`, up to `(-1)ᵖ`.
  have hδ := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (p := p) (q := q) (n := n) (q' := q + 1) (m := m)
    (by lia) rfl (by lia) h
    (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) σ
  -- Graded commutativity exchanges `π^*a` and `σ`, up to `(-1)^(p q)`.
  have hcomm := TopCat.singularCup_gradedComm (prodThomPair B F).snd K
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) (braiding_leftUnitor M) (p := p) (q := q)
    (n := n) (by lia)
    (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) σ
  rw [← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
    at hcomm ⊢
  rw [hcomm, map_zsmul, hδ, smul_smul, TopPair.pullbackCup_apply]
  -- The signs combine to `(-1)^(p (q + 1))` twice, which cancel.
  rw [smul_smul, mul_assoc, ← pow_add, show p * q + p = p * (q + 1) by ring, mul_smul,
    neg_one_pow_smul_neg_one_pow_smul]

omit [NormedSpace ℝ F] in
/-- The Thom map of `δ σ` is bijective in every degree as soon as `a ↦ δ (σ ⌣ π^*a)` is a linear
equivalence `L`, since the Thom map is `L` up to a sign. -/
private theorem bijective_pullbackCup_prodThomPair_singularCohomologyδ {q r : ℕ}
    (hq : q + 1 = r) {p n m : ℕ} (hn : q + p = n) (h : p + r = m)
    (σ : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) q)
    (L : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M m)
    (hL : ∀ a, L a = ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n m
      (by lia)) ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
        q p n hn σ (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a))) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        q r hq) σ)) := by
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        q r hq) σ)) = (((-1 : ℤ) ^ (p * r)) • ·) ∘ L :=
    funext fun a ↦ (pullbackCup_prodThomPair_singularCohomologyδ_eq_smul M hq hn h σ a).trans
      (by rw [Function.comp_apply, hL])
  rw [hcomp]
  exact Function.Involutive.bijective (neg_one_pow_smul_neg_one_pow_smul _) |>.comp L.bijective

/-! ### The Thom map of the class pulled back from the sphere -/

section Sphere

variable {d : ℕ}

/-- **The Thom map of `δ σ`.** For a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹` and the class
`σ = TauCeti.prodThomPairPuncturedClass` of `B × (F ∖ {0})`, the Thom map `a ↦ π^*a ⌣ δ σ` of the
product bundle sends `a ∈ Hᵖ(B; M)` to `(-1)^(p (d + 1)) δ (σ ⌣ π^*a)`, the image of `a` under the
equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` up to that sign. -/
theorem pullbackCup_prodThomPair_singularCohomologyδ (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    {p m : ℕ} (h : p + (d + 1) = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          d (d + 1)) (prodThomPairPuncturedClass K B e)) a =
      ((-1 : ℤ) ^ (p * (d + 1))) •
        prodThomPairSingularCohomologySphereEquiv M B e p m (by lia) a := by
  rw [prodThomPairSingularCohomologySphereEquiv_apply]
  exact pullbackCup_prodThomPair_singularCohomologyδ_eq_smul M rfl rfl h _ a

end Sphere

/-! ### The Thom map of the class of the positive side in rank one -/

section Line

/-- **The Thom map of `δ σ` in rank one.** For a continuous linear equivalence `e : F ≃L[ℝ] ℝ¹`
and the class `σ = TauCeti.prodThomPairPuncturedLineClass` of the positive side of
`B × (F ∖ {0})`, the Thom map `a ↦ π^*a ⌣ δ σ` of the product line bundle sends `a ∈ Hᵖ(B; M)` to
`(-1)^p δ (σ ⌣ π^*a)`, the image of `a` under the equivalence
`TauCeti.prodThomPairSingularCohomologyLineEquiv` up to that sign. -/
theorem pullbackCup_prodThomPair_singularCohomologyδ_prodThomPairPuncturedLineClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) {p m : ℕ} (h : p + 1 = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          0 1) (prodThomPairPuncturedLineClass K B e)) a =
      ((-1 : ℤ) ^ p) • prodThomPairSingularCohomologyLineEquiv M B e p m h a := by
  rw [pullbackCup_prodThomPair_singularCohomologyδ_eq_smul M (zero_add 1) (zero_add p) h, mul_one,
    prodThomPairSingularCohomologyLineEquiv_apply]

end Line

/-! ### Rank zero -/

section RankZero

omit [NormedSpace ℝ F] in
/-- In rank `0` (`Subsingleton F`), `B × (F ∖ {0})` is empty, so the class in `H⁰(B × F, ∅; K)`
corresponding to `1 ∈ H⁰(B × F; K)` has a bijective Thom map in every degree and for every module
of coefficients. -/
private theorem exists_forall_bijective_pullbackCup_prodThomPair_of_subsingleton [Subsingleton F] :
    ∃ v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0,
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h v) := by
  have : IsEmpty (prodThomPair B F).snd := ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
  have hπ : ⇑(prodThomPairProj B F) = Prod.fst := funext (prodThomPairProj_apply F)
  have : IsIso (prodThomPairProj B F) := TopCat.isIso_of_bijective_of_isOpenMap _
    (hπ ▸ ⟨fun x y hxy ↦ Prod.ext hxy (Subsingleton.elim _ _), fun b ↦ ⟨(b, 0), rfl⟩⟩)
    (hπ ▸ isOpenMap_fst)
  refine ⟨inv ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0) (prodThomPair B F).fst.singularCohomologyZeroOne,
    fun M p m h ↦ TopPair.bijective_pullbackCup_of_isEmpty _ _ _ (fun x ↦ ?_) M h⟩
  rw [IsIso.inv_hom_id_apply, singularCohomologyZeroEval_singularCohomologyZeroOne]
  exact isUnit_one

end RankZero

/-! ### The Thom map of a general class -/

omit [NormedSpace ℝ F] in
/-- On the fibre over `b`, the class `π^*c ⌣ v` restricts to the value of `c` at `b` times the
restriction of `v`. -/
private theorem singularCohomologyMap_prodThomPairFiberMap_pullbackCup {r : ℕ} (b : B)
    (v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) r)
    (c : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0) :
    TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r
        ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) r 0 r
          (zero_add r) v c) =
      singularCohomologyZeroEval b c •
        TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r v := by
  have hg : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
      TopCat.const (X := (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).fst)
        (Y := TopCat.of B) b ≫ 𝟙 _ :=
    TopCat.ext fun x ↦
      (congrArg (prodThomPairProj B F) (prodThomPairFiberMap_fst_apply F b x)).trans
        (prodThomPairProj_apply F (b, x))
  rw [← TopPair.pullbackCup_naturality (prodThomPairFiberMap F b) _ (prodThomPairProj B F) (𝟙 _)
      hg, TopCat.singularCohomologyMap_id,
    ConcreteCategory.id_apply, TopPair.pullbackCup_apply,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul,
    LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def,
    TopPair.singularCup_constSingularCocycle_left K _ (η := 𝟙 _) (by monoidal) (by monoidal)]

/-- For every finite rank `r ≥ 0`, the product bundle has a class whose Thom map is bijective in
every degree and for every module of coefficients (`1` for `r = 0`, and `δ σ` for `r = d + 1`). -/
private theorem exists_forall_bijective_pullbackCup_prodThomPair [FiniteDimensional ℝ F] :
    ∃ v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
        (finrank ℝ F),
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h v) := by
  generalize hr : finrank ℝ F = r
  rcases r with _ | d
  · have : Subsingleton F := Module.finrank_zero_iff.1 hr
    exact exists_forall_bijective_pullbackCup_prodThomPair_of_subsingleton
  · obtain ⟨e⟩ : Nonempty (F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :=
      ⟨ContinuousLinearEquiv.ofFinrankEq (hr.trans finrank_euclideanSpace_fin.symm)⟩
    exact ⟨_, fun M p m h ↦ bijective_pullbackCup_prodThomPair_singularCohomologyδ M rfl rfl h _
      (prodThomPairSingularCohomologySphereEquiv M B e p m (by lia))
      (prodThomPairSingularCohomologySphereEquiv_apply M e p m (by lia))⟩

/-- **The Thom isomorphism for a product bundle.** Let `F` be a finite-dimensional real normed space
of dimension `r = finrank ℝ F ≥ 0`, and let `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restrict on the fibre
pair `(F, F ∖ {0})` over every point of `B` to a generator of the `K`-module `Hʳ(F, F ∖ {0}; K)`.
Then for every `K`-module `M` and every degree `p`, the Thom map
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^*a ⌣ u`, is bijective. -/
theorem bijective_pullbackCup_prodThomPair [FiniteDimensional ℝ F]
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h u) := by
  obtain ⟨v, hv⟩ := exists_forall_bijective_pullbackCup_prodThomPair (B := B) (F := F) (K := K)
  -- `u = π^*c ⌣ v` for a degree-zero class `c`, since the Thom map of `v` is onto in degree `0`.
  obtain ⟨c, rfl⟩ := (hv (ModuleCat.of K K) 0 _ (zero_add _)).2 u
  -- The values of `c` are units: on the fibre over `b`, `u` is `c(b)` times the restriction of
  -- `v`, and generates the local cohomology `Hʳ(F, F ∖ {0}; K) ≅ K`.
  have hc (b : B) : IsUnit (singularCohomologyZeroEval b c) := by
    have hb := congrArg (Submodule.map (singularCohomologyComplSingletonFinrankEquivSelf
      (ModuleCat.of K K) (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)).toLinearMap) (hu b)
    rw [Submodule.map_span, Set.image_singleton,
      singularCohomologyMap_prodThomPairFiberMap_pullbackCup, LinearEquiv.coe_toLinearMap,
      map_smul, Submodule.map_top, LinearEquiv.range] at hb
    exact isUnit_of_mul_isUnit_left (Ideal.span_singleton_eq_top.1 hb)
  obtain ⟨c', hcc', hc'c⟩ := exists_singularCup_eq_one c hc
  -- So the Thom map of `u` is that of `v` after the bijective cup product with `c`.
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h
      ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) _ 0 _
        (zero_add _) v c)) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h v) ∘ fun a ↦
        (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p rfl a c :=
    funext (TopPair.pullbackCup_pullbackCup _ _ (add_zero p) (zero_add _) h h v c)
  rw [hcomp]
  exact (hv M p m h).comp (bijective_singularCup_left_of_singularCup_eq_one hcc' hc'c M p)

/-- **The Thom map of `pr₂^* g` on a product bundle is bijective.** For any generator `g` of
`Hʳ(F, F ∖ {0}; K)`, `r = finrank ℝ F`, the map `a ↦ π^* a ⌣ pr₂^* g` is bijective from `Hᵖ(B; M)`
to `Hᵐ(B × F, B × (F ∖ {0}); M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair_snd [FiniteDimensional ℝ F]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)} (hg : Submodule.span K {g} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g)) :=
  bijective_pullbackCup_prodThomPair M _ (fun b ↦ by
    rw [← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
    exact hg) h

variable (B F) in
/-- **The Thom isomorphism for a product bundle**, bundled as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, for any fibrewise-generating class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` (`r = finrank ℝ F`). -/
def prodThomPairPullbackCupEquiv [FiniteDimensional ℝ F]
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M u hu h)

/-- `TauCeti.prodThomPairPullbackCupEquiv` applies `TopPair.pullbackCup` along
`TauCeti.prodThomPairProj`. -/
@[simp]
theorem prodThomPairPullbackCupEquiv_apply [FiniteDimensional ℝ F]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M B F p m h u hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a :=
  (rfl)

end TauCeti
