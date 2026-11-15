/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space and `F` a finite-dimensional real normed space of dimension
`r ≥ 2`. The product bundle `B × F → B` has Thom pair `(B × F, B × (F ∖ {0}))`
(`TauCeti.prodThomPair`) and projection `π : B × F → B` (`TauCeti.prodThomPairProj`). For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` with coefficients in a commutative ring `K`, the map

`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^*a ⌣ u`

(`TopPair.pullbackCup`) is the Thom map of `u`. This file proves that it is bijective in every
degree and for every module of coefficients `M` as soon as `u` restricts on the fibre pair
`(F, F ∖ {0})` over every point to a generator of `Hʳ(F, F ∖ {0}; K) ≅ K`
(`TauCeti.bijective_pullbackCup_prodThomPair`). This is the Thom isomorphism over a single
trivializing open set, the case that the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union` extends to unions of trivializing open sets. The
ranks `0` and `1`, where `F ∖ {0}` is empty or has two components, are not treated here: the
cohomology of `B × (F ∖ {0})` used below is computed from that of a sphere of positive dimension.

The proof first treats the class `δ σ`, where `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); K)` is pulled back from the
generator of the cohomology of the sphere (`TauCeti.prodThomPairPuncturedClass`) and `δ` is the
connecting morphism of the pair. The connecting morphism is linear over the cohomology of
`B × F` up to sign (`TopPair.singularCohomologyδ_singularCup`), and the cup product is graded
commutative (`TopCat.singularCup_gradedComm`), so

`π^*a ⌣ δ σ = (-1)^(p r) δ (σ ⌣ π^*a)`

for `a` of degree `p` (`TauCeti.pullbackCup_prodThomPair_singularCohomologyδ`). The right-hand
side is, up to that sign, the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv`
computed from the cohomology of `Sʳ⁻¹ × B`, so the Thom map of `δ σ` is bijective.

A general class `u` is then `π^*c ⌣ δ σ` for a unique `c ∈ H⁰(B; K)`. Restricted to the fibre over
`b`, it is the value `c(b)` times the restriction of `δ σ`; since `Hʳ(F, F ∖ {0}; K)` is one copy
of `K`, it can only generate if `c(b)` is a unit. A degree-zero class whose values are units is a
unit for the cup product (`TauCeti.exists_singularCup_eq_one`), and the Thom map of `u` is that of
`δ σ` composed with the cup product by `c`, which is then bijective.

## Main results

* `TauCeti.pullbackCup_prodThomPair_singularCohomologyδ`: the Thom map of `δ σ` is, up to the sign
  `(-1)^(p r)`, the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv`.
* `TauCeti.bijective_pullbackCup_prodThomPair`: **the Thom isomorphism for a product bundle** of
  rank at least `2`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof, which starts from the product case.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle and then by Mayer–Vietoris).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The Thom map of the class pulled back from the sphere -/

section Sphere

variable {d : ℕ}

/-- **The Thom map of `δ σ`.** For a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²` and the class
`σ = TauCeti.prodThomPairPuncturedClass` of `B × (F ∖ {0})`, the Thom map `a ↦ π^*a ⌣ δ σ` of the
product bundle sends `a ∈ Hᵖ(B; M)` to `(-1)^(p (d + 2)) δ (σ ⌣ π^*a)`, the image of `a` under the
equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` up to that sign. -/
theorem pullbackCup_prodThomPair_singularCohomologyδ (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    {p m : ℕ} (h : p + (d + 2) = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e)) a =
      ((-1 : ℤ) ^ (p * (d + 2))) •
        prodThomPairSingularCohomologySphereEquiv M B e p m (by lia) a := by
  -- The connecting morphism moves the cup product with `π^*a` past `δ`, up to `(-1)ᵖ`.
  have hδ := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (p := p) (q := d + 1) (n := d + 1 + p)
    (q' := d + 2) (m := m) (by lia) rfl (by lia) h
    (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) (prodThomPairPuncturedClass K B e)
  -- Graded commutativity exchanges `π^*a` and `σ`, up to `(-1)^(p (d + 1))`.
  have hcomm := TopCat.singularCup_gradedComm (prodThomPair B F).snd K
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) (braiding_leftUnitor M) (p := p) (q := d + 1)
    (n := d + 1 + p) (by lia)
    (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)
    (prodThomPairPuncturedClass K B e)
  rw [← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
    at hcomm
  rw [prodThomPairSingularCohomologySphereEquiv_apply, ← map_comp_prodThomPairProj,
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hcomm, map_zsmul, hδ,
    smul_smul, TopPair.pullbackCup_apply, smul_smul, ← pow_add, ← pow_add,
    Even.neg_one_pow ⟨p * (d + 2), by ring⟩, one_smul]

/-- The Thom map of `δ σ` is bijective in every degree, since it is the equivalence
`TauCeti.prodThomPairSingularCohomologySphereEquiv` up to a sign. -/
private theorem bijective_pullbackCup_prodThomPair_singularCohomologyδ
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) {p m : ℕ} (h : p + (d + 2) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) := by
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) =
      (((-1 : ℤ) ^ (p * (d + 2))) • ·) ∘ prodThomPairSingularCohomologySphereEquiv M B e p m
        (by lia) :=
    funext (pullbackCup_prodThomPair_singularCohomologyδ M e h)
  rw [hcomp]
  refine Function.Involutive.bijective (fun x ↦ ?_) |>.comp (LinearEquiv.bijective _)
  rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

end Sphere

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

/-- In rank at least `2` the product bundle has a class whose Thom map is bijective in every
degree and for every module of coefficients: the class `δ σ`. -/
private theorem exists_forall_bijective_pullbackCup_prodThomPair (hF : 2 ≤ finrank ℝ F) :
    ∃ v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
        (finrank ℝ F),
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h v) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by lia)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hF
  obtain ⟨e⟩ : Nonempty (F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hd])⟩
  generalize finrank ℝ F = r at hd ⊢
  subst hd
  exact ⟨_, fun M p m h ↦ bijective_pullbackCup_prodThomPair_singularCohomologyδ M e h⟩

/-- **The Thom isomorphism for a product bundle.** Let `F` be a real normed space of finite
dimension `r ≥ 2`, and let `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restrict on the fibre pair
`(F, F ∖ {0})` over every point of `B` to a generator of the `K`-module `Hʳ(F, F ∖ {0}; K)`.
Then for every `K`-module `M` and every degree `p`, the Thom map
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^*a ⌣ u`, is bijective. -/
theorem bijective_pullbackCup_prodThomPair (hF : 2 ≤ finrank ℝ F)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h u) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by lia)
  obtain ⟨v, hv⟩ := exists_forall_bijective_pullbackCup_prodThomPair (B := B) (K := K) hF
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
  exact (hv M p m h).comp (bijective_singularCup_right_of_singularCup_eq_one hcc' hc'c M p)

end TauCeti
