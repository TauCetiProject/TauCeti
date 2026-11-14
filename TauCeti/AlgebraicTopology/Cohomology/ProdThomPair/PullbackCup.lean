/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Linear
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for a product bundle

Let `K` be a commutative ring, `M` a `K`-module, `B` a topological space, and `F` a
finite-dimensional real normed space of dimension `r = finrank ℝ F`. For the Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) and the projection `π : B × F → B`
(`TauCeti.prodThomPairProj`), this file proves that the pullback-cup map

`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^* a ⌣ u`,  `p + r = m`,

(`TopPair.pullbackCup`) is bijective whenever `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restricts on every
fibre pair `(F, F ∖ {0})` (`TauCeti.prodThomPairFiberMap`) to a `K`-module generator of
`Hʳ(F, F ∖ {0}; K)` (`TauCeti.bijective_pullbackCup_prodThomPair`, bundled as
`TauCeti.prodThomPairPullbackCupEquiv`).

## Proof outline

1. **Positive rank via the sphere bundle.** When `e : F ≃L[ℝ] ℝᵈ⁺¹`, the equivalence
   `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends `a ∈ Hᵖ(B; M)` to `δ (σ ⌣ π₀^* a)`,
   where `σ ∈ Hᵈ(B × (F ∖ {0}); K)` is `TauCeti.prodThomPairPuncturedClass`. Graded commutativity
   (`TopCat.singularCup_gradedComm`) and the module property of the connecting morphism
   (`TopPair.singularCohomologyδ_singularCup`) identify `δ (σ ⌣ π₀^* a)` up to the sign
   `(-1)^(p d + p)` with `π^* a ⌣ δ σ`, proving bijectivity for `u₀ = δ σ`. Naturality along
   `B → PUnit` shows `u₀ = pr₂^* g₀` for a generator `g₀` of `Hᵈ⁺¹(F, F ∖ {0}; K)`, and any two
   generators of `Hᵈ⁺¹(F, F ∖ {0}; K) ≃ₗ[K] K` differ by a unit of `K`.
2. **Rank zero.** When `F` is zero-dimensional, `B × (F ∖ {0})` is empty, so relative cohomology
   agrees with absolute cohomology (`TopPair.isIso_singularCohomologyπ_of_isEmpty`), `π` is an
   isomorphism, and `pr₂^* g` acts as multiplication by a unit of `K`.
3. **General fibrewise-generating classes.** Fix a generator `g ∈ Hʳ(F, F ∖ {0}; K)`. Surjectivity
   of `φ ↦ π^* φ ⌣ pr₂^* g` in base degree `0` writes any `u` as `π^* φ ⌣ pr₂^* g` with
   `φ ∈ H⁰(B; K)`. Restricting to the fibre over `b : B` gives `φ(b) • g`, so `φ(b)` is a unit of
   `K` at every point `b`, hence `φ` is a cup-product unit in `H⁰(B; K)`
   (`TauCeti.exists_singularCup_eq_one`). Associativity (`TopPair.singularCup_assoc`) factors the
   map for `u` as `a ↦ a ⌣ φ` followed by the map for `pr₂^* g`.

## Main definitions and results

* `TauCeti.bijective_pullbackCup_prodThomPair_snd`: `a ↦ π^* a ⌣ pr₂^* g` is bijective for any
  generator `g` of `Hʳ(F, F ∖ {0}; K)`.
* `TauCeti.bijective_pullbackCup_prodThomPair`: `a ↦ π^* a ⌣ u` is bijective whenever `u`
  restricts to a generator on every fibre.
* `TauCeti.prodThomPairPullbackCupEquiv`: the `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)` given by `a ↦ π^* a ⌣ u`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §10, Lemma 10.3 and Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K]

/-! ### Generators of rank-one free modules -/

private lemma isUnit_of_span_eq_top {L : Type*} [AddCommGroup L] [Module K L] (e : L ≃ₗ[K] K)
    {x : L} (hx : Submodule.span K {x} = ⊤) : IsUnit (e x) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hx.symm ▸ Submodule.mem_top (x := e.symm 1))
  exact IsUnit.of_mul_eq_one_right c (by simpa [map_smul, smul_eq_mul] using congrArg e hc)

private lemma exists_isUnit_smul_eq_of_span_eq_top {L : Type*} [AddCommGroup L] [Module K L]
    (e : L ≃ₗ[K] K) {g g' : L} (hg : Submodule.span K {g} = ⊤)
    (hg' : Submodule.span K {g'} = ⊤) : ∃ u : Kˣ, (u : K) • g = g' := by
  have hu : IsUnit (e g) := isUnit_of_span_eq_top e hg
  have hu' : IsUnit (e g') := isUnit_of_span_eq_top e hg'
  refine ⟨hu'.unit * hu.unit⁻¹, e.injective ?_⟩
  simp [map_smul, smul_eq_mul, mul_assoc]

private lemma bijective_units_smul {L₁ L₂ : Type*} [AddCommGroup L₁] [Module K L₁]
    [AddCommGroup L₂] [Module K L₂] (u : Kˣ) {f : L₁ →ₗ[K] L₂} (hf : Function.Bijective f) :
    Function.Bijective ((u : K) • f) := by
  have hperm : Function.Bijective (fun y : L₂ ↦ (u : K) • y) :=
    ⟨fun x y h ↦ by simpa [smul_smul] using congrArg ((↑u⁻¹ : K) • ·) h,
      fun y ↦ ⟨(↑u⁻¹ : K) • y, by simp [smul_smul]⟩⟩
  exact hperm.comp hf

/-! ### Positive rank via the punctured sphere bundle -/

section PositiveRank

variable (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ}

/-- For `e : F ≃L[ℝ] ℝᵈ⁺¹`, `TauCeti.prodThomPairSingularCohomologySphereEquiv` agrees up to the
Koszul sign `(-1)^(p d + p)` with `TopPair.pullbackCup` for `δ σ`. -/
private theorem prodThomPairSingularCohomologySphereEquiv_eq_sign_pullbackCup
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p m : ℕ) (h : p + (d + 1) = m)
    (c : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairSingularCohomologySphereEquiv M B e p m h c =
      ((-1 : ℤ) ^ (p * d + p)) •
        (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
          (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
            (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e))) c := by
  rw [prodThomPairSingularCohomologySphereEquiv_apply, ← map_comp_prodThomPairProj,
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  have hcomm := (prodThomPair B F).snd.singularCup_gradedComm K
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
    (braiding_leftUnitor M) (add_comm p d)
    (TopCat.singularCohomologyMap (prodThomPair B F).map p
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p c))
    (prodThomPairPuncturedClass K B e)
  -- `𝟙_ (ModuleCat K)` is `ModuleCat.of K K` by definition of the monoidal structure on
  -- `ModuleCat K`.
  have hδ := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (add_comm p d) rfl (by omega) h
    (TopCat.singularCohomologyMap (prodThomPairProj B F) p c)
    (prodThomPairPuncturedClass K B e)
  rw [hcomm, map_zsmul, hδ, smul_smul, ← pow_add, TopPair.pullbackCup_apply]

private theorem bijective_pullbackCup_singularCohomologyδ_puncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p m : ℕ) (h : p + (d + 1) = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
          (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)))) := by
  let z : ℤ := (-1) ^ (p * d + p)
  have hz : z * z = 1 := by
    dsimp [z]
    rw [← mul_pow]
    norm_num
  have hinv : Function.Bijective (fun y : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K M m ↦ z • y) :=
    Function.Involutive.bijective fun y ↦ by rw [smul_smul, hz, one_smul]
  have heq : (fun y ↦ z • y) ∘ ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
      (d + 1) p m h (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)))) =
      ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) :=
    funext fun c ↦ (prodThomPairSingularCohomologySphereEquiv_eq_sign_pullbackCup M e p m h c).symm
  exact (Function.Bijective.of_comp_iff' hinv _).1
    (heq ▸ (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective)

private theorem exists_span_eq_top_and_pullback_eq_singularCohomologyδ_puncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1),
      Submodule.span K {g₀} = ⊤ ∧
        TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1) g₀ =
          ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
            (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)) := by
  let u_pt : (prodThomPair PUnit.{w + 1} F).singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 1) :=
    ((prodThomPair PUnit.{w + 1} F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K PUnit.{w + 1} e))
  let g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 1) :=
    TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).hom (d + 1) u_pt
  have hspan_one : Submodule.span K
      {(TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne (k := K)} = ⊤ :=
    Submodule.eq_top_iff'.2 fun x ↦ Submodule.mem_span_singleton.2
      ⟨singularCohomologyZeroEval PUnit.unit x,
        (eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne PUnit.unit x).symm⟩
  have hu_pt_eq : (prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} K)) PUnit.{w + 1}
      e 0 (d + 1)) ((TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne (k := K)) = u_pt := by
    rw [TopCat.singularCohomologyZeroOne_def]
    exact prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle e
  have hspan_g₀ : Submodule.span K {g₀} = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun y ↦ ?_
    let E₁ := prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} K)) PUnit.{w + 1}
      e 0 (d + 1)
    let y' := TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).inv (d + 1) y
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (hspan_one.symm ▸ Submodule.mem_top (x := E₁.symm y'))
    refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
    have hc' : c • u_pt = y' := by
      simpa [E₁, map_smul, hu_pt_eq] using congrArg E₁ hc
    have hy :
        TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).hom (d + 1) y' = y := by
      simp [y', ← TopPair.singularCohomologyMap_comp_apply]
    exact (map_smul
      (TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).hom (d + 1)).hom c
      u_pt).symm.trans ((congrArg
        (TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).hom (d + 1)) hc').trans hy)
  have hg₀_pull : TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1) g₀ =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)) := by
    have hmap : prodThomPairSnd B F ≫ (complZeroPairIsoProdThomPair F).hom =
        prodThomPairMap F (ContinuousMap.const B PUnit.unit) :=
      TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
        (prodThomPairFiberMap_fst_apply F PUnit.unit _).trans
          ((congrArg (Prod.mk PUnit.unit) (prodThomPairSnd_fst_apply F p)).trans
            (prodThomPairMap_fst_apply F (ContinuousMap.const B PUnit.unit) p).symm))
    dsimp [g₀, u_pt]
    rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, hmap,
      ← ConcreteCategory.comp_apply,
      TopPair.singularCohomologyδ_naturality (prodThomPairMap F (ContinuousMap.const B PUnit.unit))
        d (d + 1),
      ConcreteCategory.comp_apply,
      singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
  exact ⟨g₀, hspan_g₀, hg₀_pull⟩

private theorem bijective_pullbackCup_prodThomPair_snd_of_equiv
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p m : ℕ) (h : p + (d + 1) = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
        (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1) g)) := by
  have : FiniteDimensional ℝ F := e.symm.toLinearEquiv.finiteDimensional
  have hfin : finrank ℝ F = d + 1 := by
    rw [e.toLinearEquiv.finrank_eq, finrank_euclideanSpace_fin]
  obtain ⟨g₀', hspan_g₀', hg₀'_pull⟩ :=
    exists_span_eq_top_and_pullback_eq_singularCohomologyδ_puncturedClass (B := B) (K := K) e
  let e_loc : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1) ≃ₗ[K] K :=
    (hfin ▸ singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (x := (0 : F)) (by simp) :
      (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1) ≃ₗ[K] ModuleCat.of K K)
  obtain ⟨c, rfl⟩ := exists_isUnit_smul_eq_of_span_eq_top e_loc hspan_g₀' hg
  rw [map_smul, map_smul, hg₀'_pull]
  exact bijective_units_smul c (bijective_pullbackCup_singularCohomologyδ_puncturedClass M e p m h)

end PositiveRank

/-! ### Rank zero -/

section RankZero

variable (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F]

private theorem bijective_pullbackCup_prodThomPair_snd_of_subsingleton [Subsingleton F]
    (p m : ℕ) (h : p + 0 = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) 0}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
        (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g)) := by
  obtain rfl : p = m := by omega
  let PF := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have : IsEmpty (prodThomPair B F).snd := ⟨fun p ↦ p.2 (Subsingleton.elim p.1.2 0)⟩
  have : IsEmpty PF.snd := ⟨fun q ↦ q.2 (Subsingleton.elim q.1 0)⟩
  have : PathConnectedSpace ↥PF.fst := inferInstanceAs (PathConnectedSpace F)
  let z₀ : ↥PF.fst := (0 : F)
  let π_B := (prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K M p
  let π_F := PF.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
  let s : TopCat.of B ⟶ (prodThomPair B F).fst :=
    ConcreteCategory.ofHom (C := TopCat.{w}) ⟨fun b ↦ (b, (0 : F)), by fun_prop⟩
  have hproj_iso : IsIso (prodThomPairProj B F) :=
    ⟨s,
      TopCat.ext fun p ↦ Prod.ext (prodThomPairProj_apply F p) (Subsingleton.elim 0 p.2),
      TopCat.ext fun b ↦ prodThomPairProj_apply F (b, 0)⟩
  -- Identify `π_F g ∈ H⁰(F; K)` with `c • 1` for a unit `c : Kˣ`.
  let ev_F : PF.fst.singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0 ≃ₗ[K] K :=
    LinearEquiv.ofLinearMap
      (f := singularCohomologyZeroEval z₀)
      (g := LinearMap.toSpanSingleton K _ (PF.fst.singularCohomologyZeroOne (k := K)))
      (LinearMap.ext fun c ↦ by simp)
      (LinearMap.ext fun x ↦ by
        dsimp
        exact (eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne z₀ x).symm)
  let e_F := (asIso π_F).toLinearEquiv.trans ev_F
  have hc : IsUnit (e_F g) := isUnit_of_span_eq_top e_F hg
  have hπF_g : π_F g = (hc.unit : K) • PF.fst.singularCohomologyZeroOne (k := K) := by
    rw [hc.unit_spec]
    exact eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne z₀ (π_F g)
  have hπB_pull : (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0 (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g) =
      (hc.unit : K) • ((prodThomPair B F).fst).singularCohomologyZeroOne (k := K) := by
    have hnat := ConcreteCategory.congr_hom
      (TopPair.singularCohomologyπ_naturality (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
        (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) 0) g
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [← hnat, hπF_g, map_smul, singularCohomologyMap_singularCohomologyZeroOne]
  -- Compose `pullbackCup` with the isomorphism `π_B : Hᵖ(B × F, ∅; M) ≅ Hᵖ(B × F; M)`.
  have hcomp : ⇑π_B ∘ ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g)) =
      ⇑((hc.unit : K) • (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
        (M := M) (prodThomPairProj B F) p).hom) := by
    funext a
    dsimp only [Function.comp_apply]
    rw [TopPair.pullbackCup_apply, TopPair.singularCohomologyπ_singularCup]
    refine Eq.trans (congrArg _ hπB_pull) ?_
    rw [map_smul, LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
    exact congrArg ((hc.unit : K) • ·)
      (TopCat.singularCup_constSingularCocycle_right _ K (η := 𝟙 _)
        (by monoidal) (by monoidal) h _)
  have hbij_proj : Function.Bijective
      (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
        (prodThomPairProj B F) p).hom :=
    ((singularCohomologyFunctor (ModuleCat.of K K) K M p).mapIso
      (asIso (prodThomPairProj B F)).op).toLinearEquiv.bijective
  have hbij_πB : Function.Bijective π_B := (asIso π_B).toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff' hbij_πB _).1
    (hcomp ▸ bijective_units_smul hc.unit hbij_proj)

end RankZero

/-! ### General finite-dimensional fibre and fibrewise-generating classes -/

variable (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem bijective_pullbackCup_prodThomPair_snd_aux (r p m : ℕ)
    (hr : finrank ℝ F = r) (h : p + r = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) r}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
        (TopPair.singularCohomologyMap (prodThomPairSnd B F) r g)) := by
  rcases r with _ | d
  · have : Subsingleton F := Module.finrank_zero_iff.1 hr
    exact bijective_pullbackCup_prodThomPair_snd_of_subsingleton M p m h hg
  · let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
      ContinuousLinearEquiv.ofFinrankEq (hr.trans finrank_euclideanSpace_fin.symm)
    exact bijective_pullbackCup_prodThomPair_snd_of_equiv M e p m h hg

/-- **The Thom map of `pr₂^* g` on a product bundle is bijective.** For any generator `g` of
`Hʳ(F, F ∖ {0}; K)`, `r = finrank ℝ F`, the map `a ↦ π^* a ⌣ pr₂^* g` is bijective from `Hᵖ(B; M)`
to `Hᵐ(B × F, B × (F ∖ {0}); M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair_snd (p m : ℕ) (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
        (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g)) :=
  bijective_pullbackCup_prodThomPair_snd_aux M (finrank ℝ F) p m rfl h hg

private theorem bijective_singularCup_right_of_forall_isUnit (p : ℕ)
    {φ : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0}
    (hφ : ∀ b : B, IsUnit (singularCohomologyZeroEval b φ)) :
    Function.Bijective (fun a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ↦
      (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
        (add_zero p) a φ) := by
  obtain ⟨ψ, hφψ, hψφ⟩ := exists_singularCup_eq_one φ hφ
  let rcup (θ : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0)
      (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p :=
    (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p) a θ
  have hrcup_comp (θ₁ θ₂ : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0)
      (hθ : (TopCat.of B).singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl θ₁ θ₂ =
        (TopCat.of B).singularCohomologyZeroOne)
      (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
      rcup θ₂ (rcup θ₁ a) = a := by
    dsimp [rcup]
    calc (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p)
          ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
            (add_zero p) a θ₁) θ₂
      _ = (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
            (add_zero p) a
            ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
              (λ_ (𝟙_ (ModuleCat.{w} K))).hom 0 0 0 rfl θ₁ θ₂) :=
        (TopCat.of B).singularCup_assoc K (by monoidal) (by monoidal)
          (add_zero p) (add_zero p) rfl (add_zero p) a θ₁ θ₂
      _ = a := by
        rw [hθ, TopCat.singularCohomologyZeroOne_def]
        exact (TopCat.of B).singularCup_constSingularCocycle_right K (η := 𝟙 _)
          (by monoidal) (by monoidal) (add_zero p) a
  exact ⟨Function.LeftInverse.injective (hrcup_comp φ ψ hφψ),
    Function.RightInverse.surjective (hrcup_comp ψ φ hψφ)⟩

/-- **The Thom isomorphism for a product bundle.** Let `F` be a finite-dimensional real normed
space of dimension `r = finrank ℝ F`, and let `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restrict on every
fibre pair `(F, F ∖ {0})` (`TauCeti.prodThomPairFiberMap`) to a `K`-module generator of
`Hʳ(F, F ∖ {0}; K)`. Then for every `K`-module `M` and `p + r = m`, the pullback-cup map
`a ↦ π^* a ⌣ u` is bijective from `Hᵖ(B; M)` to `Hᵐ(B × F, B × (F ∖ {0}); M)`. -/
theorem bijective_pullbackCup_prodThomPair (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B,
      Submodule.span K {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b)
        (finrank ℝ F) u)} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g, hg⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (x := (0 : F)) (by simp)
  let ug := TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g
  obtain ⟨φ, hφ⟩ := (bijective_pullbackCup_prodThomPair_snd (ModuleCat.of K K) 0 (finrank ℝ F)
    (zero_add _) hg).2 u
  have hφ_unit : ∀ b : B, IsUnit (singularCohomologyZeroEval b φ) := by
    intro b
    let PF := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
    have hfib_proj : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
        TopCat.const (X := PF.fst) b ≫ 𝟙 (TopCat.of B) := by
      rw [Category.comp_id]
      exact TopCat.ext fun x ↦
        (congrArg (prodThomPairProj B F) (prodThomPairFiberMap_fst_apply F b x)).trans
          ((prodThomPairProj_apply F (b, x)).trans
            (TopCat.const_apply (X := PF.fst) (Y := TopCat.of B) b x).symm)
    have hfib := TopPair.pullbackCup_naturality (prodThomPairFiberMap F b)
      (TopCat.const (X := PF.fst) b) (prodThomPairProj B F) (𝟙 (TopCat.of B)) hfib_proj
      (zero_add (finrank ℝ F)) ug φ
    rw [TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply, hφ] at hfib
    have hug_fib :
        TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) ug = g := by
      dsimp [ug]
      rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
        prodThomPairFiberMap_comp_prodThomPairSnd, TopPair.singularCohomologyMap_id,
        ConcreteCategory.id_apply]
    have hval : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u =
        singularCohomologyZeroEval b φ • g := by
      rw [← hfib, hug_fib, TopPair.pullbackCup_apply,
        singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul,
        LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
      exact congrArg (singularCohomologyZeroEval b φ • ·)
        (TopPair.singularCup_constSingularCocycle_left K _ (η := 𝟙 _)
          (by monoidal) (by monoidal) (zero_add _) g)
    let e_loc := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (x := (0 : F)) (by simp)
    have htop : Submodule.span K {singularCohomologyZeroEval b φ • g} = ⊤ := hval ▸ hu b
    have hprod : IsUnit (singularCohomologyZeroEval b φ * (e_loc g : K)) := by
      simpa [map_smul, smul_eq_mul] using isUnit_of_span_eq_top e_loc htop
    exact isUnit_of_mul_isUnit_left hprod
  have hfac : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h ug) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
          (add_zero p) a φ := by
    funext a
    dsimp only [Function.comp_apply]
    rw [← hφ, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
      ← TopCat.singularCup_naturality]
    exact (TopPair.singularCup_assoc K (prodThomPair B F) (by monoidal) (by monoidal)
      (add_zero p) h (zero_add (finrank ℝ F)) h _ _ _).symm
  rw [hfac]
  exact (bijective_pullbackCup_prodThomPair_snd M p m h hg).comp
    (bijective_singularCup_right_of_forall_isUnit M p hφ_unit)

variable (B F) in
/-- **The Thom isomorphism for a product bundle**, bundled as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, for any class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` (`r = finrank ℝ F`) whose restriction to every fibre spans
`Hʳ(F, F ∖ {0}; K)`. -/
def prodThomPairPullbackCupEquiv (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B,
      Submodule.span K {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b)
        (finrank ℝ F) u)} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M p m h hu)

/-- `TauCeti.prodThomPairPullbackCupEquiv` applies `TopPair.pullbackCup` along `prodThomPairProj`.
-/
@[simp]
theorem prodThomPairPullbackCupEquiv_apply (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B,
      Submodule.span K {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b)
        (finrank ℝ F) u)} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M B F p m h u hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a :=
  (rfl)

end TauCeti
