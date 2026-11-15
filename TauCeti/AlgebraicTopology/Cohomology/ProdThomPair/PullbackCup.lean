/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Linear
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for a product bundle

Let `K` be a commutative ring, `M` a `K`-module, `B` a topological space, and `F` a
finite-dimensional real normed space of dimension `r = finrank ℝ F`. For the product Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) and projection `π : B × F → B`
(`TauCeti.prodThomPairProj`), this file proves that `TopPair.pullbackCup`,
`a ↦ π^* a ⌣ u : Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)` (`p + r = m`), is bijective whenever
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restricts on every fibre `(F, F ∖ {0})`
(`TauCeti.prodThomPairFiberMap`) to a generator of `Hʳ(F, F ∖ {0}; K)`.

This upgrades the coordinate-dependent positive-rank calculation
`TauCeti.prodThomPairSingularCohomologySphereEquiv` (`c ↦ δ (σ ⌣ π₀^* c)`) from
`TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere` to `TopPair.pullbackCup` for arbitrary
fibrewise-generating classes `u` across all finite ranks `r ≥ 0`, providing the coordinate-free
local trivialization model for `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair` in
`TauCeti.Topology.VectorBundle.Thom.Isomorphism`.

## Main definitions and results

* `TauCeti.bijective_pullbackCup_prodThomPair_snd`: `a ↦ π^* a ⌣ pr₂^* g` is bijective for any
  generator `g` of `Hʳ(F, F ∖ {0}; K)`.
* `TauCeti.bijective_pullbackCup_prodThomPair`: `a ↦ π^* a ⌣ u` is bijective whenever `u`
  restricts to a generator on every fibre.
* `TauCeti.prodThomPairPullbackCupEquiv`: the `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)` given by `a ↦ π^* a ⌣ u`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §10, Lemma 10.3 and Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K]

section PositiveRank

variable (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ}

private theorem prodThomPairSingularCohomologySphereEquiv_eq_sign_pullbackCup
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p m : ℕ) (h : p + (d + 1) = m)
    (c : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairSingularCohomologySphereEquiv M B e p m h c =
      ((-1 : ℤ) ^ (p * d + p)) • (prodThomPair B F).pullbackCup M (prodThomPairProj B F)
        (d + 1) p m h (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
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
  -- `𝟙_ (ModuleCat K)` is definitionally `ModuleCat.of K K`.
  have hδ := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (add_comm p d) rfl (by omega) h
    (TopCat.singularCohomologyMap (prodThomPairProj B F) p c) (prodThomPairPuncturedClass K B e)
  rw [hcomm, map_zsmul, hδ, smul_smul, ← pow_add, TopPair.pullbackCup_apply]

private theorem bijective_pullbackCup_singularCohomologyδ_puncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p m : ℕ) (h : p + (d + 1) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)))) := by
  set Φ := (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
    (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)))
  have heq : (fun y ↦ ((-1 : ℤ) ^ (p * d + p)) • y) ∘ ⇑Φ =
      ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) :=
    funext fun c ↦ (prodThomPairSingularCohomologySphereEquiv_eq_sign_pullbackCup M e p m h c).symm
  exact (Function.Bijective.of_comp_iff'
    ((isUnit_neg_one (α := ℤ)).pow (p * d + p)).smul_bijective _).1
    (heq ▸ (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective)

private theorem exists_span_eq_top_and_pullback_eq_singularCohomologyδ_puncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1),
      Submodule.span K {g₀} = ⊤ ∧
        TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1) g₀ =
          ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
            (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K B e)) := by
  let u_pt := (prodThomPair PUnit.{w + 1} F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
    (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl (prodThomPairPuncturedClass K PUnit.{w + 1} e)
  let g₀ := TopPair.singularCohomologyMap (complZeroPairIsoProdThomPair F).hom (d + 1) u_pt
  have hspan_one : Submodule.span K
      {(TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne (k := K)} = ⊤ :=
    (singularCohomologyZeroEvalEquiv (X := TopCat.of PUnit.{w + 1}) PUnit.unit
      ).span_singleton_eq_top_iff_isUnit.2 (by simp)
  let E₁ := prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} K)) PUnit.{w + 1} e 0
    (d + 1)
  have hu_pt_eq : E₁ ((TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne (k := K)) = u_pt := by
    rw [TopCat.singularCohomologyZeroOne_def]
    exact prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle e
  let e₀ := ((TopPair.singularCohomologyFunctor (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
    (d + 1)).mapIso (complZeroPairIsoProdThomPair F).op).toLinearEquiv
  have hmap : prodThomPairSnd B F ≫ (complZeroPairIsoProdThomPair F).hom =
      prodThomPairMap F (ContinuousMap.const B PUnit.unit) :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
      (prodThomPairFiberMap_fst_apply F PUnit.unit _).trans
        ((congrArg (Prod.mk PUnit.unit) (prodThomPairSnd_fst_apply F p)).trans
          (prodThomPairMap_fst_apply F (ContinuousMap.const B PUnit.unit) p).symm))
  refine ⟨g₀, (e₀.span_singleton_apply_eq_top_iff (x := u_pt)).2
    (hu_pt_eq ▸ E₁.span_singleton_apply_eq_top_iff.2 hspan_one), ?_⟩
  dsimp [g₀, u_pt]
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp, hmap,
    ← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F (ContinuousMap.const B PUnit.unit))
      d (d + 1),
    ConcreteCategory.comp_apply,
    singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]

private theorem bijective_pullbackCup_prodThomPair_snd_of_equiv
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (p m : ℕ) (h : p + (d + 1) = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1)} (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1) g)) := by
  have : FiniteDimensional ℝ F := e.symm.toLinearEquiv.finiteDimensional
  have hfin : finrank ℝ F = d + 1 := by rw [e.toLinearEquiv.finrank_eq, finrank_euclideanSpace_fin]
  obtain ⟨g₀', hspan_g₀', hg₀'_pull⟩ :=
    exists_span_eq_top_and_pullback_eq_singularCohomologyδ_puncturedClass (B := B) (K := K) e
  let e_loc : _ ≃ₗ[K] K := (hfin ▸ singularCohomologyComplSingletonFinrankEquivSelf
    (ModuleCat.of K K) (OpenPartialHomeomorph.refl F) (x := (0 : F)) (by simp) :
    _ ≃ₗ[K] ModuleCat.of K K)
  obtain ⟨c, rfl⟩ := e_loc.exists_units_smul_eq_of_span_singleton_eq_top hspan_g₀' hg
  rw [map_smul, map_smul, hg₀'_pull, LinearMap.coe_smul, Pi.smul_def]
  exact c.isUnit.smul_bijective.comp
    (bijective_pullbackCup_singularCohomologyδ_puncturedClass M e p m h)

end PositiveRank

section RankZero

variable (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]

private theorem bijective_pullbackCup_prodThomPair_snd_of_subsingleton [Subsingleton F]
    (p m : ℕ) (h : p + 0 = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) 0} (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g)) := by
  obtain rfl : p = m := by omega
  let PF := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have : IsEmpty (prodThomPair B F).snd := ⟨fun p ↦ p.2 (Subsingleton.elim p.1.2 0)⟩
  have : IsEmpty PF.snd := ⟨fun q ↦ q.2 (Subsingleton.elim q.1 0)⟩
  have : PathConnectedSpace ↥PF.fst := inferInstanceAs (PathConnectedSpace F)
  let π_B := (prodThomPair B F).singularCohomologyπ (ModuleCat.of K K) K M p
  let π_F := PF.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
  have : IsIso (prodThomPairProj B F) :=
    ⟨ConcreteCategory.ofHom (C := TopCat.{w}) ⟨fun b ↦ (b, (0 : F)), by fun_prop⟩,
      TopCat.ext fun p ↦ Prod.ext (prodThomPairProj_apply F p) (Subsingleton.elim 0 p.2),
      TopCat.ext fun b ↦ prodThomPairProj_apply F (b, 0)⟩
  let e_F := (asIso π_F).toLinearEquiv.trans (singularCohomologyZeroEvalEquiv (X := PF.fst) (0 : F))
  have hc : IsUnit (e_F g) := e_F.span_singleton_eq_top_iff_isUnit.1 hg
  have hπF_g : π_F g = (hc.unit : K) • PF.fst.singularCohomologyZeroOne (k := K) := by
    rw [← singularCohomologyZeroEvalEquiv_symm_apply (X := PF.fst) (0 : F), hc.unit_spec]
    exact ((singularCohomologyZeroEvalEquiv (X := PF.fst) (0 : F)).symm_apply_apply (π_F g)).symm
  have hπB_pull : (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0 (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g) =
      (hc.unit : K) • ((prodThomPair B F).fst).singularCohomologyZeroOne (k := K) := by
    have hnat := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) 0) g
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [← hnat, hπF_g, map_smul, singularCohomologyMap_singularCohomologyZeroOne]
  have hcomp : ⇑π_B ∘ ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g)) =
      (fun y ↦ (hc.unit : K) • y) ∘ ⇑(TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
        (M := M) (prodThomPairProj B F) p).hom := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, TopPair.pullbackCup_apply,
      TopPair.singularCohomologyπ_singularCup]
    refine (congrArg _ hπB_pull).trans ?_
    rw [map_smul, TopCat.singularCohomologyZeroOne_def]
    exact congrArg ((hc.unit : K) • ·) (TopCat.singularCup_constSingularCocycle_right _ K (η := 𝟙 _)
      (by monoidal) (by monoidal) h _)
  have hbij_proj : Function.Bijective (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := M) (prodThomPairProj B F) p).hom :=
    ((singularCohomologyFunctor (ModuleCat.of K K) K M p).mapIso
      (asIso (prodThomPairProj B F)).op).toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff' (asIso π_B).toLinearEquiv.bijective _).1
    (hcomp ▸ hc.unit.isUnit.smul_bijective.comp hbij_proj)

end RankZero

variable (M : ModuleCat.{w} K) {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The Thom map of `pr₂^* g` on a product bundle is bijective.** For any generator `g` of
`Hʳ(F, F ∖ {0}; K)`, `r = finrank ℝ F`, the map `a ↦ π^* a ⌣ pr₂^* g` is bijective from `Hᵖ(B; M)`
to `Hᵐ(B × F, B × (F ∖ {0}); M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair_snd (p m : ℕ) (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)} (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g)) := by
  generalize hr : finrank ℝ F = r at h g hg ⊢
  rcases r with _ | d
  · have : Subsingleton F := Module.finrank_zero_iff.1 hr
    exact bijective_pullbackCup_prodThomPair_snd_of_subsingleton M p m h hg
  · exact bijective_pullbackCup_prodThomPair_snd_of_equiv M
      (ContinuousLinearEquiv.ofFinrankEq (hr.trans finrank_euclideanSpace_fin.symm)) p m h hg

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem singularCohomologyMap_prodThomPairFiberMap_pullbackCup_snd_zero
    (b : B) {r : ℕ} (h : 0 + r = r)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) r)
    (φ : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0) :
    TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r
        ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) r 0 r h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) r g) φ) =
      singularCohomologyZeroEval b φ • g := by
  let PF := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have hfib_proj : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
      TopCat.const (X := PF.fst) b ≫ 𝟙 (TopCat.of B) := by
    rw [Category.comp_id]
    exact TopCat.ext fun x ↦ (congrArg (prodThomPairProj B F)
      (prodThomPairFiberMap_fst_apply F b x)).trans ((prodThomPairProj_apply F (b, x)).trans
        (TopCat.const_apply (X := PF.fst) (Y := TopCat.of B) b x).symm)
  have hfib := TopPair.pullbackCup_naturality (prodThomPairFiberMap F b)
    (TopCat.const (X := PF.fst) b) (prodThomPairProj B F) (𝟙 (TopCat.of B)) hfib_proj h
    (TopPair.singularCohomologyMap (prodThomPairSnd B F) r g) φ
  rw [TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply] at hfib
  rw [← hfib, ← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyMap_comp,
    prodThomPairFiberMap_comp_prodThomPairSnd, TopPair.singularCohomologyMap_id,
    ConcreteCategory.id_apply, TopPair.pullbackCup_apply,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul,
    LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
  exact congrArg (singularCohomologyZeroEval b φ • ·)
    (TopPair.singularCup_constSingularCocycle_left K _ (η := 𝟙 _) (by monoidal) (by monoidal) h g)

/-- **The Thom isomorphism for a product bundle.** If `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)`
(`r = finrank ℝ F`) restricts on every fibre `(F, F ∖ {0})` (`TauCeti.prodThomPairFiberMap`) to a
`K`-module generator of `Hʳ(F, F ∖ {0}; K)`, then `a ↦ π^* a ⌣ u` is bijective from `Hᵖ(B; M)` to
`Hᵐ(B × F, B × (F ∖ {0}); M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u)} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g, hg⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (x := (0 : F)) (by simp)
  let ug := TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g
  obtain ⟨φ, hφ⟩ := (bijective_pullbackCup_prodThomPair_snd (ModuleCat.of K K) 0 (finrank ℝ F)
    (zero_add _) hg).2 u
  let e_loc := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
    (OpenPartialHomeomorph.refl F) (x := (0 : F)) (by simp)
  -- Restricting `u = π^* φ ⌣ pr₂^* g` to the fibre over `b` shows `φ(b) ∈ Kˣ`.
  have hφ_unit (b : B) : IsUnit (singularCohomologyZeroEval b φ) := by
    have htop := hu b
    rw [← hφ, singularCohomologyMap_prodThomPairFiberMap_pullbackCup_snd_zero] at htop
    exact isUnit_of_mul_isUnit_left (by
      simpa [map_smul, smul_eq_mul] using e_loc.span_singleton_eq_top_iff_isUnit.1 htop)
  have hfac : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h ug) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p
          (add_zero p) a φ := by
    funext a
    rw [Function.comp_apply, ← hφ, TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
      TopPair.pullbackCup_apply, ← TopCat.singularCup_naturality]
    exact (TopPair.singularCup_assoc K (prodThomPair B F) (by monoidal) (by monoidal)
      (add_zero p) h (zero_add (finrank ℝ F)) h _ _ _).symm
  rw [hfac]
  exact (bijective_pullbackCup_prodThomPair_snd M p m h hg).comp
    (bijective_singularCup_right_of_forall_isUnit M p hφ_unit)

variable (B F) in
/-- **The Thom isomorphism for a product bundle**, bundled as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, for any fibrewise-generating class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` (`r = finrank ℝ F`). -/
def prodThomPairPullbackCupEquiv (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u)} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M p m h hu)

/-- `TauCeti.prodThomPairPullbackCupEquiv` applies `TopPair.pullbackCup` along
`TauCeti.prodThomPairProj`. -/
@[simp]
theorem prodThomPairPullbackCupEquiv_apply (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {(TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u)} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M B F p m h u hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a := (rfl)

end TauCeti
