/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Line
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space, `F` a finite-dimensional real normed space of dimension `r`, `K` a
commutative ring and `M` a `K`-module. If `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restricts on the fibre
pair `(F, F ∖ {0})` over every point of `B` to a generator of `Hʳ(F, F ∖ {0}; K)`, then for every
base degree `p` and `m = p + r`, the map

`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^*a ⌣ u`,

(`TopPair.pullbackCup` along `TauCeti.prodThomPairProj`) is bijective
(`TauCeti.bijective_pullbackCup_prodThomPair`, bundled as
`TauCeti.prodThomPairPullbackCupEquiv`). This is the local case of the Thom isomorphism: over a
subset of the base set of a linear trivialization, a vector bundle is isomorphic to a product
bundle, and the Mayer–Vietoris step (`TopCat.bijective_pullbackCupRestrict_union`) glues these
local bijections across finite unions of trivializing open sets.

## Proof outline

1. For any relative class of the form `δ σ` with `σ ∈ H^q(B × (F ∖ {0}); K)` and `q + 1 = r`, the
   compatibility of the connecting morphism with the cup product
   (`TopPair.singularCohomologyδ_singularCup`) and graded commutativity on `B × (F ∖ {0})`
   (`TopCat.singularCup_gradedComm`) rewrite `π^*a ⌣ δ σ` as `(-1)^(p + p q) δ (σ ⌣ π₀^*a)`
   (`TauCeti.pullbackCup_prodThomPairProj_singularCohomologyδ_apply`).
2. We first construct a single reference class `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose pullback `u₀` along
   the fibre projection `B × F → F` has `a ↦ π^*a ⌣ u₀` bijective over every base `B`:
   * for `r = 0`, `F = {0}`, `B × (F ∖ {0})` is empty, so relative cohomology is isomorphic to
     absolute cohomology via `TopPair.singularCohomologyπ`, and cupping on the right with `1`
     reduces the map to pullback along the homeomorphism `B × F ≃ₜ B`;
   * for `r = 1`, `u₀ = δ σ` for `TauCeti.prodThomPairPuncturedLineClass` via `F ≃L[ℝ] ℝ`, and
     `TauCeti.prodThomPairSingularCohomologyLineEquiv` gives bijectivity;
   * for `r = d + 2`, `u₀ = δ σ` for `TauCeti.prodThomPairPuncturedClass` via `F ≃L[ℝ] ℝᵈ⁺²`, and
     `TauCeti.prodThomPairSingularCohomologySphereEquiv` gives bijectivity.
   Evaluating this bijectivity over `PUnit` in degree `0` shows that `g₀` generates
   `Hʳ(F, F ∖ {0}; K)`.
3. For a general fibrewise-generating class `u`, comparing `u|_b` with `g₀` via the local
   cohomology isomorphism `Hʳ(F, F ∖ {0}; K) ≃ₗ[K] K`
   (`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`) produces a unit `f(b) ∈ K` on each
   fibre with `u|_b = f(b) • g₀`. Homotopy invariance along paths in `B`
   (`TauCeti.singularCohomologyMap_prodThomPairFiberMap_eq_of_joined`) makes `f` constant on path
   components, so `f` is realized by a cup-invertible class `α ∈ H⁰(B; K)`
   (`TauCeti.exists_singularCohomologyZeroEval_eq`, `TauCeti.exists_singularCup_eq_one`). Since
   top-degree classes of the product Thom pair are determined on fibres
   (`TauCeti.singularCohomology_prodThomPair_ext`), `u = π^*α ⌣ u₀`, and associativity factors
   `a ↦ π^*a ⌣ u` as right cup multiplication by the unit `α` followed by `a ↦ π^*a ⌣ u₀`.

## Main definitions and results

* `TauCeti.singularCohomologyMap_prodThomPairFiberMap_eq_of_joined`: restrictions to fibres over
  points in the same path component agree.
* `TauCeti.pullbackCup_prodThomPairProj_singularCohomologyδ_apply`: `π^*a ⌣ δ σ =
  (-1)^(p + p q) δ (σ ⌣ π₀^*a)`.
* `TauCeti.bijective_pullbackCup_prodThomPair`: `a ↦ π^*a ⌣ u` is bijective for any
  fibrewise-generating class `u`.
* `TauCeti.prodThomPairPullbackCupEquiv`: the `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.2 and Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w v u

namespace TauCeti

section PathHomotopy

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}
  {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F] [Zero F]

/-- **Restrictions to fibres in the same path component agree**: if `b₁` and `b₂` are joined by a
path in `B`, the inclusions of the fibre pairs `(F, F ∖ {0})` over `b₁` and `b₂` into
`(B × F, B × (F ∖ {0}))` are homotopic as maps of pairs, so they induce the same map on relative
singular cohomology in every degree. -/
theorem singularCohomologyMap_prodThomPairFiberMap_eq_of_joined {b₁ b₂ : B} (h : Joined b₁ b₂)
    (n : ℕ) (u : (prodThomPair B F).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (prodThomPairFiberMap F b₁) n u =
      TopPair.singularCohomologyMap (prodThomPairFiberMap F b₂) n u := by
  obtain ⟨γ⟩ := h
  let g (b : B) : TopCat.of F ⟶ TopCat.of (B × F) := TopCat.ofHom ⟨fun x : F ↦ (b, x), by fun_prop⟩
  have hb (b : B) (hb' : Set.MapsTo (g b) ({0}ᶜ : Set F) {p : B × F | p.2 ≠ 0}) :
      prodThomPairFiberMap F b = TopPair.ofSubsetMap (g b) hb' :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
      (prodThomPairFiberMap_fst_apply F b x).trans (TopPair.ofSubsetMap_fst_apply (g b) hb' x).symm)
  let H : (g b₁).hom.Homotopy (g b₂).hom :=
    { toFun q := (γ q.1, q.2)
      continuous_toFun := by fun_prop
      map_zero_left x := by simp [g]
      map_one_left x := by simp [g] }
  let hpair := TopPair.ofSubsetHomotopy (B := ({0}ᶜ : Set F)) (B' := {p : B × F | p.2 ≠ 0})
    H fun _ _ hx ↦ hx
  rw [hb b₁, hb b₂]
  exact ConcreteCategory.congr_hom (hpair.congr_singularCohomologyMap R k M n) u

end PathHomotopy

section ConnectingSign

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F] [Zero F]

private theorem neg_one_pow_zsmul_involutive {A : Type*} [AddCommGroup A] (s : ℕ) :
    Function.Involutive fun x : A ↦ ((-1 : ℤ) ^ s) • x := fun x ↦ by
  dsimp only
  rw [smul_smul, ← mul_pow]
  simp

/-- **Cupping with a coboundary on the product Thom pair.** For `σ ∈ H^q(B × (F ∖ {0}); K)` with
`q + 1 = r` and `a ∈ Hᵖ(B; M)`, `π^*a ⌣ δ σ = (-1)^(p + p q) δ (σ ⌣ π₀^*a)`, where `π` and `π₀` are
the projections of `B × F` and `B × (F ∖ {0})` onto `B`. -/
theorem pullbackCup_prodThomPairProj_singularCohomologyδ_apply
    {q r p n' m : ℕ} (hq : q + 1 = r) (hn' : q + p = n') (hm : n' + 1 = m) (h : p + r = m)
    (σ : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) q)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
          (𝟙_ (ModuleCat.{w} K)) q r hq σ) a =
      ((-1 : ℤ) ^ (p + p * q)) •
        (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n' m hm
          ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
            q p n' hn' σ (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)) := by
  let P := prodThomPair B F
  have hδ := P.singularCohomologyδ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
    (by omega : p + q = n') hq hm h (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) σ
  have hrestr : TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) P.map p
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p a) =
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairPuncturedProj B F) p a := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      map_comp_prodThomPairProj]
  have hcomm := P.snd.singularCup_gradedComm K (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) (braiding_leftUnitor M) (by omega : p + q = n')
    (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) σ
  -- `pullbackCup` uses `ModuleCat.of K K`, which is definitionally `𝟙_ (ModuleCat K)` in `hδ`.
  have hδ' : ((-1 : ℤ) ^ p) • P.pullbackCup M (prodThomPairProj B F) r p m h
      (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q r hq σ) a =
        P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n' m hm
          (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p q n' (by omega)
            (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) σ) := by
    rw [TopPair.pullbackCup_apply]
    exact hδ.symm.trans (congrArg (fun x ↦ P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M
      n' m hm (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p q n'
        (by omega) x σ)) hrestr)
  have hcup : P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p q n' (by omega)
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) σ =
        ((-1 : ℤ) ^ (p * q)) • P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          q p n' hn' σ (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) := by
    rw [hcomm]
    exact (neg_one_pow_zsmul_involutive (p * q) _).symm
  calc P.pullbackCup M (prodThomPairProj B F) r p m h _ a
      = ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ p) • P.pullbackCup M (prodThomPairProj B F) r p m h _ a) :=
          (neg_one_pow_zsmul_involutive p _).symm
    _ = ((-1 : ℤ) ^ p) • P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M n' m hm
          (((-1 : ℤ) ^ (p * q)) • P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
            q p n' hn' σ (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)) := by
          rw [hδ', hcup]
    _ = _ := by rw [map_zsmul, smul_smul, ← pow_add]

end ConnectingSign

section ReferenceGenerator

variable {K : Type w} [CommRing K]

/-- `prodThomPairSnd B F` followed by the fibre inclusion over `PUnit.unit` is the map of Thom
pairs induced by the constant map to `PUnit`. -/
private theorem prodThomPairSnd_comp_prodThomPairFiberMap_punit
    (B : Type w) [TopologicalSpace B] (F : Type w) [TopologicalSpace F] [Zero F] :
    prodThomPairSnd B F ≫ prodThomPairFiberMap F PUnit.unit =
      prodThomPairMap F (ContinuousMap.const B (PUnit.unit : PUnit.{w + 1})) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
    (prodThomPairFiberMap_fst_apply F PUnit.unit _).trans
      ((congrArg (Prod.mk PUnit.unit) (prodThomPairSnd_fst_apply F p)).trans
        (prodThomPairMap_fst_apply F _ p).symm))

/-- Rank-zero case: `F` is a subsingleton, so the punctured subspaces are empty and `pullbackCup`
reduces via `TopPair.singularCohomologyπ` to pullback along `B × F ≃ₜ B`. -/
private theorem exists_fiberClass_bijective_pullbackCup_zero
    (F : Type w) [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (hr : finrank ℝ F = 0) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) 0,
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)) := by
  have : Subsingleton F := Module.finrank_zero_iff.1 hr
  let _ : Unique F := uniqueOfSubsingleton 0
  have : IsEmpty (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).snd :=
    ⟨fun x ↦ x.2 (Subsingleton.elim x.1 0)⟩
  let PF := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  let g₀ := inv (PF.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (PF.fst.singularCohomologyZeroOne (k := K))
  have hg₀_π : PF.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 g₀ =
      PF.fst.singularCohomologyZeroOne (k := K) := by
    dsimp only [g₀]
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  subst h
  have : IsEmpty (prodThomPair B F).snd := ⟨fun q ↦ q.2 (Subsingleton.elim q.1.2 0)⟩
  let P := prodThomPair B F
  have hπg₀ : P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀) =
        P.fst.singularCohomologyZeroOne (k := K) := by
    have hnat := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K))
      (prodThomPairSnd B F) 0) g₀
    simp only [ConcreteCategory.comp_apply] at hnat
    rw [← hnat, hg₀_π, singularCohomologyMap_singularCohomologyZeroOne]
  have hπ : Function.Bijective (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M (p + 0)) :=
    (asIso (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M (p + 0))).toLinearEquiv.bijective
  have hproj : IsIso (prodThomPairProj B F) := by
    have heq : prodThomPairProj B F = (TopCat.isoOfHomeo (Homeomorph.prodUnique B F)).hom :=
      TopCat.ext fun x ↦ prodThomPairProj_apply F x
    rw [heq]
    infer_instance
  have hproj_bij : Function.Bijective (TopCat.singularCohomologyMap
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) (prodThomPairProj B F) p) :=
    ((singularCohomologyFunctor (𝟙_ (ModuleCat.{w} K)) K M p).mapIso
      (asIso (prodThomPairProj B F)).op).toLinearEquiv.bijective
  refine (Function.Bijective.of_comp_iff' hπ _).1 ?_
  have hcomp : ⇑(P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M (p + 0)) ∘
      ⇑(P.pullbackCup M (prodThomPairProj B F) 0 p (p + 0) rfl
        (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)) =
        ⇑(TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
          (prodThomPairProj B F) p) := by
    funext a
    simp only [Function.comp_apply, TopPair.pullbackCup_apply]
    refine (TopPair.singularCohomologyπ_singularCup K P (λ_ (𝟙_ (ModuleCat.{w} K))).inv
      (ρ_ M).hom p 0 (p + 0) rfl
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p a)
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 g₀)).trans ?_
    rw [hπg₀, TopCat.singularCohomologyZeroOne_def]
    exact P.fst.singularCup_constSingularCocycle_right K (η := 𝟙 _) (by monoidal) (by monoidal)
      (add_zero p) _
  rwa [hcomp]

/-- Rank-one case: `F ≃L[ℝ] ℝ`, using `TauCeti.prodThomPairSingularCohomologyLineEquiv`. -/
private theorem exists_fiberClass_bijective_pullbackCup_one
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hr : finrank ℝ F = 1) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) 1,
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 1 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 g₀)) := by
  let e : F ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp [hr])
  let g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) 1 :=
    TopPair.singularCohomologyMap (prodThomPairFiberMap F PUnit.unit) 1
      (((prodThomPair PUnit.{w + 1} F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) 0 1 rfl) (prodThomPairPuncturedLineClass K PUnit.{w + 1} e))
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  have hu₀ : TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 g₀ =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) 0 1 rfl) (prodThomPairPuncturedLineClass K B e) := by
    rw [← TopPair.singularCohomologyMap_comp_apply,
      prodThomPairSnd_comp_prodThomPairFiberMap_punit, ← ConcreteCategory.comp_apply,
      TopPair.singularCohomologyδ_naturality (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
        (M := 𝟙_ (ModuleCat.{w} K)) _ 0 1 rfl,
      ConcreteCategory.comp_apply,
      singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedLineClass]
  have heq : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 1 g₀)) =
        ((fun y ↦ ((-1 : ℤ) ^ (p + p * 0)) • y) ∘
          ⇑(prodThomPairSingularCohomologyLineEquiv M B e p m h)) := by
    funext a
    simp only [Function.comp_apply, hu₀,
      pullbackCup_prodThomPairProj_singularCohomologyδ_apply M rfl (zero_add p) h h,
      prodThomPairSingularCohomologyLineEquiv_apply]
  rw [heq]
  exact (neg_one_pow_zsmul_involutive _).bijective.comp
    (prodThomPairSingularCohomologyLineEquiv M B e p m h).bijective

/-- Rank `d + 2` case: `F ≃L[ℝ] ℝᵈ⁺²`, using `TauCeti.prodThomPairSingularCohomologySphereEquiv`. -/
private theorem exists_fiberClass_bijective_pullbackCup_add_two
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (d : ℕ)
    (hr : finrank ℝ F = d + 2) :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (d + 2),
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ) (h : p + (d + 2) = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀)) := by
  let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hr])
  let g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (d + 2) :=
    TopPair.singularCohomologyMap (prodThomPairFiberMap F PUnit.unit) (d + 2)
      (((prodThomPair PUnit.{w + 1} F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl)
        (prodThomPairPuncturedClass K PUnit.{w + 1} e))
  refine ⟨g₀, fun B _ M p m h ↦ ?_⟩
  have hu₀ : TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀ =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
        (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl) (prodThomPairPuncturedClass K B e) := by
    rw [← TopPair.singularCohomologyMap_comp_apply,
      prodThomPairSnd_comp_prodThomPairFiberMap_punit, ← ConcreteCategory.comp_apply,
      TopPair.singularCohomologyδ_naturality (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
        (M := 𝟙_ (ModuleCat.{w} K)) _ (d + 1) (d + 2) rfl,
      ConcreteCategory.comp_apply,
      singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
  have heq : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 2) g₀)) =
        ((fun y ↦ ((-1 : ℤ) ^ (p + p * (d + 1))) • y) ∘
          ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h)) := by
    funext a
    simp only [Function.comp_apply, hu₀,
      pullbackCup_prodThomPairProj_singularCohomologyδ_apply M rfl rfl (by omega) h,
      prodThomPairSingularCohomologySphereEquiv_apply]
  rw [heq]
  exact (neg_one_pow_zsmul_involutive _).bijective.comp
    (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective

/-- Combining the three rank cases produces a generator `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose pullback
along `prodThomPairSnd` induces a bijection `pullbackCup` over every base `B`. -/
private theorem exists_generator_bijective_pullbackCup
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      Submodule.span K {g₀} = ⊤ ∧
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ)
        (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
          (finrank ℝ F) p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g₀)) := by
  suffices ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) (p m : ℕ)
        (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F)
          (finrank ℝ F) p m h
          (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g₀)) by
    obtain ⟨g₀, hbij⟩ := this
    refine ⟨g₀, ?_, hbij⟩
    -- Over `PUnit` in degree `0`, `1 ∈ H⁰(pt; K)` spans and maps via `pullbackCup` to `π₂^* g₀`,
    -- which maps via `(F, F ∖ {0}) ≅ prodThomPair PUnit F` to `g₀`.
    have hone : Submodule.span K
        {((TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne (k := K))} = ⊤ := by
      refine Submodule.eq_top_iff'.2 fun x ↦ Submodule.mem_span_singleton.2
        ⟨singularCohomologyZeroEval PUnit.unit x, (singularCohomologyZero_ext fun y ↦ ?_).symm⟩
      have hy : y = PUnit.unit := Subsingleton.elim _ _
      rw [hy, map_smul, singularCohomologyZeroEval_singularCohomologyZeroOne, smul_eq_mul, mul_one]
    let e₁ := LinearEquiv.ofBijective ((prodThomPair PUnit.{w + 1} F).pullbackCup
      (ModuleCat.of K K) (prodThomPairProj PUnit.{w + 1} F) (finrank ℝ F) 0 (finrank ℝ F)
      (zero_add _) (TopPair.singularCohomologyMap (prodThomPairSnd PUnit.{w + 1} F)
        (finrank ℝ F) g₀)) (hbij PUnit.{w + 1} (ModuleCat.of K K) 0 (finrank ℝ F) (zero_add _))
    let u_pt := TopPair.singularCohomologyMap (prodThomPairSnd PUnit.{w + 1} F) (finrank ℝ F) g₀
    have hu_pt : Submodule.span K {u_pt} = ⊤ := by
      have he₁ : e₁ ((TopCat.of PUnit.{w + 1}).singularCohomologyZeroOne (k := K)) = u_pt := by
        rw [LinearEquiv.ofBijective_apply, TopCat.singularCohomologyZeroOne_def]
        exact TopPair.pullbackCup_one _ _ (zero_add _) _
      rw [← he₁, e₁.span_singleton_apply_eq_top_iff]
      exact hone
    let e₂ := LinearEquiv.ofBijective
      (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K)
        (prodThomPairFiberMap F PUnit.unit) (finrank ℝ F)).hom
      (Function.bijective_iff_has_inverse.2
        ⟨TopPair.singularCohomologyMap (prodThomPairSnd PUnit.{w + 1} F) (finrank ℝ F),
          fun x ↦ by
            rw [← TopPair.singularCohomologyMap_comp_apply,
              prodThomPairSnd_comp_prodThomPairFiberMap, TopPair.singularCohomologyMap_id,
              ConcreteCategory.id_apply],
          fun x ↦ by
            rw [← TopPair.singularCohomologyMap_comp_apply,
              prodThomPairFiberMap_comp_prodThomPairSnd, TopPair.singularCohomologyMap_id,
              ConcreteCategory.id_apply]⟩)
    have he₂ : e₂ u_pt = g₀ := by
      rw [LinearEquiv.ofBijective_apply, ModuleCat.Hom.hom,
        ← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
    rw [← he₂, e₂.span_singleton_apply_eq_top_iff]
    exact hu_pt
  rcases hr : finrank ℝ F with _ | _ | d
  · exact exists_fiberClass_bijective_pullbackCup_zero F hr
  · exact exists_fiberClass_bijective_pullbackCup_one F hr
  · exact exists_fiberClass_bijective_pullbackCup_add_two F d hr

private theorem singularCohomologyMap_const_eq_smul_constSingularCocycle
    {R₀ : ModuleCat.{w} K} (hR₀ : R₀ = 𝟙_ (ModuleCat.{w} K)) {X Y : TopCat.{w}} (y : Y)
    (α : Y.singularCohomology R₀ K R₀ 0)
    (α' : Y.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (hα : HEq α α') :
    TopCat.singularCohomologyMap (R := R₀) (k := K) (M := R₀)
        (TopCat.const (X := X) (Y := Y) y) 0 α =
      singularCohomologyZeroEval y α' •
        (X.singularCochainComplex R₀ K R₀).homologyπ 0 (X.constSingularCocycle K (𝟙 R₀)) := by
  subst hR₀
  cases hα
  rw [singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
    TopCat.singularCohomologyZeroOne_def]

end ReferenceGenerator

section Main

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Right cup multiplication on `Hᵖ(B; M)` by a cup-invertible class `α ∈ H⁰(B; K)` is bijective. -/
private theorem bijective_singularCup_degreeZero_right {X : TopCat.{w}}
    {α β : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0}
    (hαβ : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl α β = X.singularCohomologyZeroOne)
    (hβα : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl β α = X.singularCohomologyZeroOne)
    (p : ℕ) :
    Function.Bijective (fun a : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ↦
      X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p) a α) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun a ↦ X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (add_zero p) a β,
      fun a ↦ ?_, fun a ↦ ?_⟩
  · dsimp only
    rw [X.singularCup_assoc K (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ' := (ρ_ M).hom)
      (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom) (by monoidal) (by monoidal) (add_zero p)
      (add_zero p) (zero_add 0) (add_zero p) a α β, hαβ, TopCat.singularCohomologyZeroOne_def]
    exact X.singularCup_constSingularCocycle_right K (η := 𝟙 _) (by monoidal) (by monoidal)
      (add_zero p) a
  · dsimp only
    rw [X.singularCup_assoc K (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (μ' := (ρ_ M).hom)
      (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom) (by monoidal) (by monoidal) (add_zero p)
      (add_zero p) (zero_add 0) (add_zero p) a β α, hβα, TopCat.singularCohomologyZeroOne_def]
    exact X.singularCup_constSingularCocycle_right K (η := 𝟙 _) (by monoidal) (by monoidal)
      (add_zero p) a

/-- **The Thom isomorphism for a product bundle.** Let `F` be a finite-dimensional real normed
space of dimension `r`, and let `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` be a class whose restriction to
the fibre pair `(F, F ∖ {0})` over every point of `B` generates `Hʳ(F, F ∖ {0}; K)`. Then for every
`K`-module `M`, every base degree `p` and `m = p + r`, the map `a ↦ π^*a ⌣ u` from `Hᵖ(B; M)` to
`Hᵐ(B × F, B × (F ∖ {0}); M)` is bijective. -/
theorem bijective_pullbackCup_prodThomPair {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g₀, hg₀_span, hg₀_bij⟩ := exists_generator_bijective_pullbackCup (K := K) F
  let φ : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) ≃ₗ[K] K :=
    singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
  have hg₀_unit : IsUnit (φ g₀) := φ.span_singleton_eq_top_iff_isUnit.1 hg₀_span
  let u₀ := TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g₀
  let f : B → K := fun b ↦
    φ (TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u) *
      ↑(hg₀_unit.unit⁻¹)
  have hf_joined : ∀ b₁ b₂ : B, Joined b₁ b₂ → f b₁ = f b₂ := fun b₁ b₂ hj ↦ by
    dsimp only [f]
    rw [singularCohomologyMap_prodThomPairFiberMap_eq_of_joined hj]
  obtain ⟨α, hα⟩ := exists_singularCohomologyZeroEval_eq (X := TopCat.of B) f hf_joined
  have hα_unit : ∀ b : B, IsUnit (singularCohomologyZeroEval b α) := fun b ↦ by
    rw [hα]
    exact (φ.span_singleton_eq_top_iff_isUnit.1 (hu b)).mul hg₀_unit.unit⁻¹.isUnit
  obtain ⟨β, hαβ, hβα⟩ := exists_singularCup_eq_one α hα_unit
  -- `u` agrees with `π^*α ⌣ u₀` on every fibre, so `u = π^*α ⌣ u₀` on `B × F`.
  have hu_eq : u = (prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F)
      (finrank ℝ F) 0 (finrank ℝ F) (zero_add _) u₀ α := by
    refine singularCohomology_prodThomPair_ext fun b ↦ ?_
    let PF := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
    have hconst : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
        𝟙 PF.fst ≫ TopCat.const (X := PF.fst) (Y := TopCat.of B) b := by
      rw [Category.id_comp]
      exact TopCat.ext fun (x : F) ↦ (prodThomPairProj_apply F _).trans
        ((congrArg Prod.fst (prodThomPairFiberMap_fst_apply F b x)).trans
          (TopCat.const_apply (X := PF.fst) (Y := TopCat.of B) b x).symm)
    rw [← TopPair.pullbackCup_naturality (prodThomPairFiberMap F b) (𝟙 PF.fst)
      (prodThomPairProj B F) (TopCat.const (X := PF.fst) (Y := TopCat.of B) b) hconst]
    have hu₀b : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u₀ = g₀ := by
      rw [← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
    have hconst_α := singularCohomologyMap_const_eq_smul_constSingularCocycle
      (R₀ := ModuleCat.of K K) rfl (X := PF.fst) (Y := TopCat.of B) b α α HEq.rfl
    rw [hu₀b, hconst_α, hα, map_smul, PF.pullbackCup_one]
    apply φ.injective
    simp only [f, map_smul, smul_eq_mul, mul_assoc]
    rw [IsUnit.val_inv_mul, mul_one]
  -- Associativity factors `pullbackCup ... u` as `pullbackCup ... u₀` after `a ↦ a ⌣ α`.
  have hfac : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p 0 p (add_zero p) a α := by
    funext a
    simp only [Function.comp_apply, hu_eq, TopPair.pullbackCup_apply]
    rw [← TopCat.singularCup_naturality]
    exact ((prodThomPair B F).singularCup_assoc K (by monoidal) (by monoidal) (add_zero p) h
      (zero_add _) h _ _ _).symm
  rw [hfac]
  exact (hg₀_bij B M p m h).comp (bijective_singularCup_degreeZero_right M hαβ hβα p)

/-- **The Thom isomorphism for a product bundle**, as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^*a ⌣ u`, for `p + finrank ℝ F = m` and any
class `u` whose restriction to every fibre generates `H^{finrank ℝ F}(F, F ∖ {0}; K)`. -/
def prodThomPairPullbackCupEquiv {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M h hu)

/-- `TauCeti.prodThomPairPullbackCupEquiv` evaluates as `TopPair.pullbackCup` along
`TauCeti.prodThomPairProj`. -/
@[simp]
theorem prodThomPairPullbackCupEquiv_apply {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M h hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a :=
  -- `prodThomPairPullbackCupEquiv` is `LinearEquiv.ofBijective` of `pullbackCup`.
  (rfl)

/-- Left inverse law for `TauCeti.prodThomPairPullbackCupEquiv` applied to `TopPair.pullbackCup`. -/
@[simp]
theorem prodThomPairPullbackCupEquiv_symm_apply_self {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPairPullbackCupEquiv M h hu).symm
        ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a) = a :=
  (prodThomPairPullbackCupEquiv M h hu).symm_apply_apply a

end Main

end TauCeti
