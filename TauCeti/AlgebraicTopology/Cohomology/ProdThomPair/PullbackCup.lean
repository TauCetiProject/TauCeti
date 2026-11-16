/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space, `F` a finite-dimensional real normed space of rank
`r = finrank ℝ F`, `K` a commutative ring, and `M` a `K`-module. For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` of the Thom pair `TauCeti.prodThomPair B F` whose restriction
`u|_b ∈ Hʳ(F, F ∖ {0}; K)` along `TauCeti.prodThomPairFiberMap F b` generates `Hʳ(F, F ∖ {0}; K)`
for every `b : B`, this file proves that the map

`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^* a ⌣ u`,  `p + r = m`,

(`TopPair.pullbackCup` along `TauCeti.prodThomPairProj B F`) is bijective in every degree `p`
(`TauCeti.bijective_pullbackCup_prodThomPair`), giving the `K`-linear equivalence
`TauCeti.prodThomPairPullbackCupEquiv`. This is the local model of the cohomological Thom
isomorphism, before gluing over trivializing open sets by Mayer–Vietoris.

## Proof outline

First we construct, for every finite rank `r`, one fibre class `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose
pullback `u₀ = pr₂^* g₀` along `TauCeti.prodThomPairSnd B F` has bijective `pullbackCup` for all
spaces `B`, all modules `M`, and all degrees `p`:

* **Rank `r = 0`**: `F` is a subsingleton, so `B × (F ∖ {0})` is empty, the map from relative to
  absolute cohomology is an isomorphism (`TopPair.isIso_singularCohomologyπ_of_isEmpty`), and the
  projection `B × F ⟶ B` is a homeomorphism. Taking `g₀` to lift the unit `0`-class of `F` makes
  `π^* a ⌣ u₀` correspond to `π^* a`.
* **Positive ranks `r = d + 1 ≥ 1`**: for a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹`,
  `TauCeti.prodThomPairSingularCohomologySphereEquiv` gives the `K`-linear equivalence
  `c ↦ δ (σ ⌣ π₀^* c)` from `Hᵖ(B; M)` to `Hᵐ(B × F, B × (F ∖ {0}); M)`, where `σ` is
  `TauCeti.prodThomPairPuncturedClass`. Graded commutativity and compatibility of the connecting
  morphism with cup products (`TopPair.singularCohomologyδ_singularCup_eq_zsmul_pullbackCup`)
  rewrite `δ (σ ⌣ π₀^* c)` as `(-1)^(p r) (π^* c ⌣ δ σ)`, and naturality along `B → PUnit`
  (`TauCeti.prodThomPairMap_const`) identifies `δ σ` with the pullback of the fibre class over a
  point.

Finally, for an arbitrary class `u` restricting to a generator on every fibre, surjectivity of
`pullbackCup` for `u₀` in degree `p = 0` with `M = K` writes `u = π^* γ ⌣ u₀` for some
`γ ∈ H⁰(B; K)`. Restricting to each fibre shows `u|_b = γ(b) • g₀`, so `γ(b)` is a unit of `K` at
every `b : B` (`LinearEquiv.span_singleton_eq_top_iff_isUnit` via
`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`), hence `γ` is a cup-product unit in
`H⁰(B; K)` (`TauCeti.exists_singularCup_eq_one`). By associativity of the relative cup product,
`π^* a ⌣ u = π^* (a ⌣ γ) ⌣ u₀`, which is a composite of two bijections
(`TopCat.bijective_singularCup_right_of_singularCup_eq_one`).

## Main definitions and results

* `TauCeti.bijective_pullbackCup_prodThomPair`: `a ↦ π^* a ⌣ u` is bijective on `prodThomPair B F`
  whenever `u` generates on every fibre.
* `TauCeti.bijective_pullbackCup_prodThomPairSnd`: the specialization to `pr₂^* g` for a generator
  `g` of `Hʳ(F, F ∖ {0}; K)`.
* `TauCeti.prodThomPairPullbackCupEquiv`: the resulting `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Sections 6–7.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Module

universe w

namespace TauCeti

/-! ### Rank zero -/

section RankZero

variable {F : Type w} [TopologicalSpace F] [Zero F] [Subsingleton F]
variable {K : Type w} [CommRing K]

/-- In rank zero, the fibre class lifting the unit `0`-class of `F` across `H⁰(F, ∅) ≅ H⁰(F)`. -/
private def rankZeroFiberClass :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) 0 :=
  inv ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomologyπ
    (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).fst.singularCohomologyZeroOne (k := K))

/-- In rank zero, `pullbackCup` with the pullback of `rankZeroFiberClass` is bijective. -/
private theorem bijective_pullbackCup_rankZero (B : Type w) [TopologicalSpace B]
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + 0 = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 (rankZeroFiberClass (K := K)))) := by
  subst h
  let P := prodThomPair B F
  let : Unique F := ⟨⟨0⟩, fun x ↦ Subsingleton.elim x 0⟩
  -- `prodThomPairProj B F` is the first projection of `B × F ≃ₜ B`, hence an isomorphism.
  have hproj : prodThomPairProj B F = (TopCat.isoOfHomeo (Homeomorph.prodUnique B F)).hom :=
    TopCat.ext fun x ↦ prodThomPairProj_apply F x
  have : IsIso (prodThomPairProj B F) := hproj ▸ inferInstance
  let u₀ : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0 :=
    TopPair.singularCohomologyMap (prodThomPairSnd B F) 0 (rankZeroFiberClass (K := K))
  -- The image of `u₀ = pr₂^* g₀` in `H⁰(B × F; K)` is the unit `0`-class.
  have huπ : P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 u₀ =
      P.fst.singularCohomologyZeroOne := by
    have hπ0 : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomologyπ
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 (rankZeroFiberClass (K := K)) =
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).fst.singularCohomologyZeroOne := by
      rw [rankZeroFiberClass, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id,
        ConcreteCategory.id_apply]
    have hnat := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K))
      (prodThomPairSnd B F) 0) (rankZeroFiberClass (K := K))
    simp only [ConcreteCategory.comp_apply] at hnat
    exact hnat.symm.trans ((congrArg _ hπ0).trans
      (singularCohomologyMap_singularCohomologyZeroOne _))
  -- Applying `singularCohomologyπ` turns `pullbackCup` into `(prodThomPairProj B F)^*`.
  have hcomp : ⇑(P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) ∘
      ⇑(P.pullbackCup M (prodThomPairProj B F) 0 p (p + 0) rfl u₀) =
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p := by
    funext a
    simp only [Function.comp_apply, TopPair.pullbackCup_apply]
    refine (P.singularCohomologyπ_singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
      p 0 p (Nat.add_zero p) (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) u₀).trans ?_
    rw [huπ, TopCat.singularCohomologyZeroOne_def]
    exact P.fst.singularCup_constSingularCocycle_right K (η := 𝟙 _)
      (by monoidal) (by monoidal) (Nat.add_zero p) _
  have hπbij : Function.Bijective (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) :=
    (asIso (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p)).toLinearEquiv.bijective
  have hprojBij : Function.Bijective (TopCat.singularCohomologyMap
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) (prodThomPairProj B F) p) :=
    ((singularCohomologyFunctor (𝟙_ (ModuleCat.{w} K)) K M p).mapIso
      (asIso (prodThomPairProj B F)).op).toLinearEquiv.bijective
  exact (hπbij.of_comp_iff' _).1 (hcomp ▸ hprojBij)

end RankZero

/-! ### Positive ranks -/

section PositiveRank

variable {K : Type w} [CommRing K] {F : Type w} [TopologicalSpace F] [AddCommMonoid F]
  [Module ℝ F] {d : ℕ}

/-- The model fibre class in positive rank `d + 1`: `δ σ` over a point, restricted to
`(F, F ∖ {0})`. -/
private def sphereFiberClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (d + 1) :=
  TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1})) (d + 1)
    ((prodThomPair PUnit.{w + 1} F).singularCohomologyδ
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl
      (prodThomPairPuncturedClass K PUnit.{w + 1} e))

/-- In positive rank `d + 1`, `pullbackCup` with the pullback of `sphereFiberClass` is bijective. -/
private theorem bijective_pullbackCup_sphere (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + (d + 1) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1)
        (sphereFiberClass (K := K) e))) := by
  have hu : TopPair.singularCohomologyMap (prodThomPairSnd B F) (d + 1)
        (sphereFiberClass (K := K) e) =
      (prodThomPair B F).singularCohomologyδ
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) d (d + 1) rfl
        (prodThomPairPuncturedClass K B e) := by
    rw [sphereFiberClass, ← TopPair.singularCohomologyMap_comp_apply,
      ← prodThomPairMap_const B F PUnit.unit, ← ConcreteCategory.comp_apply,
      TopPair.singularCohomologyδ_naturality _ d (d + 1) rfl, ConcreteCategory.comp_apply,
      singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
  rw [hu]
  refine (((isUnit_neg_one : IsUnit (-1 : ℤ)).pow (p * (d + 1))).smul_bijective.of_comp_iff' _).1 ?_
  have heq : (((-1 : ℤ) ^ (p * (d + 1)) • ·) ∘
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 1) p m h
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          d (d + 1) rfl (prodThomPairPuncturedClass K B e)))) =
      ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) := by
    funext c
    simp only [Function.comp_apply]
    rw [prodThomPairSingularCohomologySphereEquiv_apply]
    have key := ((prodThomPair B F).singularCohomologyδ_singularCup_eq_zsmul_pullbackCup M
      (prodThomPairProj B F) (Nat.add_comm p d) rfl (by omega) h
      (prodThomPairPuncturedClass K B e) c).symm
    rwa [map_comp_prodThomPairProj] at key
  rw [heq]
  exact (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective

end PositiveRank

/-! ### Arbitrary finite rank and arbitrary fibrewise-generating class -/

section General

variable {K : Type w} [CommRing K]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every finite-dimensional real normed space `F` has a class `g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose
pullback `pr₂^* g₀` makes `pullbackCup` bijective over all bases `B`, coefficient modules `M`, and
degrees `p`. -/
private theorem exists_bijective_pullbackCup_prodThomPair_model :
    ∃ g₀ : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      ∀ (B' : Type w) [TopologicalSpace B'] (M : ModuleCat.{w} K) {p m : ℕ}
        (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B' F).pullbackCup M (prodThomPairProj B' F)
          (finrank ℝ F) p m h (TopPair.singularCohomologyMap (prodThomPairSnd B' F)
            (finrank ℝ F) g₀)) := by
  generalize hr : finrank ℝ F = r
  rcases r with _ | d
  · have : Subsingleton F := finrank_zero_iff.1 hr
    exact ⟨rankZeroFiberClass, fun B' _ M _ _ h ↦ bijective_pullbackCup_rankZero B' M h⟩
  · let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
      (LinearEquiv.ofFinrankEq F (EuclideanSpace ℝ (Fin (d + 1)))
        (by simp [hr])).toContinuousLinearEquiv
    exact ⟨sphereFiberClass e, fun B' _ M _ _ h ↦ bijective_pullbackCup_sphere B' e M h⟩

/-- **The Thom isomorphism for a product bundle.** For a finite-dimensional real normed space `F`
of rank `r = finrank ℝ F` and a class `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` whose restriction to the
fibre pair `(F, F ∖ {0})` over every point `b : B` generates `Hʳ(F, F ∖ {0}; K)`, the map
`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, is bijective for every `K`-module `M`
and every `p + r = m`. -/
theorem bijective_pullbackCup_prodThomPair {B : Type w} [TopologicalSpace B] (M : ModuleCat.{w} K)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g₀, hg₀⟩ := exists_bijective_pullbackCup_prodThomPair_model (K := K) (F := F)
  let u₀ := TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g₀
  -- Express `u = π^* γ ⌣ u₀` using surjectivity for `u₀` in base degree `0` with `M = K`.
  obtain ⟨γ, hγ⟩ := (hg₀ B (ModuleCat.of K K) (Nat.zero_add (finrank ℝ F))).2 u
  -- Restricting to the fibre over `b` gives `u|_b = γ(b) • g₀`, so `γ(b)` is a unit of `K`.
  have hunit (b : B) : IsUnit (singularCohomologyZeroEval b γ) := by
    have hprojb : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
        TopCat.const b :=
      TopCat.ext fun x ↦ (congrArg (prodThomPairProj B F)
        (prodThomPairFiberMap_fst_apply F b x)).trans (prodThomPairProj_apply F (b, x))
    have hfib : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u =
        singularCohomologyZeroEval b γ • g₀ := by
      rw [← hγ, TopPair.pullbackCup_apply, ← TopPair.singularCup_naturality,
        ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hprojb,
        ← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply,
        singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
        map_smul, LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def]
      exact congrArg (singularCohomologyZeroEval b γ • ·)
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCup_constSingularCocycle_left K
          (η := 𝟙 _) (by monoidal) (by monoidal) (Nat.zero_add _) g₀)
    let φ := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of K K)
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
    have hφ : IsUnit (φ (TopPair.singularCohomologyMap (prodThomPairFiberMap F b)
        (finrank ℝ F) u)) :=
      φ.span_singleton_eq_top_iff_isUnit.1 (hu b)
    rw [hfib, map_smul, smul_eq_mul] at hφ
    exact isUnit_of_mul_isUnit_left hφ
  obtain ⟨γ', h₁, h₂⟩ := exists_singularCup_eq_one (X := TopCat.of B) γ hunit
  -- By associativity, `pullbackCup u` is `pullbackCup u₀` composed with `a ↦ a ⌣ γ`.
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p 0 p (Nat.add_zero p) a γ := by
    funext a
    simp only [Function.comp_apply, ← hγ, TopPair.pullbackCup_apply,
      ← TopCat.singularCup_naturality]
    exact ((prodThomPair B F).singularCup_assoc K (by monoidal) (by monoidal)
      (Nat.add_zero p) h (Nat.zero_add _) h _ _ u₀).symm
  rw [hcomp]
  exact (hg₀ B M h).comp
    ((TopCat.of B).bijective_singularCup_right_of_singularCup_eq_one M p γ γ' h₁ h₂)

/-- **The Thom isomorphism for `pr₂^* g` on a product bundle**: if `g` generates
`Hʳ(F, F ∖ {0}; K)`, then `pullbackCup` of `pr₂^* g` on `prodThomPair B F` is bijective in every
degree `p`. -/
theorem bijective_pullbackCup_prodThomPairSnd (B : Type w) [TopologicalSpace B]
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
      (TopPair.singularCohomologyMap (prodThomPairSnd B F) (finrank ℝ F) g)) :=
  bijective_pullbackCup_prodThomPair M h fun b ↦ by
    rw [← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
    exact hg

variable {B : Type w} [TopologicalSpace B]

variable (M : ModuleCat.{w} K) in
/-- **The Thom isomorphism of a product bundle as a linear equivalence**,
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^* a ⌣ u`, for `p + finrank ℝ F = m` and a
class `u` whose restriction to every fibre generates `Hʳ(F, F ∖ {0}; K)`. -/
def prodThomPairPullbackCupEquiv {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M h hu)

@[simp]
theorem prodThomPairPullbackCupEquiv_apply (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M h hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a :=
  (rfl)

end General

end TauCeti
