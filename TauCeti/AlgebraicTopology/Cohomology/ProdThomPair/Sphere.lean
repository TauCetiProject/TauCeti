/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic

/-!
# Cohomology of the Thom pair of a product bundle of positive rank

Let `B` be a topological space and `F` a real topological vector space of positive dimension
`r = d + 1 ≥ 1`, given with a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹`. This file
computes the singular cohomology, with coefficients in any module `M` over a commutative ring `k`,
of the complement `B × (F ∖ {0})` of the zero section of the product bundle `B × F → B` in degrees
`n + d ≥ r - 1`, and of its Thom pair `(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) in degrees
`n + r ≥ r`, for every base degree `n`.

* `B × (F ∖ {0})` is homotopy equivalent to `Sᵈ × B` by `(b, x) ↦ (e x / ‖e x‖, b)`
  (`TauCeti.prodThomPairPuncturedHomotopyEquiv`, in
  `TauCeti.AlgebraicTopology.Singular.ProdThomPair`). Let `σ ∈ Hᵈ(B × (F ∖ {0}); k)` be the
  pullback of the standard generator of `Hᵈ(Sᵈ; k)`
  (`TauCeti.singularCohomologyTopCatSphereZeroGenerator` for `d = 0`,
  `TauCeti.singularCohomologyTopCatSphereGenerator` for `d ≥ 1`) along the first component
  (`TauCeti.prodThomPairPuncturedClass`), and `π : B × (F ∖ {0}) → B` the projection
  (`TauCeti.prodThomPairPuncturedProj`). The decomposition of the cohomology of `Sᵈ × B`
  (`TopCat.singularCohomologySphereZeroProdEquiv` for `d = 0`,
  `TopCat.singularCohomologySphereProdSlantEquiv` for `d ≥ 1`) becomes
  `Hⁿ⁺ᵈ(B; M) × Hⁿ(B; M) ≃ Hⁿ⁺ᵈ(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`
  (`TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`).
* Whenever `F` is nontrivial, the projection `B × (F ∖ {0}) → B` has a continuous section, so
  `π^*` is injective (`TauCeti.injective_singularCohomologyMap_prodThomPairPuncturedProj`); when
  `F` is also contractible, the map `Hᵐ(B × F, B × (F ∖ {0}); M) → Hᵐ(B × F; M)` vanishes
  (`TauCeti.singularCohomologyπ_prodThomPair_eq_zero`) and the connecting morphism `δ` identifies
  any complement of `im π^*` with relative cohomology
  (`TauCeti.bijective_singularCohomologyδ_comp_inr_of_prodThomPair`). Applied to the sphere
  decomposition above, `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
  `Hⁿ(B; M) ≃ Hⁿ⁺ʳ(B × F, B × (F ∖ {0}); M)` for every `n`
  (`TauCeti.prodThomPairSingularCohomologySphereEquiv`), sending the unit of `H⁰(B; k)` to `δ σ`
  (`TauCeti.prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle`).

This is the computation behind the positive-rank product case of the Thom isomorphism in
cohomology (`TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup`), which also treats
rank `0` (where `F ∖ {0}` is empty). Below degree `r` the relative cohomology vanishes
(`TauCeti.isZero_singularCohomology_prodThomPair`), and in degree `r` alone, for every rank,
`TauCeti.prodThomPairSingularCohomologyEquiv` identifies `Hʳ(B × F, B × (F ∖ {0}))` with
`Hom(H₀(B), M)`; both are in `TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic`.

## Main definitions and results

* `TauCeti.injective_singularCohomologyMap_prodThomPairPuncturedProj`,
  `TauCeti.singularCohomologyπ_prodThomPair_eq_zero`,
  `TauCeti.bijective_singularCohomologyδ_comp_inr_of_prodThomPair`: rank-independent section and
  long-exact-sequence lemmas for `[ContractibleSpace F] [Nontrivial F]`.
* `TauCeti.prodThomPairPuncturedClass`: the class `σ ∈ Hᵈ(B × (F ∖ {0}); k)` pulled back from `Sᵈ`.
* `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`:
  `Hⁿ⁺ᵈ(B; M) × Hⁿ(B; M) ≃ Hⁿ⁺ᵈ(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`.
* `TauCeti.prodThomPairSingularCohomologySphereEquiv`:
  `Hⁿ(B; M) ≃ Hⁿ⁺ʳ(B × F, B × (F ∖ {0}); M)`, `c ↦ δ (σ ⌣ π^* c)`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle and then by Mayer–Vietoris), and Section 3.2 (the
  cohomology of a product with a sphere).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w

namespace TauCeti

section RankIndependent

/-- Pulling back along the punctured projection `B × (F ∖ {0}) → B` is injective whenever `F` is
nontrivial, since any nonzero vector `v : F` gives a continuous section `b ↦ (b, v)`. -/
theorem injective_singularCohomologyMap_prodThomPairPuncturedProj
    {k : Type*} [Ring k] [Linear k (ModuleCat.{w} k)] (R M : ModuleCat.{w} k)
    (B : Type w) [TopologicalSpace B] {F : Type w} [TopologicalSpace F] [Zero F]
    [Nontrivial F] (m : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (prodThomPairPuncturedProj B F) m) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  let s : TopCat.of B ⟶ (prodThomPair B F).snd :=
    TopCat.ofHom ⟨fun b ↦ ⟨(b, v), hv⟩, by fun_prop⟩
  have hs : s ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
    TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (s b)
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap s m) fun b ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hs,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

/-- When `F` is contractible and nontrivial, the map
`Hᵐ(B × F, B × (F ∖ {0})) → Hᵐ(B × F)` from relative to absolute singular cohomology vanishes in
every degree `m`. -/
@[simp]
theorem singularCohomologyπ_prodThomPair_eq_zero
    {k : Type*} [Ring k] [Linear k (ModuleCat.{w} k)] (R M : ModuleCat.{w} k)
    (B : Type w) [TopologicalSpace B] {F : Type w} [TopologicalSpace F] [Zero F]
    [ContractibleSpace F] [Nontrivial F] (m : ℕ)
    (z : (prodThomPair B F).singularCohomology R k M m) :
    (prodThomPair B F).singularCohomologyπ R k M m z = 0 := by
  let P := prodThomPair B F
  let b := inv (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
    (prodThomPairProj B F) m) (P.singularCohomologyπ R k M m z)
  have hb : TopCat.singularCohomologyMap (prodThomPairProj B F) m b =
      P.singularCohomologyπ R k M m z := by
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  have h0 := ConcreteCategory.congr_hom
    (P.singularCohomologyπ_comp_singularCohomologyMap R k M m) z
  rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h0
  rw [← hb, injective_singularCohomologyMap_prodThomPairPuncturedProj R M B m
    (h0.trans (map_zero _).symm), map_zero]

/-- Given a decomposition `D : H^q(B) × Hⁿ(B) ≃ₗ[k] H^q(B × (F ∖ {0}))` whose first summand is
pullback along `B × F → B` followed by restriction to `B × (F ∖ {0})`, the composite
`c ↦ δ (D (0, c))` is bijective `Hⁿ(B) → Hᵐ(B × F, B × (F ∖ {0}))` whenever `F` is contractible and
nontrivial and `q + 1 = m`. -/
theorem bijective_singularCohomologyδ_comp_inr_of_prodThomPair
    {k : Type*} [CommRing k] [Linear k (ModuleCat.{w} k)] (R M : ModuleCat.{w} k)
    {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F] [Zero F]
    [ContractibleSpace F] [Nontrivial F] {n q m : ℕ} (hqm : q + 1 = m)
    (D : ((TopCat.of B).singularCohomology R k M q ×
      (TopCat.of B).singularCohomology R k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology R k M q)
    (hD : ∀ b, D (b, 0) = TopCat.singularCohomologyMap (prodThomPair B F).map q
      (TopCat.singularCohomologyMap (prodThomPairProj B F) q b)) :
    Function.Bijective
      (((prodThomPair B F).singularCohomologyδ R k M q m hqm).hom ∘ₗ
        D.toLinearMap ∘ₗ LinearMap.inr k _ _) := by
  let P := prodThomPair B F
  let f := (P.singularCohomologyδ R k M q m hqm).hom ∘ₗ D.toLinearMap ∘ₗ LinearMap.inr k _ _
  have hf (c) : f c = P.singularCohomologyδ R k M q m hqm (D (0, c)) := rfl
  refine ⟨(injective_iff_map_eq_zero f).2 fun c hc ↦ ?_, fun z ↦ ?_⟩
  · rw [hf] at hc
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_subspace R k M q m hqm) _ hc
    let b := inv (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (prodThomPairProj B F) q) y
    have hb : TopCat.singularCohomologyMap (prodThomPairProj B F) q b = y := by
      rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
    rw [← hb, ← hD b] at hy
    exact congrArg Prod.snd (D.injective hy).symm
  · obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative R k M q m hqm) z
      (singularCohomologyπ_prodThomPair_eq_zero R M B m z)
    obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
    have hδ0 : P.singularCohomologyδ R k M q m hqm (D (b', 0)) = 0 := by
      rw [hD b', ← ConcreteCategory.comp_apply,
        P.singularCohomologyMap_comp_singularCohomologyδ R k M q m hqm]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
    have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
    refine ⟨c, ?_⟩
    rw [hf, hbc, map_add, map_add, hδ0, zero_add]

end RankIndependent

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] {d : ℕ}

/-- A point of the sphere `Sᵈ⁺¹`, at which the slant products of
`TopCat.singularCohomologySphereProdSlantEquiv` are taken. -/
private def sphereBasePoint (d : ℕ) : TopCat.sphere.{w} (d + 1) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- The standard generator of `Hᵈ(Sᵈ; k)` for every `d : ℕ`:
`TauCeti.singularCohomologyTopCatSphereZeroGenerator` at `d = 0` and
`TauCeti.singularCohomologyTopCatSphereGenerator` at `d + 1`. -/
private def sphereGen (k : Type w) [CommRing k] : (d : ℕ) →
    (TopCat.sphere.{w} d).singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d
  | 0 => singularCohomologyTopCatSphereZeroGenerator k
  | d + 1 => singularCohomologyTopCatSphereGenerator k d

/-- Unified decomposition `Hⁿ⁺ᵈ(Y; M) × Hⁿ(Y; M) ≃ₗ[k] Hⁿ⁺ᵈ(Sᵈ × Y; M)` for every `d : ℕ`. -/
private def sphereProdEquiv (M : ModuleCat.{w} k) (Y : TopCat.{w}) (n : ℕ) : (d : ℕ) →
    (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (TopCat.sphere.{w} d ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d)
  | 0 => TopCat.singularCohomologySphereZeroProdEquiv M Y n
  | d + 1 => (TopCat.singularCohomologySphereProdSlantEquiv M Y (sphereBasePoint d) n).symm

private theorem sphereProdEquiv_apply (M : ModuleCat.{w} k) (Y : TopCat.{w}) (n : ℕ) :
    ∀ (d : ℕ) (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n),
      sphereProdEquiv M Y n d bc =
        TopCat.singularCohomologyMap (snd _ Y) (n + d) bc.1 +
          (TopCat.sphere.{w} d ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
            d n (n + d) (add_comm d n)
            (TopCat.singularCohomologyMap (fst _ Y) d (sphereGen k d))
            (TopCat.singularCohomologyMap (snd _ Y) n bc.2)
  | 0, bc => TopCat.singularCohomologySphereZeroProdEquiv_apply M Y n bc
  | d + 1, bc => TopCat.singularCohomologySphereProdSlantEquiv_symm_apply M Y
      (sphereBasePoint d) n bc

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv`, as a morphism of
`TopCat`. -/
private abbrev sphereProdMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPair B F).snd ⟶ TopCat.sphere.{w} d ⊗ TopCat.of B :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun

variable (k B) in
/-- The class of `Hᵈ(B × (F ∖ {0}); k)` pulled back from the generator of `Hᵈ(Sᵈ; k)`
(`TauCeti.singularCohomologyTopCatSphereZeroGenerator` for `d = 0`,
`TauCeti.singularCohomologyTopCatSphereGenerator` for `d ≥ 1`) along the radial projection
`(b, x) ↦ e x / ‖e x‖`. -/
def prodThomPairPuncturedClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d :=
  TopCat.singularCohomologyMap (sphereProdMap e ≫ fst _ _) d (sphereGen k d)

variable (k B) in
/-- In rank `1` (`d = 0`), `TauCeti.prodThomPairPuncturedClass` is the pullback of
`TauCeti.singularCohomologyTopCatSphereZeroGenerator` along the first component of
`TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
theorem prodThomPairPuncturedClass_zero (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1)) :
    prodThomPairPuncturedClass k B e =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun ≫ fst _ _) 0
        (singularCohomologyTopCatSphereZeroGenerator k) :=
  (rfl)

variable (k B) in
/-- In rank `d + 2`, `TauCeti.prodThomPairPuncturedClass` is the pullback of
`TauCeti.singularCohomologyTopCatSphereGenerator` along the first component of
`TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
theorem prodThomPairPuncturedClass_succ (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    prodThomPairPuncturedClass k B e =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun ≫ fst _ _) (d + 1)
        (singularCohomologyTopCatSphereGenerator k d) :=
  (rfl)

/-- The composite of the homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv` with
the projection onto `B` is the projection of the punctured product bundle. -/
private theorem sphereProdMap_snd (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    sphereProdMap e ≫ snd _ _ = prodThomPairPuncturedProj B F :=
  TopCat.ext fun p ↦ (prodThomPairPuncturedHomotopyEquiv_apply_snd e p).trans
    (prodThomPairPuncturedProj_apply F p).symm

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv` induces isomorphisms
on singular cohomology. -/
private instance isIso_singularCohomologyMap_sphereProdMap
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
      (sphereProdMap (B := B) e) n) :=
  (prodThomPairPuncturedHomotopyEquiv B e).isIso_singularCohomologyMap _ k M n

/-- The decomposition of the cohomology of the punctured product bundle in degree `n + d`,
transported from that of `Sᵈ × B`. -/
private def puncturedEquivAux (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) :=
  (sphereProdEquiv M (TopCat.of B) n d).trans
    (asIso (TopCat.singularCohomologyMap (sphereProdMap e) (n + d))).toLinearEquiv

private theorem puncturedEquivAux_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    puncturedEquivAux M e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) (n + d) bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          d n (n + d) (add_comm d n) (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) := by
  rw [← sphereProdMap_snd e]
  simp only [puncturedEquivAux, LinearEquiv.trans_apply, sphereProdEquiv_apply,
    Iso.toLinearEquiv_apply, asIso_hom, map_add, prodThomPairPuncturedClass,
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, TopCat.singularCup_naturality]

/-- The map `(b, c) ↦ π^* b + σ ⌣ π^* c` into the cohomology of the punctured product bundle. -/
private def puncturedMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ)
    (h : n + d = m) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) →ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m).hom
    ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        d n m ((add_comm d n).trans h) (prodThomPairPuncturedClass k B e) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom)

private theorem puncturedMap_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ)
    (h : n + d = m)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    puncturedMap M e n m h bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          d n m ((add_comm d n).trans h) (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  -- `puncturedMap` is this sum by definition.
  (rfl)

private theorem bijective_puncturedMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ)
    (h : n + d = m) :
    Function.Bijective (puncturedMap (B := B) M e n m h) := by
  subst h
  have heq : ⇑(puncturedEquivAux (B := B) M e n) = puncturedMap M e n _ rfl :=
    funext fun bc ↦
      (puncturedEquivAux_apply M e n bc).trans (puncturedMap_apply M e n _ rfl bc).symm
  exact heq ▸ (puncturedEquivAux M e n).bijective

variable (B) in
/-- **The cohomology of the punctured product bundle in degrees at least `d`.** For a
continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹` and `m = n + d`, every class of
`Hᵐ(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c` with `b ∈ Hᵐ(B; M)` and `c ∈ Hⁿ(B; M)`,
where `π` is the projection to `B` and `σ` is the class `TauCeti.prodThomPairPuncturedClass`
(`TauCeti.prodThomPairPuncturedSingularCohomologyEquiv_apply`).
This is the decomposition of the cohomology of `Sᵈ × B`
(`TopCat.singularCohomologySphereZeroProdEquiv` for `d = 0`,
`TopCat.singularCohomologySphereProdSlantEquiv` for `d ≥ 1`), transported along the homotopy
equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
def prodThomPairPuncturedSingularCohomologyEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (n m : ℕ) (h : n + d = m := by lia) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (puncturedMap M e n m h) (bijective_puncturedMap M e n m h)

/-- The decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv` sends `(b, c)` to
`π^* b + σ ⌣ π^* c`. -/
@[simp]
theorem prodThomPairPuncturedSingularCohomologyEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + d = m)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairPuncturedSingularCohomologyEquiv M B e n m h bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          d n m ((add_comm d n).trans h) (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  puncturedMap_apply M e n m h bc

/-- The classes `π^* b` of the decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`
are the restrictions of the classes of `B × F` pulled back from `B`. -/
private theorem prodThomPairPuncturedSingularCohomologyEquiv_apply_zero
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + d = m)
    (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    prodThomPairPuncturedSingularCohomologyEquiv M B e n m h (b, 0) =
      TopCat.singularCohomologyMap (prodThomPair B F).map _
        (TopCat.singularCohomologyMap (prodThomPairProj B F) _ b) := by
  rw [prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, map_zero, add_zero,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]

/-- The map `c ↦ δ (σ ⌣ π^* c)`, written as `δ ∘ D ∘ inr` for the decomposition `D` of the
cohomology of the punctured product bundle. -/
private def sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ)
    (h : n + (d + 1) = m) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n →ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + n) m (by omega)).hom ∘ₗ
    (prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + n)).toLinearMap ∘ₗ
      LinearMap.inr k _ _

private theorem sphereDeltaMap_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ)
    (h : n + (d + 1) = m) (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    sphereDeltaMap M e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + n) m (by omega))
        ((prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + n)) (0, c)) :=
  -- `sphereDeltaMap` is this composite by definition.
  (rfl)

private theorem bijective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (n m : ℕ) (h : n + (d + 1) = m) :
    Function.Bijective (sphereDeltaMap (B := B) M e n m h) := by
  have : ContractibleSpace F := e.toHomeomorph.contractibleSpace
  have : Nontrivial F := e.toEquiv.nontrivial
  exact bijective_singularCohomologyδ_comp_inr_of_prodThomPair (𝟙_ (ModuleCat.{w} k)) M (by omega)
    (prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + n))
    (prodThomPairPuncturedSingularCohomologyEquiv_apply_zero M e n (d + n) (add_comm _ _))

variable (B) in
/-- **The cohomology of the Thom pair of a positive-rank product bundle in degrees at least its
rank.** Let `e : F ≃L[ℝ] ℝᵈ⁺¹` be a continuous linear equivalence, so that `F` has dimension
`r = d + 1 ≥ 1`. Then, for every base degree `n` and `m = n + r`, `c ↦ δ (σ ⌣ π^* c)` is a
`k`-linear equivalence `Hⁿ(B; M) ≃ Hᵐ(B × F, B × (F ∖ {0}); M)`, where `π : B × (F ∖ {0}) → B`
is the projection, `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); k)` is `TauCeti.prodThomPairPuncturedClass`, and `δ`
is the connecting morphism of the pair
(`TauCeti.prodThomPairSingularCohomologySphereEquiv_apply`). -/
def prodThomPairSingularCohomologySphereEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (n m : ℕ) (h : n + (d + 1) = m := by lia) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (sphereDeltaMap M e n m h) (bijective_sphereDeltaMap M e n m h)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends `c` to
`δ (σ ⌣ π^* c)`. -/
@[simp]
theorem prodThomPairSingularCohomologySphereEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + (d + 1) = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologySphereEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + n) m (by omega))
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          d n (d + n) rfl (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologySphereEquiv, LinearEquiv.ofBijective_apply,
    sphereDeltaMap_apply, prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, zero_add]

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends the unit
`1 ∈ H⁰(B; k)`, the class of the constant `0`-cocycle, to `δ σ`, where `σ` is
`TauCeti.prodThomPairPuncturedClass`. -/
theorem prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} k)) B e 0 (d + 1))
        (((TopCat.of B).singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k
          (𝟙_ (ModuleCat.{w} k))).homologyπ 0
          ((TopCat.of B).constSingularCocycle k (𝟙 (𝟙_ (ModuleCat.{w} k))))) =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        d (d + 1) rfl) (prodThomPairPuncturedClass k B e) := by
  rw [prodThomPairSingularCohomologySphereEquiv_apply,
    TopCat.singularCohomologyMap_homologyπ_constSingularCocycle]
  exact congrArg _ (TopCat.singularCup_constSingularCocycle_right _ k (η := 𝟙 _)
    (by simp [unitors_inv_equal]) (by simp [unitors_equal]) rfl _)

/-! ### Naturality in the base -/

section Naturality

variable {B' : Type w} [TopologicalSpace B'] (g : C(B, B'))

/-- The class `σ` of `TauCeti.prodThomPairPuncturedClass` is natural in the base. -/
@[simp]
theorem singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) d
        (prodThomPairPuncturedClass k B' e) = prodThomPairPuncturedClass k B e := by
  have h : TopPair.Hom.snd (prodThomPairMap F g) ≫ sphereProdMap e ≫ fst _ _ =
      sphereProdMap e ≫ fst _ _ := by
    ext p
    apply ULift.ext
    apply Subtype.ext
    refine ((coe_prodThomPairPuncturedHomotopyEquiv_apply_fst e _).trans ?_).trans
      (coe_prodThomPairPuncturedHomotopyEquiv_apply_fst e p).symm
    exact congrArg (fun x : F ↦ ‖e x‖⁻¹ • e x)
      (congrArg Prod.snd (prodThomPairMap_snd_apply F g p))
  rw [prodThomPairPuncturedClass, prodThomPairPuncturedClass, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, h]

/-- The decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv` is natural in the
base: restricting `π^* b + σ ⌣ π^* c` along the map induced by `g : B → B'` gives
`π^* (g^* b) + σ ⌣ π^* (g^* c)`. -/
theorem prodThomPairPuncturedSingularCohomologyEquiv_naturality
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + d = m := by lia)
    (bc : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) m
        (prodThomPairPuncturedSingularCohomologyEquiv M B' e n m h bc) =
      prodThomPairPuncturedSingularCohomologyEquiv M B e n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom g) m bc.1,
          TopCat.singularCohomologyMap (TopCat.ofHom g) n bc.2) := by
  rw [prodThomPairPuncturedSingularCohomologyEquiv_apply,
    prodThomPairPuncturedSingularCohomologyEquiv_apply, map_add,
    ← TopCat.singularCup_naturality,
    singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
  simp only [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    snd_prodThomPairMap_comp_prodThomPairPuncturedProj]

/-- **Naturality of the cohomology of the Thom pair of a product bundle.** The equivalence
`TauCeti.prodThomPairSingularCohomologySphereEquiv` commutes with the maps induced by a continuous
map `g : B → B'` of the bases. -/
theorem prodThomPairSingularCohomologySphereEquiv_naturality
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + (d + 1) = m := by lia)
    (c : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopPair.singularCohomologyMap (prodThomPairMap F g) m
        (prodThomPairSingularCohomologySphereEquiv M B' e n m h c) =
      prodThomPairSingularCohomologySphereEquiv M B e n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom g) n c) := by
  rw [prodThomPairSingularCohomologySphereEquiv, prodThomPairSingularCohomologySphereEquiv,
    LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, sphereDeltaMap_apply,
    sphereDeltaMap_apply, ← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) (d + n) m (by omega),
    ConcreteCategory.comp_apply,
    prodThomPairPuncturedSingularCohomologyEquiv_naturality M g e n _ (add_comm _ _), map_zero]

end Naturality

end TauCeti
