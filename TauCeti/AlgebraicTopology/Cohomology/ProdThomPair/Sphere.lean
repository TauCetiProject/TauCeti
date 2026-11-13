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

/-!
# Cohomology of the Thom pair of a product bundle in degrees at least the rank

Let `B` be a topological space and `F` a real topological vector space of dimension
`r = d + 2 ≥ 2`, given with a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²`. This file
computes the singular cohomology, with coefficients in any module `M` over a commutative ring `k`,
of the complement `B × (F ∖ {0})` of the zero section of the product bundle `B × F → B` in degrees
`n + (d + 1) ≥ r - 1`, and of its Thom pair `(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) in
degrees `n + r ≥ r`, for every base degree `n`.

* `B × (F ∖ {0})` is homotopy equivalent to `Sᵈ⁺¹ × B` by `(b, x) ↦ (e x / ‖e x‖, b)`
  (`TauCeti.prodThomPairPuncturedHomotopyEquiv`, in
  `TauCeti.AlgebraicTopology.Singular.ProdThomPair`). Let `σ ∈ Hᵈ⁺¹(B × (F ∖ {0}); k)` be the
  pullback of the generator of `Hᵈ⁺¹(Sᵈ⁺¹; k)` along the first component
  (`TauCeti.prodThomPairPuncturedClass`), and `π : B × (F ∖ {0}) → B` the projection
  (`TauCeti.prodThomPairPuncturedProj`). The decomposition of the cohomology of `Sᵈ⁺¹ × B`
  (`TopCat.singularCohomologySphereProdSlantEquiv`) becomes
  `Hⁿ⁺ᵈ⁺¹(B; M) × Hⁿ(B; M) ≃ Hⁿ⁺ᵈ⁺¹(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`
  (`TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`).
* In the long exact sequence of the pair, the restriction from `Hᵐ(B × F; M)` to
  `Hᵐ(B × (F ∖ {0}); M)` is injective, since `F` is contractible and the projection
  `B × (F ∖ {0}) → B` has a section; its image is the classes `π^* b`. So the connecting morphism
  `δ` identifies the classes `σ ⌣ π^* c` with the whole relative cohomology in degree `n + r`:
  `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
  `Hⁿ(B; M) ≃ Hⁿ⁺ʳ(B × F, B × (F ∖ {0}); M)` for every `n`
  (`TauCeti.prodThomPairSingularCohomologySphereEquiv`). It sends the unit of `H⁰(B; k)` to `δ σ`
  (`TauCeti.prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle`).

This is the computation behind the product case of the Thom isomorphism in cohomology, which is
then extended by Mayer–Vietoris over unions of trivializing open sets. Below degree `r` the
relative cohomology vanishes (`TauCeti.isZero_singularCohomology_prodThomPair`), and in degree `r`
alone, for every rank, `TauCeti.prodThomPairSingularCohomologyEquiv` identifies
`Hʳ(B × F, B × (F ∖ {0}))` with `Hom(H₀(B), M)`; both are in
`TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic`. The homology counterpart for every rank
is `TauCeti.prodThomPairSingularHomologyIso` in degrees `n + r`, with
`TauCeti.isZero_singularHomology_prodThomPair` below `r`. The ranks `0` and `1`, where `F ∖ {0}`
is empty or has two contractible components, are not treated here.

## Main definitions and results

* `TauCeti.prodThomPairPuncturedClass`: the class `σ` pulled back from the sphere.
* `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`:
  `Hⁿ⁺ᵈ⁺¹(B; M) × Hⁿ(B; M) ≃ Hⁿ⁺ᵈ⁺¹(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`.
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

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] {d : ℕ}

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv`, as a morphism of
`TopCat`. -/
private abbrev sphereProdMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    (prodThomPair B F).snd ⟶ TopCat.sphere.{w} (d + 1) ⊗ TopCat.of B :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun

variable (k B) in
/-- The class of `Hᵈ⁺¹(B × (F ∖ {0}); k)` pulled back from the generator of `Hᵈ⁺¹(Sᵈ⁺¹; k)`
(`TauCeti.singularCohomologyTopCatSphereGenerator`) along the radial projection
`(b, x) ↦ e x / ‖e x‖`. -/
def prodThomPairPuncturedClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      (d + 1) :=
  TopCat.singularCohomologyMap
    (sphereProdMap e ≫ fst _ _) (d + 1)
    (singularCohomologyTopCatSphereGenerator k d)

variable (k B) in
/-- The class `TauCeti.prodThomPairPuncturedClass` is the pullback of the generator of
`Hᵈ⁺¹(Sᵈ⁺¹; k)` along the first component of `TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
theorem prodThomPairPuncturedClass_def (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    prodThomPairPuncturedClass k B e =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun ≫ fst _ _) (d + 1)
        (singularCohomologyTopCatSphereGenerator k d) :=
  (rfl)

/-- A point of the sphere `Sᵈ⁺¹`, at which the slant products of
`TopCat.singularCohomologySphereProdSlantEquiv` are taken. -/
private def sphereBasePoint (d : ℕ) : TopCat.sphere.{w} (d + 1) :=
  ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- The composite of the homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv` with
the projection onto `B` is the projection of the punctured product bundle. -/
private theorem sphereProdMap_snd (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    sphereProdMap e ≫ snd _ _ = prodThomPairPuncturedProj B F :=
  TopCat.ext fun p ↦ (prodThomPairPuncturedHomotopyEquiv_apply_snd e p).trans
    (prodThomPairPuncturedProj_apply F p).symm

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv` induces isomorphisms
on singular cohomology. -/
private instance isIso_singularCohomologyMap_sphereProdMap
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
      (sphereProdMap (B := B) e) n) :=
  (prodThomPairPuncturedHomotopyEquiv B e).isIso_singularCohomologyMap _ k M n

/-- The decomposition of the cohomology of the punctured product bundle in the degree
`n + (d + 1)`, transported from that of `Sᵈ⁺¹ × B`. -/
private def puncturedEquivAux (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) :=
  (TopCat.singularCohomologySphereProdSlantEquiv M (TopCat.of B) (sphereBasePoint d) n).symm.trans
    (asIso (TopCat.singularCohomologyMap (sphereProdMap e) (n + (d + 1)))).toLinearEquiv

private theorem puncturedEquivAux_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    puncturedEquivAux M e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) (n + (d + 1)) bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n (n + (d + 1)) (add_comm (d + 1) n) (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) := by
  rw [← sphereProdMap_snd e]
  simp only [puncturedEquivAux, LinearEquiv.trans_apply,
    TopCat.singularCohomologySphereProdSlantEquiv_symm_apply, Iso.toLinearEquiv_apply, asIso_hom,
    map_add, prodThomPairPuncturedClass, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, TopCat.singularCup_naturality]

/-- The map `(b, c) ↦ π^* b + σ ⌣ π^* c` into the cohomology of the punctured product bundle. -/
private def puncturedMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ)
    (h : n + (d + 1) = m) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) →ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m).hom
    ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        (d + 1) n m ((add_comm (d + 1) n).trans h) (prodThomPairPuncturedClass k B e) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom)

private theorem puncturedMap_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ)
    (h : n + (d + 1) = m)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    puncturedMap M e n m h bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n m ((add_comm (d + 1) n).trans h) (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  -- `puncturedMap` is this sum by definition.
  (rfl)

private theorem bijective_puncturedMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ)
    (h : n + (d + 1) = m) :
    Function.Bijective (puncturedMap (B := B) M e n m h) := by
  subst h
  have heq : ⇑(puncturedEquivAux (B := B) M e n) = puncturedMap M e n _ rfl :=
    funext fun bc ↦
      (puncturedEquivAux_apply M e n bc).trans (puncturedMap_apply M e n _ rfl bc).symm
  exact heq ▸ (puncturedEquivAux M e n).bijective

variable (B) in
/-- **The cohomology of the punctured product bundle in degrees at least `d + 1`.** For a
continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²` and `m = n + (d + 1)`, every class of
`Hᵐ(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c` with `b ∈ Hᵐ(B; M)` and `c ∈ Hⁿ(B; M)`,
where `π` is the projection to `B` and `σ` is the class `TauCeti.prodThomPairPuncturedClass`
(`TauCeti.prodThomPairPuncturedSingularCohomologyEquiv_apply`).
This is the decomposition of the cohomology of `Sᵈ⁺¹ × B`
(`TopCat.singularCohomologySphereProdSlantEquiv`), transported along the homotopy equivalence
`TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
def prodThomPairPuncturedSingularCohomologyEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n m : ℕ) (h : n + (d + 1) = m := by lia) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (puncturedMap M e n m h) (bijective_puncturedMap M e n m h)

/-- The decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv` sends `(b, c)` to
`π^* b + σ ⌣ π^* c`. -/
@[simp]
theorem prodThomPairPuncturedSingularCohomologyEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ) (h : n + (d + 1) = m)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairPuncturedSingularCohomologyEquiv M B e n m h bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) m bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n m ((add_comm (d + 1) n).trans h) (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  puncturedMap_apply M e n m h bc

omit [Module ℝ F] in
/-- Every class of `Hᵐ(B × F; M)` is pulled back from the base, since `F` is contractible. -/
private theorem exists_singularCohomologyMap_prodThomPairProj_eq [ContractibleSpace F] (m : ℕ)
    (y : (prodThomPair B F).fst.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    ∃ b, TopCat.singularCohomologyMap (prodThomPairProj B F) m b = y := by
  have := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} k)) k M m
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at this
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply F p).symm
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
    (prodThomPairProj B F) m) := hproj ▸ this
  refine ⟨inv (TopCat.singularCohomologyMap (prodThomPairProj B F) m) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- Pulling back along the projection `B × (F ∖ {0}) → B` is injective, since the projection has
the section `b ↦ (b, e⁻¹ v)` for a unit vector `v`. -/
private theorem injective_singularCohomologyMap_prodThomPairPuncturedProj
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (m : ℕ) :
    Function.Injective (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k)
      (M := M) (prodThomPairPuncturedProj B F) m) := by
  let v : F := e.symm (EuclideanSpace.single 0 1)
  have hv : v ≠ 0 := by simp [v]
  let s : TopCat.of B ⟶ (prodThomPair B F).snd :=
    TopCat.ofHom ⟨fun b ↦ ⟨(b, v), hv⟩, by fun_prop⟩
  have hs : s ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
    TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (s b)
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap s m) fun b ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hs,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

/-- The classes `π^* b` of the decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`
are the restrictions of the classes of `B × F` pulled back from `B`. -/
private theorem prodThomPairPuncturedSingularCohomologyEquiv_apply_zero
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ) (h : n + (d + 1) = m)
    (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    prodThomPairPuncturedSingularCohomologyEquiv M B e n m h (b, 0) =
      TopCat.singularCohomologyMap (prodThomPair B F).map _
        (TopCat.singularCohomologyMap (prodThomPairProj B F) _ b) := by
  rw [prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, map_zero, add_zero,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]

/-- The map `c ↦ δ (σ ⌣ π^* c)`, written as `δ ∘ D ∘ inr` for the decomposition `D` of the
cohomology of the punctured product bundle. -/
private def sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ)
    (h : n + (d + 2) = m) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n →ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m).hom ∘ₗ
    (prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + 1 + n)).toLinearMap ∘ₗ
      LinearMap.inr k _ _

private theorem sphereDeltaMap_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ)
    (h : n + (d + 2) = m) (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    sphereDeltaMap M e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m)
        ((prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + 1 + n)) (0, c)) :=
  -- `sphereDeltaMap` is this composite by definition.
  (rfl)

/-- `c ↦ δ (σ ⌣ π^* c)` is injective: if `δ (D (0, c)) = 0`, then `D (0, c)` is restricted from
`B × F`, where every class is pulled back from `B`, so `D (0, c) = D (b, 0)` for some `b`. -/
private theorem injective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n m : ℕ) (h : n + (d + 2) = m) :
    Function.Injective (sphereDeltaMap (B := B) M e n m h) := by
  have := e.toHomeomorph.contractibleSpace
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  rw [sphereDeltaMap_apply] at hc
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((prodThomPair B F).singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} k)) k M
      (d + 1 + n) m) _ hc
  obtain ⟨b, rfl⟩ := exists_singularCohomologyMap_prodThomPairProj_eq M _ y
  rw [← prodThomPairPuncturedSingularCohomologyEquiv_apply_zero M e n _ (add_comm _ _)] at hy
  exact congrArg Prod.snd
    ((prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + 1 + n)).injective hy).symm

/-- `c ↦ δ (σ ⌣ π^* c)` is surjective. A class `z` of the pair maps to a class of `B × F` pulled
back from `B` whose restriction to `B × (F ∖ {0})` vanishes; since `π^*` is injective, `z` maps to
zero, so `z = δ (D (b, c))` by exactness, and `δ (D (b, 0)) = 0` as `D (b, 0)` is restricted from
`B × F`. -/
private theorem surjective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n m : ℕ) (h : n + (d + 2) = m) :
    Function.Surjective (sphereDeltaMap (B := B) M e n m h) := by
  have := e.toHomeomorph.contractibleSpace
  let P := prodThomPair B F
  let D := prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + 1 + n)
  intro z
  obtain ⟨b, hb⟩ := exists_singularCohomologyMap_prodThomPairProj_eq M _
    (P.singularCohomologyπ _ k M _ z)
  have hπ : P.singularCohomologyπ _ k M _ z = 0 := by
    have h0 := ConcreteCategory.congr_hom
      (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} k)) k M m) z
    rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
    rw [← hb, injective_singularCohomologyMap_prodThomPairPuncturedProj M e _
      (h0.trans (map_zero _).symm), map_zero]
  obtain ⟨x, rfl⟩ : ∃ x, (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m) x = z :=
    (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m) z hπ
  obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
  refine ⟨c, ?_⟩
  have hδ : (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m) (D (b', 0)) = 0 := by
    rw [prodThomPairPuncturedSingularCohomologyEquiv_apply_zero M e n _ (add_comm _ _) b',
      ← ConcreteCategory.comp_apply,
      P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
  rw [sphereDeltaMap_apply, hbc, map_add, map_add, hδ, zero_add]

private theorem bijective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n m : ℕ) (h : n + (d + 2) = m) :
    Function.Bijective (sphereDeltaMap (B := B) M e n m h) :=
  ⟨injective_sphereDeltaMap M e n m h, surjective_sphereDeltaMap M e n m h⟩

variable (B) in
/-- **The cohomology of the Thom pair of a product bundle in degrees at least its rank.** Let
`e : F ≃L[ℝ] ℝᵈ⁺²` be a continuous linear equivalence, so that `F` has dimension
`r = d + 2 ≥ 2`. Then, for every base degree `n` and `m = n + r`, `c ↦ δ (σ ⌣ π^* c)` is a
`k`-linear equivalence `Hⁿ(B; M) ≃ Hᵐ(B × F, B × (F ∖ {0}); M)`, where `π : B × (F ∖ {0}) → B`
is the projection, `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); k)` is `TauCeti.prodThomPairPuncturedClass`, and `δ`
is the connecting morphism of the pair
(`TauCeti.prodThomPairSingularCohomologySphereEquiv_apply`). -/
def prodThomPairSingularCohomologySphereEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n m : ℕ) (h : n + (d + 2) = m := by lia) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective (sphereDeltaMap M e n m h) (bijective_sphereDeltaMap M e n m h)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends `c` to
`δ (σ ⌣ π^* c)`. -/
@[simp]
theorem prodThomPairSingularCohomologySphereEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ) (h : n + (d + 2) = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologySphereEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + 1 + n) m)
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n (d + 1 + n) rfl (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologySphereEquiv, LinearEquiv.ofBijective_apply,
    sphereDeltaMap_apply, prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, zero_add]

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends the unit
`1 ∈ H⁰(B; k)`, the class of the constant `0`-cocycle, to `δ σ`, where `σ` is
`TauCeti.prodThomPairPuncturedClass`. -/
theorem prodThomPairSingularCohomologySphereEquiv_homologyπ_constSingularCocycle
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    (prodThomPairSingularCohomologySphereEquiv (𝟙_ (ModuleCat.{w} k)) B e 0 (d + 2))
        (((TopCat.of B).singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k
          (𝟙_ (ModuleCat.{w} k))).homologyπ 0
          ((TopCat.of B).constSingularCocycle k (𝟙 (𝟙_ (ModuleCat.{w} k))))) =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass k B e) := by
  rw [prodThomPairSingularCohomologySphereEquiv_apply,
    TopCat.singularCohomologyMap_homologyπ_constSingularCocycle,
    TopCat.singularCup_constSingularCocycle_right _ k (η := 𝟙 _)
      (by simp [unitors_inv_equal]) (by simp [unitors_equal])]

/-! ### Naturality in the base -/

section Naturality

variable {B' : Type w} [TopologicalSpace B'] (g : C(B, B'))

/-- The class `σ` of `TauCeti.prodThomPairPuncturedClass` is natural in the base. -/
@[simp]
theorem singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) (d + 1)
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
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ) (h : n + (d + 1) = m := by lia)
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
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n m : ℕ) (h : n + (d + 2) = m := by lia)
    (c : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopPair.singularCohomologyMap (prodThomPairMap F g) m
        (prodThomPairSingularCohomologySphereEquiv M B' e n m h c) =
      prodThomPairSingularCohomologySphereEquiv M B e n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom g) n c) := by
  rw [prodThomPairSingularCohomologySphereEquiv, prodThomPairSingularCohomologySphereEquiv,
    LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, sphereDeltaMap_apply,
    sphereDeltaMap_apply, ← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) (d + 1 + n) m,
    ConcreteCategory.comp_apply,
    prodThomPairPuncturedSingularCohomologyEquiv_naturality M g e n _ (add_comm _ _), map_zero]

end Naturality

end TauCeti
