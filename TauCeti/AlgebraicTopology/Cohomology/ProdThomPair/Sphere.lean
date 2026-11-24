/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance

/-!
# Cohomology of the Thom pair of a product bundle in degrees at least the rank

Let `B` be a topological space and `F` a real topological vector space of positive dimension
`r = d + 1 ≥ 1`, given with a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺¹`. This file
computes the singular cohomology, with coefficients in any module `M` over a commutative ring `k`,
of the complement `B × (F ∖ {0})` of the zero section of the product bundle `B × F → B` in degrees
`n + d ≥ r - 1`, and of its Thom pair `(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`) in
degrees `n + r ≥ r`, for every base degree `n`.

* `B × (F ∖ {0})` is homotopy equivalent to `Sᵈ × B` by `(b, x) ↦ (e x / ‖e x‖, b)`
  (`TauCeti.prodThomPairPuncturedHomotopyEquiv`, in
  `TauCeti.AlgebraicTopology.Singular.ProdThomPair`). Let `σ ∈ Hᵈ(B × (F ∖ {0}); k)` be the
  pullback of the standard top class of `Hᵈ(Sᵈ; k)`
  (`TauCeti.singularCohomologyTopCatSphereTopClass`, in
  `TauCeti.AlgebraicTopology.Cohomology.Sphere.Basic`: the indicator of the positive pole for
  `d = 0` and the generator for `d ≥ 1`) along the first component
  (`TauCeti.prodThomPairPuncturedClass`), and `π : B × (F ∖ {0}) → B` the projection
  (`TauCeti.prodThomPairPuncturedProj`). The unified decomposition of the cohomology of `Sᵈ × B`
  (`TopCat.singularCohomologySphereTopProdEquiv`, in
  `TauCeti.AlgebraicTopology.Cohomology.Sphere.Product`) becomes
  `Hⁿ⁺ᵈ(B; M) × Hⁿ(B; M) ≃ Hⁿ⁺ᵈ(B × (F ∖ {0}); M)`, `(b, c) ↦ π^* b + σ ⌣ π^* c`
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
`TauCeti.isZero_singularHomology_prodThomPair` below `r`. In rank `1`, where `F ∖ {0}` has two
contractible components, `TauCeti.prodThomPairSingularCohomologyLineEquiv` describes the same
relative cohomology through the class of the positive side.

## Main definitions and results

* `TauCeti.prodThomPairPuncturedClass`: the class `σ` pulled back from the sphere `Sᵈ`.
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

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F] {d : ℕ}

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv`, as a morphism of
`TopCat`. -/
private abbrev sphereProdMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPair B F).snd ⟶ TopCat.sphere.{w} d ⊗ TopCat.of B :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun

variable (k B) in
/-- The class of `Hᵈ(B × (F ∖ {0}); k)` pulled back from `Hᵈ(Sᵈ; k)`
(`TauCeti.singularCohomologyTopCatSphereTopClass`) along the radial projection
`(b, x) ↦ e x / ‖e x‖`. -/
def prodThomPairPuncturedClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d :=
  TopCat.singularCohomologyMap
    (sphereProdMap e ≫ fst _ _) d
    (singularCohomologyTopCatSphereTopClass k d)

variable (k B) in
/-- The class `TauCeti.prodThomPairPuncturedClass` is the pullback of the standard class of
`Hᵈ(Sᵈ; k)` along the first component of `TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
theorem prodThomPairPuncturedClass_def (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    prodThomPairPuncturedClass k B e =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv B e).toFun ≫ fst _ _) d
        (singularCohomologyTopCatSphereTopClass k d) :=
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

/-- The decomposition of the cohomology of the punctured product bundle in the degree
`n + d`, transported from that of `Sᵈ × B`. -/
private def puncturedEquivAux (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + d) :=
  (TopCat.singularCohomologySphereTopProdEquiv M (TopCat.of B) d n).symm.trans
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
  simp only [puncturedEquivAux, LinearEquiv.trans_apply,
    TopCat.singularCohomologySphereTopProdEquiv_symm_apply,
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
This is the decomposition of the cohomology of `Sᵈ × B`, transported along the homotopy equivalence
`TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
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

variable (B) in
/-- **The cohomology of the Thom pair of a product bundle in degrees at least its rank.** Let
`e : F ≃L[ℝ] ℝᵈ⁺¹` be a continuous linear equivalence, so that `F` has dimension
`r = d + 1 ≥ 1`. Then, for every base degree `n` and `m = n + r`, `c ↦ δ (σ ⌣ π^* c)` is a
`k`-linear equivalence `Hⁿ(B; M) ≃ Hᵐ(B × F, B × (F ∖ {0}); M)`, where `π : B × (F ∖ {0}) → B`
is the projection, `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); k)` is `TauCeti.prodThomPairPuncturedClass`, and `δ`
is the connecting morphism of the pair
(`TauCeti.prodThomPairSingularCohomologySphereEquiv_apply`). -/
def prodThomPairSingularCohomologySphereEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (n m : ℕ) (h : n + (d + 1) = m := by lia) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m :=
  LinearEquiv.ofBijective
    (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + n) m).hom ∘ₗ
      (prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + n)).toLinearMap ∘ₗ
        LinearMap.inr k _ _) <| by
    have := e.toHomeomorph.contractibleSpace
    exact bijective_singularCohomologyδ_prodThomPair_comp_inr M
      (v := e.symm (EuclideanSpace.single 0 1)) (by simp) (d + n) m _
      (prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + n))
      (prodThomPairPuncturedSingularCohomologyEquiv_apply_zero M e n _ (add_comm _ _))

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` is `c ↦ δ (D (0, c))` for
the decomposition `D` of the cohomology of the punctured product bundle. -/
private theorem prodThomPairSingularCohomologySphereEquiv_eq
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + (d + 1) = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologySphereEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + n) m)
        ((prodThomPairPuncturedSingularCohomologyEquiv M B e n (d + n)) (0, c)) :=
  -- The equivalence is this composite by definition.
  (rfl)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends `c` to
`δ (σ ⌣ π^* c)`. -/
@[simp]
theorem prodThomPairSingularCohomologySphereEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) (n m : ℕ) (h : n + (d + 1) = m)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologySphereEquiv M B e n m h c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (d + n) m)
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          d n (d + n) rfl (prodThomPairPuncturedClass k B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologySphereEquiv_eq,
    prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, zero_add]

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
        d (d + 1)) (prodThomPairPuncturedClass k B e) := by
  rw [prodThomPairSingularCohomologySphereEquiv_apply,
    TopCat.singularCohomologyMap_homologyπ_constSingularCocycle]
  exact congrArg
    ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      d (d + 1))
    (TopCat.singularCup_constSingularCocycle_right _ k (η := 𝟙 _)
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
  rw [prodThomPairSingularCohomologySphereEquiv_eq, prodThomPairSingularCohomologySphereEquiv_eq,
    ← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) (d + n) m,
    ConcreteCategory.comp_apply,
    prodThomPairPuncturedSingularCohomologyEquiv_naturality M g e n _ (add_comm _ _), map_zero]

end Naturality

end TauCeti
