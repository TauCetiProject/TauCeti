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
# Cohomology of the Thom pair of a product bundle in every degree

Let `B` be a topological space and `F` a real normed space of dimension `r = d + 2 ≥ 2`, given
with a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²`. This file computes the singular
cohomology, with coefficients in any module `M` over a commutative ring `k`, of the complement
`B × (F ∖ {0})` of the zero section of the product bundle `B × F → B`, and of its Thom pair
`(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`), in every degree.

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
  `δ` identifies the classes `σ ⌣ π^* c` with the whole relative cohomology:
  `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
  `Hⁿ(B; M) ≃ Hⁿ⁺ʳ(B × F, B × (F ∖ {0}); M)` for every `n`
  (`TauCeti.prodThomPairSingularCohomologySphereEquiv`).

This is the computation behind the product case of the Thom isomorphism in cohomology, in every
degree, which is then extended by Mayer–Vietoris over unions of trivializing open sets. In degree
`r` alone, and for every rank, `TauCeti.prodThomPairSingularCohomologyEquiv` identifies
`Hʳ(B × F, B × (F ∖ {0}))` with `Hom(H₀(B), M)`; the homology counterpart in every degree and every
rank is
`TauCeti.prodThomPairSingularHomologyIso`. The ranks `0` and `1`, where `F ∖ {0}` is empty or has
two contractible components, are not treated here.

## Main definitions and results

* `TauCeti.prodThomPairPuncturedClass`: the class `σ` pulled back from the sphere.
* `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`: the cohomology of `B × (F ∖ {0})`.
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

variable {B : Type w} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ}

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv`, as a morphism of
`TopCat`. -/
private abbrev sphereProdMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    (prodThomPair B F).snd ⟶ TopCat.sphere.{w} (d + 1) ⊗ TopCat.of B :=
  TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv e).toFun

variable (k) in
/-- The class of `Hᵈ⁺¹(B × (F ∖ {0}); k)` pulled back from the generator of `Hᵈ⁺¹(Sᵈ⁺¹; k)`
(`TauCeti.singularCohomologyTopCatSphereGenerator`) along the radial projection
`(b, x) ↦ e x / ‖e x‖`. -/
def prodThomPairPuncturedClass (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))
      (d + 1) :=
  TopCat.singularCohomologyMap
    (sphereProdMap e ≫ fst _ _) (d + 1)
    (singularCohomologyTopCatSphereGenerator k d)

/-- The class `TauCeti.prodThomPairPuncturedClass` is the pullback of the generator of
`Hᵈ⁺¹(Sᵈ⁺¹; k)` along the first component of `TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
theorem prodThomPairPuncturedClass_def (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    prodThomPairPuncturedClass (B := B) k e =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (prodThomPairPuncturedHomotopyEquiv e).toFun ≫ fst _ _) (d + 1)
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
  TopCat.ext (prodThomPairPuncturedHomotopyEquiv_apply_snd e)

/-- The homotopy equivalence `TauCeti.prodThomPairPuncturedHomotopyEquiv` induces isomorphisms
on singular cohomology. -/
private instance isIso_singularCohomologyMap_sphereProdMap
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
      (sphereProdMap (B := B) e) n) :=
  (prodThomPairPuncturedHomotopyEquiv e).isIso_singularCohomologyMap _ k M n

/-- **The cohomology of the punctured product bundle.** For a continuous linear equivalence
`e : F ≃L[ℝ] ℝᵈ⁺²`, every class of `Hⁿ⁺ᵈ⁺¹(B × (F ∖ {0}); M)` is uniquely `π^* b + σ ⌣ π^* c`
with `b ∈ Hⁿ⁺ᵈ⁺¹(B; M)` and `c ∈ Hⁿ(B; M)`, where `π` is the projection to `B` and `σ` is the
class `TauCeti.prodThomPairPuncturedClass`
(`TauCeti.prodThomPairPuncturedSingularCohomologyEquiv_apply`).
This is the decomposition of the cohomology of `Sᵈ⁺¹ × B`
(`TopCat.singularCohomologySphereProdSlantEquiv`), transported along the homotopy equivalence
`TauCeti.prodThomPairPuncturedHomotopyEquiv`. -/
def prodThomPairPuncturedSingularCohomologyEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) ≃ₗ[k]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) :=
  (TopCat.singularCohomologySphereProdSlantEquiv M (TopCat.of B) (sphereBasePoint d) n).symm.trans
    (asIso (TopCat.singularCohomologyMap (sphereProdMap e) (n + (d + 1)))).toLinearEquiv

/-- The decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv` sends `(b, c)` to
`π^* b + σ ⌣ π^* c`. -/
@[simp]
theorem prodThomPairPuncturedSingularCohomologyEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairPuncturedSingularCohomologyEquiv M e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) (n + (d + 1)) bc.1 +
        (prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n (n + (d + 1)) (add_comm (d + 1) n) (prodThomPairPuncturedClass k e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) := by
  rw [← sphereProdMap_snd e]
  simp only [prodThomPairPuncturedSingularCohomologyEquiv, LinearEquiv.trans_apply,
    TopCat.singularCohomologySphereProdSlantEquiv_symm_apply, Iso.toLinearEquiv_apply, asIso_hom,
    map_add, prodThomPairPuncturedClass, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, TopCat.singularCup_naturality]

variable (B F) in
/-- The projection `B × F → B`, as a morphism out of the ambient space of the Thom pair. -/
private def baseProj : (prodThomPair B F).fst ⟶ TopCat.of B :=
  TopCat.ofHom ContinuousMap.fst

/-- Every class of `Hᵐ(B × F; M)` is pulled back from the base, since `F` is contractible. -/
private theorem exists_singularCohomologyMap_baseProj_eq (m : ℕ)
    (y : (prodThomPair B F).fst.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M m) :
    ∃ b, TopCat.singularCohomologyMap (baseProj B F) m b = y := by
  have := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} k)) k M m
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at this
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} k)) (k := k) (M := M)
    (baseProj B F) m) := this
  refine ⟨inv (TopCat.singularCohomologyMap (baseProj B F) m) y, ?_⟩
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
  have hs : s ≫ prodThomPairPuncturedProj B F = 𝟙 _ := rfl
  refine Function.LeftInverse.injective (g := TopCat.singularCohomologyMap s m) fun b ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hs,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

/-- The classes `π^* b` of the decomposition `TauCeti.prodThomPairPuncturedSingularCohomologyEquiv`
are the restrictions of the classes of `B × F` pulled back from `B`. -/
private theorem prodThomPairPuncturedSingularCohomologyEquiv_apply_zero
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1))) :
    prodThomPairPuncturedSingularCohomologyEquiv M e n (b, 0) =
      TopCat.singularCohomologyMap (prodThomPair B F).map _
        (TopCat.singularCohomologyMap (baseProj B F) _ b) := by
  rw [prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, map_zero, add_zero,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp]
  rfl

/-- The map `c ↦ δ (σ ⌣ π^* c)`, written as `δ ∘ D ∘ inr` for the decomposition `D` of the
cohomology of the punctured product bundle. -/
private def sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n →ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 2)) :=
  ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1))
    (n + (d + 2))).hom ∘ₗ
    (prodThomPairPuncturedSingularCohomologyEquiv M e n).toLinearMap ∘ₗ LinearMap.inr k _ _

private theorem sphereDeltaMap_apply (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    sphereDeltaMap M e n c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1))
        (n + (d + 2))) (prodThomPairPuncturedSingularCohomologyEquiv M e n (0, c)) :=
  -- `sphereDeltaMap` is this composite by definition.
  (rfl)

/-- `c ↦ δ (σ ⌣ π^* c)` is injective: if `δ (D (0, c)) = 0`, then `D (0, c)` is restricted from
`B × F`, where every class is pulled back from `B`, so `D (0, c) = D (b, 0)` for some `b`. -/
private theorem injective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    Function.Injective (sphereDeltaMap (B := B) M e n) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  rw [sphereDeltaMap_apply] at hc
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((prodThomPair B F).singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} k)) k M
      (n + (d + 1)) (n + (d + 2))) _ hc
  obtain ⟨b, rfl⟩ := exists_singularCohomologyMap_baseProj_eq M _ y
  rw [← prodThomPairPuncturedSingularCohomologyEquiv_apply_zero] at hy
  exact congrArg Prod.snd ((prodThomPairPuncturedSingularCohomologyEquiv M e n).injective hy).symm

/-- `c ↦ δ (σ ⌣ π^* c)` is surjective. A class `z` of the pair maps to a class of `B × F` pulled
back from `B` whose restriction to `B × (F ∖ {0})` vanishes; since `π^*` is injective, `z` maps to
zero, so `z = δ (D (b, c))` by exactness, and `δ (D (b, 0)) = 0` as `D (b, 0)` is restricted from
`B × F`. -/
private theorem surjective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    Function.Surjective (sphereDeltaMap (B := B) M e n) := by
  let P := prodThomPair B F
  let D := prodThomPairPuncturedSingularCohomologyEquiv (B := B) M e n
  intro z
  obtain ⟨b, hb⟩ := exists_singularCohomologyMap_baseProj_eq M _
    (P.singularCohomologyπ _ k M _ z)
  have hπ : P.singularCohomologyπ _ k M _ z = 0 := by
    have h0 := ConcreteCategory.congr_hom
      (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} k)) k M
        (n + (d + 2))) z
    rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp] at h0
    rw [← hb, injective_singularCohomologyMap_prodThomPairPuncturedProj M e _
      (h0.trans (map_zero _).symm), map_zero]
  obtain ⟨x, rfl⟩ : ∃ x, (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1))
      (n + (d + 2))) x = z :=
    (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1))
        (n + (d + 2))) z hπ
  obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
  refine ⟨c, ?_⟩
  have hδ : (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) (n + (d + 2)))
      (D (b', 0)) = 0 := by
    rw [prodThomPairPuncturedSingularCohomologyEquiv_apply_zero M e n b',
      ← ConcreteCategory.comp_apply,
      P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M
        (n + (d + 1)) (n + (d + 2))]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  have hbc : ((b', c) : _ × _) = (b', 0) + (0, c) := by simp
  rw [sphereDeltaMap_apply, hbc, map_add, map_add, hδ, zero_add]

private theorem bijective_sphereDeltaMap (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ) :
    Function.Bijective (sphereDeltaMap (B := B) M e n) :=
  ⟨injective_sphereDeltaMap M e n, surjective_sphereDeltaMap M e n⟩

/-- **The cohomology of the Thom pair of a product bundle in every degree.** Let `F` be a real
normed space with a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²`, so that `F` has dimension
`r = d + 2 ≥ 2`. Then `c ↦ δ (σ ⌣ π^* c)` is a `k`-linear equivalence
`Hⁿ(B; M) ≃ Hⁿ⁺ʳ(B × F, B × (F ∖ {0}); M)` for every `n`, where `π : B × (F ∖ {0}) → B` is the
projection, `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); k)` is `TauCeti.prodThomPairPuncturedClass`, and `δ` is the
connecting morphism of the pair (`TauCeti.prodThomPairSingularCohomologySphereEquiv_apply`). -/
def prodThomPairSingularCohomologySphereEquiv (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    (n : ℕ) :
    (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 2)) :=
  LinearEquiv.ofBijective (sphereDeltaMap M e n) (bijective_sphereDeltaMap M e n)

/-- The equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` sends `c` to
`δ (σ ⌣ π^* c)`. -/
@[simp]
theorem prodThomPairSingularCohomologySphereEquiv_apply
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    prodThomPairSingularCohomologySphereEquiv M e n c =
      ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1))
        (n + (d + 2)))
        ((prodThomPair B F).snd.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          (d + 1) n (n + (d + 1)) (add_comm (d + 1) n) (prodThomPairPuncturedClass k e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c)) := by
  rw [prodThomPairSingularCohomologySphereEquiv, LinearEquiv.ofBijective_apply,
    sphereDeltaMap_apply, prodThomPairPuncturedSingularCohomologyEquiv_apply, map_zero, zero_add]

/-! ### Naturality in the base -/

section Naturality

variable {B' : Type w} [TopologicalSpace B'] (g : C(B, B'))

/-- The class `σ` of `TauCeti.prodThomPairPuncturedClass` is natural in the base. -/
@[simp]
theorem singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) (d + 1)
        (prodThomPairPuncturedClass k e) = prodThomPairPuncturedClass (B := B) k e := by
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
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (bc : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M (n + (d + 1)) ×
      (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) (n + (d + 1))
        (prodThomPairPuncturedSingularCohomologyEquiv M e n bc) =
      prodThomPairPuncturedSingularCohomologyEquiv M e n
        (TopCat.singularCohomologyMap (TopCat.ofHom g) (n + (d + 1)) bc.1,
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
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) (n : ℕ)
    (c : (TopCat.of B').singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopPair.singularCohomologyMap (prodThomPairMap F g) (n + (d + 2))
        (prodThomPairSingularCohomologySphereEquiv M e n c) =
      prodThomPairSingularCohomologySphereEquiv M e n
        (TopCat.singularCohomologyMap (TopCat.ofHom g) n c) := by
  simp only [prodThomPairSingularCohomologySphereEquiv, LinearEquiv.ofBijective_apply,
    sphereDeltaMap_apply]
  rw [← ConcreteCategory.comp_apply,
    TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) (n + (d + 1)) (n + (d + 2)),
    ConcreteCategory.comp_apply, prodThomPairPuncturedSingularCohomologyEquiv_naturality, map_zero]

end Naturality

end TauCeti
