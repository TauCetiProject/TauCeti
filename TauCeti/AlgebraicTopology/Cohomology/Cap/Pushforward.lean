/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.ChainMap
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
import TauCeti.CategoryTheory.Preadditive.Injective.Basic

/-!
# The relative cap product followed by push-forward

For a topological pair `P = (X, Z)`, a continuous map `p₀ : X ⟶ Y`, and a relative class
`u ∈ Hⁿ(X, Z; K)` over a commutative ring `K`, this file defines the homological counterpart of
`TopPair.pullbackCup`,

`TopPair.pushforwardCap`: `Hₘ(X, Z; A) ⟶ Hₚ(Y; A)`, `x ↦ p₀_*(x ⌢ u)` (`n + p = m`),

as a `K`-linear map in `u` for any `K`-module `A`. Applied to the Thom pair `(E, E₀)` of a bundle
and its projection `π : E ⟶ B`, this is `TauCeti.homologyThomMap`.

Under the Kronecker pairing (`TopPair.singularCap_comp_singularKronecker`) and graded commutativity
(`TopPair.singularCup_gradedComm`), `pushforwardCap` is transpose to `TopPair.pullbackCup` up to
`(-1)^(n p)`: `⟨a, p₀_*(x ⌢ u)⟩ = (-1)^(n p) ⟨p₀^* a ⌣ u, x⟩`
(`TopPair.pushforwardCap_comp_singularKronecker`). Over a field `K`, universal coefficient duality
(`TopCat.singularCohomologyDualEquiv`, `TopPair.singularCohomologyDualEquiv`) implies that
bijectivity of `p₀_*(- ⌢ u)` on `K`-homology is equivalent to that of `p₀^*(-) ⌣ u` on
`K`-cohomology (`TopPair.bijective_pushforwardCap_iff`). Over any commutative ring `K`, when the
Kronecker maps of `Y` in degree `p` and of `(X, Z)` in degree `m` are bijective, invertibility
of `p₀_*(- ⌢ u)` yields bijectivity of `TopPair.pullbackCup` for `M`
(`TopPair.bijective_pullbackCup_of_isIso_pushforwardCap`). Conversely, over any commutative ring,
if `p₀^*(-) ⌣ u` is bijective with coefficients in every injective `K`-module, then `p₀_*(- ⌢ u)` is
an isomorphism on `K`-homology (`TopPair.isIso_pushforwardCap_of_bijective_pullbackCup`): for
injective coefficients the Kronecker maps are bijective, so precomposition with `p₀_*(- ⌢ u)` is
bijective on morphisms into every injective module, and injective modules detect isomorphisms
(`CategoryTheory.Injective.isCoseparating_isInjective` and
`CategoryTheory.ObjectProperty.IsCoseparating.isCodetecting`).

At the chain level, a relative cocycle `φ` of degree `n` representing `u` gives a chain map
`x ↦ (-1)^(n p) p₀_*(x ⌢ φ)` from the relative chains of `(X, Z)` to the chains of `Y` placed `n`
degrees higher (`TopPair.pushforwardCapChainMap`, an instance of
`TauCeti.ChainComplex.capChainMap`). It induces `p₀_*(- ⌢ u)` on homology up to sign, so it is a
quasi-isomorphism when `p₀_*(- ⌢ u)` is an isomorphism in every degree and the relative homology
vanishes below `n` (`TopPair.quasiIso_pushforwardCapChainMap`), and it is natural in maps of pairs
(`TopPair.pushforwardCapChainMap_naturality`). This is the form in which the homology Thom
isomorphism can be compared with chain maps, for instance equivariant ones.

## Main definitions and results

* `TopPair.pushforwardCap`, `TopPair.pushforwardCap_naturality`: `x ↦ p₀_*(x ⌢ u)` and naturality.
* `TopPair.pushforwardCap_eq_cap`: `pushforwardCap` as a single `TauCeti.ChainComplex.cap`.
* `TopPair.pushforwardCap_comp_singularKronecker`: Kronecker duality with `TopPair.pullbackCup`.
* `TopPair.bijective_pushforwardCap_iff`: field duality between `pushforwardCap` and `pullbackCup`.
* `TopPair.bijective_pullbackCup_of_isIso_pushforwardCap`: duality transferring invertibility of
  `pushforwardCap` to bijectivity of `pullbackCup` when the Kronecker maps in degrees `p` and `m`
  are bijective.
* `TopPair.isIso_pushforwardCap_of_bijective_pullbackCup`: over any commutative ring, bijectivity
  of `pullbackCup` for all injective coefficient modules makes `pushforwardCap` an isomorphism.
* `TopPair.pushforwardCapChainMap`: `x ↦ p₀_*(x ⌢ φ)` for a relative cocycle `φ`, as a chain map
  to the shifted chains of `Y`, with its naturality `TopPair.pushforwardCapChainMap_naturality`.
* `TopPair.homologyMap_pushforwardCapChainMap_comp_extendHomologyIso_hom`: on homology it is
  `pushforwardCap` of the class of `φ`, up to sign.
* `TopPair.quasiIso_pushforwardCapChainMap`: it is a quasi-isomorphism when `pushforwardCap` of
  the class is an isomorphism in every degree and the relative homology vanishes below `n`.

## References

* E. H. Spanier, *Algebraic Topology*, Chapter 5, §§6–7.
* A. Hatcher, *Algebraic Topology*, §3.3.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory MonoidalCategory

universe w

namespace TopPair

/-- For `P = (X, Z)`, `p₀ : X ⟶ Y`, and `u ∈ Hⁿ(X, Z; K)`, the morphism `Hₘ(X, Z; A) ⟶ Hₚ(Y; A)`,
`x ↦ p₀_*(x ⌢ u)` (`n + p = m`), `K`-linear in `u` (`TopPair.singularCap` followed by `(Hₚ).map p₀`,
paired via the left unitor `K ⊗ A ≅ A`). -/
def pushforwardCap {K : Type w} [CommRing K] (P : TopPair.{w}) {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y)
    (A : ModuleCat.{w} K) (n p m : ℕ) (h : n + p = m) :
    P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (P.singularHomology A m ⟶
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj Y) :=
  Linear.rightComp K _
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map p₀) ∘ₗ
    P.singularCap K (λ_ A).inv (λ_ A).hom n p m h

/-- `TopPair.pushforwardCap` is `TopPair.singularCap` postcomposed with `(Hₚ(-; A)).map p₀`. -/
theorem pushforwardCap_apply {K : Type w} [CommRing K] (P : TopPair.{w}) {Y : TopCat.{w}}
    (p₀ : P.fst ⟶ Y) (A : ModuleCat.{w} K) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.pushforwardCap p₀ A n p m h u = P.singularCap K (λ_ A).inv (λ_ A).hom n p m h u ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map p₀ := (rfl)

/-- `TopPair.pushforwardCap` is the cap product `TauCeti.ChainComplex.cap` along the relative
Alexander–Whitney diagonal, with the pairing of coefficients followed by the push-forward along
`p₀` as the action. -/
theorem pushforwardCap_eq_cap {K : Type w} [CommRing K] (P : TopPair.{w}) {Y : TopCat.{w}}
    (p₀ : P.fst ⟶ Y) (A : ModuleCat.{w} K) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.pushforwardCap p₀ A n p m h u =
      TauCeti.ChainComplex.cap K (P.alexanderWhitneyDiagonal (λ_ A).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
          SSet.chainComplexMap (TopCat.toSSet.map p₀) A) n p m h u := by
  have := TauCeti.ChainComplex.cap_naturality (k := K) (P.alexanderWhitneyDiagonal (λ_ A).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) A)
    (P.alexanderWhitneyDiagonal (λ_ A).inv) ((TopCat.toSSet.obj P.fst).chainComplexPairing
      (λ_ A).hom) (𝟙 _) (𝟙 _) (𝟙 _) (SSet.chainComplexMap (TopCat.toSSet.map p₀) A)
    (by simp) (by simp) n p m h u
  simp only [op_id, CategoryTheory.Functor.map_id, TauCeti.ChainComplex.linearYonedaFunctor_obj,
    HomologicalComplex.homologyMap_id, ModuleCat.hom_id, LinearMap.id_coe, id_eq,
    Category.id_comp] at this
  rw [pushforwardCap_apply, singularCap_def]
  exact this

/-- **Naturality of `x ↦ p₀_*(x ⌢ u)`** in maps of pairs covering maps of targets. -/
theorem pushforwardCap_naturality {K : Type w} [CommRing K] {P P' : TopPair.{w}}
    {Y Y' : TopCat.{w}} (φ : P' ⟶ P) (p₀ : P.fst ⟶ Y) (p₀' : P'.fst ⟶ Y') (g : Y' ⟶ Y)
    (hφ : TopPair.Hom.fst φ ≫ p₀ = p₀' ≫ g) (A : ModuleCat.{w} K) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P'.pushforwardCap p₀' A n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
      TopPair.singularHomologyMap φ A m ≫ P.pushforwardCap p₀ A n p m h u := by
  rw [pushforwardCap_apply, pushforwardCap_apply, Category.assoc, ← Functor.map_comp, ← hφ,
    Functor.map_comp, ← Category.assoc, TopPair.singularCap_naturality, Category.assoc]

/-- **Kronecker duality between `TopPair.pushforwardCap` and `TopPair.pullbackCup`**:
`⟨a, p₀_*(x ⌢ u)⟩ = (-1)^(n p) ⟨p₀^* a ⌣ u, x⟩` for `u ∈ Hⁿ(P; K)`, `a ∈ Hᵖ(Y; K, M)`, `n + p = m`.
-/
theorem pushforwardCap_comp_singularKronecker {K : Type w} [CommRing K] (P : TopPair.{w})
    {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y) {M : ModuleCat.{w} K} {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    P.pushforwardCap p₀ (ModuleCat.of K K) n p m h u ≫ Y.singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • P.singularKronecker K m (P.pullbackCup M p₀ n p m (by omega) u a) := by
  rw [pushforwardCap_apply, Category.assoc, ← TopCat.singularKronecker_naturality,
    TopPair.singularCap_comp_singularKronecker, TopPair.pullbackCup_apply,
    TopPair.singularCup_gradedComm K P (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ M).hom) (μ := (ρ_ M).hom) ?_ ?_ (by omega),
    map_zsmul, mul_comm]
  -- `𝟙_ (ModuleCat K)` is definitionally `ModuleCat.of K K`.
  · rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor M

/-- **Over a field, `TopPair.pushforwardCap` is bijective if and only if `TopPair.pullbackCup` is**
(`n + p = m`, coefficients in `K`). -/
theorem bijective_pushforwardCap_iff {K : Type w} [Field K] (P : TopPair.{w}) {Y : TopCat.{w}}
    (p₀ : P.fst ⟶ Y) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (P.pushforwardCap p₀ (ModuleCat.of K K) n p m h u).hom ↔
      Function.Bijective (P.pullbackCup (ModuleCat.of K K) p₀ n p m (by omega) u) := by
  set T := (P.pushforwardCap p₀ (ModuleCat.of K K) n p m h u).hom
  have hc : ((-1 : K) ^ (n * p)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have key (a) : P.singularCohomologyDualEquiv m
      (P.pullbackCup (ModuleCat.of K K) p₀ n p m (by omega) u a) =
      LinearEquiv.smulOfNeZero K _ _ hc (T.dualMap (Y.singularCohomologyDualEquiv p a)) := by
    ext x
    have hx := congrArg (fun φ ↦ φ.hom x) (P.pushforwardCap_comp_singularKronecker p₀ h u a)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply] at hx
    rw [LinearEquiv.smulOfNeZero_apply, LinearMap.smul_apply, LinearMap.dualMap_apply,
      TopPair.singularCohomologyDualEquiv_apply, TopCat.singularCohomologyDualEquiv_apply, hx]
    simp [← Int.cast_smul_eq_zsmul K, ← mul_assoc, ← mul_pow]
  have e : ⇑(P.pullbackCup (ModuleCat.of K K) p₀ n p m (by omega) u) =
      ⇑(P.singularCohomologyDualEquiv m).symm ∘ ⇑(LinearEquiv.smulOfNeZero K _ _ hc) ∘
        ⇑T.dualMap ∘ ⇑(Y.singularCohomologyDualEquiv p) :=
    funext fun a ↦ by simp only [Function.comp_apply, ← key, LinearEquiv.symm_apply_apply]
  rw [e, EquivLike.comp_bijective, EquivLike.comp_bijective, EquivLike.bijective_comp,
    LinearMap.dualMap_bijective_iff]

/-- Over a commutative ring `K`, if the Kronecker maps of `Y` in degree `p` and of `P` in degree
`m` are bijective and `TopPair.pushforwardCap` in degree `m = n + p` is an isomorphism in
`ModuleCat K`, then `TopPair.pullbackCup` in degree `p` (`p + n = m`) is bijective for `M`. -/
theorem bijective_pullbackCup_of_isIso_pushforwardCap {K : Type w} [CommRing K] (P : TopPair.{w})
    {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y) (M : ModuleCat.{w} K) {n p m : ℕ} (h : p + n = m)
    (hY : Function.Bijective (Y.singularKronecker (R := ModuleCat.of K K) (M := M) K p))
    (hP : Function.Bijective (P.singularKronecker (R := ModuleCat.of K K) (M := M) K m))
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    [IsIso (P.pushforwardCap p₀ (ModuleCat.of K K) n p m ((add_comm n p).trans h) u)] :
    Function.Bijective (P.pullbackCup M p₀ n p m h u) := by
  let T := asIso (P.pushforwardCap p₀ (ModuleCat.of K K) n p m ((add_comm n p).trans h) u)
  let eY := LinearEquiv.ofBijective _ hY
  let eP := LinearEquiv.ofBijective _ hP
  have hcomp : ⇑(P.pullbackCup M p₀ n p m h u) = ⇑eP.symm ∘ (fun ψ ↦ ((-1 : ℤ) ^ (n * p)) • ψ) ∘
      ⇑(Linear.homCongr K T.symm (Iso.refl M)) ∘ ⇑eY :=
    funext fun a ↦ eP.injective <| by
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, Linear.homCongr_apply,
        Iso.symm_inv, Iso.refl_hom, Category.comp_id, eP, eY, T, asIso_hom,
        LinearEquiv.ofBijective_apply]
      have hx := congrArg (((-1 : ℤ) ^ (n * p)) • ·)
        (P.pushforwardCap_comp_singularKronecker p₀ ((add_comm n p).trans h) u a)
      have hc : (-1 : ℤ) ^ (n * p) * (-1 : ℤ) ^ (n * p) = 1 := by rw [← mul_pow]; simp
      rw [smul_smul, hc, one_zsmul] at hx
      exact hx.symm
  rw [hcomp]
  exact eP.symm.bijective.comp (((isUnit_neg_one.pow (n * p)).smul_bijective.comp
    (Linear.homCongr K T.symm (Iso.refl M)).bijective).comp eY.bijective)

/-- **Cohomology with injective coefficients detects the homology map** `x ↦ p₀_*(x ⌢ u)`: over a
commutative ring `K`, if `TopPair.pullbackCup` in degree `p` (`p + n = m`) is bijective with
coefficients in every injective `K`-module `M`, then `TopPair.pushforwardCap` with coefficients
in `K` is an isomorphism `Hₘ(X, Z; K) ≅ Hₚ(Y; K)` in `ModuleCat K`. No hypothesis on `K` or on
the homology is needed, unlike the field case `TopPair.bijective_pushforwardCap_iff`. -/
theorem isIso_pushforwardCap_of_bijective_pullbackCup {K : Type w} [CommRing K] (P : TopPair.{w})
    {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : ∀ (M : ModuleCat.{w} K) [Injective M],
      Function.Bijective (P.pullbackCup M p₀ n p m (by omega) u)) :
    IsIso (P.pushforwardCap p₀ (ModuleCat.of K K) n p m h u) := by
  refine (Injective.isCoseparating_isInjective (C := ModuleCat.{w} K)).isCodetecting _
    fun M _ ↦ Function.Bijective.existsUnique ?_
  -- With injective coefficients both Kronecker maps are bijective.
  let eY := Y.singularKroneckerEquiv (R := ModuleCat.of K K) (M := M) K p
  have hP : Function.Bijective (P.singularKronecker (R := ModuleCat.of K K) (M := M) K m) := by
    rw [TopPair.singularKronecker_def]
    exact TauCeti.ChainComplex.kronecker_bijective m
  -- Through them, precomposition with `p₀_*(- ⌢ u)` is `±` the cup map `p₀^*(-) ⌣ u`.
  have hcomp : CategoryStruct.comp (P.pushforwardCap p₀ (ModuleCat.of K K) n p m h u) =
      (fun ψ ↦ ((-1 : ℤ) ^ (n * p)) • ψ) ∘ ⇑(P.singularKronecker K m) ∘
        ⇑(P.pullbackCup M p₀ n p m (by omega) u) ∘ ⇑eY.symm := by
    funext g
    obtain ⟨a, rfl⟩ := eY.surjective g
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    rw [TopCat.singularKroneckerEquiv_apply]
    exact P.pushforwardCap_comp_singularKronecker p₀ h u a
  rw [hcomp]
  exact (isUnit_neg_one.pow (n * p)).smul_bijective.comp
    (hP.comp ((hu M).comp eY.symm.bijective))

section ChainMap

open HomologicalComplex ComplexShape

variable {K : Type w} [CommRing K] (P : TopPair.{w}) {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y)
  (A : ModuleCat.{w} K) (n : ℕ)

/-- **`x ↦ p₀_*(x ⌢ φ)` as a chain map.** For a relative cocycle `φ` of degree `n` of the pair
`P = (X, Z)` with coefficients in `K` and a map `p₀ : X ⟶ Y`, the chain map from the relative
chains of `P` to the chains of `Y` placed `n` degrees higher which sends a relative chain `x` of
degree `n + p` to `(-1)^(n p) p₀_*(x ⌢ φ)`, with coefficients in any `K`-module `A`: capping with
`φ` (`TauCeti.ChainComplex.capChainMap`) along the relative Alexander–Whitney diagonal, paired by
the left unitor `K ⊗ A ≅ A` and followed by the push-forward along `p₀`. On homology it is
`TopPair.pushforwardCap` of the class of `φ`, up to sign
(`TopPair.homologyMap_pushforwardCapChainMap_comp_extendHomologyIso_hom`). -/
def pushforwardCapChainMap (φ : (P.singularChainComplex (ModuleCat.of K K)).X n ⟶ ModuleCat.of K K)
    (hφ : (P.singularChainComplex (ModuleCat.of K K)).d (n + 1) n ≫ φ = 0) :
    P.singularChainComplex A ⟶
      ((TopCat.toSSet.obj Y).chainComplex A).extend (embeddingDownNatAdd n) :=
  TauCeti.ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ A).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
      SSet.chainComplexMap (TopCat.toSSet.map p₀) A) n φ hφ

/-- `TopPair.pushforwardCapChainMap` is capping with the cocycle along the relative
Alexander–Whitney diagonal, with the pairing of coefficients followed by the push-forward along
`p₀` as the action. -/
theorem pushforwardCapChainMap_def
    (φ : (P.singularChainComplex (ModuleCat.of K K)).X n ⟶ ModuleCat.of K K)
    (hφ : (P.singularChainComplex (ModuleCat.of K K)).d (n + 1) n ≫ φ = 0) :
    P.pushforwardCapChainMap p₀ A n φ hφ =
      TauCeti.ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ A).inv)
        ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom ≫
          SSet.chainComplexMap (TopCat.toSSet.map p₀) A) n φ hφ :=
  (rfl)

/-- **Naturality of `x ↦ p₀_*(x ⌢ φ)` as a chain map**, the chain-level projection formula: for a
map of pairs `f : P' ⟶ P` covering `g : Y' ⟶ Y`, in the sense that `f ≫ p₀ = p₀' ≫ g` on the
ambient spaces, pushing chains forward along `f` and then capping with `φ` is capping with the
pull-back `f^*φ` and then pushing forward along `g`. -/
theorem pushforwardCapChainMap_naturality {P' : TopPair.{w}} {Y' : TopCat.{w}} (f : P' ⟶ P)
    (p₀' : P'.fst ⟶ Y') (g : Y' ⟶ Y) (hf : Hom.fst f ≫ p₀ = p₀' ≫ g)
    (φ : (P.singularChainComplex (ModuleCat.of K K)).X n ⟶ ModuleCat.of K K)
    (hφ : (P.singularChainComplex (ModuleCat.of K K)).d (n + 1) n ≫ φ = 0) :
    singularChainComplexMap f A ≫ P.pushforwardCapChainMap p₀ A n φ hφ =
      P'.pushforwardCapChainMap p₀' A n ((singularChainComplexMap f (ModuleCat.of K K)).f n ≫ φ)
          (by rw [← (singularChainComplexMap f (ModuleCat.of K K)).comm_assoc, hφ,
            Limits.comp_zero]) ≫
        extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) A) (embeddingDownNatAdd n) := by
  -- Pushing forward along `p₀'` and then `g` is pushing forward along `f` and then `p₀`.
  have hg : SSet.chainComplexMap (TopCat.toSSet.map p₀') A ≫
      SSet.chainComplexMap (TopCat.toSSet.map g) A =
        SSet.chainComplexMap (TopCat.toSSet.map (Hom.fst f)) A ≫
          SSet.chainComplexMap (TopCat.toSSet.map p₀) A := by
    simp only [← Functor.map_comp, hf]
  -- The two sides of the action square differ only in writing the unit `𝟙_ (ModuleCat K)` of the
  -- monoidal structure as `ModuleCat.of K K`, which `rfl` identifies.
  exact TauCeti.ChainComplex.capChainMap_naturality _ _ _ _ _ _ _ _
    (alexanderWhitneyDiagonal_naturality f (λ_ A).inv)
    (by rw [Category.assoc, hg, ← SSet.chainComplexPairing_naturality_assoc]; rfl) hφ

/-- **`x ↦ p₀_*(x ⌢ φ)` as a chain map computes `TopPair.pushforwardCap`**: for a relative cocycle
`φ` of degree `n`, the map it induces on homology in degree `m = n + p`, read in `Hₚ(Y; A)`, is
`(-1)^(n p)` times `x ↦ p₀_*(x ⌢ u)` for the class `u` of `φ`. -/
theorem homologyMap_pushforwardCapChainMap_comp_extendHomologyIso_hom (p m : ℕ) (h : n + p = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles n) :
    homologyMap (P.pushforwardCapChainMap p₀ A n
          ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles n φ)
          (TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ)) m ≫
        (((TopCat.toSSet.obj Y).chainComplex A).extendHomologyIso (embeddingDownNatAdd n)
          ((embeddingDownNatAdd_f n p).trans (by omega))).hom =
      ((-1 : ℤ) ^ (n * p)) • P.pushforwardCap p₀ A n p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ n φ) := by
  -- The cocycle is an element of the module of cochains, so the general statement is applied up
  -- to unfolding that module and `TopPair.pushforwardCapChainMap` rather than by rewriting.
  refine (TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom (k := K) _ _ p m
    h φ).trans ?_
  exact congrArg (((-1 : ℤ) ^ (n * p)) • ·) (pushforwardCap_eq_cap P p₀ A h _).symm

/-- **`x ↦ p₀_*(x ⌢ φ)` is a quasi-isomorphism** onto the chains of `Y` placed `n` degrees higher
when the relative homology of `P` with coefficients in `A` vanishes below `n` and
`x ↦ p₀_*(x ⌢ u)` is an isomorphism `Hₙ₊ₚ(X, Z; A) ≅ Hₚ(Y; A)` in every degree, for the class
`u` of the relative cocycle `φ`. -/
theorem quasiIso_pushforwardCapChainMap
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles n)
    (hP : ∀ m < n, Limits.IsZero (P.singularHomology A m))
    (hu : ∀ p m (h : n + p = m), IsIso (P.pushforwardCap p₀ A n p m h
      ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ n φ))) :
    QuasiIso (P.pushforwardCapChainMap p₀ A n
      ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles n φ)
      (TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles n (n + 1) φ)) := by
  refine TauCeti.ChainComplex.quasiIso_capChainMap (k := K) _ _ φ
    (fun m hm ↦ (exactAt_iff_isZero_homology _ m).2 (hP m hm)) fun p m h ↦ ?_
  rw [← pushforwardCap_eq_cap]
  exact hu p m h

end ChainMap

end TopPair

end
