/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion

/-!
# The homology Thom map and the Thom isomorphism over a field

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**homology Thom map** of `u` is

`Φ_u : Hₘ(E, E₀; A) ⟶ Hₚ(B; A)`,  `x ↦ π_*(x ⌢ u)`,  `n + p = m`,

the relative cap product `Hₘ(E, E₀) ⟶ Hₚ(E)` with `u` (`TopPair.singularCap`) followed by the
push-forward along the projection `π : E ⟶ B`, for any `K`-module of coefficients `A`. When `u` is
a Thom class of a real vector bundle of rank `n` (for instance the unique Thom class with
coefficients in `ZMod 2`, or the Thom class of an orientation) it is the map of the Thom
isomorphism in homology (Spanier, Chapter 5, Section 7), the homological counterpart of the
cohomology Thom map `TauCeti.thomMap`, `a ↦ π^*a ⌣ u` (Milnor and Stasheff, Theorem 10.4).

Relative homology of Thom pairs is what attaching a disc bundle produces: when a bundle `ν` is
attached along its sphere bundle, the relative homology of the attachment is that of the Thom pair
`(ν, ν₀)`. So the homology Thom map is the map which identifies such a relative group, shifted by
the rank, with the homology of the base, as in the relative homology of a sublevel pair across a
Morse–Bott critical level.

This file sets up the homology Thom map, relates it to `TauCeti.thomMap` via the Kronecker pairing,
and deduces the Thom isomorphism in both homology and cohomology over an arbitrary base when `K` is
a field:

1. **Functorial properties**: `TauCeti.homologyThomMap` is `K`-linear in `u`, natural in maps of
   Thom pairs covering maps of bases (`TauCeti.homologyThomMap_naturality`) and in pull-backs of
   bundles (`TauCeti.homologyThomMap_pullback`), and restricts on each fibre `(E_b, E_b ∖ {0})` to
   capping with the fibre restriction of `u` followed by pushing forward along the constant map
   (`TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`).
2. **Kronecker duality**: with chain coefficients `K` and cohomology values in any `K`-module `M`,
   `⟨a, Φ_u(x)⟩ = (-1)^(n p) ⟨π^*a ⌣ u, x⟩` (`TauCeti.homologyThomMap_comp_singularKronecker`).
   Over a field `K`, the universal coefficient isomorphism identifies cohomology with the dual of
   homology, so `Φ_u` is bijective in degree `m = n + p` if and only if `TauCeti.thomMap` with
   coefficients in `K` is bijective in degree `p` (`TauCeti.bijective_homologyThomMap_iff`).
3. **Global Thom isomorphism over a field and an arbitrary base**: over each finite union `U_s` of
   trivializing open sets, `TopCat.pullbackCupRestrict` is bijective by
   `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`, so the restricted homology Thom map is
   an isomorphism. Passing to the filtered colimit of singular homology over all finite unions of
   the chosen trivializing sets
   (`TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion` and
   `TopCat.isColimitMapCoconeSingularHomology`) proves that `Φ_u` is an isomorphism in
   `ModuleCat K` over any base `B` with no compactness assumption
   (`TauCeti.isIso_homologyThomMap_of_field`, `TauCeti.homologyThomIsoOfField`). Applying the
   universal coefficient equivalence `Hᵖ(-; K, M) ≃ₗ[K] (Hₚ(-; K) ⟶ M)` then yields the cohomology
   Thom isomorphism `Hᵖ(B; K, M) ≃ₗ[K] Hᵐ(E, E₀; K, M)` for every `K`-vector space `M` over any
   base `B` (`TauCeti.bijective_thomMap_of_field`, `TauCeti.thomEquivOfField`), covering in
   particular `ZMod 2` coefficients for arbitrary unoriented bundles and `ℚ` or `ℝ` coefficients
   for oriented bundles.

## Main definitions and results

* `TauCeti.homologyThomMap`: the homology Thom map `x ↦ π_*(x ⌢ u)`, linear in `u`.
* `TauCeti.homologyThomMap_naturality`, `TauCeti.homologyThomMap_pullback`: naturality.
* `TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`: the restriction to a fibre.
* `TauCeti.homologyThomMap_comp_singularKronecker`: the homology Thom map is the transpose of the
  Thom map, up to the sign `(-1)^(n p)`.
* `TauCeti.bijective_homologyThomMap_iff`: over a field, the homology Thom map is bijective exactly
  when the Thom map is.
* `TauCeti.isIso_homologyThomMap_of_field`, `TauCeti.bijective_homologyThomMap_of_field`,
  `TauCeti.homologyThomIsoOfField`: the homology Thom isomorphism over a field and an arbitrary
  base.
* `TauCeti.bijective_thomMap_of_field`, `TauCeti.thomEquivOfField`: the cohomology Thom isomorphism
  with arbitrary vector-space coefficients over a field and an arbitrary base.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.3 (the identity
  `⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩`) and Section 4.D, Theorem 4D.10.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section PushforwardCap

/-- Cap with a relative class `u ∈ Hⁿ(P; K)` followed by push-forward along a map `p₀ : P.fst ⟶ Y`
out of the ambient space of `P`. -/
private def pushforwardCap {K : Type w} [CommRing K] (P : TopPair.{w}) {Y : TopCat.{w}}
    (p₀ : P.fst ⟶ Y) (A : ModuleCat.{w} K) (n p m : ℕ) (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.singularHomology A m ⟶ ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj Y :=
  P.singularCap K (λ_ A).inv (λ_ A).hom n p m h u ≫
    ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map p₀

private theorem pushforwardCap_naturality {K : Type w} [CommRing K] {P P' : TopPair.{w}}
    {Y Y' : TopCat.{w}} (φ : P' ⟶ P) (p₀ : P.fst ⟶ Y) (p₀' : P'.fst ⟶ Y') (g : Y' ⟶ Y)
    (hφ : TopPair.Hom.fst φ ≫ p₀ = p₀' ≫ g) (A : ModuleCat.{w} K) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    pushforwardCap P' p₀' A n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
      TopPair.singularHomologyMap φ A m ≫ pushforwardCap P p₀ A n p m h u := by
  dsimp only [pushforwardCap]
  rw [Category.assoc, ← Functor.map_comp, ← hφ, Functor.map_comp, ← Category.assoc,
    TopPair.singularCap_naturality, Category.assoc]

private theorem pushforwardCap_comp_singularKronecker {K : Type w} [CommRing K] (P : TopPair.{w})
    {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y) {M : ModuleCat.{w} K} {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    pushforwardCap P p₀ (ModuleCat.of K K) n p m h u ≫ Y.singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • P.singularKronecker K m
        (P.pullbackCup M p₀ n p m (by omega) u a) := by
  -- `⟨a, p₀_*(x ⌢ u)⟩ = ⟨p₀^*a, x ⌢ u⟩ = ⟨u ⌣ p₀^*a, x⟩`, and `u ⌣ p₀^*a = (-1)^(n p) p₀^*a ⌣ u`.
  dsimp only [pushforwardCap]
  rw [Category.assoc, ← TopCat.singularKronecker_naturality,
    TopPair.singularCap_comp_singularKronecker, TopPair.pullbackCup_apply,
    TopPair.singularCup_gradedComm K P (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ M).hom)
      (μ := (ρ_ M).hom) ?_ ?_ (by omega), map_zsmul, mul_comm]
  -- `pullbackCup` cups along `(λ_ (𝟙_ (ModuleCat K))).inv`, while `singularCap` uses
  -- `ModuleCat.of K K`; both `rfl`s close the definitional equality
  -- `𝟙_ (ModuleCat K) = ModuleCat.of K K`.
  · rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor M

private theorem bijective_pushforwardCap_iff {K : Type w} [Field K] (P : TopPair.{w})
    {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y) {n p m : ℕ} (h : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (pushforwardCap P p₀ (ModuleCat.of K K) n p m h u).hom ↔
      Function.Bijective (P.pullbackCup (ModuleCat.of K K) p₀ n p m (by omega) u) := by
  set T := (pushforwardCap P p₀ (ModuleCat.of K K) n p m h u).hom
  have hc : ((-1 : K) ^ (n * p)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have key : ∀ a, P.singularCohomologyDualEquiv m
      (P.pullbackCup (ModuleCat.of K K) p₀ n p m (by omega) u a) =
      LinearEquiv.smulOfNeZero K _ _ hc (T.dualMap (Y.singularCohomologyDualEquiv p a)) := by
    intro a
    ext x
    have hx := congrArg (fun φ ↦ φ.hom x) (pushforwardCap_comp_singularKronecker P p₀ h u a)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply] at hx
    rw [LinearEquiv.smulOfNeZero_apply, LinearMap.smul_apply, LinearMap.dualMap_apply,
      TopPair.singularCohomologyDualEquiv_apply, TopCat.singularCohomologyDualEquiv_apply, hx]
    simp [← Int.cast_smul_eq_zsmul K, ← mul_assoc, ← mul_pow]
  have e : ⇑(P.pullbackCup (ModuleCat.of K K) p₀ n p m (by omega) u) =
      ⇑(P.singularCohomologyDualEquiv m).symm ∘ ⇑(LinearEquiv.smulOfNeZero K _ _ hc) ∘
        ⇑T.dualMap ∘ ⇑(Y.singularCohomologyDualEquiv p) := by
    funext a
    simp only [Function.comp_apply, ← key, LinearEquiv.symm_apply_apply]
  rw [e, EquivLike.comp_bijective, EquivLike.comp_bijective, EquivLike.bijective_comp,
    LinearMap.dualMap_bijective_iff]

private theorem bijective_pullbackCup_of_isIso_pushforwardCap {K : Type w} [Field K]
    (P : TopPair.{w}) {Y : TopCat.{w}} (p₀ : P.fst ⟶ Y) (M : ModuleCat.{w} K) {n p m : ℕ}
    (h : p + n = m) (h' : n + p = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    [IsIso (pushforwardCap P p₀ (ModuleCat.of K K) n p m h' u)] :
    Function.Bijective (P.pullbackCup M p₀ n p m h u) := by
  let T := asIso (pushforwardCap P p₀ (ModuleCat.of K K) n p m h' u)
  let c : ℤ := (-1 : ℤ) ^ (n * p)
  have hc : c * c = 1 := by
    dsimp only [c]
    rw [← mul_pow]
    simp
  let eT : (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj Y ⟶ M) ≃
      (P.singularHomology (ModuleCat.of K K) m ⟶ M) :=
    { toFun φ := c • (T.hom ≫ φ)
      invFun ψ := c • (T.inv ≫ ψ)
      left_inv φ := by
        dsimp only
        rw [Preadditive.comp_zsmul, Iso.inv_hom_id_assoc, smul_smul, hc, one_zsmul]
      right_inv ψ := by
        dsimp only
        rw [Preadditive.comp_zsmul, Iso.hom_inv_id_assoc, smul_smul, hc, one_zsmul] }
  let eY := Y.singularKroneckerEquivOfProjectiveHomology (ModuleCat.of K K) M p
  let eP := P.singularKroneckerEquivOfProjectiveHomology (ModuleCat.of K K) M m
  have hcomp : ⇑(P.pullbackCup M p₀ n p m h u) = ⇑eP.symm ∘ ⇑eT ∘ ⇑eY := by
    funext a
    apply eP.injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, eP, eY, eT, Equiv.coe_fn_mk, T,
      asIso_hom, TopPair.singularKroneckerEquivOfProjectiveHomology_apply,
      TopCat.singularKroneckerEquivOfProjectiveHomology_apply]
    have hx := congrArg (c • ·) (pushforwardCap_comp_singularKronecker P p₀ h' u a)
    rw [smul_smul, hc, one_zsmul] at hx
    exact hx.symm
  rw [hcomp, EquivLike.comp_bijective, EquivLike.comp_bijective]
  exact eY.bijective

end PushforwardCap

section HomologyThomMap

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (A : ModuleCat.{w} K)

/-- **The homology Thom map** `x ↦ π_*(x ⌢ u)` of a relative class `u ∈ Hⁿ(E, E₀; K)`, from
`Hₘ(E, E₀; A)` to `Hₚ(B; A)`, `n + p = m`, as a `K`-linear function of `u`. The cochain
coefficients are `K`, and both the coefficient morphism and the pairing of values are the left
unitor `K ⊗ A ≅ A`. For a Thom class `u` of a real vector bundle of rank `n` it is the map of
the Thom isomorphism in homology. -/
def homologyThomMap (n p m : ℕ) (h : n + p = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      ((thomPair F E).singularHomology A m ⟶
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of B)) :=
  Linear.rightComp K _ (((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
      (thomPairProj F E)) ∘ₗ
    (thomPair F E).singularCap K (λ_ A).inv (λ_ A).hom n p m h

variable {A}

/-- The homology Thom map is the relative cap product with `u` followed by the push-forward along
the projection. -/
theorem homologyThomMap_apply {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F E A n p m h u =
      (thomPair F E).singularCap K (λ_ A).inv (λ_ A).hom n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (thomPairProj F E) :=
  (rfl)

/-- **Naturality of the homology Thom map.** A map of Thom pairs `φ : (E', E'₀) ⟶ (E, E₀)` covering
a map of bases `g : B' ⟶ B` intertwines the homology Thom map of the pull-back `φ^*u` with that of
`u`: `g_* Φ_{φ^*u}(x) = Φ_u(φ_* x)`. -/
theorem homologyThomMap_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type*}
    [TopologicalSpace F'] {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')]
    [∀ b, Zero (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F' E' A n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
      TopPair.singularHomologyMap φ A m ≫ homologyThomMap F E A n p m h u :=
  pushforwardCap_naturality φ (thomPairProj F E) (thomPairProj F' E') g hφ A h u

attribute [local instance] pullbackFiberZero in
/-- **The homology Thom map of a pull-back bundle.** For a continuous map `f : B' ⟶ B`, pushing
the homology Thom map of the pull-back of `u` to `f^*E` forward along `f` is the homology Thom map
of `u` on the push-forward to the Thom pair of `E`. -/
theorem homologyThomMap_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F ((⇑f) *ᵖ E) A n p m h
          (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (TopCat.ofHom f) =
      TopPair.singularHomologyMap (pullbackThomPairMap F E f) A m ≫
        homologyThomMap F E A n p m h u :=
  homologyThomMap_naturality F E _ _ (pullbackThomPairMap_fst_comp_thomPairProj F E f) h u

/-- **The homology Thom map on a fibre.** On the image of the fibre pair `(E_b, E_b ∖ {0})`, the
homology Thom map of `u` is the cap product with the restriction of `u` to the fibre, pushed forward
along the constant map at `b`. -/
theorem singularHomologyMap_fiberThomPairMap_comp_homologyThomMap (b : B) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    TopPair.singularHomologyMap (fiberThomPairMap F E b) A m ≫ homologyThomMap F E A n p m h u =
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCap K (λ_ A).inv
          (λ_ A).hom n p m h (TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (TopCat.ofHom (ContinuousMap.const (E b) b)) := by
  rw [homologyThomMap_apply, ← Category.assoc, ← TopPair.singularCap_naturality, Category.assoc,
    ← Functor.map_comp, fiberThomPairMap_fst_comp_thomPairProj]

/-- **The homology Thom map is the transpose of the Thom map**: for `u ∈ Hⁿ(E, E₀; K)`,
`a ∈ Hᵖ(B; K, M)` and `x ∈ Hₘ(E, E₀; K)`, `m = n + p`, the Kronecker pairing of `a` with the
homology Thom map `Φ_u(x) = π_*(x ⌢ u)` is `(-1)^(n p)` times the pairing of the Thom map
`π^*a ⌣ u` (`TauCeti.thomMap`) with `x`. -/
theorem homologyThomMap_comp_singularKronecker {M : ModuleCat.{w} K} {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ (TopCat.of B).singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • (thomPair F E).singularKronecker K m
        (thomMap F E M n p m (by omega) u a) := by
  rw [thomMap_def]
  exact pushforwardCap_comp_singularKronecker (thomPair F E) (thomPairProj F E) h u a

/-- **Over a field, the homology Thom map is bijective exactly when the Thom map is**: for
`u ∈ Hⁿ(E, E₀; K)` and `m = n + p`, the homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is bijective
if and only if the Thom map `Hᵖ(B; K) ⟶ Hᵐ(E, E₀; K)` is. Through the universal coefficient
isomorphisms `TopCat.singularCohomologyDualEquiv` and `TopPair.singularCohomologyDualEquiv`, the
Thom map is `±` the dual map of the homology Thom map
(`TauCeti.homologyThomMap_comp_singularKronecker`), and a linear map between vector spaces is
bijective exactly when its dual map is. -/
theorem bijective_homologyThomMap_iff {K : Type w} [Field K] {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom ↔
      Function.Bijective (thomMap F E (ModuleCat.of K K) n p m (by omega) u) := by
  rw [thomMap_def]
  exact bijective_pushforwardCap_iff (thomPair F E) (thomPairProj F E) h u

end HomologyThomMap

section IsomorphismOfField

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [Field K]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- The restriction of the bundle projection `π : E ⟶ B` to `E|_W ⟶ W`. -/
private def thomPairOverProj (F : Type w) [NormedAddCommGroup F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] (W : Set B) :
    (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).restrictPreimage
    W)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- The homology Thom map restricted to a subset `W` of the base: capping on `(E|_W, E₀|_W)` with
the restriction of `u` followed by pushing forward along `E|_W ⟶ W`. -/
private def homologyThomMapOver {K : Type w} [CommRing K] (A : ModuleCat.{w} K) (W : Set B)
    (n p m : ℕ) (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (thomPairOver F E W).singularHomology A m ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of W) :=
  pushforwardCap (thomPairOver F E W) (thomPairOverProj F E W) A n p m h
    (TopPair.singularCohomologyMap
      (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W) n u)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem homologyThomMapOver_naturality {K : Type w} [CommRing K] (A : ModuleCat.{w} K)
    {W W' : Set B} (hWW' : W ⊆ W') {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMapOver A W n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (TopCat.ofHom (ContinuousMap.inclusion hWW')) =
      TopPair.singularHomologyMap (thomPairOverMap F E hWW') A m ≫
        homologyThomMapOver A W' n p m h u := by
  have hu : TopPair.singularCohomologyMap (thomPairOverMap F E hWW') n
      (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W') n u) =
      TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u := by
    rw [← TopPair.singularCohomologyMap_comp_apply, thomPairOverMap_comp_restrictPreimagePairMap]
  dsimp only [homologyThomMapOver]
  rw [← hu]
  exact pushforwardCap_naturality (thomPairOverMap F E hWW') (thomPairOverProj F E W')
    (thomPairOverProj F E W) (TopCat.ofHom (ContinuousMap.inclusion hWW'))
    (TopCat.ext fun v : π F E ⁻¹' W ↦
      Subtype.ext (congrArg (fun x : π F E ⁻¹' W' ↦ x.1.proj)
        (thomPairOverMap_fst_apply F E hWW' v))) A h _

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem homologyThomMapOver_comp_map_subtypeVal {K : Type w} [CommRing K]
    (A : ModuleCat.{w} K) (W : Set B) {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMapOver A W n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) =
      TopPair.singularHomologyMap
          (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) A m ≫
        homologyThomMap F E A n p m h u := by
  have hι : thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom =
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W := by
    rw [thomPairOverUnivIso_hom, thomPairOverMap_comp_restrictPreimagePairMap]
  have hproj : TopPair.Hom.fst (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom)
      ≫ thomPairProj F E =
      thomPairOverProj F E W ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :=
    TopCat.ext fun v : π F E ⁻¹' W ↦
      (congrArg (thomPairProj F E)
        ((congrArg (TopPair.Hom.fst (thomPairOverUnivIso F E).hom)
          (thomPairOverMap_fst_apply F E (subset_univ W) v)).trans
          (thomPairOverUnivIso_hom_fst_apply F E ⟨v.1, trivial⟩))).trans
        (thomPairProj_apply F E v.1)
  dsimp only [homologyThomMapOver]
  rw [← hι]
  exact pushforwardCap_naturality _ (thomPairProj F E) (thomPairOverProj F E W)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) hproj A h u

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem bijective_homologyThomMapOver_iff (W : Set B) {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (homologyThomMapOver (ModuleCat.of K K) W n p m h u).hom ↔
      Function.Bijective
        (TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
          (zeroSectionCompl F E) (ModuleCat.of K K) W n p m (by omega) u) := by
  rw [TopCat.pullbackCupRestrict_apply]
  exact bijective_pushforwardCap_iff (thomPairOver F E W) (thomPairOverProj F E W) h _

private theorem isIso_homologyThomMapOver_finiteTrivializingUnion {p m : ℕ}
    (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (s : Finset B) :
    IsIso (homologyThomMapOver (ModuleCat.of K K) (⋃ b ∈ s, (trivializationAt F E b).baseSet)
      (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  rw [ConcreteCategory.isIso_iff_bijective, bijective_homologyThomMapOver_iff]
  exact bijective_pullbackCupRestrict_thomPair_biUnion (ModuleCat.of K K) s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) p m (by omega)
    fun b _ ↦ hu b

variable (F E) in
/-- The finite unions of the chosen trivializing open sets, as subspaces of the base. -/
private def baseFiniteTrivializingUnionDiagram : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom (ContinuousMap.inclusion (biUnion_subset_biUnion_left f.le))

variable (F E) in
/-- The inclusions of the finite unions of the chosen trivializing open sets into the base. -/
private def baseFiniteTrivializingUnionCocone :
    Cocone (baseFiniteTrivializingUnionDiagram (B := B) F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
variable (F E K) in
/-- In every degree, the singular homology of the base is the filtered colimit of the homologies of
the finite unions of the chosen trivializing open sets. -/
private def isColimitSingularHomologyBaseFiniteTrivializingUnion (p : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).mapCocone
      (baseFiniteTrivializingUnionCocone (B := B) F E)) :=
  isColimitMapCoconeSingularHomology (ModuleCat.of K K) p
    (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ IsEmbedding.subtypeVal) fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
variable (K) in
private theorem singularHomology_thomPairOver_finiteTrivializingUnion_eq (m : ℕ) (s : Finset B) :
    (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) =
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) m := by
  rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
variable (K) in
private theorem singularHomology_thomPair_eq (m : ℕ) :
    (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt =
      (thomPair F E).singularHomology (ModuleCat.of K K) m := by
  rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]

/-- The restricted homology Thom maps assemble into a natural isomorphism over the diagram of finite
unions of the chosen trivializing open sets. -/
private def homologyThomMapOverNatIso {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
  NatIso.ofComponents
    (fun s ↦ eqToIso (singularHomology_thomPairOver_finiteTrivializingUnion_eq K m s) ≪≫
      @asIso _ _ _ _ (homologyThomMapOver (ModuleCat.of K K)
        (⋃ b ∈ s, (trivializationAt F E b).baseSet) (finrank ℝ F) p m h u)
        (isIso_homologyThomMapOver_finiteTrivializingUnion h hu s))
    fun {s t} f ↦ by
      have := isIso_homologyThomMapOver_finiteTrivializingUnion h hu s
      have := isIso_homologyThomMapOver_finiteTrivializingUnion h hu t
      dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
      simp only [thomPairFiniteTrivializingUnionDiagram_map,
        TopPair.singularHomologyFunctor_map, Iso.trans_hom, eqToIso.hom, asIso_hom,
        Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg (eqToHom _ ≫ ·)
        (homologyThomMapOver_naturality (ModuleCat.of K K)
          (W := ⋃ b ∈ s, (trivializationAt F E b).baseSet)
          (W' := ⋃ b ∈ t, (trivializationAt F E b).baseSet)
          (biUnion_subset_biUnion_left f.le) h u).symm

@[simp]
private theorem homologyThomMapOverNatIso_hom_app {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (s : Finset B) :
    (homologyThomMapOverNatIso h hu).hom.app s =
      eqToHom (singularHomology_thomPairOver_finiteTrivializingUnion_eq K m s) ≫
        homologyThomMapOver (ModuleCat.of K K)
          (⋃ b ∈ s, (trivializationAt F E b).baseSet) (finrank ℝ F) p m h u :=
  (rfl)

/-- **The homology Thom isomorphism over a field** (Spanier, Chapter 5, Section 7). For a real
vector bundle `E → B` over an arbitrary base `B`, a field `K`, and any Thom class
`u ∈ Hʳ(E, E₀; K)` (`r = finrank ℝ F`), the homology Thom map `x ↦ π_*(x ⌢ u)` is an isomorphism
`Hₘ(E, E₀; K) ≅ Hₚ(B; K)` (`r + p = m`) in `ModuleCat K`. -/
theorem isIso_homologyThomMap_of_field (p m : ℕ) (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let P₂ := isColimitSingularHomologyBaseFiniteTrivializingUnion F E K p
  let α := homologyThomMapOverNatIso h hu
  have hcocone : eqToHom (singularHomology_thomPair_eq (F := F) (E := E) K m) ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ (?_ : _ = _).trans (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
    have hmap : (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).mapCocone
        (baseFiniteTrivializingUnionCocone (B := B) F E)).ι.app s =
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := rfl
    rw [hmap]
    dsimp only [Functor.mapCocone_ι_app, α]
    simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
      homologyThomMapOverNatIso_hom_app, Category.assoc, TopPair.singularHomologyMap_comp,
      TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← TopPair.singularHomologyMap_comp_assoc]
    exact congrArg (eqToHom _ ≫ ·)
      (homologyThomMapOver_comp_map_subtypeVal (ModuleCat.of K K)
        (⋃ b ∈ s, (trivializationAt F E b).baseSet) h u).symm
  have : IsIso (eqToHom (singularHomology_thomPair_eq (F := F) (E := E) K m) ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
    rw [hcocone]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_left (eqToHom (singularHomology_thomPair_eq K m)) _

/-- **The homology Thom map is bijective over a field** on an arbitrary base `B`. -/
theorem bijective_homologyThomMap_of_field (p m : ℕ) (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 (isIso_homologyThomMap_of_field p m h hu)

variable (F E) in
/-- **The homology Thom isomorphism over a field**, bundled as an isomorphism
`Hₘ(E, E₀; K) ≅ Hₚ(B; K)` (`finrank ℝ F + p = m`) in `ModuleCat K`, over an arbitrary base `B`. -/
def homologyThomIsoOfField (p m : ℕ) (h : finrank ℝ F + p = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  @asIso _ _ _ _ (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)
    (isIso_homologyThomMap_of_field p m h hu)

/-- The forward morphism of `TauCeti.homologyThomIsoOfField` is `TauCeti.homologyThomMap`. -/
@[simp]
theorem homologyThomIsoOfField_hom (p m : ℕ) (h : finrank ℝ F + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (homologyThomIsoOfField F E p m h u hu).hom =
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u :=
  (rfl)

/-- **The cohomology Thom isomorphism over a field and an arbitrary base** (Milnor–Stasheff,
Theorem 10.4; Hatcher, Theorem 4D.10). For a real vector bundle `E → B` over an arbitrary base `B`,
a field `K`, any `K`-vector space `M`, and any Thom class `u ∈ Hʳ(E, E₀; K)` (`r = finrank ℝ F`),
the Thom map `a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; K, M)` to `Hᵐ(E, E₀; K, M)` (`p + r = m`). -/
theorem bijective_thomMap_of_field (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  have h' : finrank ℝ F + p = m := by omega
  have : IsIso (pushforwardCap (thomPair F E) (thomPairProj F E) (ModuleCat.of K K)
      (finrank ℝ F) p m h' u) :=
    isIso_homologyThomMap_of_field p m h' hu
  rw [thomMap_def]
  exact bijective_pullbackCup_of_isIso_pushforwardCap (thomPair F E) (thomPairProj F E) M h h' u

variable (F E) in
/-- **The cohomology Thom isomorphism over a field and an arbitrary base**, bundled as a `K`-linear
equivalence `Hᵖ(B; K, M) ≃ₗ[K] Hᵐ(E, E₀; K, M)` (`p + finrank ℝ F = m`). -/
def thomEquivOfField (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (bijective_thomMap_of_field M p m h hu)

/-- `TauCeti.thomEquivOfField` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfField_apply (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfField F E M p m h u hu a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end IsomorphismOfField

end TauCeti
