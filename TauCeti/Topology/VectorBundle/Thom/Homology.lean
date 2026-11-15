/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The homology Thom map of a vector bundle

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**homology Thom map** of `u` is

`Φ_u : Hₘ(E, E₀; A) ⟶ Hₚ(B; A)`,  `x ↦ π_*(x ⌢ u)`,  `n + p = m`,

the relative cap product `Hₘ(E, E₀) ⟶ Hₚ(E)` with `u` (`TopPair.singularCap`) followed by the
push-forward along the projection `π : E ⟶ B`, for any `K`-module of coefficients `A`. When `u` is
a Thom class of a real vector bundle of rank `n` (for instance the unique Thom class with
coefficients in `ZMod 2`, or the Thom class of an orientation) it is the map of the Thom
isomorphism in homology, which is bijective in every degree (Spanier, Chapter 5, Section 7); this
file does not prove that. It is the homological counterpart of the cohomology Thom map
`TauCeti.thomMap`, `a ↦ π^*a ⌣ u`, whose bijectivity is Milnor and Stasheff's Theorem 10.4.

Relative homology of Thom pairs is what attaching a disc bundle produces: when a bundle `ν` is
attached along its sphere bundle, the relative homology of the attachment is that of the Thom pair
`(ν, ν₀)`. So the homology Thom map is the map which identifies such a relative group, shifted by
the rank, with the homology of the base, as in the relative homology of a sublevel pair across a
Morse–Bott critical level.

This file sets up the map and the properties a proof of the isomorphism uses. It is `K`-linear in
`u` (`TauCeti.homologyThomMap`). It is natural in maps of Thom pairs covering maps of the bases
(`TauCeti.homologyThomMap_naturality`), in particular in pull-backs of bundles
(`TauCeti.homologyThomMap_pullback`), so it commutes with the restriction to open sets of the base
that the Mayer–Vietoris argument uses. On the fibre pair `(E_b, E_b ∖ {0})` over a point `b`, it is
the cap product with the restriction of `u`, pushed forward along the constant map at `b`
(`TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`).

With coefficients in `K` itself, the homology Thom map is the transpose of the cohomology Thom map
`TauCeti.thomMap` under the Kronecker pairing, up to a sign:
`⟨a, Φ_u(x)⟩ = (-1)^(n p) ⟨π^*a ⌣ u, x⟩` for `a ∈ Hᵖ(B; K)` and `x ∈ Hₘ(E, E₀; K)`
(`TauCeti.homologyThomMap_comp_singularKronecker`). The cap product with `u` is adjoint to the cup
product `u ⌣ π^*a` with `u` on the left, and graded commutativity of the cup product of relative
and absolute classes (`TopPair.singularCup_gradedComm`) moves `u` to the right, where the Thom map
has it. Over a field the Kronecker pairing identifies cohomology with the dual of homology, so the
homology Thom map is bijective in a degree exactly when the Thom map is bijective in the
corresponding degree (`TauCeti.bijective_homologyThomMap_iff`): the Thom isomorphism in cohomology
over a field gives the one in homology, and conversely.

## Main definitions and results

* `TauCeti.homologyThomMap`: the homology Thom map `x ↦ π_*(x ⌢ u)`, linear in `u`.
* `TauCeti.homologyThomMap_naturality`, `TauCeti.homologyThomMap_pullback`: naturality.
* `TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`: the restriction to a fibre.
* `TauCeti.homologyThomMap_comp_singularKronecker`: the homology Thom map is the transpose of the
  Thom map, up to the sign `(-1)^(n p)`.
* `TauCeti.bijective_homologyThomMap_iff`: over a field, the homology Thom map is bijective exactly
  when the Thom map is.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.3, the identity
  `⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩`.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory AlgebraicTopology

universe w

namespace TauCeti

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
      TopPair.singularHomologyMap φ A m ≫ homologyThomMap F E A n p m h u := by
  rw [homologyThomMap_apply, homologyThomMap_apply, Category.assoc, ← Functor.map_comp, ← hφ,
    Functor.map_comp, ← Category.assoc, TopPair.singularCap_naturality, Category.assoc]

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
`a ∈ Hᵖ(B; K)` and `x ∈ Hₘ(E, E₀; K)`, `m = n + p`, the Kronecker pairing of `a` with the homology
Thom map `Φ_u(x) = π_*(x ⌢ u)` is `(-1)^(n p)` times the pairing of the Thom map
`π^*a ⌣ u` (`TauCeti.thomMap`) with `x`. -/
theorem homologyThomMap_comp_singularKronecker {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ (TopCat.of B).singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • (thomPair F E).singularKronecker K m
        (thomMap F E (ModuleCat.of K K) n p m (by omega) u a) := by
  -- `⟨a, π_*(x ⌢ u)⟩ = ⟨π^*a, x ⌢ u⟩ = ⟨u ⌣ π^*a, x⟩`, and `u ⌣ π^*a = (-1)^(n p) π^*a ⌣ u`.
  rw [homologyThomMap_apply, Category.assoc, ← TopCat.singularKronecker_naturality,
    TopPair.singularCap_comp_singularKronecker, thomMap_apply,
    TopPair.singularCup_gradedComm K (thomPair F E) (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ (ModuleCat.of K K)).hom)
      (μ := (ρ_ (ModuleCat.of K K)).hom) ?_ ?_ (by omega), map_zsmul, mul_comm]
  -- `thomMap` cups along `(λ_ (𝟙_ (ModuleCat K))).inv`, while the cap product side uses
  -- `ModuleCat.of K K`; both remaining `rfl`s close the definitional equality
  -- `𝟙_ (ModuleCat K) = ModuleCat.of K K` of Mathlib's monoidal structure on `ModuleCat K`.
  · rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor _

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
  set T := (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom
  have hc : ((-1 : K) ^ (n * p)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  -- The linear form of `π^*a ⌣ u` is `(-1)^(n p)` times the dual map of `T` applied to that
  -- of `a`.
  have key : ∀ a, (thomPair F E).singularCohomologyDualEquiv m
      (thomMap F E (ModuleCat.of K K) n p m (by omega) u a) =
      LinearEquiv.smulOfNeZero K _ _ hc
        (T.dualMap ((TopCat.of B).singularCohomologyDualEquiv p a)) := by
    intro a
    ext x
    have hx := congrArg (fun φ ↦ φ.hom x) (homologyThomMap_comp_singularKronecker F E h u a)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply] at hx
    rw [LinearEquiv.smulOfNeZero_apply, LinearMap.smul_apply, LinearMap.dualMap_apply,
      TopPair.singularCohomologyDualEquiv_apply, TopCat.singularCohomologyDualEquiv_apply, hx]
    simp [← Int.cast_smul_eq_zsmul K, ← mul_assoc, ← mul_pow]
  have e : ⇑(thomMap F E (ModuleCat.of K K) n p m (by omega) u) =
      ⇑((thomPair F E).singularCohomologyDualEquiv m).symm ∘ ⇑(LinearEquiv.smulOfNeZero K _ _ hc) ∘
        ⇑T.dualMap ∘ ⇑((TopCat.of B).singularCohomologyDualEquiv p) := by
    funext a
    simp only [Function.comp_apply, ← key, LinearEquiv.symm_apply_apply]
  rw [e, EquivLike.comp_bijective, EquivLike.comp_bijective, EquivLike.bijective_comp,
    LinearMap.dualMap_bijective_iff]

end TauCeti
