/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.Topology.VectorBundle.EulerClass

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

## Main definitions and results

* `TauCeti.homologyThomMap`: the homology Thom map `x ↦ π_*(x ⌢ u)`, linear in `u`.
* `TauCeti.homologyThomMap_naturality`, `TauCeti.homologyThomMap_pullback`: naturality.
* `TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`: the restriction to a fibre.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
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

end TauCeti
