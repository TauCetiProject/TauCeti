/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Pushforward
public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion

/-!
# The homology Thom map and the Thom isomorphism in homology

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**homology Thom map** of `u` is

`Φ_u : Hₘ(E, E₀; A) ⟶ Hₚ(B; A)`,  `x ↦ π_*(x ⌢ u)`,  `n + p = m`,

the relative cap product `Hₘ(E, E₀) ⟶ Hₚ(E)` with `u` (`TopPair.singularCap`) followed by the
push-forward along the projection `π : E ⟶ B`, for any `K`-module of coefficients `A`: the map
`TopPair.pushforwardCap` of the Thom pair and its projection. When `u` is
a Thom class of a real vector bundle of rank `n` (for instance the unique Thom class with
coefficients in `ZMod 2`, or the Thom class of an orientation) it is the map of the Thom
isomorphism in homology (Spanier, Chapter 5, Section 7), the homological counterpart of the
cohomology Thom map `TauCeti.thomMap`, `a ↦ π^*a ⌣ u` (Milnor and Stasheff, Theorem 10.4).

Relative homology of Thom pairs is what attaching a disc bundle produces: when a bundle `ν` is
attached along its sphere bundle, the relative homology of the attachment is that of the Thom pair
`(ν, ν₀)`. So the homology Thom map is the map which identifies such a relative group, shifted by
the rank, with the homology of the base, as in the relative homology of a sublevel pair across a
Morse–Bott critical level.

This file sets up `TauCeti.homologyThomMap`, relates it to `TauCeti.thomMap` via Kronecker duality,
passes from cohomology to homology over any commutative ring `K`, proves the Thom isomorphism in
homology over an arbitrary base and an arbitrary commutative ring `K`, and deduces the Thom
isomorphism in cohomology over an arbitrary base over a field:

1. **Functoriality**: `TauCeti.homologyThomMap` is `K`-linear in `u`, natural
   (`TauCeti.homologyThomMap_naturality`, `TauCeti.homologyThomMap_pullback`), and restricts on
   fibres to capping with the fibre restriction of `u` pushed forward along the constant map
   (`TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`).
2. **Kronecker duality**: `⟨a, Φ_u(x)⟩ = (-1)^(n p) ⟨π^*a ⌣ u, x⟩`
   (`TauCeti.homologyThomMap_comp_singularKronecker`); over a field `K`, `Φ_u` with coefficients
   `A = K` is bijective iff `TauCeti.thomMap` over `K` is (`TauCeti.bijective_homologyThomMap_iff`).
3. **Over any commutative ring**: with injective coefficients `I` the Kronecker maps are bijective,
   so the Thom map with values in `I` is `±` precomposition with `Φ_u` on morphisms to `I`.
   Injective modules detect monomorphisms
   (`CategoryTheory.Injective.mono_iff_forall_surjective_comp`) and, being coseparating
   (`CategoryTheory.Injective.isCoseparating_isInjective`), epimorphisms. Hence `Φ_u` with
   coefficients `A = K` is injective, surjective, or bijective exactly when every Thom map
   `Hᵖ(B; I) ⟶ Hᵐ(E, E₀; I)` is surjective, injective, or bijective
   (`TauCeti.injective_homologyThomMap_iff_forall_surjective_thomMap`,
   `TauCeti.surjective_homologyThomMap_iff_forall_injective_thomMap`,
   `TauCeti.bijective_homologyThomMap_iff_forall_bijective_thomMap`): the Thom isomorphism in
   cohomology with all coefficient modules gives the Thom isomorphism in integral homology.
4. **Global Thom isomorphism in homology**: over a finite union of trivializing open sets the Thom
   map is bijective for every coefficient module
   (`TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`), in particular for every injective
   one, so the homology Thom map with coefficients `A = K` is an isomorphism there
   (`TopPair.isIso_pushforwardCap_of_bijective_pullbackCup`). The filtered
   colimit of singular homology over finite trivializing unions
   (`TauCeti.isColimitMapCoconeSingularHomology` via
   `TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion` and
   `TauCeti.isColimitMapCoconeSingularHomologyBaseFiniteTrivializingUnion`) then shows that for
   any Thom class `u`, `Φ_u` is an isomorphism `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` over any base `B`
   (`TauCeti.isIso_homologyThomMap`, `TauCeti.homologyThomIso`). For `K = ℤ` and the Thom class of
   an orientation this is the integral Thom isomorphism `Hₚ₊ᵣ(E, E₀; ℤ) ≅ Hₚ(B; ℤ)`.
5. **Global Thom isomorphism in cohomology over a field**: UCT
   (`TopPair.bijective_pullbackCup_of_isIso_pushforwardCap`) then gives
   `Hᵖ(B; K, M) ≃ₗ[K] Hᵐ(E, E₀; K, M)` for a field `K` (`TauCeti.bijective_thomMap_of_field`,
   `TauCeti.thomEquivOfField`).

## Main definitions and results

* `TauCeti.homologyThomMap`: the homology Thom map `x ↦ π_*(x ⌢ u)`, linear in `u`.
* `TauCeti.homologyThomMap_naturality`, `TauCeti.homologyThomMap_pullback`: naturality.
* `TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`: the restriction to a fibre.
* `TauCeti.homologyThomMap_comp_singularKronecker`: the homology Thom map is the transpose of the
  Thom map, up to the sign `(-1)^(n p)`.
* `TauCeti.bijective_homologyThomMap_iff`: over a field, the homology Thom map is bijective
  exactly when the Thom map is.
* `TauCeti.isIso_homologyThomMap`, `TauCeti.bijective_homologyThomMap`,
  `TauCeti.homologyThomIso`: for a Thom class `u` with coefficients in a commutative ring `K`, the
  homology Thom isomorphism `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` (`A = K`) over any base.
* `TauCeti.finrank_singularHomology_thomPair_of_isThomClass`: over a field, for a bundle with a Thom
  class, `dim Hₘ(E, E₀; K) = bₚ(B; K)`.
* `TauCeti.finrank_singularHomology_thomPair_of_subsingleton_units`: over a field whose only unit
  is `1`, such as `ZMod 2`, `dim Hₘ(E, E₀; K) = bₚ(B; K)` for every bundle, oriented or not.
* `TauCeti.finrank_singularHomology_thomPair_eq_ite`: over a field, the dimensions of the homology
  of the Thom pair in every degree from those in degrees at least the rank, the homology below the
  rank vanishing.
* `TauCeti.bijective_thomMap_of_field`, `TauCeti.thomEquivOfField`: the cohomology Thom isomorphism
  over a field and an arbitrary base with vector-space coefficients `M`.
* `TauCeti.bijective_homologyThomMap_iff_forall_bijective_thomMap`: over any commutative ring, the
  homology Thom map is bijective exactly when the Thom map is bijective with values in every
  injective module, with the injective and surjective halves
  `TauCeti.injective_homologyThomMap_iff_forall_surjective_thomMap` and
  `TauCeti.surjective_homologyThomMap_iff_forall_injective_thomMap`.

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
  (thomPair F E).pushforwardCap (thomPairProj F E) A n p m h

/-- The homology Thom map of a vector bundle is `TopPair.pushforwardCap` of its Thom pair and its
projection. -/
theorem homologyThomMap_def (n p m : ℕ) (h : n + p = m) :
    homologyThomMap F E A n p m h = (thomPair F E).pushforwardCap (thomPairProj F E) A n p m h :=
  (rfl)

variable {A}

/-- The homology Thom map is the relative cap product with `u` followed by the push-forward along
the projection. -/
theorem homologyThomMap_apply {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F E A n p m h u =
      (thomPair F E).singularCap K (λ_ A).inv (λ_ A).hom n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (thomPairProj F E) :=
  TopPair.pushforwardCap_apply _ _ A h u

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
  TopPair.pushforwardCap_naturality φ (thomPairProj F E) (thomPairProj F' E') g hφ A h u

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
`a ∈ Hᵖ(B; M)` with coefficients in any `K`-module `M` and `x ∈ Hₘ(E, E₀; K)`, `m = n + p`, the
Kronecker pairing of `a` with the homology Thom map `Φ_u(x) = π_*(x ⌢ u)` is `(-1)^(n p)` times
the pairing of the Thom map `π^*a ⌣ u` (`TauCeti.thomMap`) with `x`, both with values in `M`. -/
theorem homologyThomMap_comp_singularKronecker {M : ModuleCat.{w} K} {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ (TopCat.of B).singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • (thomPair F E).singularKronecker K m
        (thomMap F E M n p m (by omega) u a) := by
  rw [thomMap_def, homologyThomMap_def]
  exact (thomPair F E).pushforwardCap_comp_singularKronecker (thomPairProj F E) h u a

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
  rw [thomMap_def, homologyThomMap_def]
  exact (thomPair F E).bijective_pushforwardCap_iff (thomPairProj F E) h u

section Injective

variable {n p m : ℕ} (h : n + p = m)
  (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
  (I : ModuleCat.{w} K)

/-- Through the Kronecker maps of `B` and of `(E, E₀)` with values in a `K`-module `I`, the Thom map
`Hᵖ(B; I) ⟶ Hᵐ(E, E₀; I)` is `(-1)^(n p)` times the precomposition with the homology Thom map
`Hₘ(E, E₀; K) ⟶ Hₚ(B; K)`. -/
private theorem singularKronecker_comp_thomMap :
    ⇑((thomPair F E).singularKronecker K m (R := ModuleCat.of K K) (M := I)) ∘
        ⇑(thomMap F E I n p m (by omega) u) =
      (fun g ↦ ((-1 : ℤ) ^ (n * p)) • g) ∘
        (fun g ↦ homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ g) ∘
          ⇑((TopCat.of B).singularKronecker K p (R := ModuleCat.of K K) (M := I)) := by
  funext a
  simp [homologyThomMap_comp_singularKronecker F E h u a, smul_smul, ← mul_pow]

/-- Multiplication by the sign `(-1)^(n p)` is an involution. -/
private theorem involutive_neg_one_pow_smul {X Y : ModuleCat.{w} K} :
    Function.Involutive fun g : X ⟶ Y ↦ ((-1 : ℤ) ^ (n * p)) • g := fun g ↦ by
  simp [smul_smul, ← mul_pow]

/-- With injective coefficients `I`, the Thom map is surjective exactly when precomposition with
the homology Thom map is surjective on morphisms to `I`. -/
private theorem surjective_thomMap_iff [Injective I] :
    Function.Surjective (thomMap F E I n p m (by omega) u) ↔
      Function.Surjective fun g : _ ⟶ I ↦ homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ g := by
  rw [← Function.Surjective.of_comp_iff' ((thomPair F E).singularKronecker_bijective K m),
    singularKronecker_comp_thomMap F E h u I,
    Function.Surjective.of_comp_iff' involutive_neg_one_pow_smul.bijective,
    Function.Surjective.of_comp_iff _ ((TopCat.of B).singularKronecker_bijective K p).2]

/-- With injective coefficients `I`, the Thom map is injective exactly when precomposition with
the homology Thom map is injective on morphisms to `I`. -/
private theorem injective_thomMap_iff [Injective I] :
    Function.Injective (thomMap F E I n p m (by omega) u) ↔
      Function.Injective fun g : _ ⟶ I ↦ homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ g := by
  rw [← ((thomPair F E).singularKronecker_bijective K m).1.of_comp_iff,
    singularKronecker_comp_thomMap F E h u I, involutive_neg_one_pow_smul.injective.of_comp_iff,
    Function.Injective.of_comp_iff' _ ((TopCat.of B).singularKronecker_bijective K p)]

/-- **Injectivity of the homology Thom map over any commutative ring**: for `u ∈ Hⁿ(E, E₀; K)` and
`m = n + p`, the homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is injective exactly when the Thom map
`Hᵖ(B; I) ⟶ Hᵐ(E, E₀; I)` is surjective for every injective `K`-module `I`. With injective
coefficients the Kronecker maps are the universal coefficient isomorphisms, through which the
Thom map is `±` the transpose of the homology Thom map
(`TauCeti.homologyThomMap_comp_singularKronecker`), and injective modules detect monomorphisms
(`CategoryTheory.Injective.mono_iff_forall_surjective_comp`). -/
theorem injective_homologyThomMap_iff_forall_surjective_thomMap :
    Function.Injective (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom ↔
      ∀ (I : ModuleCat.{w} K) [Injective I],
        Function.Surjective (thomMap F E I n p m (by omega) u) := by
  rw [← ModuleCat.mono_iff_injective, Injective.mono_iff_forall_surjective_comp]
  exact forall_congr' fun I ↦ forall_congr' fun _ ↦ (surjective_thomMap_iff F E h u I).symm

/-- **Surjectivity of the homology Thom map over any commutative ring**: for `u ∈ Hⁿ(E, E₀; K)`
and `m = n + p`, the homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is surjective exactly when the
Thom map `Hᵖ(B; I) ⟶ Hᵐ(E, E₀; I)` is injective for every injective `K`-module `I`; injective
modules are coseparating (`CategoryTheory.Injective.isCoseparating_isInjective`), so they detect
epimorphisms. -/
theorem surjective_homologyThomMap_iff_forall_injective_thomMap :
    Function.Surjective (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom ↔
      ∀ (I : ModuleCat.{w} K) [Injective I],
        Function.Injective (thomMap F E I n p m (by omega) u) := by
  rw [← ModuleCat.epi_iff_surjective, Injective.isCoseparating_isInjective.epi_iff]
  exact forall_congr' fun I ↦ forall_congr' fun _ ↦ (injective_thomMap_iff F E h u I).symm

/-- **The Thom isomorphism in homology over any commutative ring**: for `u ∈ Hⁿ(E, E₀; K)` and
`m = n + p`, the homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is bijective exactly when the Thom
map `Hᵖ(B; I) ⟶ Hᵐ(E, E₀; I)` is bijective for every injective `K`-module `I`. So the Thom
isomorphism in cohomology with all coefficient modules, for instance with `K = ℤ` for the Thom
class of an orientation, gives the Thom isomorphism in integral homology. Over a field, where
every module is injective, `TauCeti.bijective_homologyThomMap_iff` needs only the coefficients
`K`. -/
theorem bijective_homologyThomMap_iff_forall_bijective_thomMap :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom ↔
      ∀ (I : ModuleCat.{w} K) [Injective I],
        Function.Bijective (thomMap F E I n p m (by omega) u) := by
  rw [Function.Bijective, injective_homologyThomMap_iff_forall_surjective_thomMap,
    surjective_homologyThomMap_iff_forall_injective_thomMap]
  exact ⟨fun h I _ ↦ ⟨h.2 I, h.1 I⟩, fun h ↦ ⟨fun I _ ↦ (h I).2, fun I _ ↦ (h I).1⟩⟩

end Injective

end HomologyThomMap

section Isomorphism

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private def homologyThomMapOver (A : ModuleCat.{w} K) (W : Set B)
    (n p m : ℕ) (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (thomPairOver F E W).singularHomology A m ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of W) :=
  (thomPairOver F E W).pushforwardCap (thomPairOverProj F E W) A n p m h
    (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem homologyThomMapOver_naturality (A : ModuleCat.{w} K)
    {W W' : Set B} (hWW' : W ⊆ W') {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMapOver A W n p m h u ≫ ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
        (TopCat.ofHom (ContinuousMap.inclusion hWW')) =
      TopPair.singularHomologyMap (thomPairOverMap F E hWW') A m ≫
        homologyThomMapOver A W' n p m h u := by
  dsimp only [homologyThomMapOver]
  rw [← thomPairOverMap_comp_restrictPreimagePairMap F E hWW',
    TopPair.singularCohomologyMap_comp_apply]
  exact TopPair.pushforwardCap_naturality (thomPairOverMap F E hWW') (thomPairOverProj F E W')
    (thomPairOverProj F E W) (TopCat.ofHom (ContinuousMap.inclusion hWW'))
    (thomPairOverMap_fst_comp_thomPairOverProj F E hWW') A h _

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
private theorem homologyThomMapOver_comp_map_subtypeVal (A : ModuleCat.{w} K) (W : Set B)
    {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMapOver A W n p m h u ≫ ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩) =
      TopPair.singularHomologyMap
        (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) A m ≫
        homologyThomMap F E A n p m h u := by
  have hι : thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom =
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W := by
    rw [thomPairOverUnivIso_hom, thomPairOverMap_comp_restrictPreimagePairMap]
  dsimp only [homologyThomMapOver]
  rw [← hι, homologyThomMap_def]
  exact TopPair.pushforwardCap_naturality _ (thomPairProj F E) (thomPairOverProj F E W)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
    (by rw [hι, restrictPreimagePairMap_fst_comp_thomPairProj]) A h u

private theorem isIso_homologyThomMapOver_finiteTrivializingUnion {p m : ℕ}
    (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (s : Finset B) :
    IsIso (homologyThomMapOver (ModuleCat.of K K) (⋃ b ∈ s, (trivializationAt F E b).baseSet)
      (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  -- Over a finite trivializing union the Thom map is bijective for every coefficient module.
  refine TopPair.isIso_pushforwardCap_of_bijective_pullbackCup _ _ h _ fun M _ ↦ ?_
  rw [← bijective_pullbackCupRestrict_thomPairProj_iff]
  exact bijective_pullbackCupRestrict_thomPair_biUnion M s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) p m (by omega) fun b _ ↦ hu b

private def homologyThomMapOverNatIso {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
  NatIso.ofComponents
    (fun s ↦ eqToIso (singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionDiagram_obj
        (ModuleCat.of K K) m s) ≪≫
      @asIso _ _ _ _ (homologyThomMapOver (ModuleCat.of K K)
        (⋃ b ∈ s, (trivializationAt F E b).baseSet) (finrank ℝ F) p m h u)
        (isIso_homologyThomMapOver_finiteTrivializingUnion h hu s) ≪≫ eqToIso (by simp))
    fun {s t} f ↦ by
      have := isIso_homologyThomMapOver_finiteTrivializingUnion h hu s
      have := isIso_homologyThomMapOver_finiteTrivializingUnion h hu t
      simp only [Functor.comp_obj, Functor.comp_map, thomPairFiniteTrivializingUnionDiagram_map,
        baseFiniteTrivializingUnionDiagram_map, Functor.map_comp, eqToHom_map,
        TopPair.singularHomologyFunctor_map, Iso.trans_hom, eqToIso.hom, asIso_hom,
        Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]
      rw [reassoc_of% (homologyThomMapOver_naturality (ModuleCat.of K K)
        (W := ⋃ b ∈ s, (trivializationAt F E b).baseSet)
        (W' := ⋃ b ∈ t, (trivializationAt F E b).baseSet)
        (biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)) h u)]

/-- **The homology Thom isomorphism** (Spanier, Chapter 5, Section 7): for `E → B` over any base
`B`, a commutative ring `K`, and a Thom class `u ∈ Hʳ(E, E₀; K)` (`r = finrank ℝ F`),
`homologyThomMap` is an isomorphism `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` (`r + p = m`) in `ModuleCat K`. For
`K = ℤ` and the Thom class of an orientation this is the integral Thom isomorphism. -/
theorem isIso_homologyThomMap (p m : ℕ) (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let P₂ := isColimitMapCoconeSingularHomologyBaseFiniteTrivializingUnion F E (ModuleCat.of K K) p
  let α := homologyThomMapOverNatIso h hu
  let hthom := singularHomologyFunctor_obj_thomPairFiniteTrivializingUnionCocone_pt
    (F := F) (E := E) (ModuleCat.of K K) m
  let hbase := congrArg (((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj)
    (baseFiniteTrivializingUnionCocone_pt F E).symm
  have hcocone : eqToHom hthom ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u ≫ eqToHom hbase =
      (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ (?_ : _ = _).trans (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
    dsimp only [Functor.mapCocone_ι_app, α, homologyThomMapOverNatIso,
      NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom, asIso_hom]
    simp only [thomPairFiniteTrivializingUnionCocone_ι_app,
      baseFiniteTrivializingUnionCocone_ι_app, Functor.map_comp, eqToHom_map,
      TopPair.singularHomologyFunctor_map, Category.assoc, TopPair.singularHomologyMap_comp,
      TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      eqToHom_trans]
    rw [← TopPair.singularHomologyMap_comp_assoc,
      reassoc_of% (homologyThomMapOver_comp_map_subtypeVal (ModuleCat.of K K)
        (⋃ b ∈ s, (trivializationAt F E b).baseSet) h u).symm]
  have : IsIso (eqToHom hthom ≫
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u ≫ eqToHom hbase) :=
    hcocone.symm ▸ (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  have := IsIso.of_isIso_comp_left (eqToHom hthom)
    (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u ≫ eqToHom hbase)
  exact IsIso.of_isIso_comp_right _ (eqToHom hbase)

/-- **The homology Thom map is bijective** on any base `B`: for a Thom class `u ∈ Hʳ(E, E₀; K)`
with coefficients in a commutative ring `K` (`r = finrank ℝ F`), the homology Thom map with
coefficients in `K`, `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` (`r + p = m`), is bijective. -/
theorem bijective_homologyThomMap (p m : ℕ) (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 (isIso_homologyThomMap p m h hu)

variable (F E) in
/-- **The homology Thom isomorphism**, bundled as `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` over any base `B` and
any commutative ring `K`. -/
def homologyThomIso (p m : ℕ) (h : finrank ℝ F + p = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  @asIso _ _ _ _ _ (isIso_homologyThomMap p m h hu)

/-- The forward morphism of `TauCeti.homologyThomIso` is `TauCeti.homologyThomMap`. -/
@[simp]
theorem homologyThomIso_hom (p m : ℕ) (h : finrank ℝ F + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (homologyThomIso F E p m h u hu).hom =
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u := (rfl)

end Isomorphism

section IsomorphismOfField

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [Field K]

/-- **The cohomology Thom isomorphism over a field and an arbitrary base** (Milnor–Stasheff,
Theorem 10.4; Hatcher, Theorem 4D.10): for `E → B` over any `B`, a field `K`, any `K`-vector space
`M`, and any Thom class `u`, `thomMap` is bijective from `Hᵖ(B; K, M)` to `Hᵐ(E, E₀; K, M)`. -/
theorem bijective_thomMap_of_field (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  have : IsIso ((thomPair F E).pushforwardCap (thomPairProj F E) (ModuleCat.of K K)
      (finrank ℝ F) p m (by omega) u) := isIso_homologyThomMap p m (by omega) hu
  rw [thomMap_def]
  exact (thomPair F E).bijective_pullbackCup_of_isIso_pushforwardCap (thomPairProj F E) M h
    ((TopCat.of B).singularKronecker_bijective_of_projective_homology (ModuleCat.of K K) M p)
    ((thomPair F E).singularKronecker_bijective_of_projective_homology (ModuleCat.of K K) M m) u

variable (F E) in
/-- **The cohomology Thom isomorphism over a field and an arbitrary base**, bundled as
`Hᵖ(B; K, M) ≃ₗ[K] Hᵐ(E, E₀; K, M)`. -/
def thomEquivOfField (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_field M p m h hu)

/-- `TauCeti.thomEquivOfField` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfField_apply (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfField F E M p m h u hu a = thomMap F E M (finrank ℝ F) p m h u a := (rfl)

variable (F E) in
/-- **The homology Thom isomorphism, in dimensions.** Let `E → B` be a real vector bundle with
fibres of dimension `r` over any base, and `K` a field. If `E` has a Thom class with coefficients in
`K`, then `dim Hₘ(E, E₀; K)` is the Betti number `bₚ(B; K)` whenever `r + p = m`
(`TauCeti.homologyThomIso`). -/
theorem finrank_singularHomology_thomPair_of_isThomClass (p m : ℕ) (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    finrank K ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat K) =
      bettiNumber K B p := by
  rw [bettiNumber_def]
  exact (homologyThomIso F E p m h u hu).toLinearEquiv.finrank_eq

variable (F E) in
/-- **The mod `2` homology Thom isomorphism, in dimensions.** Let `K` be a field whose only unit is
`1`, such as `ZMod 2`. For a real vector bundle `E → B` with fibres of dimension `r`, over any base
and with no orientation, `dim Hₘ(E, E₀; K)` is the Betti number `bₚ(B; K)` whenever `r + p = m`:
the bundle has a Thom class with coefficients in `K`
(`TauCeti.existsUnique_isThomClass_of_subsingleton_units`), and its homology Thom map is an
isomorphism (`TauCeti.homologyThomIso`). -/
theorem finrank_singularHomology_thomPair_of_subsingleton_units [FiniteDimensional ℝ F]
    [Subsingleton Kˣ] (p m : ℕ) (h : finrank ℝ F + p = m) :
    finrank K ((thomPair F E).singularHomology (ModuleCat.of K K) m : ModuleCat K) =
      bettiNumber K B p := by
  have hu := (existsUnique_isThomClass_of_subsingleton_units (F := F) (E := E) K).exists
  exact finrank_singularHomology_thomPair_of_isThomClass F E p m h hu.choose_spec

variable (F E) in
/-- **The dimensions of the homology of a Thom pair in every degree.** Let `E → B` be a real vector
bundle of rank `r` and `K` a field. If `dim H_{r + p}(E, E₀; K) = d p` for every `p`, then
`dim Hₙ(E, E₀; K)` is `d (n - r)` when `r ≤ n`, and `0` when `n < r`. -/
theorem finrank_singularHomology_thomPair_eq_ite [FiniteDimensional ℝ F] {r : ℕ}
    (hr : finrank ℝ F = r) (d : ℕ → ℕ)
    (hd : ∀ p, finrank K ((thomPair F E).singularHomology (ModuleCat.of K K) (r + p) :
      ModuleCat K) = d p) (n : ℕ) :
    finrank K ((thomPair F E).singularHomology (ModuleCat.of K K) n : ModuleCat K) =
      if r ≤ n then d (n - r) else 0 := by
  split_ifs with hrn
  · rw [← hd, Nat.add_sub_cancel' hrn]
  · exact ModuleCat.finrank_eq_zero_of_isZero
      (isZero_singularHomology_thomPair (F := F) (E := E) (ModuleCat.of K K) (by omega))

end IsomorphismOfField

end TauCeti
