/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.Topology.VectorBundle.EulerClass
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Isomorphism
import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
import TauCeti.Topology.VectorBundle.Thom.Class

/-!
# The Thom isomorphism in cohomology

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**Thom map** of `u` is

`Φ_u : Hᵖ(B; M) ⟶ Hᵖ⁺ⁿ(E, E₀; M)`,  `a ↦ π^*a ⌣ u`,

the pull-back along the projection `π : E ⟶ B` followed by the cup product of absolute and
relative cohomology (`TopPair.singularCup`), for any `K`-module of coefficients `M`: the map
`TopPair.pullbackCup` of the Thom pair and its projection.

This file sets up `TauCeti.thomMap` and `TauCeti.thomMapOver` and proves the **Thom isomorphism**
(Milnor–Stasheff, Theorem 10.4; Hatcher, Theorem 4D.10; Spanier, Chapter 5, Section 7) over any
commutative ring `K` with `K`-module coefficients `M` for every finite rank `r = finrank ℝ F ≥ 0`
whenever `B` admits a finite trivializing cover (extended to arbitrary bases over a field in
`TauCeti.Topology.VectorBundle.Thom.Homology`):

1. **Basic and subset-restricted properties**: `TauCeti.thomMap` is `K`-bilinear, sends
   `1 ∈ H⁰(B; K)` to `u` (`TauCeti.thomMap_one`), is natural (`TauCeti.thomMap_naturality`,
   `TauCeti.thomMap_pullback`), is `H^*(B; K)`-linear (`TauCeti.thomMap_singularCup`), and restricts
   on fibres to cupping with the fibre restriction of `u`
   (`TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`). Over any subset `W ⊆ B`,
   `TauCeti.thomMapOver` restricts `u` to `(E|_W, E₀|_W)`, commutes with subset inclusions,
   ambient restriction, and pullback along `W ↪ B` (`TauCeti.thomMapOver_naturality`,
   `TauCeti.thomMapOver_singularCohomologyMap_subtypeVal`,
   `TauCeti.singularCohomologyMap_pullbackSubtypeValThomPairMap_thomMapOver`,
   `TauCeti.bijective_thomMapOver_iff_pullback`). For a real vector bundle, the Euler class map
   `TauCeti.eulerClass` sends `Φ_u(a)` to `a ⌣ e(u)` (`TauCeti.eulerClass_thomMap`).
2. **Local and finite-union isomorphisms**: an `ℝ`-linear trivialization identifies `(E|_W, E₀|_W)`
   with `(W × F, W × (F ∖ {0}))` (`Bundle.Trivialization.thomPairOverIso`), reducing
   `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair` (bundled as
   `Bundle.Trivialization.thomEquivOver`, with global-Thom-class specialization
   `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`) to
   `TauCeti.bijective_pullbackCup_prodThomPair`. Mayer–Vietoris induction
   (`TopCat.bijective_pullbackCupRestrict_union`) with below-rank vanishing
   (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`) over open sets, combined with
   pullback to `⋃ i ∈ s, W i` (`TauCeti.bijective_thomMapOver_iff_pullback`), gives
   `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion` and `TauCeti.thomEquivOverBiUnion` over
   arbitrary finite unions of trivializing sets without requiring `W i` to be open.
3. **Global Thom isomorphisms and equivalences** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`
   (`p + finrank ℝ F = m`) for any `TauCeti.IsThomClass`:
   `TauCeti.IsThomClass.bijective_thomMap_of_baseSet_eq_univ`, `Bundle.Trivialization.thomEquiv`,
   `TauCeti.IsThomClass.trivialThomEquiv`, `TauCeti.thomEquivOfBiUnionEqUniv`,
   `TauCeti.thomEquivOfIUnionEqUniv`, and `TauCeti.thomEquivOfCompactSpace`.

## Main definitions and results

* `TauCeti.thomMap`, `TauCeti.thomMapOver`: the Thom map `a ↦ π^*a ⌣ u` and its restriction over
  `W ⊆ B`, bilinear in `u` and `a`.
* `TauCeti.thomMap_one`, `TauCeti.thomMapOver_one`: `Φ_u(1) = u` and its subset form.
* `TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`, `TauCeti.thomMapOver_naturality`,
  `TauCeti.thomMapOver_singularCohomologyMap_subtypeVal`,
  `TauCeti.singularCohomologyMap_pullbackSubtypeValThomPairMap_thomMapOver`,
  `TauCeti.bijective_thomMapOver_iff_pullback`: naturality and pullback compatibility.
* `TauCeti.thomMap_singularCup`: linearity over the cohomology of the base.
* `TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`: the restriction to a fibre.
* `TauCeti.eulerClass_thomMap`: the Euler class map sends `Φ_u(a)` to `a ⌣ e(u)`.
* `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair`,
  `Bundle.Trivialization.thomEquivOver`,
  `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`,
  `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`, `TauCeti.thomEquivOverBiUnion`: local
  and finite-union bijectivity and linear equivalences over arbitrary trivializing subsets.
* `TauCeti.IsThomClass.bijective_thomMap_of_baseSet_eq_univ`, `Bundle.Trivialization.thomEquiv`,
  `TauCeti.IsThomClass.bijective_thomMap_trivial`, `TauCeti.IsThomClass.trivialThomEquiv`,
  `TauCeti.bijective_thomMap_of_biUnion_eq_univ`, `TauCeti.thomEquivOfBiUnionEqUniv`,
  `TauCeti.bijective_thomMap_of_iUnion_eq_univ`, `TauCeti.thomEquivOfIUnionEqUniv`,
  `TauCeti.bijective_thomMap_of_compactSpace`, `TauCeti.thomEquivOfCompactSpace`: global Thom
  isomorphisms over trivializable bundles, finite trivializing covers, and compact bases.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module Set

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom map** `a ↦ π^*a ⌣ u` of a relative class `u ∈ Hⁿ(E, E₀; K)`, from `Hᵖ(B; M)` to
`Hᵐ(E, E₀; M)`, `p + n = m`, as a `K`-bilinear map of `u` and `a`. The chain coefficients are `K`,
and the pairing of values is the right unitor `M ⊗ K ≅ M`. For a Thom class `u` of a real vector
bundle of rank `n` it is the Thom isomorphism. -/
def thomMap (n p m : ℕ) (h : p + n = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (thomPair F E).pullbackCup M (thomPairProj F E) n p m h

/-- The Thom map of a vector bundle is `TopPair.pullbackCup` of its Thom pair and its projection,
so the results stated for the latter, such as the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union`, apply to it. -/
theorem thomMap_def (n p m : ℕ) (h : p + n = m) :
    thomMap F E M n p m h = (thomPair F E).pullbackCup M (thomPairProj F E) n p m h :=
  (rfl)

variable {M}

/-- The Thom map is the cup product of the pull-back to the total space with `u`. -/
theorem thomMap_apply {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F E M n p m h u a =
      (thomPair F E).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (thomPairProj F E) p a) u :=
  TopPair.pullbackCup_apply _ _ h u a

/-- **The Thom map sends `1` to `u`**: the image of the class of the constant `0`-cocycle with
value `1 ∈ K` is `u`. -/
@[simp]
theorem thomMap_one {n : ℕ} (h : 0 + n = n)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMap F E (ModuleCat.of K K) n 0 n h u
        (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
          ((TopCat.of B).constSingularCocycle K (𝟙 (ModuleCat.of K K)))) = u :=
  TopPair.pullbackCup_one _ _ h u

/-- **Naturality of the Thom map.** A map of Thom pairs `φ : (E', E'₀) ⟶ (E, E₀)` covering a map
of bases `g : B' ⟶ B` intertwines the Thom map of `u` with that of its pull-back `φ^*u`:
`Φ_{φ^*u}(g^*a) = φ^*Φ_u(a)`. -/
theorem thomMap_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type*} [TopologicalSpace F']
    {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, Zero (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g) {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F' E' M n p m h (TopPair.singularCohomologyMap φ n u)
        (TopCat.singularCohomologyMap g p a) =
      TopPair.singularCohomologyMap φ m (thomMap F E M n p m h u a) :=
  TopPair.pullbackCup_naturality φ _ _ g hφ h u a

attribute [local instance] pullbackFiberZero in
/-- **The Thom map of a pull-back bundle.** For a continuous map `f : B' ⟶ B`, the Thom map of
the pull-back of `u` to `f^*E` sends `f^*a` to the pull-back of `Φ_u(a)`. -/
theorem thomMap_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F ((⇑f) *ᵖ E) M n p m h
        (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom f) p a) =
      TopPair.singularCohomologyMap (pullbackThomPairMap F E f) m (thomMap F E M n p m h u a) :=
  thomMap_naturality F E _ _ (pullbackThomPairMap_fst_comp_thomPairProj F E f) h u a

/-- **The Thom map on a fibre.** Restricted to the fibre pair `(E_b, E_b ∖ {0})`, the Thom map
of `u` is the cup product of the pull-back of `a` along the constant map at `b` with the
restriction of `u`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomMap (b : B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) m (thomMap F E M n p m h u a) =
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCup K
        (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.const (E b) b)) p a)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u) := by
  rw [thomMap_apply, ← TopPair.singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, fiberThomPairMap_fst_comp_thomPairProj]
  rfl

/-- **The Thom map is linear over the cohomology of the base**: for `a ∈ H^q(B; K)` and
`b ∈ Hᵖ(B; M)`, `Φ_u(a ⌣ b) = π^*a ⌣ Φ_u(b)`. -/
theorem thomMap_singularCup {n p q r m s : ℕ} (h : p + n = m) (hqp : q + p = r)
    (hrn : r + n = s) (hqm : q + m = s)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) q)
    (b : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F E M n r s hrn u
        ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p r hqp a b) =
      (thomPair F E).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q m s hqm
        (TopCat.singularCohomologyMap (thomPairProj F E) q a) (thomMap F E M n p m h u b) := by
  rw [thomMap_apply, thomMap_apply, ← TopCat.singularCup_naturality]
  exact TopPair.singularCup_assoc K (thomPair F E) (by monoidal) (by monoidal) hqp hrn h hqm _ _ _

/-- Bijectivity of `TopCat.pullbackCupRestrict` along `TauCeti.thomPairProj` over `W` is
equivalent to bijectivity of `TopPair.pullbackCup` on `TauCeti.thomPairOver F E W`. -/
theorem bijective_pullbackCupRestrict_thomPairProj_iff (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E)
        (zeroSectionCompl F E) M W n p m h u) ↔
      Function.Bijective ((thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) n p m h
        (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u)) := by
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      (Function.Bijective (TopCat.pullbackCupRestrict π' (zeroSectionCompl F E) M W n p m h u) ↔
        Function.Bijective ((thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) n p m h
          (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
            (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u))) from
    this _ rfl
  intro π' hπ'
  rw [thomPairProj_def] at hπ'
  subst hπ'
  rw [TopCat.pullbackCupRestrict_apply, thomPairOverProj_def]
  rfl

section ThomMapOver

variable (M) in
/-- **The Thom map over a subset `W` of the base**: the `K`-bilinear map sending a global relative
class `u ∈ Hⁿ(E, E₀; K)` and `a ∈ Hᵖ(W; M)` to `(π|_W)^* a ⌣ (u|_W) ∈ Hᵐ(E|_W, E₀|_W; M)`, for
`p + n = m`. -/
def thomMapOver (W : Set B) (n p m : ℕ) (h : p + n = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  (thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) n p m h ∘ₗ
    (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n).hom

variable (M) in
/-- `TauCeti.thomMapOver` is `TopPair.pullbackCup` along `TauCeti.thomPairOverProj` composed with
restriction to `(E|_W, E₀|_W)`. -/
theorem thomMapOver_def (W : Set B) (n p m : ℕ) (h : p + n = m) :
    thomMapOver F E M W n p m h =
      (thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) n p m h ∘ₗ
        (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n).hom :=
  (rfl)

/-- Evaluating `TauCeti.thomMapOver` at `u` gives `TopPair.pullbackCup` along
`TauCeti.thomPairOverProj` and the restriction of `u` to `(E|_W, E₀|_W)`. -/
theorem thomMapOver_apply (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMapOver F E M W n p m h u =
      (thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) n p m h
        (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u) :=
  (rfl)

variable (M) in
/-- `TauCeti.thomMapOver` agrees with `TopCat.pullbackCupRestrict` of the bundle projection and
`zeroSectionCompl`. -/
theorem thomMapOver_eq_pullbackCupRestrict (W : Set B) (n p m : ℕ) (h : p + n = m) :
    thomMapOver F E M W n p m h =
      TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
        (zeroSectionCompl F E) M W n p m h := by
  ext u a
  rw [thomMapOver_apply, TopCat.pullbackCupRestrict_apply, thomPairOverProj_def]
  rfl

/-- **Over `W`, `thomMapOver` sends `1` to the restriction of `u`** to `(E|_W, E₀|_W)`. -/
@[simp]
theorem thomMapOver_one (W : Set B) {n : ℕ} (h : 0 + n = n)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMapOver F E (ModuleCat.of K K) W n 0 n h u
        (((TopCat.of W).singularCochainComplex (ModuleCat.of K K) K
          (ModuleCat.of K K)).homologyπ 0
          ((TopCat.of W).constSingularCocycle K (𝟙 (ModuleCat.of K K)))) =
      TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u := by
  rw [thomMapOver_apply]
  exact TopPair.pullbackCup_one _ _ h _

/-- **Naturality of `thomMapOver` in the subset**: for `W ⊆ W'`, restricting `a ∈ Hᵖ(W'; M)` to `W`
and applying `thomMapOver` over `W` agrees with applying `thomMapOver` over `W'` and restricting
along `thomPairOverMap`. -/
theorem thomMapOver_naturality {W W' : Set B} (hWW' : W ⊆ W') {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W').singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h u
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hWW')) p a) =
      TopPair.singularCohomologyMap (thomPairOverMap F E hWW') m
        (thomMapOver F E M W' n p m h u a) := by
  rw [thomMapOver_apply, thomMapOver_apply,
    ← thomPairOverMap_comp_restrictPreimagePairMap F E hWW',
    TopPair.singularCohomologyMap_comp_apply]
  exact TopPair.pullbackCup_naturality (thomPairOverMap F E hWW') _ _ _
    (thomPairOverMap_fst_comp_thomPairOverProj F E hWW') h _ a

/-- **Compatibility of `thomMapOver` with `thomMap` under restriction from `B` to `W`**: evaluating
`thomMapOver` over `W` at the restriction of `a ∈ Hᵖ(B; M)` agrees with restricting `thomMap` of `a`
to `(E|_W, E₀|_W)`. -/
theorem thomMapOver_singularCohomologyMap_subtypeVal (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h u
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W)) p a) =
      TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) m
        (thomMap F E M n p m h u a) := by
  rw [thomMapOver_eq_pullbackCupRestrict, thomMap_def, thomPairProj_def]
  exact TopCat.pullbackCupRestrict_singularCohomologyMap_subtypeVal _ _ M W h u a

attribute [local instance] pullbackFiberZero in
/-- **Compatibility of `thomMapOver` with `thomMap` of the pullback bundle along `W ↪ B`**: pulling
`thomMapOver` over `W` back along `pullbackSubtypeValThomPairMap` gives `thomMap` of the pulled-back
class on `(ContinuousMap.subtypeVal W) *ᵖ E`. -/
theorem singularCohomologyMap_pullbackSubtypeValThomPairMap_thomMapOver (W : Set B) {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (pullbackSubtypeValThomPairMap F E W) m
        (thomMapOver F E M W n p m h u a) =
      thomMap F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) M n p m h
        (TopPair.singularCohomologyMap
          (pullbackThomPairMap F E (ContinuousMap.subtypeVal W)) n u) a := by
  have hcomm : TopPair.Hom.fst (pullbackSubtypeValThomPairMap F E W) ≫ thomPairOverProj F E W =
      thomPairProj F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) ≫ 𝟙 (TopCat.of W) := by
    rw [Category.comp_id, pullbackSubtypeValThomPairMap_fst_comp_thomPairOverProj]
  have key := (TopPair.pullbackCup_naturality (pullbackSubtypeValThomPairMap F E W)
    (thomPairProj F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E)) (thomPairOverProj F E W)
    (𝟙 (TopCat.of W)) hcomm h
    (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u) a).symm
  simpa [thomMapOver_apply, thomMap_def, ← TopPair.singularCohomologyMap_comp_apply] using key

/-- Over `Set.univ`, `thomMapOver` is bijective if and only if `thomMap` is. -/
theorem bijective_thomMapOver_univ_iff {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M univ n p m h u) ↔
      Function.Bijective (thomMap F E M n p m h u) := by
  rw [thomMapOver_eq_pullbackCupRestrict, thomMap_def, thomPairProj_def]
  exact TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h u

/-- Over the empty set `∅ ⊆ B`, `thomMapOver` is bijective in every degree because both domain and
codomain vanish. -/
theorem bijective_thomMapOver_empty {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M ∅ n p m h u) := by
  rw [thomMapOver_eq_pullbackCupRestrict]
  exact TopCat.bijective_pullbackCupRestrict_empty _ _ M h u

attribute [local instance] pullbackFiberZero in
/-- Over any subset `W ⊆ B`, `thomMapOver` of `u` is bijective if and only if `thomMap` of the
pulled-back class `i^* u` on the pullback bundle `i^* E` along `i = ContinuousMap.subtypeVal W` is
bijective. -/
theorem bijective_thomMapOver_iff_pullback (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M W n p m h u) ↔
      Function.Bijective (thomMap F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) M n p m h
        (TopPair.singularCohomologyMap
          (pullbackThomPairMap F E (ContinuousMap.subtypeVal W)) n u)) := by
  rw [thomMapOver_apply, thomMap_def,
    ← pullbackSubtypeValThomPairMap_comp_restrictPreimagePairMap F E W,
    TopPair.singularCohomologyMap_comp_apply]
  have hcomm : TopPair.Hom.fst (pullbackSubtypeValThomPairMap F E W) ≫ thomPairOverProj F E W =
      thomPairProj F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) ≫ 𝟙 (TopCat.of W) := by
    rw [Category.comp_id, pullbackSubtypeValThomPairMap_fst_comp_thomPairOverProj]
  exact (TopPair.bijective_pullbackCup_iff_of_isIso (pullbackSubtypeValThomPairMap F E W)
    (𝟙 (TopCat.of W)) hcomm h _).symm

end ThomMapOver

section EulerClass

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

/-- **The Euler class map on the image of the Thom map**: for `u ∈ Hⁿ(E, E₀; K)` and
`a ∈ Hᵖ(B; M)`, the Euler class of `π^*a ⌣ u` is `a ⌣ e(u)`, the cup product of `a` with the Euler
class of `u`. -/
theorem eulerClass_thomMap {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    eulerClass (ModuleCat.of K K) K M F E m (thomMap F E M n p m h u a) =
      (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h a
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u) := by
  rw [eulerClass_def, eulerClass_def, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    thomMap_apply, TopPair.singularCohomologyπ_singularCup, ← TopCat.singularCup_naturality,
    ← ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom,
    ConcreteCategory.id_apply]
  -- The two sides differ only in writing the chain coefficients `K` as `𝟙_ (ModuleCat K)`.
  rfl

end EulerClass

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

include e in
/-- **Local Thom isomorphism over a trivializing set**: for `W ⊆ e.baseSet` and `u ∈ Hʳ(E, E₀; K)`
(`r = finrank ℝ F`) spanning `Hʳ(E_b, E_b ∖ {0}; K)` over every `b ∈ W`,
`TopCat.pullbackCupRestrict` of `u` over `W` is bijective in every degree. -/
theorem bijective_pullbackCupRestrict_thomPair [FiniteDimensional ℝ F] {W : Set B}
    (hW : W ⊆ e.baseSet) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E)
      (zeroSectionCompl F E) M W (finrank ℝ F) p m h u) := by
  rw [bijective_pullbackCupRestrict_thomPairProj_iff]
  set u_W := TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
    (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) (finrank ℝ F) u
  let φ := e.thomPairOverIso ℝ hW
  let u_prod := TopPair.singularCohomologyMap φ.inv (finrank ℝ F) u_W
  have hu_W : TopPair.singularCohomologyMap φ.hom (finrank ℝ F) u_prod = u_W := by
    simp [u_prod, ← TopPair.singularCohomologyMap_comp_apply]
  have hproj : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F =
      thomPairOverProj F E W ≫ 𝟙 (TopCat.of W) :=
    (e.thomPairOverIso_hom_fst_comp_prodThomPairProj ℝ hW).trans (Category.comp_id _).symm
  rw [← hu_W, TopPair.bijective_pullbackCup_iff_of_isIso φ.hom (𝟙 (TopCat.of W)) hproj h u_prod]
  refine bijective_pullbackCup_prodThomPair M u_prod (fun b ↦ ?_) h
  have hu_prod : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u_prod =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b.val (hW b.property)).complZeroPairIso.inv (finrank ℝ F)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b.val) (finrank ℝ F) u) := by
    dsimp only [u_prod, u_W, φ]
    rw [← TopPair.singularCohomologyMap_comp_apply,
      e.prodThomPairFiberMap_comp_thomPairOverIso_inv ℝ hW b,
      TopPair.singularCohomologyMap_comp_apply,
      ← TopPair.singularCohomologyMap_comp_apply (fiberThomPairOverMap F E b.property),
      fiberThomPairOverMap_comp_restrictPreimagePairMap]
  rw [hu_prod]
  exact ((((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
    (finrank ℝ F)).mapIso
      (e.continuousLinearEquivAt ℝ b.val (hW b.property)).complZeroPairIso.symm.op).toLinearEquiv
    ).span_singleton_apply_eq_top_iff).2 (hu b.val b.property)

/-- **Local Thom isomorphism over a trivializing set**, bundled as
`Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)`. -/
def thomEquivOver [FiniteDimensional ℝ F] {W : Set B} (hW : W ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMapOver F E M W (finrank ℝ F) p m h u)
    ((bijective_pullbackCupRestrict_thomPairProj_iff F E W h u).1
      (e.bijective_pullbackCupRestrict_thomPair M hW p m h hu))

/-- `Bundle.Trivialization.thomEquivOver` applies `TauCeti.thomMapOver`. -/
@[simp]
theorem thomEquivOver_apply [FiniteDimensional ℝ F] {W : Set B} (hW : W ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquivOver M hW p m h u hu a = thomMapOver F E M W (finrank ℝ F) p m h u a :=
  (rfl)

end Bundle.Trivialization

namespace TauCeti

section Isomorphism

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism over a trivializing set.** Let `E` be a real vector bundle of finite
rank `r = finrank ℝ F ≥ 0`, let `u ∈ Hʳ(E, E₀; K)` be a Thom class, and let `W` be contained
in the base set of a linear trivialization `e`. Then for every `K`-module `M` and every degree `p`,
the Thom map of the restriction of `u` to the Thom pair `(E|_W, E₀|_W)` of the restriction of the
bundle to `W`, `Hᵖ(W; M) ⟶ Hᵖ⁺ʳ(E|_W, E₀|_W; M)`, `a ↦ π^*a ⌣ u|`
(`TopCat.pullbackCupRestrict`), is bijective. These are the sets over which the Mayer–Vietoris
step `TopCat.bijective_pullbackCupRestrict_union` starts. -/
theorem IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M W
      _ p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  exact e.bijective_pullbackCupRestrict_thomPair M hW p m h fun b _ ↦ hu b

/-- **The Thom isomorphism for a trivializable bundle.** For a real vector bundle `E` with a linear
trivialization over its whole base, the Thom map `Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u`, of
every Thom class `u` is bijective, for every `K`-module `M` and every degree `p`. -/
theorem IsThomClass.bijective_thomMap_of_baseSet_eq_univ
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) (e : Trivialization F (π F E))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M _ p m h u) := by
  rw [thomMap_def]
  exact (TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h u).1
    (hu.bijective_pullbackCupRestrict_of_subset_baseSet M e he.ge h)

end Isomorphism

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism for a trivializable bundle** as `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquiv (he : e.baseSet = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (hu.bijective_thomMap_of_baseSet_eq_univ M e he h)

/-- `Bundle.Trivialization.thomEquiv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquiv_apply (he : e.baseSet = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquiv M he p m h u hu a = thomMap F E M (finrank ℝ F) p m h u a := (rfl)

end Bundle.Trivialization

namespace TauCeti

section TrivialBundle

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism for `Bundle.Trivial B F`**: for any Thom class `u` of the trivial
bundle, `thomMap` is bijective in every degree. -/
theorem IsThomClass.bijective_thomMap_trivial (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) :
    Function.Bijective (thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u) :=
  hu.bijective_thomMap_of_baseSet_eq_univ M (Bundle.Trivial.trivialization B F)
    (Bundle.Trivial.trivialization_baseSet B F) h

/-- **The Thom isomorphism for `Bundle.Trivial B F`**, bundled as
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def IsThomClass.trivialThomEquiv (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (hu.bijective_thomMap_trivial M p m h)

/-- `TauCeti.IsThomClass.trivialThomEquiv` applies `TauCeti.thomMap`. -/
@[simp]
theorem IsThomClass.trivialThomEquiv_apply (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.trivialThomEquiv M p m h a = thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u a :=
  (rfl)

end TrivialBundle

section Isomorphism

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- Helper transporting `TauCeti.isZero_singularCohomology_thomPairOver_biUnion` along
`TauCeti.thomPairProj_def`. -/
private theorem isZero_singularCohomology_thomPairProj_biUnion [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {j : ℕ} (hj : j < finrank ℝ F) :
    IsZero ((TopPair.ofInclusion (inter_subset_left :
      thomPairProj F E ⁻¹' (⋃ i ∈ s, W i) ∩ zeroSectionCompl F E ⊆
        thomPairProj F E ⁻¹' (⋃ i ∈ s, W i))).singularCohomology (ModuleCat.of K K) K M j) := by
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      IsZero ((TopPair.ofInclusion (inter_subset_left :
        π' ⁻¹' (⋃ i ∈ s, W i) ∩ zeroSectionCompl F E ⊆
          π' ⁻¹' (⋃ i ∈ s, W i))).singularCohomology (ModuleCat.of K K) K M j) from
    this _ rfl
  intro π' hπ'
  rw [thomPairProj_def] at hπ'
  subst hπ'
  exact isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s hWo hWe hj

/-- Open-set Mayer–Vietoris induction step for
`TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`. -/
private theorem bijective_pullbackCupRestrict_thomPair_biUnion_of_isOpen [FiniteDimensional ℝ F]
    {ι : Type*} (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E)
      (zeroSectionCompl F E) M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    rw [(by simp : (⋃ i ∈ (∅ : Finset ι), W i) = ∅)]
    exact TopCat.bijective_pullbackCupRestrict_empty _ _ M h u
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a ha
    have hWi (i : ι) (hi : i ∈ s) :
        ∃ (e' : Trivialization F (π F E)) (_ : e'.IsLinear ℝ), W a ∩ W i ⊆ e'.baseSet :=
      let ⟨e', he', hi'⟩ := hWe i (hs i hi); ⟨e', he', inter_subset_right.trans hi'⟩
    refine TopCat.bijective_pullbackCupRestrict_union (thomPairProj F E) (zeroSectionCompl F E) M
      (hWo a ha) (isOpen_biUnion fun i hi ↦ hWo i (hs i hi)) u
      (fun q _ ↦ e.bijective_pullbackCupRestrict_thomPair M he q _ rfl
        fun b hb ↦ hu b (mem_iUnion₂.2 ⟨a, ha, hb⟩))
      (fun q _ ↦ ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) q _ rfl
        fun b hb ↦ let ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hb; hu b (mem_iUnion₂.2 ⟨i, hs i hi, hbi⟩))
      (fun q _ ↦ ?_) (fun j hj ↦ ?_) h
    · rw [inter_iUnion₂]
      exact ih (W := fun i ↦ W a ∩ W i) (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi))) hWi q _ rfl
        fun b hb ↦ let ⟨_, _, hbi⟩ := mem_iUnion₂.1 hb; hu b (mem_iUnion₂.2 ⟨a, ha, hbi.1⟩)
    · rw [inter_iUnion₂]
      exact isZero_singularCohomology_thomPairProj_biUnion M s
        (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi))) hWi (by omega)

/-- **Thom isomorphism over a finite union of trivializing sets**: if each `W i` (`i ∈ s`) is
contained in an `ℝ`-linear trivialization's base set, and `u ∈ Hʳ(E, E₀; K)` restricts to a
generator on every fibre over `⋃ i ∈ s, W i`, then `TopCat.pullbackCupRestrict` is bijective in
every degree. Neither openness of `W i` nor generation outside `⋃ i ∈ s, W i` is required. -/
theorem bijective_pullbackCupRestrict_thomPair_biUnion [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E)
      (zeroSectionCompl F E) M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  let Y : Set B := ⋃ i ∈ s, W i
  let f : C(Y, B) := ContinuousMap.subtypeVal Y
  rw [bijective_pullbackCupRestrict_thomPairProj_iff, ← thomMapOver_apply]
  refine (bijective_thomMapOver_iff_pullback F E Y h u).2 ?_
  rw [thomMap_def]
  refine (TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h _).1 ?_
  let U (i : {i // i ∈ s}) : Set Y := ((hWe i.val i.property).choose.pullback f).baseSet
  have hU_univ : (⋃ i ∈ s.attach, U i) = univ := by
    refine eq_univ_of_forall fun ⟨b, hb⟩ ↦ ?_
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hb
    exact mem_iUnion₂.2 ⟨⟨i, hi⟩, Finset.mem_attach s ⟨i, hi⟩,
      (hWe i hi).choose_spec.choose_spec hbi⟩
  rw [← hU_univ]
  refine bijective_pullbackCupRestrict_thomPair_biUnion_of_isOpen (E := (⇑f) *ᵖ E) M s.attach
    (fun i _ ↦ ((hWe i.val i.property).choose.pullback f).open_baseSet)
    (fun i _ ↦ ?_) p m h fun y _ ↦ ?_
  · have : (hWe i.val i.property).choose.IsLinear ℝ := (hWe i.val i.property).choose_spec.choose
    exact ⟨(hWe i.val i.property).choose.pullback f, inferInstance, subset_rfl⟩
  · -- On `f *ᵖ E`, the `Zero` instance in `pullbackThomPairMap` and the one from `AddCommMonoid`
    -- agree up to unfolding `Pullback`, so `congrArg` identifies the composite fibre map.
    have hfib : TopPair.singularCohomologyMap (fiberThomPairMap F ((⇑f) *ᵖ E) y) (finrank ℝ F)
        (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) (finrank ℝ F) u) =
        TopPair.singularCohomologyMap (fiberThomPairMap F E y.val) (finrank ℝ F) u :=
      (TopPair.singularCohomologyMap_comp_apply _ _ _ _).symm.trans <|
        congrArg (fun φ ↦ TopPair.singularCohomologyMap φ (finrank ℝ F) u)
          (fiberThomPairMap_comp_pullbackThomPairMap F E f y)
    rw [hfib]
    exact hu y.val y.property

/-- **The Thom isomorphism over a finite union of trivializing sets**, bundled as
`Hᵖ(⋃ i ∈ s, W i; M) ≃ₗ[K] Hᵐ(E|_{⋃ i ∈ s, W i}, E₀|_{⋃ i ∈ s, W i}; M)`. -/
def thomEquivOverBiUnion [FiniteDimensional ℝ F] {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u)
    ((bijective_pullbackCupRestrict_thomPairProj_iff F E (⋃ i ∈ s, W i) h u).1
      (bijective_pullbackCupRestrict_thomPair_biUnion M s hWe p m h hu))

/-- `TauCeti.thomEquivOverBiUnion` applies `TauCeti.thomMapOver`. -/
@[simp]
theorem thomEquivOverBiUnion_apply [FiniteDimensional ℝ F] {ι : Type*} (s : Finset ι)
    {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOverBiUnion M s hWe p m h u hu a =
      thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The Thom isomorphism over a finite trivializing cover** (`Finset`-indexed). -/
theorem bijective_thomMap_of_biUnion_eq_univ {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  rw [thomMap_def]
  refine (TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h u).1 ?_
  rw [← hW]
  exact bijective_pullbackCupRestrict_thomPair_biUnion M s hWe p m h fun b _ ↦ hu b

/-- **The Thom isomorphism over a finite trivializing cover** (`Finset`-indexed), bundled as
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfBiUnionEqUniv {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_biUnion_eq_univ M s hWe hW p m h hu)

/-- `TauCeti.thomEquivOfBiUnionEqUniv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfBiUnionEqUniv_apply {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfBiUnionEqUniv M s hWe hW p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a := (rfl)

/-- **The Thom isomorphism over a finite trivializing cover** (`Finite`-indexed). -/
theorem bijective_thomMap_of_iUnion_eq_univ {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  cases nonempty_fintype ι
  exact bijective_thomMap_of_biUnion_eq_univ M Finset.univ (fun i _ ↦ hWe i)
    (by simpa using hW) p m h hu

/-- **The Thom isomorphism over a finite trivializing cover** (`Finite`-indexed), bundled as
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfIUnionEqUniv {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_iUnion_eq_univ M hWe hW p m h hu)

/-- `TauCeti.thomEquivOfIUnionEqUniv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfIUnionEqUniv_apply {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfIUnionEqUniv M hWe hW p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a := (rfl)

/-- **The Thom isomorphism over a compact base** (Milnor–Stasheff, Theorem 10.4; Hatcher, Theorem
4D.10): for `E → B` over compact `B` and a Thom class `u`, `thomMap` is bijective in all degrees. -/
theorem bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact bijective_thomMap_of_biUnion_eq_univ M s
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩)
    (eq_univ_of_univ_subset hs) p m h hu

variable (F E) in
/-- **The Thom isomorphism over a compact base**, bundled as `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_compactSpace M p m h hu)

/-- `TauCeti.thomEquivOfCompactSpace` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfCompactSpace_apply [CompactSpace B] [VectorBundle ℝ F E]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfCompactSpace F E M p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a := (rfl)

end Isomorphism

end TauCeti
