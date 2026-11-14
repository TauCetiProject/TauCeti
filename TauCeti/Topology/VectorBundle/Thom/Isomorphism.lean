/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.Topology.VectorBundle.EulerClass
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup
import TauCeti.Topology.VectorBundle.MayerVietoris.Basic

/-!
# The Thom isomorphism in cohomology

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**Thom map** of `u` is

`Φ_u : Hᵖ(B; M) ⟶ Hᵖ⁺ⁿ(E, E₀; M)`,  `a ↦ π^*a ⌣ u`,

the pull-back along the projection `π : E ⟶ B` followed by the cup product of absolute and
relative cohomology (`TopPair.singularCup`), for any `K`-module of coefficients `M`: the map
`TopPair.pullbackCup` of the Thom pair and its projection.

This file sets up the Thom map and proves the **Thom isomorphism** (Milnor–Stasheff, Theorem 10.4;
Hatcher, Theorem 4D.10) over any commutative ring `K` and with arbitrary `K`-module coefficients
`M` whenever `B` admits a finite trivializing open cover (in particular for trivializable bundles
and over any compact base; the extension to arbitrary bases over a field is in
`TauCeti.Topology.VectorBundle.Thom.Homology`):

1. **Basic properties of `TauCeti.thomMap`**: it is `K`-bilinear in `u` and `a`, sends the unit
   `1 ∈ H⁰(B; K)` to `u` (`TauCeti.thomMap_one`), is natural in maps of Thom pairs covering maps of
   bases (`TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`), is linear over `H^*(B; K)`
   (`TauCeti.thomMap_singularCup`), and restricts on each fibre `(E_b, E_b ∖ {0})` to cup product
   with the fibre restriction of `u` (`TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`).
2. **Local Thom isomorphism** (`Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair`):
   over any subset `W` contained in the base set of an `ℝ`-linear trivialization `e`, the
   trivialization identifies `(E|_W, E₀|_W)` with `(W × F, W × (F ∖ {0}))`
   (`Bundle.Trivialization.thomPairOverIso`), reducing bijectivity of `TopCat.pullbackCupRestrict`
   to the product-bundle Thom isomorphism (`TauCeti.bijective_pullbackCup_prodThomPair`).
3. **Finite-union Mayer–Vietoris induction**
   (`TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`): inducting on a finite family of open
   trivializing subsets via `TopCat.bijective_pullbackCupRestrict_union`, with below-rank vanishing
   on intersections supplied by `TauCeti.isZero_singularCohomology_thomPairOver_biUnion`, proves
   bijectivity over any finite union of trivializing open sets.
4. **Global Thom isomorphisms**: for any Thom class `u` (`TauCeti.IsThomClass`), `Φ_u` is a
   `K`-linear equivalence `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` (`p + finrank ℝ F = m`) when `E` has a
   global linear trivialization (`Bundle.Trivialization.thomEquiv`), when `B` is covered by
   finitely many open trivializing sets (`TauCeti.thomEquivOfBiUnionEqUniv`,
   `TauCeti.thomEquivOfIUnionEqUniv`), and when `B` is compact (`TauCeti.thomEquivOfCompactSpace`).

## Main definitions and results

* `TauCeti.thomMap`: the Thom map `a ↦ π^*a ⌣ u`, bilinear in `u` and `a`.
* `TauCeti.thomMap_one`: `Φ_u(1) = u`.
* `TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`: naturality.
* `TauCeti.thomMap_singularCup`: linearity over the cohomology of the base.
* `TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`: the restriction to a fibre.
* `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair`: bijectivity over a subset of a
  linear trivialization's base set.
* `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`: bijectivity over a finite union of open
  trivializing subsets.
* `Bundle.Trivialization.bijective_thomMap`, `Bundle.Trivialization.thomEquiv`: the Thom
  isomorphism for a globally trivializable bundle.
* `TauCeti.bijective_thomMap_of_biUnion_eq_univ`, `TauCeti.thomEquivOfBiUnionEqUniv`,
  `TauCeti.bijective_thomMap_of_iUnion_eq_univ`, `TauCeti.thomEquivOfIUnionEqUniv`: the Thom
  isomorphism over a finite open trivializing cover.
* `TauCeti.bijective_thomMap_of_compactSpace`, `TauCeti.thomEquivOfCompactSpace`: the Thom
  isomorphism over a compact base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
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

/-- Rewriting `thomMap` in terms of `TopCat.ofHom ⟨π F E, _⟩` aligns its ambient space
syntactically with `TopCat.of (TotalSpace F E)` for `TopCat.pullbackCupRestrict`. -/
theorem thomMap_eq_pullbackCup_proj {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMap F E M n p m h u =
      (TopPair.ofSubset (X := TopCat.of (TotalSpace F E)) (zeroSectionCompl F E)).pullbackCup M
        (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) n p m h u :=
  congrArg (fun g ↦ (thomPair F E).pullbackCup M g n p m h u) (thomPairProj_def F E)

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

include e in
/-- **Local Thom isomorphism over a trivializing set.** For `W` contained in the base set of an
`ℝ`-linear trivialization `e`, and any class `u ∈ Hʳ(E, E₀; K)` (`r = finrank ℝ F`) whose
restriction to the fibre pair `(E_b, E_b ∖ {0})` over every `b ∈ W` spans `Hʳ(E_b, E_b ∖ {0}; K)`,
the map `TopCat.pullbackCupRestrict` of `u` over `W` is bijective in every degree. -/
theorem bijective_pullbackCupRestrict_thomPair [FiniteDimensional ℝ F] {W : Set B}
    (hW : W ⊆ e.baseSet) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K {(TopPair.singularCohomologyMap
      (fiberThomPairMap F E b) (finrank ℝ F) u)} = ⊤) :
    Function.Bijective
      (TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
        (zeroSectionCompl F E) M W (finrank ℝ F) p m h u) := by
  rw [TopCat.pullbackCupRestrict_apply]
  let π₀ : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩
  let φ := e.thomPairOverIso ℝ hW
  let u_W : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F) :=
    TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap π₀ (zeroSectionCompl F E) W)
      (finrank ℝ F) u
  let u_prod := TopPair.singularCohomologyMap φ.inv (finrank ℝ F) u_W
  have hu_W : TopPair.singularCohomologyMap φ.hom (finrank ℝ F) u_prod = u_W := by
    simp [u_prod, ← TopPair.singularCohomologyMap_comp_apply]
  have hproj : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F =
      TopCat.ofHom (π₀.hom.restrictPreimage W) ≫ 𝟙 (TopCat.of W) := by
    rw [Category.comp_id]
    refine TopCat.ext fun v ↦ Subtype.ext ?_
    exact congrArg Subtype.val
      ((congrArg (prodThomPairProj W F) (e.thomPairOverIso_hom_fst_apply ℝ hW v)).trans
        (prodThomPairProj_apply F _))
  change Function.Bijective ((thomPairOver F E W).pullbackCup M
    (TopCat.ofHom (π₀.hom.restrictPreimage W)) (finrank ℝ F) p m h u_W)
  rw [← hu_W, TopPair.bijective_pullbackCup_iff_of_isIso φ.hom (𝟙 (TopCat.of W)) hproj h u_prod]
  -- Transport the fibrewise generator condition to the product bundle `W × F`.
  refine bijective_pullbackCup_prodThomPair M p m h fun b ↦ ?_
  have hfib : prodThomPairFiberMap F b ≫ φ.inv ≫
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W =
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairMap F E b.1 := by
    have h₁ : prodThomPairFiberMap F b ≫ φ.inv =
        (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv ≫
          fiberThomPairOverMap F E b.2 := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2).symm
    rw [← Category.assoc, h₁, Category.assoc, fiberThomPairOverMap_comp_restrictPreimagePairMap]
  have hu_prod : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u_prod =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv (finrank ℝ F)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b.1) (finrank ℝ F) u) := by
    change TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F)
        (TopPair.singularCohomologyMap φ.inv (finrank ℝ F)
          (TopPair.singularCohomologyMap
            (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
              (zeroSectionCompl F E) W) (finrank ℝ F) u)) = _
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      Category.assoc, hfib, TopPair.singularCohomologyMap_comp_apply]
  let ψ := (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.symm
  let e_b : (TopPair.ofSubset (X := TopCat.of (E b.1)) ({0}ᶜ : Set (E b.1))).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) ≃ₗ[K]
      (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) :=
    ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)).mapIso ψ.op).toLinearEquiv
  have hspan := (Submodule.map_eq_top_iff (e := e_b)).2 (hu b.1 b.2)
  rw [← Submodule.span_image_linearEquiv e_b, Set.image_singleton] at hspan
  rw [hu_prod]
  exact hspan

/-- **The Thom isomorphism for a globally trivializable bundle.** If `e` is an `ℝ`-linear
trivialization of `E` over the whole base and `u` is a Thom class of `E`, then the Thom map
`a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; M)` to `Hᵐ(E, E₀; M)` (`p + finrank ℝ F = m`). -/
theorem bijective_thomMap (he : e.baseSet = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  rw [thomMap_eq_pullbackCup_proj, ← TopCat.bijective_pullbackCupRestrict_univ_iff]
  exact e.bijective_pullbackCupRestrict_thomPair M he.symm.subset p m h fun b _ ↦ hu b

/-- **The Thom isomorphism for a globally trivializable bundle**, bundled as a `K`-linear
equivalence `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquiv (he : e.baseSet = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (e.bijective_thomMap M he p m h hu)

/-- `Bundle.Trivialization.thomEquiv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquiv_apply (he : e.baseSet = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquiv M he p m h u hu a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end Bundle.Trivialization

namespace TauCeti

section Isomorphism

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
private theorem bijective_pullbackCupRestrict_thomPair_empty {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective
      (TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
        (zeroSectionCompl F E) M (∅ : Set B) n p m h u) := by
  have : Subsingleton ((TopCat.of (∅ : Set B)).singularCohomology (ModuleCat.of K K) K M p) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M (TopCat.of (∅ : Set B)) p)
  have hzero : IsZero ((thomPairOver F E ∅).singularCohomology (ModuleCat.of K K) K M m) :=
    TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
      fun j _ ↦ isZero_singularHomology_thomPairOver_empty (ModuleCat.of K K) j
  have : Subsingleton ((thomPairOver F E ∅).singularCohomology (ModuleCat.of K K) K M m) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact ⟨fun x y _ ↦ Subsingleton.elim x y, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

/-- **Thom isomorphism over a finite union of trivializing open sets.** Let `W i`, `i ∈ s`, be
finitely many open subsets of `B`, each contained in the base set of an `ℝ`-linear trivialization of
`E`. If `u ∈ Hʳ(E, E₀; K)` (`r = finrank ℝ F`) restricts to a generator on every fibre over the
union `⋃ i ∈ s, W i`, then `TopCat.pullbackCupRestrict` of `u` over `⋃ i ∈ s, W i` is bijective in
every degree. -/
theorem bijective_pullbackCupRestrict_thomPair_biUnion [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K {(TopPair.singularCohomologyMap
      (fiberThomPairMap F E b) (finrank ℝ F) u)} = ⊤) :
    Function.Bijective
      (TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
        (zeroSectionCompl F E) M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have h_empty : (⋃ i ∈ (∅ : Finset ι), W i) = ∅ := by simp
    rw [h_empty]
    exact bijective_pullbackCupRestrict_thomPair_empty M h u
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a ha
    refine TopCat.bijective_pullbackCupRestrict_union
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
      (hWo a ha) (isOpen_biUnion fun i hi ↦ hWo i (hs i hi)) u
      (fun q _ ↦ ?_) (fun q _ ↦ ?_) (fun q _ ↦ ?_) (fun j hj ↦ ?_) h
    · exact e.bijective_pullbackCupRestrict_thomPair M he q (q + finrank ℝ F) rfl
        fun b hb ↦ hu b (by
          rw [Finset.set_biUnion_insert]
          exact Or.inl hb)
    · exact ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) q (q + finrank ℝ F) rfl
        fun b hb ↦ hu b (by
          rw [Finset.set_biUnion_insert]
          exact Or.inr hb)
    · -- `W a ∩ ⋃ i ∈ s, W i` is the finite union of the trivializing open sets `W a ∩ W i`.
      rw [inter_iUnion₂]
      refine ih (W := fun i ↦ W a ∩ W i) (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi)))
        (fun i hi ↦ ?_) q (q + finrank ℝ F) rfl fun b hb ↦ ?_
      · obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩
      · obtain ⟨i, _, hbi⟩ := mem_iUnion₂.1 hb
        exact hu b (by
          rw [Finset.set_biUnion_insert]
          exact Or.inl hbi.1)
    · have hzero : IsZero ((thomPairOver F E (W a ∩ ⋃ i ∈ s, W i)).singularCohomology
          (ModuleCat.of K K) K M j) := by
        rw [inter_iUnion₂]
        refine isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
          (fun i hi ↦ (hWo a ha).inter (hWo i (hs i hi))) (fun i hi ↦ ?_) (by omega)
        obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩
      exact hzero

/-- **The Thom isomorphism over a finite open trivializing cover** (`Finset`-indexed). If `B` is
covered by finitely many open subsets `W i` (`i ∈ s`), each contained in the base set of an
`ℝ`-linear trivialization of `E`, and `u` is a Thom class of `E`, then the Thom map `a ↦ π^*a ⌣ u`
is bijective from `Hᵖ(B; M)` to `Hᵐ(E, E₀; M)` (`p + finrank ℝ F = m`). -/
theorem bijective_thomMap_of_biUnion_eq_univ {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  rw [thomMap_eq_pullbackCup_proj, ← TopCat.bijective_pullbackCupRestrict_univ_iff, ← hW]
  exact bijective_pullbackCupRestrict_thomPair_biUnion M s hWo hWe p m h fun b _ ↦ hu b

/-- **The Thom isomorphism over a finite open trivializing cover** (`Finset`-indexed), bundled as a
`K`-linear equivalence `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfBiUnionEqUniv {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (bijective_thomMap_of_biUnion_eq_univ M s hWo hWe hW p m h hu)

/-- `TauCeti.thomEquivOfBiUnionEqUniv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfBiUnionEqUniv_apply {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfBiUnionEqUniv M s hWo hWe hW p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The Thom isomorphism over a finite open trivializing cover** (`Finite`-indexed). -/
theorem bijective_thomMap_of_iUnion_eq_univ {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  cases nonempty_fintype ι
  exact bijective_thomMap_of_biUnion_eq_univ M Finset.univ (fun i _ ↦ hWo i) (fun i _ ↦ hWe i)
    (by simpa using hW) p m h hu

/-- **The Thom isomorphism over a finite open trivializing cover** (`Finite`-indexed), bundled as
a `K`-linear equivalence `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfIUnionEqUniv {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (bijective_thomMap_of_iUnion_eq_univ M hWo hWe hW p m h hu)

/-- `TauCeti.thomEquivOfIUnionEqUniv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfIUnionEqUniv_apply {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfIUnionEqUniv M hWo hWe hW p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The Thom isomorphism over a compact base** (Milnor–Stasheff, Theorem 10.4; Hatcher, Theorem
4D.10). For a real vector bundle `E → B` over a compact base `B`, any commutative ring `K`, any
`K`-module `M`, and any Thom class `u ∈ Hʳ(E, E₀; K)` (`r = finrank ℝ F`), the Thom map
`a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; M)` to `Hᵐ(E, E₀; M)` (`p + r = m`). -/
theorem bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact bijective_thomMap_of_biUnion_eq_univ M s
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩)
    (eq_univ_of_univ_subset hs) p m h hu

variable (F E) in
/-- **The Thom isomorphism over a compact base**, bundled as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` (`p + finrank ℝ F = m`). -/
def thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (bijective_thomMap_of_compactSpace M p m h hu)

/-- `TauCeti.thomEquivOfCompactSpace` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfCompactSpace_apply [CompactSpace B] [VectorBundle ℝ F E]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfCompactSpace F E M p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end Isomorphism

end TauCeti
