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
import TauCeti.Topology.VectorBundle.ModelFiber
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

This file sets up `TauCeti.thomMap` and proves the **Thom isomorphism** (Milnor–Stasheff, Theorem
10.4; Hatcher, Theorem 4D.10) over any commutative ring `K` with `K`-module coefficients `M`
for every finite rank `r = finrank ℝ F ≥ 0` whenever `B` admits a finite trivializing open cover
(extended to arbitrary bases over a field in `TauCeti.Topology.VectorBundle.Thom.Homology`):

1. **Basic properties**: `TauCeti.thomMap` is `K`-bilinear, sends `1 ∈ H⁰(B; K)` to `u`
   (`TauCeti.thomMap_one`), is natural (`TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`),
   is `H^*(B; K)`-linear (`TauCeti.thomMap_singularCup`), and restricts on fibres to cupping with
   the fibre restriction of `u` (`TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`). For a
   real vector bundle, the Euler class map `TauCeti.eulerClass` sends `Φ_u(a)` to the cup product
   `a ⌣ e(u)` of `a` with the Euler class of `u` (`TauCeti.eulerClass_thomMap`).
2. **Local and finite-union isomorphisms**: an `ℝ`-linear trivialization identifies `(E|_W, E₀|_W)`
   with `(W × F, W × (F ∖ {0}))` (`Bundle.Trivialization.thomPairOverIso`), reducing
   `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair` (and its global-Thom-class
   specialization `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`) to
   `TauCeti.bijective_pullbackCup_prodThomPair`; Mayer–Vietoris induction
   (`TopCat.bijective_pullbackCupRestrict_union`) with below-rank vanishing
   (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`) gives
   `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion` over finite open trivializing unions.
3. **Global Thom isomorphisms and equivalences** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`
   (`p + finrank ℝ F = m`) for any `TauCeti.IsThomClass`:
   `TauCeti.IsThomClass.bijective_thomMap_of_baseSet_eq_univ`, `Bundle.Trivialization.thomEquiv`,
   `TauCeti.thomEquivOfBiUnionEqUniv`, `TauCeti.thomEquivOfIUnionEqUniv`, and
   `TauCeti.thomEquivOfCompactSpace`. The model fibre `F` may lie in any universe, for instance
   `Fin r → ℝ : Type` over a base in a higher universe. The local and finite-union steps of item 2
   take `F` in the universe of the base, since they compare `(E|_W, E₀|_W)` with
   `(W × F, W × (F ∖ {0}))`. The global statements read the bundle with the model fibre
   `ULift (Fin r → ℝ)` in that universe, along the isomorphism of Thom pairs
   `TauCeti.thomPairModelFiberIso`, which lies over the identity of the base and is the identity on
   every fibre.

## Main definitions and results

* `TauCeti.thomMap`: the Thom map `a ↦ π^*a ⌣ u`, bilinear in `u` and `a`.
* `TauCeti.thomMap_one`: `Φ_u(1) = u`.
* `TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`: naturality.
* `TauCeti.thomMap_singularCup`: linearity over the cohomology of the base.
* `TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`: the restriction to a fibre.
* `TauCeti.eulerClass_thomMap`: the Euler class map sends `Φ_u(a)` to `a ⌣ e(u)`.
* `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPair`,
  `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`,
  `TauCeti.bijective_pullbackCupRestrict_thomPair_biUnion`: local and finite-union bijectivity.
* `TauCeti.IsThomClass.bijective_thomMap_of_baseSet_eq_univ`, `Bundle.Trivialization.thomEquiv`,
  `TauCeti.bijective_thomMap_of_biUnion_eq_univ`, `TauCeti.thomEquivOfBiUnionEqUniv`,
  `TauCeti.bijective_thomMap_of_iUnion_eq_univ`, `TauCeti.thomEquivOfIUnionEqUniv`,
  `TauCeti.bijective_thomMap_of_compactSpace`, `TauCeti.thomEquivOfCompactSpace`: global Thom
  isomorphisms over trivializable bundles, finite open trivializing covers, and compact bases.

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

variable {F E}

/-- A change of model fibre does not change bijectivity of the Thom map: the Thom map of `u` is
bijective exactly when that of its pull-back along `TauCeti.thomPairModelFiberIso` is, since the
isomorphism of Thom pairs lies over the identity of the base. -/
private theorem bijective_thomMap_iff_of_isInducing {F' : Type*} [TopologicalSpace F']
    [TopologicalSpace (TotalSpace F' E)] [FiberBundle F' E]
    (h_ind : Topology.IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd)
    {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMap F E M n p m h u) ↔
      Function.Bijective (thomMap F' E M n p m h
        (TopPair.singularCohomologyMap (thomPairModelFiberIso h_ind).hom n u)) := by
  have hφ : TopPair.Hom.fst (thomPairModelFiberIso h_ind).hom ≫ thomPairProj F E =
      thomPairProj F' E ≫ 𝟙 (TopCat.of B) := by
    rw [Category.comp_id]
    exact TopCat.ext fun v ↦ (thomPairProj_apply F E _).trans <|
      (congrArg TotalSpace.proj (thomPairModelFiberIso_hom_fst_apply h_ind v)).trans
        (thomPairProj_apply F' E v).symm
  let e := (TopPair.singularCohomologyMapIso (ModuleCat.of K K) K M
    (thomPairModelFiberIso h_ind) m).toLinearEquiv
  have key : ⇑(thomMap F' E M n p m h
      (TopPair.singularCohomologyMap (thomPairModelFiberIso h_ind).hom n u)) =
      e ∘ thomMap F E M n p m h u := funext fun a ↦ by
    simpa [e, TopCat.singularCohomologyMap_id] using
      thomMap_naturality F E (thomPairModelFiberIso h_ind).hom (𝟙 _) hφ h u a
  rw [key, EquivLike.comp_bijective]

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

/-- **Thom isomorphism over a finite union of trivializing open sets**: if each `W i` (`i ∈ s`) is
open and contained in an `ℝ`-linear trivialization's base set, and `u ∈ Hʳ(E, E₀; K)` restricts to
a generator on every fibre over `⋃ i ∈ s, W i`, then `TopCat.pullbackCupRestrict` is bijective. -/
theorem bijective_pullbackCupRestrict_thomPair_biUnion [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
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

/-- The Thom isomorphism over a finite open trivializing cover for a model fibre in the universe of
the base, with the degree `n = finrank ℝ F` of the class as a separate argument:
`TauCeti.bijective_thomMap_of_biUnion_eq_univ` for such model fibres. -/
private theorem bijective_thomMap_of_biUnion_eq_univ_sameUniverse [FiniteDimensional ℝ F]
    {ι : Type*} (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) {n : ℕ} (hn : finrank ℝ F = n) (p m : ℕ) (h : p + n = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : ∀ b, Submodule.span K {TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u} = ⊤) :
    Function.Bijective (thomMap F E M n p m h u) := by
  subst hn
  rw [thomMap_def]
  refine (TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h u).1 ?_
  rw [← hW]
  exact bijective_pullbackCupRestrict_thomPair_biUnion M s hWo hWe p m h fun b _ ↦ hu b

end Isomorphism

section ModelFiber

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism over a finite open trivializing cover** (`Finset`-indexed). The model
fibre may lie in any universe. -/
theorem bijective_thomMap_of_biUnion_eq_univ {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu⟩ := isThomClass_iff.1 hu
  -- Read `E` with the model fibre `F' = ULift (Fin r → ℝ)`, which lies in the universe of `B` and
  -- of the fibres, with the topology on its total space induced along the identity of points. The
  -- trivializations of `E` read through `F ≃L[ℝ] F'` are linear and keep their base sets.
  let L : F ≃L[ℝ] ULift.{w} (Fin (finrank ℝ F) → ℝ) :=
    (ContinuousLinearEquiv.ofFinrankEq (by simp)).trans ContinuousLinearEquiv.ulift.symm
  let := totalSpaceModelFiberInduced F (ULift.{w} (Fin (finrank ℝ F) → ℝ)) E
  have h_ind := isInducing_totalSpaceModelFiberInduced F (ULift.{w} (Fin (finrank ℝ F) → ℝ)) E
  let := FiberBundle.ofModelFiberHomeomorph F L.toHomeomorph h_ind
  -- The isomorphism of Thom pairs is the identity of points, so it is the identity on the fibres.
  have hfib (b : B) :
      fiberThomPairMap _ E b ≫ (thomPairModelFiberIso h_ind).hom = fiberThomPairMap F E b :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
      (congrArg (TopPair.Hom.fst (thomPairModelFiberIso h_ind).hom)
        (fiberThomPairMap_fst_apply _ E b x)).trans
        ((thomPairModelFiberIso_hom_fst_apply h_ind _).trans
          (fiberThomPairMap_fst_apply F E b x).symm))
  rw [bijective_thomMap_iff_of_isInducing h_ind]
  refine bijective_thomMap_of_biUnion_eq_univ_sameUniverse M s hWo (fun i hi ↦ ?_) hW
    L.toLinearEquiv.finrank_eq.symm p m h fun b ↦ ?_
  · obtain ⟨e, _, he⟩ := hWe i hi
    exact ⟨e.transModelFiber L.toHomeomorph h_ind, inferInstance, by simpa using he⟩
  · rw [← TopPair.singularCohomologyMap_comp_apply, hfib]
    exact hu b

/-- **The Thom isomorphism over a finite open trivializing cover** (`Finset`-indexed), bundled as
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfBiUnionEqUniv {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_biUnion_eq_univ M s hWo hWe hW p m h hu)

/-- `TauCeti.thomEquivOfBiUnionEqUniv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfBiUnionEqUniv_apply {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i ∈ s, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfBiUnionEqUniv M s hWo hWe hW p m h u hu a =
      thomMap F E M (finrank ℝ F) p m h u a := (rfl)

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
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`. -/
def thomEquivOfIUnionEqUniv {ι : Type*} [Finite ι] {W : ι → Set B} (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective _ (bijective_thomMap_of_iUnion_eq_univ M hWo hWe hW p m h hu)

/-- `TauCeti.thomEquivOfIUnionEqUniv` applies `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfIUnionEqUniv_apply {ι : Type*} [Finite ι] {W : ι → Set B}
    (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : (⋃ i, W i) = univ) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfIUnionEqUniv M hWo hWe hW p m h u hu a =
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
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
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

/-- **The Thom isomorphism for a trivializable bundle.** For a real vector bundle `E` with a linear
trivialization over its whole base, the Thom map `Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u`, of
every Thom class `u` is bijective, for every `K`-module `M` and every degree `p`. The model fibre
may lie in any universe. -/
theorem IsThomClass.bijective_thomMap_of_baseSet_eq_univ
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) (e : Trivialization F (π F E))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M _ p m h u) :=
  bijective_thomMap_of_biUnion_eq_univ M {()} (fun _ _ ↦ isOpen_univ)
    (fun _ _ ↦ ⟨e, inferInstance, he.ge⟩) (Finset.set_biUnion_singleton _ _) p m h hu

end ModelFiber

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
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
