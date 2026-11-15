/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.Topology.VectorBundle.Smul

/-!
# The Gysin sequence of a real vector bundle

Let `E → B` be a real vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero
section, and let `π₀ : E₀ → B` be the restriction of the projection
(`TauCeti.zeroSectionComplProj`). The projection `π : E → B` is a homotopy equivalence with
homotopy inverse the zero section `s : B → E`, through the fibrewise scaling `(t, v) ↦ t • v`
(`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`), so `s^* : Hⁿ(E) ⟶ Hⁿ(B)` is an isomorphism
with inverse `π^*`
(`TauCeti.singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj`), and
replacing `Hⁿ(E)` by `Hⁿ(B)` in the long exact sequence of the pair `(E, E₀)` gives the exact
sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

whose maps out of relative cohomology are the Euler class maps `TauCeti.eulerClass`, followed by
pullback along `π₀` and the connecting morphisms of the pair
(`TauCeti.exact_eulerClass_singularCohomologyMap_zeroSectionComplProj`,
`TauCeti.exact_singularCohomologyMap_zeroSectionComplProj_singularCohomologyδ`,
`TauCeti.exact_singularCohomologyδ_eulerClass`). These hold for arbitrary coefficients and need no
orientation and no condition on the base.

For a relative class `u ∈ Hⁿ(E, E₀; K)` the Euler class map sends the image `π^*a ⌣ u` of
`a ∈ Hᵖ(B; M)` under the Thom map `TauCeti.thomMap` to `a ⌣ e(u)`, the cup product of `a` with the
Euler class of `u` (`TauCeti.eulerClass_thomMap`). When the Thom map of `u` is bijective (this is
the Thom isomorphism, which holds for a Thom class by Milnor and Stasheff, Theorem 10.4, and is not
proved in this file), it identifies `Hᵖ⁺ⁿ(E, E₀; M)` with `Hᵖ(B; M)`, and the sequence above
becomes the **Gysin sequence**

`⋯ ⟶ Hᵖ(B) ⟶ Hᵖ⁺ⁿ(B) ⟶ Hᵖ⁺ⁿ(E₀) ⟶ Hᵖ⁺¹(B) ⟶ Hᵖ⁺ⁿ⁺¹(B) ⟶ ⋯`,

whose maps are the cup product `a ↦ a ⌣ e(u)` with the Euler class, the pullback along `π₀`, and
the Gysin connecting map `TauCeti.gysinδ`, the connecting morphism of the pair followed by the
inverse of the Thom map (`TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`,
`TauCeti.exact_singularCohomologyMap_gysinδ`, `TauCeti.exact_gysinδ_singularCup_eulerClass`). Each
statement asks for the bijectivity, or only the surjectivity, of the Thom map in the single degree
that it uses.

When the fibre norm is continuous on the total space, for instance for a continuous Riemannian
bundle, the inclusion `S(E) → E₀` of the sphere bundle (`TauCeti.sphereBundleInclusion`) is a
homotopy equivalence (`TauCeti.sphereBundleHomotopyEquiv`), and the sequence is the Gysin sequence
of the sphere bundle `S(E) → B`, with the pullback along `S(E) → B` and the connecting map
`TauCeti.sphereGysinδ`
(`TauCeti.exact_singularCup_eulerClass_singularCohomologyMap_sphereBundleProj`,
`TauCeti.exact_singularCohomologyMap_sphereBundleProj_sphereGysinδ`,
`TauCeti.exact_sphereGysinδ_singularCup_eulerClass`).

## Main definitions

* `TauCeti.zeroSectionComplProj`: the projection `E₀ → B`.
* `TauCeti.sphereBundleInclusion`: the inclusion `S(E) → E₀`.
* `TauCeti.gysinδ`: the Gysin connecting map `Hˡ(E₀; M) ⟶ H^q(B; M)`, `l + 1 = q + n`.
* `TauCeti.sphereGysinδ`: the Gysin connecting map `Hˡ(S(E); M) ⟶ H^q(B; M)`.

## Main results

* `TauCeti.exact_eulerClass_singularCohomologyMap_zeroSectionComplProj`,
  `TauCeti.exact_singularCohomologyMap_zeroSectionComplProj_singularCohomologyδ`,
  `TauCeti.exact_singularCohomologyδ_eulerClass`: the long exact sequence of the Thom pair, with
  the cohomology of the total space replaced by that of the base.
* `TauCeti.eulerClass_thomMap`: the Euler class map sends `π^*a ⌣ u` to `a ⌣ e(u)`.
* `TauCeti.exact_singularCup_eulerClass_singularCohomologyMap`,
  `TauCeti.exact_singularCohomologyMap_gysinδ`, `TauCeti.exact_gysinδ_singularCup_eulerClass`:
  the Gysin sequence of a class whose Thom map is bijective.
* `TauCeti.exact_singularCup_eulerClass_singularCohomologyMap_sphereBundleProj`,
  `TauCeti.exact_singularCohomologyMap_sphereBundleProj_sphereGysinδ`,
  `TauCeti.exact_sphereGysinδ_singularCup_eulerClass`: the Gysin sequence of the sphere bundle.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12, Theorem 12.2 (the Gysin sequence) and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, the Gysin sequence following Corollary 4D.11.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory
universe w v u

namespace TauCeti

section ZeroSection

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The zero section followed by the projection is the identity of the base. -/
@[reassoc (attr := simp)]
theorem zeroSectionHom_comp_thomPairProj : zeroSectionHom F E ≫ thomPairProj F E = 𝟙 _ :=
  TopCat.ext fun b ↦ by
    rw [ConcreteCategory.comp_apply, zeroSectionHom_apply, thomPairProj_apply]
    rfl

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*)
  [Ring k] [Linear k C] (M : C)

/-- Pulling a class of the base back to the total space and then along the zero section gives the
class back. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (thomPairProj F E) n ≫
      TopCat.singularCohomologyMap (zeroSectionHom F E) n = 𝟙 _ := by
  rw [← TopCat.singularCohomologyMap_comp, zeroSectionHom_comp_thomPairProj,
    TopCat.singularCohomologyMap_id]

/-- **The zero section induces an isomorphism on cohomology**, with inverse the pullback along the
projection (`TauCeti.VectorBundle.totalSpaceHomotopyEquiv`): pulling a class of the total space
back along the zero section and then to the total space gives the class back. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (zeroSectionHom F E) n ≫
      TopCat.singularCohomologyMap (thomPairProj F E) n = 𝟙 _ := by
  let e := VectorBundle.totalSpaceHomotopyEquiv F E
  have hπ : TopCat.ofHom e.toFun = thomPairProj F E :=
    TopCat.ext fun v ↦ (congrFun (VectorBundle.coe_totalSpaceHomotopyEquiv F E) v).trans
      (thomPairProj_apply F E v).symm
  have hs : TopCat.ofHom e.invFun = zeroSectionHom F E :=
    TopCat.ext fun b ↦ (congrFun (VectorBundle.coe_totalSpaceHomotopyEquiv_symm F E) b).trans
      (zeroSectionHom_apply F E b).symm
  have h := (e.singularCohomologyIso R k M n).inv_hom_id
  rwa [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv, hπ, hs] at h

variable {F E} in
@[simp]
theorem singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply {n : ℕ}
    (x : (TopCat.of B).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (zeroSectionHom F E) n
      (TopCat.singularCohomologyMap (thomPairProj F E) n x) = x := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_comp_singularCohomologyMap_zeroSectionHom,
    ConcreteCategory.id_apply]

variable {F E} in
@[simp]
theorem singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply {n : ℕ}
    (x : (thomPair F E).fst.singularCohomology R k M n) :
    TopCat.singularCohomologyMap (thomPairProj F E) n
      (TopCat.singularCohomologyMap (zeroSectionHom F E) n x) = x := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyMap_zeroSectionHom_comp_singularCohomologyMap_thomPairProj,
    ConcreteCategory.id_apply]

/-- The projection `π₀ : E₀ → B` of the complement of the zero section to the base, the
restriction of the bundle projection. -/
def zeroSectionComplProj : (thomPair F E).snd ⟶ TopCat.of B :=
  (thomPair F E).map ≫ thomPairProj F E

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
theorem zeroSectionComplProj_def :
    zeroSectionComplProj F E = (thomPair F E).map ≫ thomPairProj F E :=
  (rfl)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
@[simp]
theorem zeroSectionComplProj_apply (v : zeroSectionCompl F E) :
    zeroSectionComplProj F E v = (v : TotalSpace F E).proj :=
  thomPairProj_apply F E (v : TotalSpace F E)

/-- **Exactness at the cohomology of the base**: `Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(E₀)`, the Euler class map
followed by the pullback along `π₀ : E₀ → B`, is exact. -/
theorem exact_eulerClass_singularCohomologyMap_zeroSectionComplProj (m : ℕ) :
    Function.Exact (eulerClass R k M F E m)
      (TopCat.singularCohomologyMap (zeroSectionComplProj F E) m) := by
  have hex : Function.Exact ((thomPair F E).singularCohomologyπ R k M m)
      (TopCat.singularCohomologyMap (thomPair F E).map m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_space R k M m)
  -- Transport exactness of `Hᵐ(E, E₀) ⟶ Hᵐ(E) ⟶ Hᵐ(E₀)` along `π^* : Hᵐ(B) ≅ Hᵐ(E)`.
  intro y
  rw [zeroSectionComplProj_def, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    hex]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
  · rw [eulerClass_def, ConcreteCategory.comp_apply, hx,
      singularCohomologyMap_zeroSectionHom_singularCohomologyMap_thomPairProj_apply]
  · rw [← hx, eulerClass_def, ConcreteCategory.comp_apply,
      singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

/-- **Exactness at the cohomology of `E₀`**: `Hᵐ(B) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀)`, the pullback along
`π₀ : E₀ → B` followed by the connecting morphism of the pair `(E, E₀)`, is exact. -/
theorem exact_singularCohomologyMap_zeroSectionComplProj_singularCohomologyδ (l m : ℕ)
    (hl : l + 1 = m) :
    Function.Exact (TopCat.singularCohomologyMap (zeroSectionComplProj F E) l)
      ((thomPair F E).singularCohomologyδ R k M l m hl) := by
  have hex : Function.Exact (TopCat.singularCohomologyMap (thomPair F E).map l)
      ((thomPair F E).singularCohomologyδ R k M l m hl) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_subspace R k M l m hl)
  -- Transport exactness of `Hˡ(E) ⟶ Hˡ(E₀) ⟶ Hᵐ(E, E₀)` along `π^* : Hˡ(B) ≅ Hˡ(E)`.
  intro y
  rw [hex, zeroSectionComplProj_def, TopCat.singularCohomologyMap_comp]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (zeroSectionHom F E) l x, ?_⟩,
    fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (thomPairProj F E) l x, hx⟩⟩
  rwa [ConcreteCategory.comp_apply,
    singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply]

/-- **Exactness at relative cohomology**: `Hˡ(E₀) ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B)`, the connecting morphism of
the pair `(E, E₀)` followed by the Euler class map, is exact, for `l + 1 = m`. -/
theorem exact_singularCohomologyδ_eulerClass (l m : ℕ) (hl : l + 1 = m) :
    Function.Exact ((thomPair F E).singularCohomologyδ R k M l m hl) (eulerClass R k M F E m) := by
  have hex : Function.Exact ((thomPair F E).singularCohomologyδ R k M l m hl)
      ((thomPair F E).singularCohomologyπ R k M m) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((thomPair F E).singularCohomology_exact_relative R k M l m hl)
  -- The Euler class map is `Hᵐ(E, E₀) ⟶ Hᵐ(E)` followed by the isomorphism `s^*`.
  intro y
  rw [← hex y, eulerClass_def, ConcreteCategory.comp_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← singularCohomologyMap_thomPairProj_singularCohomologyMap_zeroSectionHom_apply R k M
    ((thomPair F E).singularCohomologyπ R k M m y), h, map_zero]

end ZeroSection

section Gysin

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

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

/-- **Exactness of the Gysin sequence at `Hᵐ(B)`**: if the Thom map of `u ∈ Hⁿ(E, E₀; K)` is
surjective in degree `p`, then `Hᵖ(B; M) ⟶ Hᵐ(B; M) ⟶ Hᵐ(E₀; M)`, the cup product `a ↦ a ⌣ e(u)`
with the Euler class followed by the pullback along `π₀ : E₀ → B`, is exact, for `p + n = m`. -/
theorem exact_singularCup_eulerClass_singularCohomologyMap {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Surjective (thomMap F E M n p m h u)) :
    Function.Exact
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u))
      (TopCat.singularCohomologyMap (zeroSectionComplProj F E) m) := by
  intro y
  rw [exact_eulerClass_singularCohomologyMap_zeroSectionComplProj F E _ K M m y]
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨thomMap F E M n p m h u a, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hu x
    exact ⟨a, (eulerClass_thomMap F E M h u a).symm.trans hx⟩
  · exact (eulerClass_thomMap F E M h u a).trans ha

/-- **The Gysin connecting map** `Hˡ(E₀; M) ⟶ H^q(B; M)` of a class `u ∈ Hⁿ(E, E₀; K)` whose
Thom map is bijective in degree `q`, for `l + 1 = m` and `q + n = m`: the connecting morphism
`Hˡ(E₀; M) ⟶ Hᵐ(E, E₀; M)` of the pair `(E, E₀)` followed by the inverse of the Thom map. It is
characterized by `TauCeti.thomMap_gysinδ`. -/
def gysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l →ₗ[K]
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M q :=
  (LinearEquiv.ofBijective _ hu).symm.toLinearMap ∘ₗ
    ((thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M l m hl).hom

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- The Thom map sends the Gysin connecting map to the connecting morphism of the pair `(E, E₀)`:
`π^*(gysinδ y) ⌣ u = δ y`. -/
@[simp]
theorem thomMap_gysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u))
    (y : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l) :
    thomMap F E M n q m h u (gysinδ F E M hl h u hu y) =
      (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M l m hl y :=
  (LinearEquiv.ofBijective _ hu).apply_symm_apply _

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- The Gysin connecting map is the unique map whose image under the Thom map is the connecting
morphism of the pair `(E, E₀)`. -/
theorem gysinδ_eq_iff {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u))
    (y : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M q) :
    gysinδ F E M hl h u hu y = a ↔
      thomMap F E M n q m h u a =
        (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M l m hl y :=
  ⟨fun ha ↦ ha ▸ thomMap_gysinδ F E M hl h u hu y,
    fun ha ↦ hu.1 ((thomMap_gysinδ F E M hl h u hu y).trans ha.symm)⟩

/-- **Exactness of the Gysin sequence at `Hˡ(E₀)`**: if the Thom map of `u ∈ Hⁿ(E, E₀; K)` is
bijective in degree `q`, then `Hˡ(B; M) ⟶ Hˡ(E₀; M) ⟶ H^q(B; M)`, the pullback along
`π₀ : E₀ → B` followed by the Gysin connecting map, is exact, for `l + 1 = q + n`. -/
theorem exact_singularCohomologyMap_gysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    Function.Exact (TopCat.singularCohomologyMap (zeroSectionComplProj F E) l)
      (gysinδ F E M hl h u hu) := by
  intro y
  rw [← exact_singularCohomologyMap_zeroSectionComplProj_singularCohomologyδ F E _ K M l m hl y,
    gysinδ_eq_iff, map_zero, eq_comm]

/-- **Exactness of the Gysin sequence at `H^q(B)`**: if the Thom map of `u ∈ Hⁿ(E, E₀; K)` is
bijective in degree `q`, then `Hˡ(E₀; M) ⟶ H^q(B; M) ⟶ Hᵐ(B; M)`, the Gysin connecting map
followed by the cup product `a ↦ a ⌣ e(u)` with the Euler class, is exact, for `l + 1 = m` and
`q + n = m`. -/
theorem exact_gysinδ_singularCup_eulerClass {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    Function.Exact (gysinδ F E M hl h u hu)
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom q n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) := by
  intro a
  rw [LinearMap.flip_apply, ← eulerClass_thomMap,
    exact_singularCohomologyδ_eulerClass F E _ K M l m hl]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, (gysinδ_eq_iff F E M hl h u hu y a).2 hy.symm⟩,
    fun ⟨y, hy⟩ ↦ ⟨y, ((gysinδ_eq_iff F E M hl h u hu y a).1 hy).symm⟩⟩

end Gysin

section Sphere

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- The inclusion `S(E) → E₀` of the unit sphere bundle into the complement of the zero section. -/
def sphereBundleInclusion : TopCat.of (sphereBundle F E) ⟶ (thomPair F E).snd :=
  TopCat.ofHom (ContinuousMap.inclusion (sphereBundle_subset_zeroSectionCompl F E))

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] in
@[simp]
theorem coe_sphereBundleInclusion_apply (v : sphereBundle F E) :
    @Subtype.val _ (· ∈ zeroSectionCompl F E) (sphereBundleInclusion F E v) = v :=
  (rfl)

omit [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)] [VectorBundle ℝ F E] in
/-- The inclusion `S(E) → E₀` followed by the projection `π₀ : E₀ → B` is the projection of the
sphere bundle. -/
theorem sphereBundleInclusion_comp_zeroSectionComplProj :
    sphereBundleInclusion F E ≫ zeroSectionComplProj F E = TopCat.ofHom (sphereBundleProj F E) :=
  TopCat.ext fun v ↦ (zeroSectionComplProj_apply F E _).trans (sphereBundleProj_apply F E v).symm

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)

/-- The normalization `v ↦ v / ‖v‖` of `E₀` onto the sphere bundle. -/
private def sphereBundleNormalization : (thomPair F E).snd ⟶ TopCat.of (sphereBundle F E) :=
  TopCat.ofHom (sphereBundleHomotopyEquiv F E hnorm).invFun

private theorem singularCohomologyMap_sphereBundleInclusion_normalization_apply {l : ℕ}
    (y : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l) :
    TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) l
      (TopCat.singularCohomologyMap (sphereBundleInclusion F E) l y) = y := by
  -- The homotopy `e ∘ e⁻¹ ≃ id` of the homotopy equivalence `e : S(E) ≃ₕ E₀`, whose forward map
  -- is the inclusion.
  have hH : TopCat.Homotopy (sphereBundleNormalization F E hnorm ≫ sphereBundleInclusion F E)
      (𝟙 _) :=
    (sphereBundleHomotopyEquiv F E hnorm).right_inv.some.cast
      (ContinuousMap.ext fun v ↦ Subtype.ext (coe_sphereBundleHomotopyEquiv F E hnorm _)) rfl
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    hH.congr_singularCohomologyMap,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

private theorem singularCohomologyMap_sphereBundleNormalization_inclusion_apply {l : ℕ}
    (y : (TopCat.of (sphereBundle F E)).singularCohomology (ModuleCat.of K K) K M l) :
    TopCat.singularCohomologyMap (sphereBundleInclusion F E) l
      (TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) l y) = y := by
  -- The homotopy `e⁻¹ ∘ e ≃ id` of the homotopy equivalence `e : S(E) ≃ₕ E₀`, whose forward map
  -- is the inclusion.
  have hH : TopCat.Homotopy (sphereBundleInclusion F E ≫ sphereBundleNormalization F E hnorm)
      (𝟙 _) :=
    (sphereBundleHomotopyEquiv F E hnorm).left_inv.some.cast
      (ContinuousMap.ext fun v ↦ congrArg (sphereBundleHomotopyEquiv F E hnorm).invFun
        (Subtype.ext (coe_sphereBundleHomotopyEquiv F E hnorm v))) rfl
  rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    hH.congr_singularCohomologyMap,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

omit [NormedSpace ℝ F] [∀ b, NormedSpace ℝ (E b)] [VectorBundle ℝ F E] in
/-- Pullback along the projection of the sphere bundle is pullback along `π₀ : E₀ → B` followed
by restriction to `S(E)`. -/
private theorem singularCohomologyMap_sphereBundleProj_apply {m : ℕ}
    (z : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M m) :
    TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) m z =
      TopCat.singularCohomologyMap (sphereBundleInclusion F E) m
        (TopCat.singularCohomologyMap (zeroSectionComplProj F E) m z) := by
  rw [← sphereBundleInclusion_comp_zeroSectionComplProj, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply]

/-- **The Gysin connecting map of the sphere bundle** `Hˡ(S(E); M) ⟶ H^q(B; M)` of a class
`u ∈ Hⁿ(E, E₀; K)` whose Thom map is bijective in degree `q`, for `l + 1 = m` and `q + n = m`: the
pullback along the normalization `E₀ → S(E)`, `v ↦ v / ‖v‖`, which inverts the restriction
`Hˡ(E₀; M) ≅ Hˡ(S(E); M)`, followed by the Gysin connecting map `TauCeti.gysinδ` of `E₀`. It is
characterized by `TauCeti.sphereGysinδ_singularCohomologyMap`. -/
def sphereGysinδ {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    (TopCat.of (sphereBundle F E)).singularCohomology (ModuleCat.of K K) K M l →ₗ[K]
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M q :=
  gysinδ F E M hl h u hu ∘ₗ
    (TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) l).hom

/-- The Gysin connecting map of the sphere bundle on the restriction of a class of `E₀` is the
Gysin connecting map of `E₀`. -/
@[simp]
theorem sphereGysinδ_singularCohomologyMap {n q l m : ℕ} (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u))
    (y : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M l) :
    sphereGysinδ F E M hnorm hl h u hu
        (TopCat.singularCohomologyMap (sphereBundleInclusion F E) l y) =
      gysinδ F E M hl h u hu y :=
  congrArg (gysinδ F E M hl h u hu)
    (singularCohomologyMap_sphereBundleInclusion_normalization_apply F E M hnorm y)

include hnorm in
/-- **Exactness of the Gysin sequence of the sphere bundle at `Hᵐ(B)`**: if the Thom map of
`u ∈ Hⁿ(E, E₀; K)` is surjective in degree `p`, then `Hᵖ(B; M) ⟶ Hᵐ(B; M) ⟶ Hᵐ(S(E); M)`, the cup
product `a ↦ a ⌣ e(u)` with the Euler class followed by the pullback along `S(E) → B`, is exact,
for `p + n = m`. -/
theorem exact_singularCup_eulerClass_singularCohomologyMap_sphereBundleProj {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Surjective (thomMap F E M n p m h u)) :
    Function.Exact
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u))
      (TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) m) := by
  intro y
  -- The restriction `Hᵐ(E₀) ⟶ Hᵐ(S(E))` is injective.
  rw [← exact_singularCup_eulerClass_singularCohomologyMap F E M h u hu y,
    singularCohomologyMap_sphereBundleProj_apply F E M]
  refine ⟨fun hy ↦ ?_, fun hy ↦ (congrArg _ hy).trans (map_zero _)⟩
  exact ((singularCohomologyMap_sphereBundleInclusion_normalization_apply F E M hnorm _).symm.trans
    (congrArg _ hy)).trans (map_zero _)

/-- **Exactness of the Gysin sequence of the sphere bundle at `Hˡ(S(E))`**: if the Thom map of
`u ∈ Hⁿ(E, E₀; K)` is bijective in degree `q`, then `Hˡ(B; M) ⟶ Hˡ(S(E); M) ⟶ H^q(B; M)`, the
pullback along `S(E) → B` followed by the Gysin connecting map, is exact, for `l + 1 = q + n`. -/
theorem exact_singularCohomologyMap_sphereBundleProj_sphereGysinδ {n q l m : ℕ}
    (hl : l + 1 = m) (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    Function.Exact (TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) l)
      (sphereGysinδ F E M hnorm hl h u hu) := by
  intro y
  -- Transport exactness at `Hˡ(E₀)` along the isomorphism `Hˡ(E₀) ≅ Hˡ(S(E))`.
  refine (exact_singularCohomologyMap_gysinδ F E M hl h u hu _).trans
    ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
  · rw [singularCohomologyMap_sphereBundleProj_apply, hx,
      singularCohomologyMap_sphereBundleNormalization_inclusion_apply]
  · rw [← hx, singularCohomologyMap_sphereBundleProj_apply,
      singularCohomologyMap_sphereBundleInclusion_normalization_apply]

/-- **Exactness of the Gysin sequence of the sphere bundle at `H^q(B)`**: if the Thom map of
`u ∈ Hⁿ(E, E₀; K)` is bijective in degree `q`, then `Hˡ(S(E); M) ⟶ H^q(B; M) ⟶ Hᵐ(B; M)`, the
Gysin connecting map followed by the cup product `a ↦ a ⌣ e(u)` with the Euler class, is exact,
for `l + 1 = m` and `q + n = m`. -/
theorem exact_sphereGysinδ_singularCup_eulerClass {n q l m : ℕ} (hl : l + 1 = m)
    (h : q + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hu : Function.Bijective (thomMap F E M n q m h u)) :
    Function.Exact (sphereGysinδ F E M hnorm hl h u hu)
      (((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom q n m h).flip
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)) := by
  intro a
  rw [exact_gysinδ_singularCup_eulerClass F E M hl h u hu a]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨TopCat.singularCohomologyMap (sphereBundleInclusion F E) l y, ?_⟩,
    fun ⟨y, hy⟩ ↦ ⟨_, hy⟩⟩
  rwa [sphereGysinδ_singularCohomologyMap]

end Sphere

end TauCeti
