/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Gysin sequence of a vector bundle

Let `E → B` be a real vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero
section, and let `u ∈ Hⁿ(E, E₀; K)` be a class whose Thom map `Φ_u : a ↦ π^*a ⌣ u`
(`TauCeti.thomMap`) is bijective, for instance a Thom class of a bundle of rank `n`
(`TauCeti.IsThomClass`) over a compact base (`TauCeti.IsThomClass.bijective_thomMap`, for `n ≥ 2`)
or of rank zero (`TauCeti.IsThomClass.bijective_thomMap_of_finrank_eq_zero`). Write
`e = e(u) ∈ Hⁿ(B; K)` for its Euler class (`TauCeti.eulerClass`) and `π₀ : E₀ → B` for the
projection of the nonzero vectors. The **Gysin sequence** is the long exact sequence

`⋯ ⟶ Hᵖ(B; M) ⟶ Hᵖ⁺ⁿ(B; M) ⟶ Hᵖ⁺ⁿ(E₀; M) ⟶ Hᵖ⁺¹(B; M) ⟶ Hᵖ⁺ⁿ⁺¹(B; M) ⟶ ⋯`

for every `K`-module `M`, whose maps are the cup product `a ↦ a ⌣ e` with the Euler class
(`TauCeti.eulerCup`), the pull-back `π₀^*` along the projection, and the Gysin map
`ψ : Hᵐ(E₀; M) ⟶ Hᵖ(B; M)`, `p + n = m + 1` (`TauCeti.gysinMap`): the connecting map
`δ : Hᵐ(E₀; M) ⟶ Hᵐ⁺¹(E, E₀; M)` of the Thom pair followed by the inverse of the Thom isomorphism.
Since the inclusion of the unit sphere bundle into `E₀` is a homotopy equivalence
(`TauCeti.gaugeSphereBundleHomotopyEquiv`), this is the Gysin sequence of the sphere bundle. Over a
compact base and in rank `0` or at least `2`, it holds with coefficients in `ZMod 2` for the unique
Thom class of every vector bundle, and with integral coefficients for the Thom class of every
oriented one.

The sequence is the long exact sequence of the Thom pair,

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(E) ⟶ Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀) ⟶ ⋯`,

rewritten through two identifications: `Hᵐ(E) ≅ Hᵐ(B)` by `π^*`, inverse to the pull-back along
the zero section `s`, because `s ∘ π` is homotopic to the identity of `E` through `t • v`
(`TauCeti.singularCohomologyMap_zeroSectionHom_comp_thomPairProj`, in
`TauCeti/Topology/VectorBundle/EulerClass.lean`), and
`Hᵖ(B) ≅ Hᵖ⁺ⁿ(E, E₀)` by the Thom map. Under these the map `Hᵖ⁺ⁿ(E, E₀) ⟶ Hᵖ⁺ⁿ(E)` becomes the cup
product with the Euler class: the image of `Φ_u(a)` in `Hᵖ⁺ⁿ(E)` is `π^*(a ⌣ e)`
(`TauCeti.singularCohomologyπ_thomMap`).

## Main definitions

* `TauCeti.eulerCup`: the cup product `a ↦ a ⌣ e(u)` with the Euler class.
* `TauCeti.gysinMap`: the Gysin map `Hᵐ(E₀; M) ⟶ Hᵖ(B; M)`, `p + n = m + 1`, of a class `u` with
  bijective Thom map, characterized by `Φ_u ∘ ψ = δ` (`TauCeti.thomMap_gysinMap`).

## Main results

* `TauCeti.singularCohomologyπ_thomMap`: the image of `π^*a ⌣ u` in `Hᵐ(E)` is `π^*(a ⌣ e(u))`.
* `TauCeti.exact_eulerCup_singularCohomologyMap`: exactness at `Hᵖ⁺ⁿ(B)`.
* `TauCeti.exact_singularCohomologyMap_gysinMap`: exactness at `Hᵐ(E₀)`.
* `TauCeti.exact_gysinMap_eulerCup`: exactness at `Hᵖ(B)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12, Theorem 12.2 (the Gysin sequence) and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, the Gysin sequence following Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module

universe w

namespace TauCeti

/-! ### The Gysin map -/

section FiberBundle

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F] (E : B → Type w)
  [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

/-- The Gysin map `ψ : Hᵐ(E₀; M) ⟶ Hᵖ(B; M)`, `p + n = m + 1`, of a class `u ∈ Hⁿ(E, E₀; K)` whose
Thom map `Hᵖ(B; M) ⟶ Hᵐ⁺¹(E, E₀; M)` is bijective: the connecting map `Hᵐ(E₀) ⟶ Hᵐ⁺¹(E, E₀)` of
the Thom pair followed by the inverse of the Thom map. It is characterized by
`TauCeti.thomMap_gysinMap`. -/
def gysinMap {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q) :
    (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M m ⟶
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p :=
  (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M m q hm ≫
    ModuleCat.ofHom (LinearEquiv.ofBijective _ hu).symm.toLinearMap

/-- **The Gysin map is the connecting map read through the Thom isomorphism**: `Φ_u(ψ(z)) = δ z`
for `z ∈ Hᵐ(E₀; M)`. -/
@[simp]
theorem thomMap_gysinMap {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q)
    (z : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M m) :
    thomMap F E M n p q h u (gysinMap F E h hu hm z) =
      (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M m q hm z :=
  (LinearEquiv.ofBijective _ hu).apply_symm_apply _

/-- The Gysin map is determined by its characterization `Φ_u(ψ(z)) = δ z`. -/
theorem gysinMap_eq_iff {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q)
    (z : (thomPair F E).snd.singularCohomology (ModuleCat.of K K) K M m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    gysinMap F E h hu hm z = a ↔
      (thomPair F E).singularCohomologyδ (ModuleCat.of K K) K M m q hm z =
        thomMap F E M n p q h u a := by
  rw [← thomMap_gysinMap F E h hu hm z]
  exact hu.1.eq_iff.symm

/-- The pull-back to `E₀` followed by the Gysin map vanishes: the connecting map of the Thom pair
kills classes restricted from the total space. -/
@[reassoc]
theorem singularCohomologyMap_comp_gysinMap {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q) :
    TopCat.singularCohomologyMap ((thomPair F E).map ≫ thomPairProj F E) m ≫
      gysinMap F E h hu hm = 0 := by
  ext x
  rw [ConcreteCategory.comp_apply]
  refine (gysinMap_eq_iff F E h hu hm _ 0).2 ?_
  rw [map_zero, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
    TopPair.singularCohomologyMap_comp_singularCohomologyδ_apply (thomPair F E)
      (ModuleCat.of K K) K M m q hm]

end FiberBundle

section VectorBundle

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

variable {K : Type w} [CommRing K] {M : ModuleCat.{w} K}

/-! ### The Thom map and the Euler class -/

variable (M) in
/-- The cup product `a ↦ a ⌣ e(u)` with the Euler class `e(u) ∈ Hⁿ(B; K)` of a class
`u ∈ Hⁿ(E, E₀; K)`, as a map `Hᵖ(B; M) ⟶ Hᵐ(B; M)` for `p + n = m` and a `K`-module `M`. The
pairing of values is the right unitor `M ⊗ K ≅ M`, as in the Thom map `TauCeti.thomMap`. -/
def eulerCup {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) n) (p m : ℕ) (h : p + n = m) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ⟶
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M m :=
  ModuleCat.ofHom <| ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
    p n m h).flip (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u)

theorem eulerCup_apply {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) {p m : ℕ}
    (h : p + n = m) (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    eulerCup F E M u p m h a =
      (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h a
        (eulerClass (ModuleCat.of K K) K (ModuleCat.of K K) F E n u) :=
  (rfl)

/-- **The Thom map and the Euler class.** The image of `Φ_u(a) = π^*a ⌣ u` under the map
`Hᵐ(E, E₀) ⟶ Hᵐ(E)` is `π^*(a ⌣ e(u))`: the image of `u` in `Hⁿ(E)` is the pull-back along `π` of
its Euler class. -/
theorem singularCohomologyπ_thomMap {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (thomPair F E).singularCohomologyπ (ModuleCat.of K K) K M m (thomMap F E M n p m h u a) =
      TopCat.singularCohomologyMap (thomPairProj F E) m (eulerCup F E M u p m h a) := by
  rw [thomMap_apply, TopPair.singularCohomologyπ_singularCup, eulerCup_apply,
    ← TopCat.singularCup_naturality, eulerClass_def, ConcreteCategory.comp_apply]
  exact (congrArg _ (singularCohomologyMap_zeroSectionHom_comp_thomPairProj_apply F E _ _)).symm

/-! ### The Gysin sequence -/

/-- The cup product with the Euler class followed by the pull-back to `E₀` vanishes: the image of
`π^*(a ⌣ e(u))` in `Hᵐ(E₀)` is that of `Φ_u(a) ∈ Hᵐ(E, E₀)`. -/
@[reassoc]
theorem eulerCup_comp_singularCohomologyMap {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) {p m : ℕ}
    (h : p + n = m) :
    eulerCup F E M u p m h ≫
      TopCat.singularCohomologyMap ((thomPair F E).map ≫ thomPairProj F E) m = 0 := by
  ext a
  rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← singularCohomologyπ_thomMap,
    TopPair.singularCohomologyπ_comp_singularCohomologyMap_apply (thomPair F E) (ModuleCat.of K K)
      K M m, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- **Exactness of the Gysin sequence at `Hᵐ(B)`**: if the Thom map `Hᵖ(B) ⟶ Hᵐ(E, E₀)` of `u` is
surjective, `p + n = m`, then a class of `Hᵐ(B; M)` pulls back to zero on `E₀` exactly when it is
`a ⌣ e(u)` for some `a ∈ Hᵖ(B; M)`. -/
theorem exact_eulerCup_singularCohomologyMap {n : ℕ}
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n} {p m : ℕ}
    (h : p + n = m) (hu : Function.Surjective (thomMap F E M n p m h u)) :
    (ShortComplex.mk _ _ (eulerCup_comp_singularCohomologyMap F E (M := M) u h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M m) hx
  replace hx : TopCat.singularCohomologyMap (thomPair F E).map m
      (TopCat.singularCohomologyMap (thomPairProj F E) m x) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp]
    exact hx
  -- `π^*x` restricts to zero on `E₀`, so it comes from the Thom pair, where it is some `Φ_u(a)`.
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((thomPair F E).singularCohomology_exact_space (ModuleCat.of K K) K M m) _ hx
  obtain ⟨a, rfl⟩ := hu y
  refine ⟨a, ?_⟩
  -- Then `π^*x = π^*(a ⌣ e(u))`, and `π^*` is injective.
  refine singularCohomologyMap_thomPairProj_injective F E m ?_
  rw [← singularCohomologyπ_thomMap]
  exact hy

/-- **Exactness of the Gysin sequence at `Hᵐ(E₀)`**: if the Thom map `Hᵖ(B) ⟶ Hᵐ⁺¹(E, E₀)` of `u`
is bijective, `p + n = m + 1`, then a class of `Hᵐ(E₀; M)` is killed by the Gysin map exactly when
it is pulled back from `Hᵐ(B; M)`. -/
theorem exact_singularCohomologyMap_gysinMap {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q) :
    (ShortComplex.mk _ _ (singularCohomologyMap_comp_gysinMap F E h hu hm)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  dsimp only at hz
  -- `ψ(z) = 0` means `δ z = 0`, so `z` is restricted from some `w ∈ Hᵐ(E)`, and `w = π^*(s^*w)`.
  rw [gysinMap_eq_iff, map_zero] at hz
  obtain ⟨w, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((thomPair F E).singularCohomology_exact_subspace (ModuleCat.of K K) K M m q hm) _ hz
  have hw : TopCat.singularCohomologyMap ((thomPair F E).map ≫ thomPairProj F E) m
      (TopCat.singularCohomologyMap (zeroSectionHom F E) m w) =
        TopCat.singularCohomologyMap (thomPair F E).map m w := by
    rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
      singularCohomologyMap_zeroSectionHom_comp_thomPairProj_apply]
  exact ⟨_, hw⟩

/-- The Gysin map followed by the cup product with the Euler class vanishes: `π^*(ψ(z) ⌣ e(u))` is
the image in `Hᵐ⁺¹(E)` of `Φ_u(ψ(z)) = δ z`, which is zero, and `π^*` is injective. -/
@[reassoc (attr := simp)]
theorem gysinMap_comp_eulerCup {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q) :
    gysinMap F E h hu hm ≫ eulerCup F E M u p q h = 0 := by
  ext z
  rw [ConcreteCategory.comp_apply]
  refine singularCohomologyMap_thomPairProj_injective F E q ?_
  rw [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, ← singularCohomologyπ_thomMap,
    thomMap_gysinMap, TopPair.singularCohomologyδ_comp_singularCohomologyπ_apply (thomPair F E)
      (ModuleCat.of K K) K M m q hm]

/-- **Exactness of the Gysin sequence at `Hᵖ(B)`**: if the Thom map `Hᵖ(B) ⟶ Hᵐ⁺¹(E, E₀)` of `u`
is bijective, `p + n = m + 1`, then `a ∈ Hᵖ(B; M)` satisfies `a ⌣ e(u) = 0` exactly when it is the
Gysin image of a class of `Hᵐ(E₀; M)`. -/
theorem exact_gysinMap_eulerCup {n p q m : ℕ} (h : p + n = q)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hu : Function.Bijective (thomMap F E M n p q h u)) (hm : m + 1 = q) :
    (ShortComplex.mk _ _ (gysinMap_comp_eulerCup F E h hu hm)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  -- The image of `Φ_u(a)` in `Hᵐ⁺¹(E)` is `π^*(a ⌣ e(u)) = 0`, so `Φ_u(a) = δ z` for some `z`.
  have ha' : (thomPair F E).singularCohomologyπ (ModuleCat.of K K) K M q
      (thomMap F E M n p q h u a) = 0 := by
    dsimp only at ha
    rw [singularCohomologyπ_thomMap, ha, map_zero]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((thomPair F E).singularCohomology_exact_relative (ModuleCat.of K K) K M m q hm) _ ha'
  exact ⟨z, (gysinMap_eq_iff F E h hu hm z a).2 hz⟩

end VectorBundle

end TauCeti
