/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import TauCeti.Topology.VectorBundle.Orientation.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.Prod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Thom and Euler classes of direct sums

Let `E₁` and `E₂` be real vector bundles over a common base `B`, with model fibres `F₁` and `F₂`,
and let `E₁ ⊕ E₂` be their fibrewise direct sum `E₁ ×ᵇ E₂`, with model fibre `F₁ × F₂`. Its
nonzero vectors are those whose first or second component is nonzero, so the Thom pair
`(E₁ ⊕ E₂, (E₁ ⊕ E₂)₀)` receives the relative cup product
(`TopCat.singularRelativeCup`) of classes pulled back along the two projections
`p₁ : E₁ ⊕ E₂ → E₁` and `p₂ : E₁ ⊕ E₂ → E₂`:

`Hᵖ(E₁, E₁₀) × H^q(E₂, E₂₀) ⟶ Hᵖ⁺^q(E₁ ⊕ E₂, (E₁ ⊕ E₂)₀)`,  `(a, b) ↦ p₁^* a ⌣ p₂^* b`

(`TauCeti.thomPairCup`). On the fibre over a point `b` it is the same product for the vector
spaces `E₁_b` and `E₂_b` (`TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup`), and its
Euler class is the cup product of the Euler classes
(`TauCeti.eulerClass_thomPairCup`): the zero section of `E₁ ⊕ E₂` followed by `pᵢ` is the zero
section of `Eᵢ`. For the model fibres, the product
`Hᵖ(F₁, F₁ ∖ {0}) × H^q(F₂, F₂ ∖ {0}) ⟶ Hᵖ⁺^q(F₁ × F₂, (F₁ × F₂) ∖ {0})` is
`TauCeti.complZeroPairCross`. For fibres with closed points, the restriction of
`TauCeti.thomPairCup` to the fibre over `b` is this product for `E₁_b` and `E₂_b`
(`TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross`). It is
natural under products of continuous linear equivalences
(`TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`).

For orientations `o₁` and `o₂`, the direct sum carries the orientation `o₁.prod o₂`, the first
factor before the second. Normalize Thom classes as in
`TauCeti.VectorBundleOrientation.thomClassOfModel`, by orientations `ω₁`, `ω₂` of the model fibres
and classes `g₁ ∈ Hᵖ(F₁, F₁ ∖ {0})`, `g₂ ∈ H^q(F₂, F₂ ∖ {0})`. Then **the Thom class of the direct
sum, normalized by `ω₁.prod ω₂` and the product of `g₁` and `g₂`, is the product of the Thom
classes** (`TauCeti.VectorBundleOrientation.thomClassOfModel_prod`), and so **the Euler class of
the direct sum is the cup product of the Euler classes**
(`TauCeti.VectorBundleOrientation.eulerClass_thomClassOfModel_prod`), the Whitney product formula
`e(E₁ ⊕ E₂) = e(E₁) ⌣ e(E₂)`. Both hold for arbitrary coefficient modules and pairings, and over
an arbitrary base. The proof reads both sides on the fibre over each point in the product of the
preferred trivializations: it reads the product orientation as the product of the two readings,
and reversing either factor reverses both the orientation and the product of the model classes.

The integral Thom class `TauCeti.VectorBundleOrientation.thomClass` is normalized by the
generators `Orientation.localCohomologyClass`; the integral form of the formula further needs the
product of the generators selected by `ω₁` and `ω₂` to be the generator selected by
`ω₁.prod ω₂`, which this file does not prove.

## Main definitions

* `TauCeti.totalSpaceProdFst`, `TauCeti.totalSpaceProdSnd`: the projections of the total space of
  `E₁ ⊕ E₂` onto those of `E₁` and `E₂`.
* `TauCeti.thomPairCup`: the product of classes of the Thom pairs of `E₁` and `E₂`, a class of
  the Thom pair of `E₁ ⊕ E₂`.
* `TauCeti.complZeroPairCross`: the product of classes of the pairs `(V₁, V₁ ∖ {0})` and
  `(V₂, V₂ ∖ {0})`, a class of `(V₁ × V₂, (V₁ × V₂) ∖ {0})`.

## Main results

* `TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup` and
  `TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross`: the
  restriction of the product to a fibre.
* `TauCeti.eulerClass_thomPairCup`: the Euler class of the product is the cup product of the
  Euler classes.
* `TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`: naturality of the
  fibre product under products of continuous linear equivalences.
* `TauCeti.VectorBundleOrientation.thomClassOfModel_prod`: the Thom class of the direct sum is the
  product of the Thom classes.
* `TauCeti.VectorBundleOrientation.eulerClass_thomClassOfModel_prod`: the Whitney product formula
  for Euler classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9, Property 9.6 (the Euler class of a Whitney sum) and the product formula
  for Thom classes used in its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module Set

universe w v u

namespace TauCeti

section Prod

variable {B : Type w} [TopologicalSpace B]
  (F₁ : Type w) [TopologicalSpace F₁] (E₁ : B → Type w) [TopologicalSpace (TotalSpace F₁ E₁)]
  (F₂ : Type w) [TopologicalSpace F₂] (E₂ : B → Type w) [TopologicalSpace (TotalSpace F₂ E₂)]

/-- The projection of the total space of the direct sum `E₁ ⊕ E₂` onto the total space of `E₁`. -/
def totalSpaceProdFst :
    TopCat.of (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) ⟶ TopCat.of (TotalSpace F₁ E₁) :=
  TopCat.ofHom ⟨fun v ↦ ⟨v.proj, v.2.1⟩,
    continuous_fst.comp (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous⟩

/-- The projection of the total space of the direct sum `E₁ ⊕ E₂` onto the total space of `E₂`. -/
def totalSpaceProdSnd :
    TopCat.of (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) ⟶ TopCat.of (TotalSpace F₂ E₂) :=
  TopCat.ofHom ⟨fun v ↦ ⟨v.proj, v.2.2⟩,
    continuous_snd.comp (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous⟩

omit [TopologicalSpace B] [TopologicalSpace F₁] [TopologicalSpace F₂] in
@[simp]
theorem totalSpaceProdFst_apply (v : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    totalSpaceProdFst F₁ E₁ F₂ E₂ v = ⟨v.proj, v.2.1⟩ :=
  (rfl)

omit [TopologicalSpace B] [TopologicalSpace F₁] [TopologicalSpace F₂] in
@[simp]
theorem totalSpaceProdSnd_apply (v : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :
    totalSpaceProdSnd F₁ E₁ F₂ E₂ v = ⟨v.proj, v.2.2⟩ :=
  (rfl)

variable [∀ b, Zero (E₁ b)] [∀ b, Zero (E₂ b)]

omit [TopologicalSpace B] [TopologicalSpace F₁] [TopologicalSpace F₂] in
/-- If a vector of the direct sum is nonzero, then one of its components is nonzero: the nonzero
vectors of `E₁ ⊕ E₂` lie in the union of the preimages of the nonzero vectors of `E₁` and
`E₂`. -/
theorem zeroSectionCompl_prod_subset :
    zeroSectionCompl (F₁ × F₂) (E₁ ×ᵇ E₂) ⊆
      totalSpaceProdFst F₁ E₁ F₂ E₂ ⁻¹' zeroSectionCompl F₁ E₁ ∪
        totalSpaceProdSnd F₁ E₁ F₂ E₂ ⁻¹' zeroSectionCompl F₂ E₂ := by
  intro v hv
  by_contra hc
  simp only [mem_union, mem_preimage, mem_zeroSectionCompl, not_or, not_not] at hc
  exact mem_zeroSectionCompl.1 hv (Prod.ext hc.1 hc.2)

/-- If a vector of a product of two spaces with zero is nonzero, then one of its components is
nonzero. -/
theorem compl_zero_prod_subset (V₁ V₂ : Type w) [TopologicalSpace V₁] [TopologicalSpace V₂]
    [Zero V₁] [Zero V₂] :
    ({0}ᶜ : Set (TopCat.of (V₁ × V₂))) ⊆
      (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁))) ⁻¹' {0}ᶜ ∪
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) ⁻¹' {0}ᶜ := by
  intro v hv
  by_contra hc
  simp only [mem_union, mem_preimage, mem_compl_singleton_iff, not_or, not_not] at hc
  exact hv (Prod.ext hc.1 hc.2)

end Prod

section ComplZeroPairCross

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C]
  [MonoidalLinear k C]

/-- **The product of classes of the pairs `(V, V ∖ {0})`.** For spaces `V₁` and `V₂` with a zero
and closed points, such as finite-dimensional real vector spaces, this is the pairing
`Hᵖ(V₁, V₁ ∖ {0}; R, M) × H^q(V₂, V₂ ∖ {0}; S, N) ⟶ Hⁿ(V₁ × V₂, (V₁ × V₂) ∖ {0}; T, L)`,
`p + q = n`, sending `(g₁, g₂)` to the relative cup product of their pull-backs along the two
projections (`TopCat.singularRelativeCupPullback`). It is the fibre value of the product of Thom
pair classes `TauCeti.thomPairCup`
(`TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross`). -/
def complZeroPairCross (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology R k M p →ₗ[k]
      (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology S k N q →ₗ[k]
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂)) ({0}ᶜ : Set (V₁ × V₂))).singularCohomology T
          k L n :=
  TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
    (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) isOpen_compl_singleton
    isOpen_compl_singleton (compl_zero_prod_subset V₁ V₂) p q n h

theorem complZeroPairCross_def (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) :
    complZeroPairCross k V₁ V₂ u μ p q n h =
      TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) isOpen_compl_singleton
        isOpen_compl_singleton (compl_zero_prod_subset V₁ V₂) p q n h :=
  (rfl)

end ComplZeroPairCross

section ThomPairCup

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C]
  [MonoidalLinear k C]

variable {B : Type w} [TopologicalSpace B]
  {F₁ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : B → Type w} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommMonoid (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : B → Type w} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommMonoid (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

variable (F₁ E₁ F₂ E₂) in
/-- **The product of classes of two Thom pairs.** For real vector bundles `E₁` and `E₂` over a
common base, this is the pairing
`Hᵖ(E₁, E₁₀; R, M) × H^q(E₂, E₂₀; S, N) ⟶ Hⁿ(E₁ ⊕ E₂, (E₁ ⊕ E₂)₀; T, L)`, `p + q = n`, sending
`(a, b)` to the relative cup product `p₁^* a ⌣ p₂^* b` of the pull-backs along the projections
`p₁` and `p₂` of the direct sum, restricted to the Thom pair of the direct sum
(`TopCat.singularRelativeCupPullback`). -/
def thomPairCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) :
    (thomPair F₁ E₁).singularCohomology R k M p →ₗ[k]
      (thomPair F₂ E₂).singularCohomology S k N q →ₗ[k]
        (thomPair (F₁ × F₂) (E₁ ×ᵇ E₂)).singularCohomology T k L n :=
  TopCat.singularRelativeCupPullback k u μ (totalSpaceProdFst F₁ E₁ F₂ E₂)
    (totalSpaceProdSnd F₁ E₁ F₂ E₂) (isOpen_zeroSectionCompl F₁ E₁)
    (isOpen_zeroSectionCompl F₂ E₂) (zeroSectionCompl_prod_subset F₁ E₁ F₂ E₂) p q n h

variable (F₁ E₁ F₂ E₂) in
theorem thomPairCup_def (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) :
    thomPairCup k F₁ E₁ F₂ E₂ u μ p q n h =
      TopCat.singularRelativeCupPullback k u μ (totalSpaceProdFst F₁ E₁ F₂ E₂)
        (totalSpaceProdSnd F₁ E₁ F₂ E₂) (isOpen_zeroSectionCompl F₁ E₁)
        (isOpen_zeroSectionCompl F₂ E₂) (zeroSectionCompl_prod_subset F₁ E₁ F₂ E₂) p q n h :=
  (rfl)

/-- **The product of Thom pair classes on a fibre.** Restricted to the fibre pair over `b`, the
product of `a` and `a'` is the product, for the vector spaces `E₁_b` and `E₂_b`, of the
restrictions of `a` and `a'` to the fibre pairs over `b`: the relative cup product of their
pull-backs along the two projections of `E₁_b × E₂_b`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomPairCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) (b : B) (a : (thomPair F₁ E₁).singularCohomology R k M p)
    (a' : (thomPair F₂ E₂).singularCohomology S k N q) :
    TopPair.singularCohomologyMap (fiberThomPairMap (F₁ × F₂) (E₁ ×ᵇ E₂) b) n
        (thomPairCup k F₁ E₁ F₂ E₂ u μ p q n h a a') =
      TopCat.singularRelativeCupPullback k u μ
        (TopCat.ofHom (ContinuousMap.fst : C(E₁ b × E₂ b, E₁ b)))
        (TopCat.ofHom (ContinuousMap.snd : C(E₁ b × E₂ b, E₂ b)))
        (isOpen_compl_zero_fiber F₁ b) (isOpen_compl_zero_fiber F₂ b)
        (compl_zero_prod_subset (E₁ b) (E₂ b)) p q n h
        (TopPair.singularCohomologyMap (fiberThomPairMap F₁ E₁ b) p a)
        (TopPair.singularCohomologyMap (fiberThomPairMap F₂ E₂ b) q a') := by
  -- A nonzero vector of `E₁_b × E₂_b` has a nonzero component, a nonzero vector of `E₁` or `E₂`.
  have hZ (x : E₁ b × E₂ b) (hx : x ≠ 0) :
      (⟨b, x.1⟩ : TotalSpace F₁ E₁) ∈ zeroSectionCompl F₁ E₁ ∨
        (⟨b, x.2⟩ : TotalSpace F₂ E₂) ∈ zeroSectionCompl F₂ E₂ :=
    (compl_zero_prod_subset (E₁ b) (E₂ b) hx).imp mem_zeroSectionCompl.2 mem_zeroSectionCompl.2
  rw [thomPairCup_def, fiberThomPairMap_eq_ofSubsetMap (F := F₁ × F₂) (E := E₁ ×ᵇ E₂)]
  refine (TopCat.singularCohomologyMap_singularRelativeCupPullback k u μ _ _ _ _ _ _ _
    ?hZ₁ p q n h a a').trans ?_
  case hZ₁ => exact fun x hx ↦ hZ x hx
  rw [fiberThomPairMap_eq_ofSubsetMap (F := F₁) (E := E₁),
    fiberThomPairMap_eq_ofSubsetMap (F := F₂) (E := E₂)]
  refine Eq.trans ?_ (TopCat.singularRelativeCupPullback_singularCohomologyMap k u μ _ _ _ _
    (isOpen_zeroSectionCompl F₁ E₁) (isOpen_zeroSectionCompl F₂ E₂) _ _ _ _ _
    ?hZ₂ p q n h a a').symm
  case hZ₂ => exact fun x hx ↦ hZ x hx
  have h₁ : (TopCat.ofHom ⟨@TotalSpace.mk B (F₁ × F₂) (E₁ ×ᵇ E₂) b,
      FiberBundle.continuous_totalSpaceMk (F₁ × F₂) (E₁ ×ᵇ E₂) b⟩ ≫
        totalSpaceProdFst F₁ E₁ F₂ E₂ : TopCat.of (E₁ b × E₂ b) ⟶ _) =
      TopCat.ofHom ContinuousMap.fst ≫
        TopCat.ofHom ⟨TotalSpace.mk b, FiberBundle.continuous_totalSpaceMk F₁ E₁ b⟩ :=
    TopCat.ext fun _ ↦ rfl
  have h₂ : (TopCat.ofHom ⟨@TotalSpace.mk B (F₁ × F₂) (E₁ ×ᵇ E₂) b,
      FiberBundle.continuous_totalSpaceMk (F₁ × F₂) (E₁ ×ᵇ E₂) b⟩ ≫
        totalSpaceProdSnd F₁ E₁ F₂ E₂ : TopCat.of (E₁ b × E₂ b) ⟶ _) =
      TopCat.ofHom ContinuousMap.snd ≫
        TopCat.ofHom ⟨TotalSpace.mk b, FiberBundle.continuous_totalSpaceMk F₂ E₂ b⟩ :=
    TopCat.ext fun _ ↦ rfl
  simp only [h₁, h₂]

/-- **The product of Thom pair classes on a fibre with closed points.** When the fibres over `b`
are T1 spaces, the restriction of the product of `a` and `a'` to the fibre pair over `b` is the
product `complZeroPairCross` of the restrictions of `a` and `a'` to the fibre pairs over `b`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) (b : B) [T1Space (E₁ b)]
    [T1Space (E₂ b)] (a : (thomPair F₁ E₁).singularCohomology R k M p)
    (a' : (thomPair F₂ E₂).singularCohomology S k N q) :
    TopPair.singularCohomologyMap (fiberThomPairMap (F₁ × F₂) (E₁ ×ᵇ E₂) b) n
        (thomPairCup k F₁ E₁ F₂ E₂ u μ p q n h a a') =
      complZeroPairCross k (E₁ b) (E₂ b) u μ p q n h
        (TopPair.singularCohomologyMap (fiberThomPairMap F₁ E₁ b) p a)
        (TopPair.singularCohomologyMap (fiberThomPairMap F₂ E₂ b) q a') :=
  singularCohomologyMap_fiberThomPairMap_thomPairCup k u μ p q n h b a a'

variable (F₁ E₁ F₂ E₂) in
/-- The zero section of `E₁ ⊕ E₂` followed by the projection onto `E₁` is the zero section of
`E₁`. -/
@[simp, reassoc]
theorem zeroSectionHom_comp_totalSpaceProdFst :
    zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂) ≫ totalSpaceProdFst F₁ E₁ F₂ E₂ = zeroSectionHom F₁ E₁ :=
  TopCat.ext fun b ↦ by
    -- Neither `ConcreteCategory.comp_apply` nor `TopCat.comp_app` rewrites this composite, so
    -- evaluate it by `change`.
    change totalSpaceProdFst F₁ E₁ F₂ E₂ (zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂) b) =
      zeroSectionHom F₁ E₁ b
    rw [zeroSectionHom_apply, zeroSectionHom_apply, totalSpaceProdFst_apply]
    simp [zeroSection]

variable (F₁ E₁ F₂ E₂) in
/-- The zero section of `E₁ ⊕ E₂` followed by the projection onto `E₂` is the zero section of
`E₂`. -/
@[simp, reassoc]
theorem zeroSectionHom_comp_totalSpaceProdSnd :
    zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂) ≫ totalSpaceProdSnd F₁ E₁ F₂ E₂ = zeroSectionHom F₂ E₂ :=
  TopCat.ext fun b ↦ by
    -- Neither `ConcreteCategory.comp_apply` nor `TopCat.comp_app` rewrites this composite, so
    -- evaluate it by `change`.
    change totalSpaceProdSnd F₁ E₁ F₂ E₂ (zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂) b) =
      zeroSectionHom F₂ E₂ b
    rw [zeroSectionHom_apply, zeroSectionHom_apply, totalSpaceProdSnd_apply]
    simp [zeroSection]

variable (F₁ E₁ F₂ E₂) in
/-- **The Euler class of a product of Thom pair classes is the cup product of the Euler classes**:
the zero section of `E₁ ⊕ E₂` followed by the projection onto `Eᵢ` is the zero section of
`Eᵢ`. -/
@[simp]
theorem eulerClass_thomPairCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (thomPair F₁ E₁).singularCohomology R k M p)
    (a' : (thomPair F₂ E₂).singularCohomology S k N q) :
    eulerClass T k L (F₁ × F₂) (E₁ ×ᵇ E₂) n (thomPairCup k F₁ E₁ F₂ E₂ u μ p q n h a a') =
      (TopCat.of B).singularCup k u μ p q n h (eulerClass R k M F₁ E₁ p a)
        (eulerClass S k N F₂ E₂ q a') := by
  rw [eulerClass_def, ConcreteCategory.comp_apply, thomPairCup_def,
    TopCat.singularCohomologyπ_singularRelativeCupPullback]
  refine (TopCat.singularCup_naturality _ k u μ p q n h _ _).symm.trans ?_
  rw [eulerClass_def, eulerClass_def]
  refine congrArg₂ (fun x y ↦ (TopCat.of B).singularCup k u μ p q n h x y) ?_ ?_
  · rw [← zeroSectionHom_comp_totalSpaceProdFst F₁ E₁ F₂ E₂]
    exact (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp (R := R) (k := k)
      (M := M) (zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂)) (totalSpaceProdFst F₁ E₁ F₂ E₂) p) _).symm
  · rw [← zeroSectionHom_comp_totalSpaceProdSnd F₁ E₁ F₂ E₂]
    exact (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp (R := S) (k := k)
      (M := N) (zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂)) (totalSpaceProdSnd F₁ E₁ F₂ E₂) q) _).symm

end ThomPairCup

section LinearEquiv

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C]
  [MonoidalLinear k C]
  {𝕜 : Type*} [Semiring 𝕜] {V₁ V₂ W₁ W₂ : Type w}
  [TopologicalSpace V₁] [AddCommMonoid V₁] [Module 𝕜 V₁]
  [TopologicalSpace V₂] [AddCommMonoid V₂] [Module 𝕜 V₂]
  [TopologicalSpace W₁] [AddCommMonoid W₁] [Module 𝕜 W₁]
  [TopologicalSpace W₂] [AddCommMonoid W₂] [Module 𝕜 W₂]
  [T1Space V₁] [T1Space V₂] [T1Space W₁] [T1Space W₂]

/-- **Naturality of the product of local classes under product equivalences.** For continuous
linear equivalences `f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`, the product, for `V₁ × V₂`, of the
pull-backs along `f₁` and `f₂` of classes `g₁ ∈ Hᵖ(W₁, W₁ ∖ {0})` and `g₂ ∈ H^q(W₂, W₂ ∖ {0})` is
the pull-back along `f₁ × f₂` of their product for `W₁ × W₂`. -/
theorem complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom (u : T ⟶ R ⊗ S)
    (μ : M ⊗ N ⟶ L) (f₁ : V₁ ≃L[𝕜] W₁) (f₂ : V₂ ≃L[𝕜] W₂) (p q n : ℕ) (h : p + q = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of W₁) ({0}ᶜ : Set W₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of W₂) ({0}ᶜ : Set W₂)).singularCohomology S k N q) :
    complZeroPairCross k V₁ V₂ u μ p q n h
        (TopPair.singularCohomologyMap f₁.complZeroPairIso.hom p g₁)
        (TopPair.singularCohomologyMap f₂.complZeroPairIso.hom q g₂) =
      TopPair.singularCohomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom n
        (complZeroPairCross k W₁ W₂ u μ p q n h g₁ g₂) := by
  -- A nonzero vector of `V₁ × V₂` has a component with nonzero image.
  have hZ (x : V₁ × V₂) (hx : x ≠ 0) : f₁ x.1 ≠ 0 ∨ f₂ x.2 ≠ 0 := by
    rcases compl_zero_prod_subset V₁ V₂ hx with h | h
    exacts [Or.inl ((map_ne_zero_iff _ f₁.injective).2 h),
      Or.inr ((map_ne_zero_iff _ f₂.injective).2 h)]
  rw [complZeroPairCross_def, complZeroPairCross_def, ContinuousLinearEquiv.complZeroPairIso_hom,
    ContinuousLinearEquiv.complZeroPairIso_hom, ContinuousLinearEquiv.complZeroPairIso_hom]
  refine (TopCat.singularRelativeCupPullback_singularCohomologyMap k u μ _ _ _ _
    isOpen_compl_singleton isOpen_compl_singleton isOpen_compl_singleton isOpen_compl_singleton
    _ _ _ ?hZ₁ p q n h g₁ g₂).trans ?_
  case hZ₁ => exact fun x hx ↦ hZ x hx
  refine Eq.trans ?_ (TopCat.singularCohomologyMap_singularRelativeCupPullback k u μ _ _ _ _ _ _
    _ ?hZ₂ p q n h g₁ g₂).symm
  case hZ₂ => exact fun x hx ↦ hZ x hx
  have h₁ : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) ≫
      TopCat.ofHom ((f₁ : V₁ →L[𝕜] W₁) : C(V₁, W₁)) =
      TopCat.ofHom (((f₁.prodCongr f₂ : (V₁ × V₂) ≃L[𝕜] (W₁ × W₂)) : (V₁ × V₂) →L[𝕜] (W₁ × W₂)) :
        C(V₁ × V₂, W₁ × W₂)) ≫ TopCat.ofHom (ContinuousMap.fst : C(W₁ × W₂, W₁)) :=
    TopCat.ext fun _ ↦ rfl
  have h₂ : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) ≫
      TopCat.ofHom ((f₂ : V₂ →L[𝕜] W₂) : C(V₂, W₂)) =
      TopCat.ofHom (((f₁.prodCongr f₂ : (V₁ × V₂) ≃L[𝕜] (W₁ × W₂)) : (V₁ × V₂) →L[𝕜] (W₁ × W₂)) :
        C(V₁ × V₂, W₁ × W₂)) ≫ TopCat.ofHom (ContinuousMap.snd : C(W₁ × W₂, W₂)) :=
    TopCat.ext fun _ ↦ rfl
  simp only [h₁, h₂]

end LinearEquiv

namespace VectorBundleOrientation

section Whitney

variable {B : Type w} [TopologicalSpace B]
  {F₁ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {E₁ : B → Type w} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {E₂ : B → Type w} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  {m n : ℕ} {K : Type w} [CommRing K] {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} K}
  [Module.Projective K R₁] [Module.Projective K R₂] [Module.Projective K R₃]

/-- **The Thom class of a direct sum is the product of the Thom classes.** Let `o₁` and `o₂` be
orientations of real vector bundles `E₁` and `E₂` over a common base, and normalize Thom classes by
orientations `ω₁`, `ω₂` of the model fibres and classes `g₁ ∈ Hᵖ(F₁, F₁ ∖ {0})`,
`g₂ ∈ H^q(F₂, F₂ ∖ {0})`. The Thom class of the direct sum `E₁ ⊕ E₂`, with the orientation
`o₁.prod o₂` and normalized by `ω₁.prod ω₂` and the product of `g₁` and `g₂`, is the product
`p₁^* U₁ ⌣ p₂^* U₂` of the Thom classes of `E₁` and `E₂` (`TauCeti.thomPairCup`). -/
theorem thomClassOfModel_prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n)) (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (ω₁ : Orientation ℝ F₁ (Fin m)) (ω₂ : Orientation ℝ F₂ (Fin n)) (u : R₃ ⟶ R₁ ⊗ R₂)
    (μ : M₁ ⊗ M₂ ⟶ M₃)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology R₁ K M₁
      (finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology R₂ K M₂
      (finrank ℝ F₂)) :
    (o₁.prod o₂ hm hn).thomClassOfModel (by rw [Fintype.card_fin, Module.finrank_prod, hm, hn])
        (ω₁.prod ω₂ hm hn) (complZeroPairCross K F₁ F₂ u μ _ _ _ Module.finrank_prod.symm g₁ g₂) =
      thomPairCup K F₁ E₁ F₂ E₂ u μ _ _ _ Module.finrank_prod.symm
        (o₁.thomClassOfModel (by rw [Fintype.card_fin, hm]) ω₁ g₁)
        (o₂.thomClassOfModel (by rw [Fintype.card_fin, hn]) ω₂ g₂) := by
  symm
  refine eq_thomClassOfModel_of_forall_exists _ _ _ _ fun b ↦ ?_
  let e₁ := trivializationAt F₁ E₁ b
  let e₂ := trivializationAt F₂ E₂ b
  have hb₁ : b ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb₂ : b ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt' b
  have hb : b ∈ (e₁.prod e₂).baseSet := ⟨hb₁, hb₂⟩
  -- Read each factor in its own preferred trivialization, and the sum in their product.
  obtain ⟨g₁', hg₁', hr₁⟩ :=
    exists_singularCohomologyMap_fiberThomPairMap_thomClassOfModel o₁
      (by rw [Fintype.card_fin, hm]) ω₁ g₁ e₁ hb₁
  obtain ⟨g₂', hg₂', hr₂⟩ :=
    exists_singularCohomologyMap_fiberThomPairMap_thomClassOfModel o₂
      (by rw [Fintype.card_fin, hn]) ω₂ g₂ e₂ hb₂
  refine ⟨e₁.prod e₂, inferInstance, hb,
    complZeroPairCross K F₁ F₂ u μ _ _ _ Module.finrank_prod.symm g₁' g₂', ?_, ?_⟩
  · -- The product trivialization reads the product orientation as the product of the readings,
    -- and reversing either factor reverses both the orientation and the product class.
    rw [prod_apply, Trivialization.mapOrientation_prod e₁ e₂ hb₁ hb₂ _ _ hm hn]
    rcases hg₁' with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> rcases hg₂' with ⟨h₂, rfl⟩ | ⟨h₂, rfl⟩ <;>
      rw [h₁, h₂]
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨Orientation.prod_neg_right _ _ _ _, map_neg _ _⟩
    · exact Or.inr ⟨Orientation.prod_neg_left _ _ _ _,
        by simp only [complZeroPairCross_def, map_neg, LinearMap.neg_apply]⟩
    · exact Or.inl ⟨Orientation.prod_neg_neg _ _ _ _,
        by simp only [complZeroPairCross_def, map_neg, LinearMap.neg_apply, neg_neg]⟩
  · -- The fibres are T1, being homeomorphic to the model fibres.
    have : T1Space (E₁ b) :=
      (e₁.continuousLinearEquivAt ℝ b hb₁).toHomeomorph.isEmbedding.t1Space
    have : T1Space (E₂ b) :=
      (e₂.continuousLinearEquivAt ℝ b hb₂).toHomeomorph.isEmbedding.t1Space
    rw [singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross, hr₁, hr₂,
      Trivialization.continuousLinearEquivAt_prod]
    exact complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom K u μ
      (e₁.continuousLinearEquivAt ℝ b hb₁) (e₂.continuousLinearEquivAt ℝ b hb₂) _ _ _ _ g₁' g₂'

/-- **The Whitney product formula for Euler classes.** For orientations `o₁` and `o₂` of real
vector bundles `E₁` and `E₂` over a common base, the Euler class of the direct sum `E₁ ⊕ E₂`, with
the orientation `o₁.prod o₂` and the Thom class normalized by `ω₁.prod ω₂` and the product of the
model classes `g₁` and `g₂`, is the cup product of the Euler classes of `E₁` and `E₂`:
`e(E₁ ⊕ E₂) = e(E₁) ⌣ e(E₂)`. -/
theorem eulerClass_thomClassOfModel_prod (o₁ : VectorBundleOrientation F₁ E₁ (Fin m))
    (o₂ : VectorBundleOrientation F₂ E₂ (Fin n)) (hm : finrank ℝ F₁ = m) (hn : finrank ℝ F₂ = n)
    (ω₁ : Orientation ℝ F₁ (Fin m)) (ω₂ : Orientation ℝ F₂ (Fin n)) (u : R₃ ⟶ R₁ ⊗ R₂)
    (μ : M₁ ⊗ M₂ ⟶ M₃)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology R₁ K M₁
      (finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology R₂ K M₂
      (finrank ℝ F₂)) :
    TauCeti.eulerClass R₃ K M₃ (F₁ × F₂) (E₁ ×ᵇ E₂) _
        ((o₁.prod o₂ hm hn).thomClassOfModel
          (by rw [Fintype.card_fin, Module.finrank_prod, hm, hn]) (ω₁.prod ω₂ hm hn)
          (complZeroPairCross K F₁ F₂ u μ _ _ _ Module.finrank_prod.symm g₁ g₂)) =
      (TopCat.of B).singularCup K u μ _ _ _ Module.finrank_prod.symm
        (TauCeti.eulerClass R₁ K M₁ F₁ E₁ _
          (o₁.thomClassOfModel (by rw [Fintype.card_fin, hm]) ω₁ g₁))
        (TauCeti.eulerClass R₂ K M₂ F₂ E₂ _
          (o₂.thomClassOfModel (by rw [Fintype.card_fin, hn]) ω₂ g₂)) := by
  rw [thomClassOfModel_prod, eulerClass_thomPairCup]

end Whitney

end VectorBundleOrientation

end TauCeti
