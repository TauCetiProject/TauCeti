/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Cross
public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# Products of Thom pair classes of direct sums

Let `E₁` and `E₂` be real vector bundles over a common base `B`, with model fibres `F₁` and `F₂`,
and let `E₁ ⊕ E₂` be their fibrewise direct sum `E₁ ×ᵇ E₂`, with model fibre `F₁ × F₂`. A nonzero
vector of `E₁ ⊕ E₂` has a nonzero first or second component, so the Thom pair
`(E₁ ⊕ E₂, (E₁ ⊕ E₂)₀)` receives the relative cup product
(`TopCat.singularRelativeCupPullback`) of classes pulled back along the two projections
`p₁ : E₁ ⊕ E₂ → E₁` and `p₂ : E₁ ⊕ E₂ → E₂`:

`Hᵖ(E₁, E₁₀) × H^q(E₂, E₂₀) ⟶ Hᵖ⁺^q(E₁ ⊕ E₂, (E₁ ⊕ E₂)₀)`,  `(a, b) ↦ p₁^* a ⌣ p₂^* b`

(`TauCeti.thomPairCup`). On the fibre over a point `b` it is the same product for the vector
spaces `E₁_b` and `E₂_b` (`TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup`), and its
Euler class is the cup product of the Euler classes
(`TauCeti.eulerClass_thomPairCup`): the zero section of `E₁ ⊕ E₂` followed by `pᵢ` is the zero
section of `Eᵢ`. For fibres with closed points, the restriction of `TauCeti.thomPairCup` to the
fibre over `b` is the product `TauCeti.complZeroPairCross` of local classes for `E₁_b` and `E₂_b`
(`TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross`). No
orientation is involved; the oriented form is in
`TauCeti.Topology.VectorBundle.Orientation.Whitney`. These hold in any abelian monoidal category
of coefficients.

## Main definitions

* `TauCeti.totalSpaceProdFst`, `TauCeti.totalSpaceProdSnd`: the projections of the total space of
  `E₁ ⊕ E₂` onto those of `E₁` and `E₂`.
* `TauCeti.thomPairCup`: the product of classes of the Thom pairs of `E₁` and `E₂`, a class of
  the Thom pair of `E₁ ⊕ E₂`.

## Main results

* `TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup` and
  `TauCeti.singularCohomologyMap_fiberThomPairMap_thomPairCup_eq_complZeroPairCross`: the
  restriction of the product to a fibre.
* `TauCeti.eulerClass_thomPairCup`: the Euler class of the product is the cup product of the
  Euler classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9, the product formula for Thom classes used in the proof of Property 9.6.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Set

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

end Prod

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
        (TopPair.singularCohomologyMap (fiberThomPairMap F₂ E₂ b) q a') := by
  rw [complZeroPairCross_def]
  exact singularCohomologyMap_fiberThomPairMap_thomPairCup k u μ p q n h b a a'

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
the Euler class of `thomPairCup a a'` is the cup product of the Euler classes of `a` and `a'`. -/
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
  -- The zero section of `E₁ ⊕ E₂` followed by the projection onto `Eᵢ` is the zero section of `Eᵢ`.
  refine congrArg₂ (fun x y ↦ (TopCat.of B).singularCup k u μ p q n h x y) ?_ ?_
  · rw [← zeroSectionHom_comp_totalSpaceProdFst F₁ E₁ F₂ E₂]
    exact (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp (R := R) (k := k)
      (M := M) (zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂)) (totalSpaceProdFst F₁ E₁ F₂ E₂) p) _).symm
  · rw [← zeroSectionHom_comp_totalSpaceProdSnd F₁ E₁ F₂ E₂]
    exact (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp (R := S) (k := k)
      (M := N) (zeroSectionHom (F₁ × F₂) (E₁ ×ᵇ E₂)) (totalSpaceProdSnd F₁ E₁ F₂ E₂) q) _).symm

end ThomPairCup

end TauCeti
