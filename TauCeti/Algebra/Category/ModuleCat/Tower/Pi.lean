/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Products of module towers

The limit and first derived limit of an arbitrary product of countable module towers are
the products of their limits and first derived limits. The comparisons are induced by the
actual projection morphisms of towers and are natural in componentwise tower maps.

For `lim¹`, the key point is that a family is in the image of the product difference map
exactly when every component is in the image of its difference map. No surjectivity or
Mittag–Leffler hypothesis on the transitions is needed, and the index type may be empty.

The difference-map description follows Weibel, *An introduction to homological algebra*,
§3.5. We use the existing `ModuleTower.limMap` and `ModuleTower.limOneMap` for the comparisons.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe u v

variable {R : Type u} [Ring R] {ι : Type v}

/-- The levelwise product of a family of module towers. This abbreviation retains the
actual function types of its terms, so coefficients can be evaluated at each factor. -/
abbrev pi (F : ι → ModuleTower.{v} R) : ModuleTower.{v} R where
  obj n := ModuleCat.of R (∀ i, (F i).obj n)
  map f := ModuleCat.ofHom (LinearMap.piMap fun i ↦ ((F i).map f).hom)

@[simp]
theorem pi_obj (F : ι → ModuleTower.{v} R) (n : ℕᵒᵖ) :
    (pi F).obj n = ModuleCat.of R (∀ i, (F i).obj n) := (rfl)

theorem pi_map_apply (F : ι → ModuleTower.{v} R) {n m : ℕᵒᵖ} (f : n ⟶ m)
    (x : (pi F).obj n) (i : ι) :
    ((pi F).map f).hom x i = ((F i).map f).hom (x i) := (rfl)

@[simp]
theorem pi_transition_apply (F : ι → ModuleTower.{v} R) (n : ℕ)
    (x : (pi F).obj (op (n + 1))) (i : ι) :
    (pi F).transition n x i = (F i).transition n (x i) := by
  rw [transition_def, transition_def]
  -- The product functor applies its transition map separately in each factor.
  rfl

/-- The projection from a product tower to one factor. -/
def piπ (F : ι → ModuleTower.{v} R) (i : ι) : pi F ⟶ F i where
  app _ := ModuleCat.ofHom (LinearMap.proj i)

@[simp]
theorem piπ_app_apply (F : ι → ModuleTower.{v} R) (i : ι) (n : ℕᵒᵖ)
    (x : (pi F).obj n) : ((piπ F i).app n).hom x = x i := (rfl)

/-- Projecting a product family of tower terms extracts the corresponding factor family. -/
@[simp]
theorem productMap_piπ (F : ι → ModuleTower.{v} R) (x : (pi F).Product) (i : ι) :
    productMap (piπ F i) x = fun n ↦ x n i := by
  funext n
  rw [productMap_apply]
  exact piπ_app_apply F i (op n) (x n)

/-- Assemble morphisms to the factors into a morphism to their product tower. -/
def piLift {F : ι → ModuleTower.{v} R} {G : ModuleTower.{v} R}
    (f : ∀ i, G ⟶ F i) : G ⟶ pi F where
  app n := ModuleCat.ofHom (LinearMap.pi fun i ↦ ((f i).app n).hom)
  naturality _ _ g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact congr($((f i).naturality g).hom x)

@[simp]
theorem piLift_app_apply {F : ι → ModuleTower.{v} R} {G : ModuleTower.{v} R}
    (f : ∀ i, G ⟶ F i) (n : ℕᵒᵖ) (x : G.obj n) (i : ι) :
    ((piLift f).app n).hom x i = ((f i).app n).hom x := (rfl)

@[reassoc (attr := simp)]
theorem piLift_comp_piπ {F : ι → ModuleTower.{v} R} {G : ModuleTower.{v} R}
    (f : ∀ i, G ⟶ F i) (i : ι) : piLift f ≫ piπ F i = f i := by
  ext n x
  rfl

/-- Morphisms into a product tower are determined by all their projections. -/
@[ext]
theorem pi_hom_ext {F : ι → ModuleTower.{v} R} {G : ModuleTower.{v} R}
    {f g : G ⟶ pi F} (h : ∀ i, f ≫ piπ F i = g ≫ piπ F i) : f = g := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  calc
    (f.app n).hom x i = ((piπ F i).app n).hom ((f.app n).hom x) :=
      (piπ_app_apply F i n _).symm
    _ = ((piπ F i).app n).hom ((g.app n).hom x) := congr($(h i).app n x)
    _ = (g.app n).hom x i := piπ_app_apply F i n _

/-- The fan of the levelwise product projections. -/
abbrev piFan (F : ι → ModuleTower.{v} R) : Limits.Fan F :=
  Limits.Fan.mk (pi F) (piπ F)

@[simp]
theorem piFan_pt (F : ι → ModuleTower.{v} R) : (piFan F).pt = pi F := (rfl)

@[simp]
theorem piFan_proj (F : ι → ModuleTower.{v} R) (i : ι) :
    (piFan F).proj i = piπ F i := (rfl)

/-- The levelwise product is a categorical product in the category of module towers. -/
def isLimitPiFan (F : ι → ModuleTower.{v} R) : Limits.IsLimit (piFan F) :=
  Limits.Fan.IsLimit.mk _ (fun s ↦ piLift s.proj)
    (fun s i ↦ piLift_comp_piπ s.proj i)
    (fun s _ hm ↦ pi_hom_ext fun i ↦ (hm i).trans (piLift_comp_piπ s.proj i).symm)

/-- The morphism between product towers induced by maps of their factors. -/
def piMap {F G : ι → ModuleTower.{v} R} (f : ∀ i, F i ⟶ G i) : pi F ⟶ pi G :=
  piLift fun i ↦ piπ F i ≫ f i

@[simp]
theorem piMap_app_apply {F G : ι → ModuleTower.{v} R} (f : ∀ i, F i ⟶ G i)
    (n : ℕᵒᵖ) (x : (pi F).obj n) (i : ι) :
    ((piMap f).app n).hom x i = ((f i).app n).hom (x i) := (rfl)

@[reassoc (attr := simp)]
theorem piMap_comp_piπ {F G : ι → ModuleTower.{v} R}
    (f : ∀ i, F i ⟶ G i) (i : ι) : piMap f ≫ piπ G i = piπ F i ≫ f i :=
  piLift_comp_piπ _ _

@[simp]
theorem piMap_id (F : ι → ModuleTower.{v} R) : piMap (fun i ↦ 𝟙 (F i)) = 𝟙 (pi F) := by
  apply pi_hom_ext
  intro i
  simp

@[simp]
theorem piMap_comp {F G H : ι → ModuleTower.{v} R}
    (f : ∀ i, F i ⟶ G i) (g : ∀ i, G i ⟶ H i) :
    piMap (fun i ↦ f i ≫ g i) = piMap f ≫ piMap g := by
  apply pi_hom_ext
  intro i
  simp [Category.assoc]

/-- The difference map on a product tower acts componentwise. -/
theorem pi_shift_apply (F : ι → ModuleTower.{v} R) (x : (pi F).Product) (n : ℕ) (i : ι) :
    (pi F).shift x n i = (F i).shift (fun k ↦ x k i) n := by
  rw [shift_apply, shift_apply]
  exact congrArg (fun y ↦ x n i - y) (pi_transition_apply F n (x (n + 1)) i)

/-- A family belongs to the image of the product difference map exactly when all of its
component families belong to the corresponding images. -/
theorem mem_range_pi_shift_iff (F : ι → ModuleTower.{v} R) (x : (pi F).Product) :
    x ∈ LinearMap.range (pi F).shift ↔
      ∀ i, (fun n ↦ x n i) ∈ LinearMap.range (F i).shift := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨fun n ↦ y n i, funext fun n ↦ (pi_shift_apply F y n i).symm⟩
  · intro h
    choose y hy using h
    refine ⟨fun n i ↦ y i n, ?_⟩
    funext n i
    simpa only [pi_shift_apply] using congrFun (hy i) n

/-- Limits commute with arbitrary products of module towers. The forward map is induced
by the projections of towers. -/
def limPiEquiv (F : ι → ModuleTower.{v} R) : (pi F).lim ≃ₗ[R] ∀ i, (F i).lim where
  toLinearMap := LinearMap.pi fun i ↦ limMap (piπ F i)
  invFun x := ⟨fun n i ↦ (x i : (F i).Product) n,
    (mem_lim (F := pi F)).mpr fun n ↦
      funext fun i ↦ (pi_transition_apply F n _ i).trans
        ((F i).transition_coe_lim_succ (x i) n)⟩
  left_inv x := by
    apply Subtype.ext
    funext n i
    exact congrFun ((coe_limMap_apply (piπ F i) x).trans (productMap_piπ F x i)) n
  right_inv x := by
    funext i
    apply Subtype.ext
    exact (coe_limMap_apply (piπ F i) _).trans (productMap_piπ F _ i)

@[simp]
theorem limPiEquiv_apply (F : ι → ModuleTower.{v} R) (x : (pi F).lim) (i : ι) :
    limPiEquiv F x i = limMap (piπ F i) x := (rfl)

@[simp]
theorem limPiEquiv_symm_apply (F : ι → ModuleTower.{v} R) (x : ∀ i, (F i).lim)
    (n : ℕ) (i : ι) :
    ((limPiEquiv F).symm x : (pi F).Product) n i = (x i : (F i).Product) n := (rfl)

/-- The limit-product comparison commutes with componentwise maps of towers. -/
theorem limPiEquiv_naturality {F G : ι → ModuleTower.{v} R} (f : ∀ i, F i ⟶ G i)
    (x : (pi F).lim) :
    limPiEquiv G (limMap (piMap f) x) = fun i ↦ limMap (f i) (limPiEquiv F x i) := by
  funext i
  simp only [limPiEquiv_apply, ← LinearMap.comp_apply, ← limMap_comp, piMap_comp_piπ]

private theorem limOne_pi_bijective (F : ι → ModuleTower.{v} R) :
    Function.Bijective (LinearMap.pi fun i ↦ limOneMap (piπ F i)) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hx : ∀ i, (fun n ↦ x n i) ∈ LinearMap.range (F i).shift := by
      intro i
      have hi := congrFun hz i
      apply (Submodule.Quotient.mk_eq_zero _).mp
      simpa only [LinearMap.pi_apply, limOneMap_mk, productMap_piπ, Pi.zero_apply] using hi
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((mem_range_pi_shift_iff F x).mpr hx)
  · intro z
    choose x hx using fun i ↦ Submodule.Quotient.mk_surjective _ (z i)
    refine ⟨Submodule.Quotient.mk (fun n i ↦ x i n), ?_⟩
    funext i
    simpa only [LinearMap.pi_apply, limOneMap_mk, productMap_piπ] using hx i

/-- First derived limits commute with arbitrary products of module towers. The comparison
is induced by the projections, with no restriction on the transition maps. -/
def limOnePiEquiv (F : ι → ModuleTower.{v} R) : (pi F).limOne ≃ₗ[R] ∀ i, (F i).limOne :=
  LinearEquiv.ofBijective (LinearMap.pi fun i ↦ limOneMap (piπ F i)) (limOne_pi_bijective F)

@[simp]
theorem limOnePiEquiv_apply (F : ι → ModuleTower.{v} R) (x : (pi F).limOne) (i : ι) :
    limOnePiEquiv F x i = limOneMap (piπ F i) x := (rfl)

/-- The inverse comparison assembles any family of quotient representatives. -/
@[simp]
theorem limOnePiEquiv_symm_mk (F : ι → ModuleTower.{v} R) (x : ∀ i, (F i).Product) :
    (limOnePiEquiv F).symm (fun i ↦ Submodule.Quotient.mk (x i)) =
      Submodule.Quotient.mk (fun n i ↦ x i n) := by
  apply (limOnePiEquiv F).injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp only [limOnePiEquiv_apply, limOneMap_mk, productMap_piπ]

/-- The first-derived-limit product comparison commutes with componentwise tower maps. -/
theorem limOnePiEquiv_naturality {F G : ι → ModuleTower.{v} R} (f : ∀ i, F i ⟶ G i)
    (x : (pi F).limOne) :
    limOnePiEquiv G (limOneMap (piMap f) x) =
      fun i ↦ limOneMap (f i) (limOnePiEquiv F x i) := by
  funext i
  simp only [limOnePiEquiv_apply, ← LinearMap.comp_apply, ← limOneMap_comp,
    piMap_comp_piπ]

end TauCeti.ModuleTower
