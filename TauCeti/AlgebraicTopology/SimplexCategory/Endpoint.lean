/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.II
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Widesubcategory
public import TauCeti.Order.Hom.Adjoint
import Mathlib.Order.Interval.Finset.Fin

/-!
# Endpoint-preserving subcategories of the simplex category and finite-ordinal dualities

This file defines the three endpoint-preserving wide subcategories of `SimplexCategory` (`Δ`):

* `SimplexCategory.Top` (`Δ_top`): all nonempty finite ordinals `⦋n⦌`, with monotone maps
  preserving the greatest element `Fin.last n`.
* `SimplexCategory.Bot` (`Δ_bot`): all nonempty finite ordinals `⦋n⦌`, with monotone maps
  preserving the least element `0`.
* `SimplexCategory.Boundary` (`Δ_∂`): all nonempty finite ordinals `⦋n⦌` (including `⦋0⦌`, where
  the two endpoints coincide), with monotone maps preserving both `0` and `Fin.last n`.

It then constructs the two strict category dualities required for the Schanuel–Street walking
adjunction:

1. **Top/bottom duality (`Δ_topᵒᵖ ≅ Δ_bot`)**: `SimplexCategory.topOpToBot` and
   `SimplexCategory.botToTopOp`, given by `OrderHom.leftAdjoint` and `OrderHom.rightAdjoint` on
   endpoint-preserving monotone maps between finite ordinals, are strict mutual inverses and
   package as `SimplexCategory.topOpIsoBot : Cat.of Topᵒᵖ ≅ Cat.of Bot`.
2. **Finite-ordinal cut duality (`Δ₊ᵒᵖ ≅ Δ_∂`)**: sending the ordinal with `n` elements (`∅` in
   `AugmentedSimplexCategory`, or `⦋k⦌` of cardinality `k + 1`) to its chain of `n + 1` cuts `⦋n⦌`
   (`⦋0⦌`, or `⦋k + 1⦌`) and a monotone map `α` to the cut-counting map
   `x ↦ #{i | (α i).castSucc < x}` factors `SimplexCategory.II.leftOp : Δᵒᵖ ⥤ Δ` through
   `SimplexCategory.iiOpToBoundary : Δᵒᵖ ⥤ Boundary`, extends to
   `SimplexCategory.augmentedOpToBoundary : AugmentedSimplexCategoryᵒᵖ ⥤ Boundary`, and admits a
   strict inverse `SimplexCategory.boundaryToAugmentedOp : Boundary ⥤ AugmentedSimplexCategoryᵒᵖ`
   via right adjoints, packaging as
   `SimplexCategory.augmentedOpIsoBoundary : Cat.of AugmentedSimplexCategoryᵒᵖ ≅ Cat.of Boundary`.

## References

* S. Schanuel and R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques **27** (1986), 81–83.
* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Proposition 3.3.4, Observation 3.3.6,
  and Remark 3.3.8.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

namespace Fin

/-- For `i : Fin (n + 1)`, the codegeneracy map `i.predAbove` is left adjoint to the coface map
`i.castSucc.succAbove`. -/
theorem galoisConnection_predAbove_castSucc_succAbove {n : ℕ} (i : Fin (n + 1)) :
    GaloisConnection i.predAbove i.castSucc.succAbove := by
  intro x y
  rcases le_or_gt x i.castSucc with hx | hx
  · rw [Fin.predAbove_of_le_castSucc i x hx, ← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]
    rcases lt_or_ge y i with hy | hy
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hy)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hy)]
      have h1 : (x : ℕ) ≤ y := by
        have hx' : (x : ℕ) ≤ i := hx
        have _ : (i : ℕ) ≤ y := hy
        omega
      exact iff_of_true (Fin.le_def.mpr h1)
        (Fin.le_def.mpr (by simpa only [Fin.val_succ] using Nat.le_succ_of_le h1))
  · rw [Fin.predAbove_of_castSucc_lt i x hx, ← Fin.succ_le_succ_iff,
      Fin.succ_pred _ (Fin.ne_zero_of_lt hx)]
    rcases lt_or_ge y i with hy | hy
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hy)]
      have _ : (i : ℕ) < x := hx
      have _ : (y : ℕ) < i := hy
      exact iff_of_false
        (not_le_of_gt <| Fin.lt_def.mpr <| by simp only [Fin.val_succ]; omega)
        (not_le_of_gt <| Fin.lt_def.mpr <| by simp only [Fin.val_castSucc]; omega)
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hy)]

/-- For `i : Fin (n + 1)`, the coface map `i.succ.succAbove` is left adjoint to the codegeneracy
map `i.predAbove`. -/
theorem galoisConnection_succ_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) :
    GaloisConnection i.succ.succAbove i.predAbove := by
  intro y x
  rcases le_or_gt x i.castSucc with hx | hx
  · rw [Fin.predAbove_of_le_castSucc i x hx]
    conv_rhs => rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]
    rcases le_or_gt y i with hy | hy
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hy)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hy)]
      have hx' : (x : ℕ) ≤ i := hx
      have _ : (i : ℕ) < y := hy
      exact iff_of_false
        (not_le_of_gt <| Fin.lt_def.mpr <| by simp only [Fin.val_succ]; omega)
        (not_le_of_gt <| Fin.lt_def.mpr <| by simp only [Fin.val_castSucc]; omega)
  · rw [Fin.predAbove_of_castSucc_lt i x hx]
    conv_rhs => rw [← Fin.succ_le_succ_iff, Fin.succ_pred _ (Fin.ne_zero_of_lt hx)]
    rcases le_or_gt y i with hy | hy
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hy)]
      have _ : (i : ℕ) < x := hx
      have _ : (y : ℕ) ≤ i := hy
      exact iff_of_true
        (Fin.le_def.mpr <| by simp only [Fin.val_castSucc]; omega)
        (Fin.le_def.mpr <| by simp only [Fin.val_succ]; omega)
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hy)]

end Fin

namespace SimplexCategory

/-! ### Endpoint-preserving morphism properties -/

/-- The property of a morphism in `SimplexCategory` preserving the initial vertex `0`. -/
def preservesZero : MorphismProperty SimplexCategory :=
  fun {_ _} f ↦ f.toOrderHom 0 = 0

/-- The property of a morphism in `SimplexCategory` preserving the final vertex `Fin.last`. -/
def preservesLast : MorphismProperty SimplexCategory :=
  fun {x y} f ↦ f.toOrderHom (Fin.last x.len) = Fin.last y.len

/-- The property of a morphism in `SimplexCategory` preserving both endpoints `0` and
`Fin.last`. -/
def preservesEndpoints : MorphismProperty SimplexCategory :=
  fun _ _ f ↦ preservesZero f ∧ preservesLast f

theorem preservesZero_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesZero f ↔ f.toOrderHom 0 = 0 :=
  Iff.rfl

theorem preservesLast_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesLast f ↔ f.toOrderHom (Fin.last x.len) = Fin.last y.len :=
  Iff.rfl

theorem preservesEndpoints_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesEndpoints f ↔
      f.toOrderHom 0 = 0 ∧ f.toOrderHom (Fin.last x.len) = Fin.last y.len :=
  Iff.rfl

instance : preservesZero.IsMultiplicative where
  id_mem _ := rfl
  comp_mem _ _ hf hg := (congrArg _ hf).trans hg

instance : preservesLast.IsMultiplicative where
  id_mem _ := rfl
  comp_mem _ _ hf hg := (congrArg _ hf).trans hg

instance : preservesEndpoints.IsMultiplicative where
  id_mem x := ⟨preservesZero.id_mem x, preservesLast.id_mem x⟩
  comp_mem f g hf hg := ⟨preservesZero.comp_mem f g hf.1 hg.1, preservesLast.comp_mem f g hf.2 hg.2⟩

@[simp]
theorem preservesZero_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesZero (δ i) ↔ i ≠ 0 := by
  rw [preservesZero_iff]
  change i.succAbove 0 = 0 ↔ i ≠ 0
  refine ⟨fun h hi ↦ by simp [hi] at h, fun hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
  exact Fin.succ_succAbove_zero j

@[simp]
theorem preservesLast_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesLast (δ i) ↔ i ≠ Fin.last (n + 1) := by
  rw [preservesLast_iff]
  change i.succAbove (Fin.last n) = Fin.last (n + 1) ↔ i ≠ Fin.last (n + 1)
  refine ⟨fun h hi ↦ by simp [hi, Fin.ext_iff] at h, fun hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
  exact Fin.succAbove_ne_last_last (Fin.castSucc_lt_last j).ne

@[simp]
theorem preservesEndpoints_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesEndpoints (δ i) ↔ i ≠ 0 ∧ i ≠ Fin.last (n + 1) := by
  rw [preservesEndpoints_iff, ← preservesZero_iff, ← preservesLast_iff, preservesZero_δ_iff,
    preservesLast_δ_iff]

@[simp]
theorem preservesZero_σ {n : ℕ} (i : Fin (n + 1)) : preservesZero (σ i) := by
  rw [preservesZero_iff]
  exact Fin.predAbove_right_zero (i := i)

@[simp]
theorem preservesLast_σ {n : ℕ} (i : Fin (n + 1)) : preservesLast (σ i) := by
  rw [preservesLast_iff]
  exact Fin.predAbove_right_last

@[simp]
theorem preservesEndpoints_σ {n : ℕ} (i : Fin (n + 1)) : preservesEndpoints (σ i) :=
  ⟨preservesZero_σ i, preservesLast_σ i⟩

theorem preservesZero_const_zero (x y : SimplexCategory) :
    preservesZero (const x y 0) :=
  rfl

theorem preservesLast_const_last (x y : SimplexCategory) :
    preservesLast (const x y (Fin.last y.len)) :=
  rfl

@[simp]
theorem preservesEndpoints_const_to_zero (x : SimplexCategory) :
    preservesEndpoints (const x ⦋0⦌ 0) :=
  ⟨rfl, Subsingleton.elim (α := Fin 1) _ _⟩

@[simp]
theorem preservesZero_rev_map_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesZero (rev.map f) ↔ preservesLast f := by
  rw [preservesZero_iff, preservesLast_iff, rev_map_apply, Fin.rev_zero]
  change (f.toOrderHom (Fin.last x.len)).rev = 0 ↔ f.toOrderHom (Fin.last x.len) = Fin.last y.len
  rw [← Fin.rev_last, Fin.rev_inj]

@[simp]
theorem preservesLast_rev_map_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesLast (rev.map f) ↔ preservesZero f := by
  rw [preservesLast_iff, preservesZero_iff, rev_map_apply, Fin.rev_last]
  change (f.toOrderHom 0).rev = Fin.last y.len ↔ f.toOrderHom 0 = 0
  rw [← Fin.rev_zero, Fin.rev_inj]

@[simp]
theorem preservesEndpoints_rev_map_iff {x y : SimplexCategory} (f : x ⟶ y) :
    preservesEndpoints (rev.map f) ↔ preservesEndpoints f := by
  rw [preservesEndpoints_iff, preservesEndpoints_iff, ← preservesZero_iff, ← preservesLast_iff,
    ← preservesZero_iff, ← preservesLast_iff, preservesZero_rev_map_iff,
    preservesLast_rev_map_iff, and_comm]

/-! ### Endpoint wide subcategories -/

/-- The wide subcategory `Δ_top` of `SimplexCategory` whose morphisms preserve the greatest
element `Fin.last`. -/
abbrev Top : Type := WideSubcategory preservesLast

/-- The wide subcategory `Δ_bot` of `SimplexCategory` whose morphisms preserve the least element
`0`. -/
abbrev Bot : Type := WideSubcategory preservesZero

/-- The wide subcategory `Δ_∂` of `SimplexCategory` (including `⦋0⦌`) whose morphisms preserve both
endpoints `0` and `Fin.last`. -/
abbrev Boundary : Type := WideSubcategory preservesEndpoints

namespace Top

/-- The faithful inclusion `Δ_top ⥤ Δ`. -/
def inclusion : Top ⥤ SimplexCategory := wideSubcategoryInclusion preservesLast

instance : inclusion.Faithful := inferInstanceAs (wideSubcategoryInclusion preservesLast).Faithful

@[simp]
theorem inclusion_obj (x : Top) : inclusion.obj x = x.obj := rfl

@[simp]
theorem inclusion_map {x y : Top} (f : x ⟶ y) : inclusion.map f = f.hom := rfl

/-- Construct a morphism in `Top` from a morphism in `SimplexCategory` preserving the greatest
element. -/
def homMk {x y : Top} (f : x.obj ⟶ y.obj)
    (hf : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) : x ⟶ y :=
  ⟨f, hf⟩

@[simp]
theorem homMk_hom {x y : Top} (f : x.obj ⟶ y.obj)
    (hf : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) :
    (homMk f hf).hom = f :=
  rfl

@[simp]
theorem toOrderHom_last {x y : Top} (f : x ⟶ y) :
    f.hom.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len :=
  f.property

/-- Restricted coface maps `δ i.castSucc : ⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ_top`, omitting a non-last
vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n⦌⟩ : Top) ⟶ ⟨⦋n + 1⦌⟩ :=
  ⟨SimplexCategory.δ i.castSucc,
    (preservesLast_δ_iff i.castSucc).mpr (Fin.castSucc_lt_last i).ne⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_top`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : Top) ⟶ ⟨⦋n⦌⟩ :=
  ⟨SimplexCategory.σ i, preservesLast_σ i⟩

@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) : (Top.δ i).hom = SimplexCategory.δ i.castSucc :=
  rfl

@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) : (Top.σ i).hom = SimplexCategory.σ i :=
  rfl

/-- `⟨⦋0⦌⟩` is terminal in `Top`. -/
instance {x : Top} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := ⟨const x.obj ⦋0⦌ 0, Subsingleton.elim (α := Fin 1) _ _⟩
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

theorem δ_zero_hom_zero : (Top.δ (0 : Fin 1)).hom.toOrderHom 0 = 1 :=
  rfl

theorem δ_zero_comp_σ_zero : Top.δ (0 : Fin 1) ≫ Top.σ 0 = 𝟙 _ :=
  WideSubcategory.hom_ext _ (δ_comp_σ_self (i := (0 : Fin 1)))

end Top

namespace Bot

/-- The faithful inclusion `Δ_bot ⥤ Δ`. -/
def inclusion : Bot ⥤ SimplexCategory := wideSubcategoryInclusion preservesZero

instance : inclusion.Faithful := inferInstanceAs (wideSubcategoryInclusion preservesZero).Faithful

@[simp]
theorem inclusion_obj (x : Bot) : inclusion.obj x = x.obj := rfl

@[simp]
theorem inclusion_map {x y : Bot} (f : x ⟶ y) : inclusion.map f = f.hom := rfl

/-- Construct a morphism in `Bot` from a morphism in `SimplexCategory` preserving `0`. -/
def homMk {x y : Bot} (f : x.obj ⟶ y.obj) (hf : f.toOrderHom 0 = 0) : x ⟶ y :=
  ⟨f, hf⟩

@[simp]
theorem homMk_hom {x y : Bot} (f : x.obj ⟶ y.obj) (hf : f.toOrderHom 0 = 0) :
    (homMk f hf).hom = f :=
  rfl

@[simp]
theorem toOrderHom_zero {x y : Bot} (f : x ⟶ y) : f.hom.toOrderHom 0 = 0 :=
  f.property

/-- Restricted coface maps `δ i.succ : ⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ_bot`, omitting a nonzero vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n⦌⟩ : Bot) ⟶ ⟨⦋n + 1⦌⟩ :=
  ⟨SimplexCategory.δ i.succ, (preservesZero_δ_iff i.succ).mpr (Fin.succ_ne_zero i)⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_bot`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : Bot) ⟶ ⟨⦋n⦌⟩ :=
  ⟨SimplexCategory.σ i, preservesZero_σ i⟩

@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) : (Bot.δ i).hom = SimplexCategory.δ i.succ :=
  rfl

@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) : (Bot.σ i).hom = SimplexCategory.σ i :=
  rfl

/-- `⟨⦋0⦌⟩` is terminal in `Bot`. -/
instance {x : Bot} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := ⟨const x.obj ⦋0⦌ 0, rfl⟩
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

theorem δ_zero_hom_zero : (Bot.δ (0 : Fin 1)).hom.toOrderHom 0 = 0 :=
  rfl

theorem δ_zero_comp_σ_zero : Bot.δ (0 : Fin 1) ≫ Bot.σ 0 = 𝟙 _ :=
  WideSubcategory.hom_ext _ (δ_comp_σ_succ (i := (0 : Fin 1)))

end Bot

namespace Boundary

/-- The faithful inclusion `Δ_∂ ⥤ Δ`. -/
def inclusion : Boundary ⥤ SimplexCategory := wideSubcategoryInclusion preservesEndpoints

instance : inclusion.Faithful :=
  inferInstanceAs (wideSubcategoryInclusion preservesEndpoints).Faithful

@[simp]
theorem inclusion_obj (x : Boundary) : inclusion.obj x = x.obj := rfl

@[simp]
theorem inclusion_map {x y : Boundary} (f : x ⟶ y) : inclusion.map f = f.hom := rfl

/-- The faithful inclusion `Δ_∂ ⥤ Δ_top`. -/
def toTop : Boundary ⥤ Top where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom, f.property.2⟩

instance : toTop.Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) h)

@[simp]
theorem toTop_obj (x : Boundary) : toTop.obj x = ⟨x.obj⟩ := rfl

@[simp]
theorem toTop_map_hom {x y : Boundary} (f : x ⟶ y) : (toTop.map f).hom = f.hom := rfl

theorem toTop_comp_inclusion : toTop ⋙ Top.inclusion = inclusion := rfl

/-- The faithful inclusion `Δ_∂ ⥤ Δ_bot`. -/
def toBot : Boundary ⥤ Bot where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom, f.property.1⟩

instance : toBot.Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) h)

@[simp]
theorem toBot_obj (x : Boundary) : toBot.obj x = ⟨x.obj⟩ := rfl

@[simp]
theorem toBot_map_hom {x y : Boundary} (f : x ⟶ y) : (toBot.map f).hom = f.hom := rfl

theorem toBot_comp_inclusion : toBot ⋙ Bot.inclusion = inclusion := rfl

/-- Construct a morphism in `Boundary` from a morphism in `SimplexCategory` preserving both
endpoints `0` and `Fin.last`. -/
def homMk {x y : Boundary} (f : x.obj ⟶ y.obj) (h0 : f.toOrderHom 0 = 0)
    (hlast : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) : x ⟶ y :=
  ⟨f, ⟨h0, hlast⟩⟩

@[simp]
theorem homMk_hom {x y : Boundary} (f : x.obj ⟶ y.obj) (h0 : f.toOrderHom 0 = 0)
    (hlast : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) :
    (homMk f h0 hlast).hom = f :=
  rfl

@[simp]
theorem toOrderHom_zero {x y : Boundary} (f : x ⟶ y) : f.hom.toOrderHom 0 = 0 :=
  f.property.1

@[simp]
theorem toOrderHom_last {x y : Boundary} (f : x ⟶ y) :
    f.hom.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len :=
  f.property.2

/-- Restricted inner coface maps `δ i.succ.castSucc : ⦋n + 1⦌ ⟶ ⦋n + 2⦌` in `Δ_∂`, omitting
a strictly interior vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋n + 2⦌⟩ :=
  ⟨SimplexCategory.δ i.succ.castSucc, (preservesEndpoints_δ_iff i.succ.castSucc).mpr
    ⟨Fin.castSucc_ne_zero_iff.mpr (Fin.succ_ne_zero i),
      (Fin.castSucc_lt_last i.succ).ne⟩⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_∂`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋n⦌⟩ :=
  ⟨SimplexCategory.σ i, preservesEndpoints_σ i⟩

@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (Boundary.δ i).hom = SimplexCategory.δ i.succ.castSucc :=
  rfl

@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) : (Boundary.σ i).hom = SimplexCategory.σ i :=
  rfl

/-- The unique morphism to the terminal object `⟨⦋0⦌⟩` in `Boundary`. -/
def constToZero (x : SimplexCategory) : (⟨x⟩ : Boundary) ⟶ ⟨⦋0⦌⟩ :=
  ⟨const x ⦋0⦌ 0, preservesEndpoints_const_to_zero x⟩

@[simp]
theorem constToZero_hom (x : SimplexCategory) : (constToZero x).hom = const x ⦋0⦌ 0 :=
  rfl

/-- `⟨⦋0⦌⟩` is terminal in `Boundary`. -/
instance {x : Boundary} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := constToZero x.obj
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

/-- There is no endpoint-preserving map `⦋0⦌ ⟶ ⦋m + 1⦌`. -/
theorem isEmpty_hom_zero_succ (m : ℕ) : IsEmpty ((⟨⦋0⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩) :=
  ⟨fun f ↦ by
    have h0 : f.hom.toOrderHom 0 = 0 := f.property.1
    have hl : f.hom.toOrderHom 0 = Fin.last (m + 1) := f.property.2
    exact (Fin.last_pos (n := m)).ne' (hl.symm.trans h0)⟩

end Boundary

/-! ### Top/bottom duality (`Δ_topᵒᵖ ≅ Δ_bot`) -/

/-- The duality functor `Δ_topᵒᵖ ⥤ Δ_bot` taking each top-preserving map to its left adjoint. -/
def topOpToBot : Topᵒᵖ ⥤ Bot where
  obj x := ⟨x.unop.obj⟩
  map f := Bot.homMk (Hom.mk (f.unop.hom.toOrderHom.leftAdjoint f.unop.property))
    (f.unop.hom.toOrderHom.leftAdjoint_bot f.unop.property)
  map_id _ := WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by simp [OrderHom.leftAdjoint_id]
  map_comp f g := WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp [OrderHom.leftAdjoint_comp g.unop.property f.unop.property]
    rfl

/-- The duality functor `Δ_bot ⥤ Δ_topᵒᵖ` taking each bottom-preserving map to its right
adjoint. -/
def botToTopOp : Bot ⥤ Topᵒᵖ where
  obj x := op ⟨x.obj⟩
  map f := Quiver.Hom.op <| Top.homMk
    (Hom.mk (f.hom.toOrderHom.rightAdjoint f.property))
    (f.hom.toOrderHom.rightAdjoint_top f.property)
  map_id _ := Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp [OrderHom.rightAdjoint_id]
  map_comp f g := Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp [OrderHom.rightAdjoint_comp f.property g.property]
    rfl

@[simp]
theorem topOpToBot_obj (x : Topᵒᵖ) : topOpToBot.obj x = ⟨x.unop.obj⟩ := (rfl)

@[simp]
theorem botToTopOp_obj (x : Bot) : botToTopOp.obj x = op ⟨x.obj⟩ := (rfl)

@[simp]
theorem topOpToBot_map_toOrderHom {x y : Topᵒᵖ} (f : x ⟶ y) :
    (topOpToBot.map f).hom.toOrderHom = f.unop.hom.toOrderHom.leftAdjoint f.unop.property :=
  rfl

@[simp]
theorem botToTopOp_map_toOrderHom {x y : Bot} (f : x ⟶ y) :
    (botToTopOp.map f).unop.hom.toOrderHom = f.hom.toOrderHom.rightAdjoint f.property :=
  rfl

@[simp]
theorem topOpToBot_map_δ {n : ℕ} (i : Fin (n + 1)) :
    topOpToBot.map (Top.δ i).op = Bot.σ i :=
  WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.leftAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_predAbove_castSucc_succAbove i)

@[simp]
theorem topOpToBot_map_σ {n : ℕ} (i : Fin (n + 1)) :
    topOpToBot.map (Top.σ i).op = Bot.δ i :=
  WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.leftAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_succ_succAbove_predAbove i)

@[simp]
theorem botToTopOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    botToTopOp.map (Bot.δ i) = (Top.σ i).op :=
  Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.rightAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_succ_succAbove_predAbove i)

@[simp]
theorem botToTopOp_map_σ {n : ℕ} (i : Fin (n + 1)) :
    botToTopOp.map (Bot.σ i) = (Top.δ i).op :=
  Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.rightAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_predAbove_castSucc_succAbove i)

/-- `topOpToBot` and `botToTopOp` are strict left/right inverses on `Δ_topᵒᵖ`. -/
@[simp]
theorem topOpToBot_comp_botToTopOp : topOpToBot ⋙ botToTopOp = 𝟭 Topᵒᵖ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
      OrderHom.rightAdjoint_leftAdjoint f.unop.hom.toOrderHom f.unop.property

/-- `botToTopOp` and `topOpToBot` are strict left/right inverses on `Δ_bot`. -/
@[simp]
theorem botToTopOp_comp_topOpToBot : botToTopOp ⋙ topOpToBot = 𝟭 Bot :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
      OrderHom.leftAdjoint_rightAdjoint f.hom.toOrderHom f.property

/-- Strict isomorphism of categories `Δ_topᵒᵖ ≅ Δ_bot`. -/
def topOpIsoBot : Cat.of Topᵒᵖ ≅ Cat.of Bot where
  hom := topOpToBot.toCatHom
  inv := botToTopOp.toCatHom
  hom_inv_id := Cat.ext topOpToBot_comp_botToTopOp
  inv_hom_id := Cat.ext botToTopOp_comp_topOpToBot

@[simp]
theorem topOpIsoBot_hom_toFunctor : topOpIsoBot.hom.toFunctor = topOpToBot := rfl

@[simp]
theorem topOpIsoBot_inv_toFunctor : topOpIsoBot.inv.toFunctor = botToTopOp := rfl

/-! ### Cut formula, Galois property, and factorization of `SimplexCategory.II` -/

namespace II

/-- Cut-counting formula for `SimplexCategory.II.map'`: for `α : Fin (k + 1) →o Fin (m + 1)` and
cut `x : Fin (m + 2)`, `(II.map' α x : ℕ)` counts the indices `i` with `(α i).castSucc < x`. -/
theorem map'_val_eq_card {k m : ℕ} (α : Fin (k + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    (map' α x : ℕ) = (Finset.univ.filter fun i : Fin (k + 1) ↦ (α i).castSucc < x).card := by
  obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' α x)
  · rw [hy, Fin.val_castSucc]
    rw [map'_eq_castSucc_iff] at hy
    have hfilt : Finset.univ.filter (fun i : Fin (k + 1) ↦ (α i).castSucc < x) =
        Finset.Iio y := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
      refine ⟨fun hi ↦ ?_, fun hi ↦ hy.2 i hi⟩
      by_contra hnot
      have hle : y ≤ i := Fin.le_def.mpr (not_lt.mp hnot)
      exact hi.not_ge (hy.1.trans (Fin.castSucc_le_castSucc_iff.mpr (α.monotone hle)))
    rw [hfilt, Fin.card_Iio]
  · rw [hx, Fin.val_last]
    rw [map'_eq_last_iff] at hx
    rw [Finset.filter_eq_self.mpr (fun i _ ↦ hx i), Finset.card_univ, Fintype.card_fin]

/-- Galois characterization of `SimplexCategory.II.map'`:
`II.map' α x ≤ y.castSucc ↔ x ≤ (α y).castSucc`. -/
theorem map'_le_castSucc_iff {k m : ℕ} (α : Fin (k + 1) →o Fin (m + 1)) (x : Fin (m + 2))
    (y : Fin (k + 1)) :
    map' α x ≤ y.castSucc ↔ x ≤ (α y).castSucc := by
  constructor
  · intro h
    have hmem := Finset.min'_mem (finset α x) (nonempty_finset α x)
    rcases (mem_finset_iff α x (map' α x)).mp hmem with hlast | ⟨hne, hx⟩
    · exact absurd (hlast ▸ h) (Fin.castSucc_lt_last y).not_ge
    · have hle : (map' α x).castPred hne ≤ y :=
        Fin.castSucc_le_castSucc_iff.mp (by simpa [Fin.castSucc_castPred] using h)
      exact hx.trans (Fin.castSucc_le_castSucc_iff.mpr (α.monotone hle))
  · intro h
    exact Finset.min'_le (finset α x) y.castSucc ((castSucc_mem_finset_iff α x y).mpr h)

end II

/-- Factorization of `SimplexCategory.II.leftOp : Δᵒᵖ ⥤ Δ` through the boundary subcategory
`Boundary`. -/
def iiOpToBoundary : SimplexCategoryᵒᵖ ⥤ Boundary where
  obj x := ⟨⦋x.unop.len + 1⦌⟩
  map f := Boundary.homMk (II.map f.unop).unop (II.map'_zero _) (II.map'_last _)
  map_id x := WideSubcategory.hom_ext _ <| congrArg Quiver.Hom.unop (II.map_id x.unop)
  map_comp f g := WideSubcategory.hom_ext _ <| congrArg Quiver.Hom.unop (II.map_comp g.unop f.unop)

@[simp]
theorem iiOpToBoundary_obj (x : SimplexCategoryᵒᵖ) :
    iiOpToBoundary.obj x = ⟨⦋x.unop.len + 1⦌⟩ :=
  (rfl)

@[simp]
theorem iiOpToBoundary_map_hom {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    (iiOpToBoundary.map f).hom = (II.map f.unop).unop :=
  rfl

@[simp]
theorem iiOpToBoundary_comp_inclusion : iiOpToBoundary ⋙ Boundary.inclusion = II.leftOp :=
  rfl

@[simp]
theorem iiOpToBoundary_map_δ {n : ℕ} (i : Fin (n + 2)) :
    iiOpToBoundary.map (SimplexCategory.δ i).op = Boundary.σ i :=
  WideSubcategory.hom_ext _ (congrArg Quiver.Hom.unop (II_δ i))

@[simp]
theorem iiOpToBoundary_map_σ {n : ℕ} (i : Fin (n + 1)) :
    iiOpToBoundary.map (SimplexCategory.σ i).op = Boundary.δ i :=
  WideSubcategory.hom_ext _ (congrArg Quiver.Hom.unop (II_σ i))

/-! ### Finite-ordinal cut duality (`Δ₊ᵒᵖ ≅ Δ_∂`) -/

/-- The finite-ordinal cut functor `Δ₊ᵒᵖ ⥤ Δ_∂` sending `∅` (`WithInitial.star`) to `⦋0⦌` and
`⦋k⦌` (`WithInitial.of ⦋k⦌`) to `⦋k + 1⦌`. -/
def augmentedOpToBoundary : AugmentedSimplexCategoryᵒᵖ ⥤ Boundary where
  obj x := match x with
    | ⟨.of y⟩ => ⟨⦋y.len + 1⦌⟩
    | ⟨.star⟩ => ⟨⦋0⦌⟩
  map {x y} f := match x, y with
    | ⟨.of a⟩, ⟨.of b⟩ =>
      Boundary.homMk (II.map (f.unop : b ⟶ a)).unop (II.map'_zero _) (II.map'_last _)
    | ⟨.of a⟩, ⟨.star⟩ => Boundary.constToZero ⦋a.len + 1⦌
    | ⟨.star⟩, ⟨.star⟩ => 𝟙 _
    | ⟨.star⟩, ⟨.of _⟩ => (WithInitial.false_of_to_star f.unop).elim
  map_id x := by
    rcases x with ⟨a | _⟩
    · exact WideSubcategory.hom_ext _ (congrArg Quiver.Hom.unop (II.map_id a))
    · rfl
  map_comp {x y z} f g := by
    rcases x with ⟨a | _⟩ <;> rcases y with ⟨b | _⟩ <;> rcases z with ⟨c | _⟩
    · exact WideSubcategory.hom_ext _
        (congrArg Quiver.Hom.unop (II.map_comp (g.unop : c ⟶ b) (f.unop : b ⟶ a)))
    · exact Subsingleton.elim _ _
    · exact (WithInitial.false_of_to_star g.unop).elim
    · exact Subsingleton.elim _ _
    · exact (WithInitial.false_of_to_star f.unop).elim
    · exact (WithInitial.false_of_to_star f.unop).elim
    · exact (WithInitial.false_of_to_star g.unop).elim
    · exact Subsingleton.elim _ _

@[simp]
theorem augmentedOpToBoundary_obj_star :
    augmentedOpToBoundary.obj (op (WithInitial.star : AugmentedSimplexCategory)) = ⟨⦋0⦌⟩ :=
  (rfl)

@[simp]
theorem augmentedOpToBoundary_obj_of (x : SimplexCategory) :
    augmentedOpToBoundary.obj (op (WithInitial.of x)) = ⟨⦋x.len + 1⦌⟩ :=
  (rfl)

@[simp]
theorem augmentedOpToBoundary_map_of {x y : SimplexCategory} (f : y ⟶ x) :
    augmentedOpToBoundary.map (AugmentedSimplexCategory.inclusion.map f).op =
      iiOpToBoundary.map f.op :=
  rfl

@[simp]
theorem inclusion_op_comp_augmentedOpToBoundary :
    AugmentedSimplexCategory.inclusion.op ⋙ augmentedOpToBoundary = iiOpToBoundary :=
  rfl

theorem augmentedOpToBoundary_map_homTo (x : SimplexCategory) :
    augmentedOpToBoundary.map (WithInitial.homTo x).op =
      Boundary.constToZero ⦋x.len + 1⦌ :=
  rfl

theorem augmentedOpToBoundary_map_δ {n : ℕ} (i : Fin (n + 2)) :
    augmentedOpToBoundary.map (AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i)).op =
      Boundary.σ i :=
  (augmentedOpToBoundary_map_of _).trans (iiOpToBoundary_map_δ i)

theorem augmentedOpToBoundary_map_σ {n : ℕ} (i : Fin (n + 1)) :
    augmentedOpToBoundary.map (AugmentedSimplexCategory.inclusion.map (SimplexCategory.σ i)).op =
      Boundary.δ i :=
  (augmentedOpToBoundary_map_of _).trans (iiOpToBoundary_map_σ i)

/-- Given an endpoint-preserving map `g : ⦋n + 1⦌ ⟶ ⦋m + 1⦌`, its right adjoint preserves `Fin.last`
and maps non-last elements below `Fin.last (n + 1)`, hence cuts down to `⦋m⦌ ⟶ ⦋n⦌`. -/
def Boundary.cutInv {n m : ℕ} (g : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩) : ⦋m⦌ ⟶ ⦋n⦌ :=
  Hom.mk
    { toFun y := (g.hom.toOrderHom.rightAdjoint g.property.1 y.castSucc).castPred fun h ↦ by
        have hle : Fin.last (n + 1) ≤ g.hom.toOrderHom.rightAdjoint g.property.1 y.castSucc :=
          le_of_eq h.symm
        have hle' : g.hom.toOrderHom (Fin.last (n + 1)) ≤ y.castSucc :=
          (OrderHom.le_rightAdjoint_iff _ _).mp hle
        rw [Boundary.toOrderHom_last] at hle'
        exact (Fin.castSucc_lt_last y).not_ge hle'
      monotone' _ _ h :=
        Fin.castSucc_le_castSucc_iff.mp <| by
          simpa only [Fin.castSucc_castPred] using
            (g.hom.toOrderHom.rightAdjoint g.property.1).monotone
              (Fin.castSucc_le_castSucc_iff.mpr h) }

/-- Applying `SimplexCategory.II` to `Boundary.cutInv g` recovers `g`. -/
@[simp]
theorem Boundary.ii_cutInv {n m : ℕ} (g : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩) :
    (II.map (Boundary.cutInv g)).unop = g.hom := by
  refine Hom.ext _ _ (OrderHom.ext _ _ (funext fun (x : Fin (n + 2)) ↦ ?_))
  change II.map' (Boundary.cutInv g).toOrderHom x = g.hom.toOrderHom x
  apply le_antisymm
  · by_contra! hlt
    obtain ⟨y, hy⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hlt)
    have hcast : ((Boundary.cutInv g).toOrderHom y).castSucc =
        g.hom.toOrderHom.rightAdjoint g.property.1 y.castSucc :=
      Fin.ext rfl
    have hle1 : ((Boundary.cutInv g).toOrderHom y).castSucc ≥ x :=
      hcast ▸ (OrderHom.le_rightAdjoint_iff _ _).mpr hy.symm.le
    have hle2 : II.map' (Boundary.cutInv g).toOrderHom x ≤ y.castSucc :=
      (II.map'_le_castSucc_iff (Boundary.cutInv g).toOrderHom x y).mpr hle1
    exact hlt.not_ge (hy ▸ hle2)
  · by_contra! hlt
    obtain ⟨y, hy⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hlt)
    have hle : II.map' (Boundary.cutInv g).toOrderHom x ≤ y.castSucc := hy.symm.le
    have hle1 : x ≤ ((Boundary.cutInv g).toOrderHom y).castSucc :=
      (II.map'_le_castSucc_iff (Boundary.cutInv g).toOrderHom x y).mp hle
    have hcast : ((Boundary.cutInv g).toOrderHom y).castSucc =
        g.hom.toOrderHom.rightAdjoint g.property.1 y.castSucc :=
      Fin.ext rfl
    have hle2 : g.hom.toOrderHom x ≤ y.castSucc :=
      (OrderHom.le_rightAdjoint_iff _ _).mp (hcast ▸ hle1)
    exact hlt.not_ge (hy ▸ hle2)

/-- `Boundary.cutInv` is left inverse to `SimplexCategory.II`. -/
@[simp]
theorem Boundary.cutInv_ii {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    Boundary.cutInv (Boundary.homMk (II.map α).unop (II.map'_zero _) (II.map'_last _)) = α := by
  let g : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩ :=
    Boundary.homMk (II.map α).unop (II.map'_zero _) (II.map'_last _)
  change Boundary.cutInv g = α
  refine Hom.ext _ _ (OrderHom.ext _ _ (funext fun (y : Fin (m + 1)) ↦ ?_))
  have hcast : ((Boundary.cutInv g).toOrderHom y).castSucc =
      g.hom.toOrderHom.rightAdjoint g.property.1 y.castSucc :=
    Fin.ext rfl
  apply le_antisymm
  · by_contra! hlt
    have hsucc : (α.toOrderHom y).succ ≤ ((Boundary.cutInv g).toOrderHom y).castSucc :=
      Fin.le_def.mpr (Nat.succ_le_of_lt (Fin.lt_def.mp hlt))
    have hle1 : g.hom.toOrderHom (α.toOrderHom y).succ ≤ y.castSucc :=
      (OrderHom.le_rightAdjoint_iff _ _).mp (hcast ▸ hsucc)
    change II.map' α.toOrderHom (α.toOrderHom y).succ ≤ y.castSucc at hle1
    have hle2 : (α.toOrderHom y).succ ≤ (α.toOrderHom y).castSucc :=
      (II.map'_le_castSucc_iff α.toOrderHom (α.toOrderHom y).succ y).mp hle1
    exact (Fin.castSucc_lt_succ (i := α.toOrderHom y)).not_ge hle2
  · rw [← Fin.castSucc_le_castSucc_iff, hcast]
    refine (OrderHom.le_rightAdjoint_iff _ _).mpr ?_
    change II.map' α.toOrderHom (α.toOrderHom y).castSucc ≤ y.castSucc
    exact (II.map'_le_castSucc_iff α.toOrderHom (α.toOrderHom y).castSucc y).mpr le_rfl

@[simp]
theorem Boundary.cutInv_id (n : ℕ) :
    Boundary.cutInv (𝟙 (⟨⦋n + 1⦌⟩ : Boundary)) = 𝟙 ⦋n⦌ := by
  have h : 𝟙 (⟨⦋n + 1⦌⟩ : Boundary) =
      Boundary.homMk (II.map (𝟙 ⦋n⦌)).unop (II.map'_zero _) (II.map'_last _) :=
    WideSubcategory.hom_ext _ (congrArg Quiver.Hom.unop (II.map_id ⦋n⦌)).symm
  rw [h]
  exact Boundary.cutInv_ii (𝟙 ⦋n⦌)

theorem Boundary.cutInv_comp {n m p : ℕ} (f : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩)
    (g : (⟨⦋m + 1⦌⟩ : Boundary) ⟶ ⟨⦋p + 1⦌⟩) :
    Boundary.cutInv (f ≫ g) = Boundary.cutInv g ≫ Boundary.cutInv f := by
  have h : f ≫ g = Boundary.homMk (II.map (Boundary.cutInv g ≫ Boundary.cutInv f)).unop
      (II.map'_zero _) (II.map'_last _) := by
    apply WideSubcategory.hom_ext _
    simp only [II.map_comp, CategoryTheory.unop_comp, Boundary.ii_cutInv]
    rfl
  rw [h]
  exact Boundary.cutInv_ii (Boundary.cutInv g ≫ Boundary.cutInv f)

/-- The inverse functor `Δ_∂ ⥤ Δ₊ᵒᵖ` sending `⦋0⦌` to `op .star`, `⦋n + 1⦌` to `op (.of ⦋n⦌)`,
and each endpoint-preserving map `⦋n + 1⦌ ⟶ ⦋m + 1⦌` to its cut-inverse `⦋m⦌ ⟶ ⦋n⦌`. -/
def boundaryToAugmentedOp : Boundary ⥤ AugmentedSimplexCategoryᵒᵖ where
  obj x := match x.obj.len with
    | 0 => op (WithInitial.star : AugmentedSimplexCategory)
    | n + 1 => op (WithInitial.of ⦋n⦌)
  map {x y} f := match x, y with
    | ⟨⟨0⟩⟩, ⟨⟨0⟩⟩ => 𝟙 (op (WithInitial.star : AugmentedSimplexCategory))
    | ⟨⟨0⟩⟩, ⟨⟨m + 1⟩⟩ => ((Boundary.isEmpty_hom_zero_succ m).false f).elim
    | ⟨⟨n + 1⟩⟩, ⟨⟨0⟩⟩ => (WithInitial.homTo ⦋n⦌).op
    | ⟨⟨n + 1⟩⟩, ⟨⟨m + 1⟩⟩ => (Boundary.cutInv f).op
  map_id x := by
    rcases x with ⟨⟨_ | n⟩⟩
    · rfl
    · exact Quiver.Hom.unop_inj (Boundary.cutInv_id n)
  map_comp {x y z} f g := by
    rcases x with ⟨⟨_ | n⟩⟩ <;> rcases y with ⟨⟨_ | m⟩⟩ <;> rcases z with ⟨⟨_ | p⟩⟩
    · rfl
    · exact ((Boundary.isEmpty_hom_zero_succ p).false g).elim
    · exact ((Boundary.isEmpty_hom_zero_succ m).false f).elim
    · exact ((Boundary.isEmpty_hom_zero_succ m).false f).elim
    · exact Subsingleton.elim _ _
    · exact ((Boundary.isEmpty_hom_zero_succ p).false g).elim
    · exact Subsingleton.elim _ _
    · exact Quiver.Hom.unop_inj (Boundary.cutInv_comp f g)

@[simp]
theorem boundaryToAugmentedOp_obj_zero :
    boundaryToAugmentedOp.obj ⟨⦋0⦌⟩ = op (WithInitial.star : AugmentedSimplexCategory) :=
  (rfl)

@[simp]
theorem boundaryToAugmentedOp_obj_succ (n : ℕ) :
    boundaryToAugmentedOp.obj ⟨⦋n + 1⦌⟩ = op (WithInitial.of ⦋n⦌) :=
  (rfl)

@[simp]
theorem boundaryToAugmentedOp_map_constToZero (n : ℕ) :
    boundaryToAugmentedOp.map (Boundary.constToZero ⦋n + 1⦌) =
      (WithInitial.homTo ⦋n⦌).op :=
  rfl

/-- `augmentedOpToBoundary` and `boundaryToAugmentedOp` are strict left/right inverses on
`Δ₊ᵒᵖ`. -/
@[simp]
theorem augmentedOpToBoundary_comp_boundaryToAugmentedOp :
    augmentedOpToBoundary ⋙ boundaryToAugmentedOp = 𝟭 AugmentedSimplexCategoryᵒᵖ :=
  CategoryTheory.Functor.hext (fun x ↦ by rcases x with ⟨⟨_⟩ | _⟩ <;> rfl) fun x y f ↦ by
    rcases x with ⟨nx | _⟩ <;> rcases y with ⟨ny | _⟩ <;>
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
        augmentedOpToBoundary, boundaryToAugmentedOp]
    · exact heq_of_eq <| Quiver.Hom.unop_inj (Boundary.cutInv_ii (f.unop : ny ⟶ nx))
    · exact heq_of_eq (Subsingleton.elim _ _)
    · exact (WithInitial.false_of_to_star f.unop).elim
    · exact heq_of_eq (Subsingleton.elim _ _)

/-- `boundaryToAugmentedOp` and `augmentedOpToBoundary` are strict left/right inverses on
`Δ_∂`. -/
@[simp]
theorem boundaryToAugmentedOp_comp_augmentedOpToBoundary :
    boundaryToAugmentedOp ⋙ augmentedOpToBoundary = 𝟭 Boundary :=
  CategoryTheory.Functor.hext (fun x ↦ by rcases x with ⟨⟨_ | _⟩⟩ <;> rfl) fun x y f ↦ by
    rcases x with ⟨⟨_ | n⟩⟩ <;> rcases y with ⟨⟨_ | m⟩⟩ <;>
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
        augmentedOpToBoundary, boundaryToAugmentedOp]
    · exact heq_of_eq (Subsingleton.elim _ _)
    · exact ((Boundary.isEmpty_hom_zero_succ m).false f).elim
    · exact heq_of_eq (Subsingleton.elim _ _)
    · exact heq_of_eq <| WideSubcategory.hom_ext _ (Boundary.ii_cutInv f)

/-- `iiOpToBoundary` is faithful. -/
instance : iiOpToBoundary.Faithful where
  map_injective {x y f g} h := by
    obtain ⟨⟨n⟩⟩ := x
    obtain ⟨⟨m⟩⟩ := y
    have h' := congrArg Boundary.cutInv h
    exact Quiver.Hom.unop_inj <| by
      have hf : Boundary.cutInv (iiOpToBoundary.map f) = f.unop := Boundary.cutInv_ii f.unop
      have hg : Boundary.cutInv (iiOpToBoundary.map g) = g.unop := Boundary.cutInv_ii g.unop
      exact hf.symm.trans (h'.trans hg)

/-- Strict isomorphism of categories `Δ₊ᵒᵖ ≅ Δ_∂`. -/
def augmentedOpIsoBoundary : Cat.of AugmentedSimplexCategoryᵒᵖ ≅ Cat.of Boundary where
  hom := augmentedOpToBoundary.toCatHom
  inv := boundaryToAugmentedOp.toCatHom
  hom_inv_id := Cat.ext augmentedOpToBoundary_comp_boundaryToAugmentedOp
  inv_hom_id := Cat.ext boundaryToAugmentedOp_comp_augmentedOpToBoundary

@[simp]
theorem augmentedOpIsoBoundary_hom_toFunctor :
    augmentedOpIsoBoundary.hom.toFunctor = augmentedOpToBoundary :=
  rfl

@[simp]
theorem augmentedOpIsoBoundary_inv_toFunctor :
    augmentedOpIsoBoundary.inv.toFunctor = boundaryToAugmentedOp :=
  rfl

@[simp]
theorem boundaryToAugmentedOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    boundaryToAugmentedOp.map (Boundary.δ i) =
      (AugmentedSimplexCategory.inclusion.map (SimplexCategory.σ i)).op := by
  rw [← iiOpToBoundary_map_σ]
  exact Quiver.Hom.unop_inj (Boundary.cutInv_ii (SimplexCategory.σ i))

@[simp]
theorem boundaryToAugmentedOp_map_σ {n : ℕ} (i : Fin (n + 2)) :
    boundaryToAugmentedOp.map (Boundary.σ i) =
      (AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i)).op := by
  rw [← iiOpToBoundary_map_δ]
  exact Quiver.Hom.unop_inj (Boundary.cutInv_ii (SimplexCategory.δ i))

end SimplexCategory
