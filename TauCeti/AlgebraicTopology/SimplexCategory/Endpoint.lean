/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Widesubcategory
public import TauCeti.AlgebraicTopology.SimplicialObject.II
public import TauCeti.Order.Hom.Adjoint
import TauCeti.Order.Fin.Basic

/-!
# Endpoint-preserving subcategories of the simplex category and finite-ordinal dualities

This file defines the three endpoint-preserving wide subcategories of `SimplexCategory` (`Δ`):

* `TauCeti.SimplexCategory.LastPreserving` (`Δ_top`): all nonempty finite ordinals `⦋n⦌`, with
  monotone maps preserving the greatest element `Fin.last n`.
* `TauCeti.SimplexCategory.ZeroPreserving` (`Δ_bot`): all nonempty finite ordinals `⦋n⦌`, with
  monotone maps preserving the least element `0`.
* `TauCeti.SimplexCategory.Boundary` (`Δ_∂`): all nonempty finite ordinals `⦋n⦌` (including `⦋0⦌`,
  where the two endpoints coincide), with monotone maps preserving both `0` and `Fin.last n`.

It then constructs the two strict category dualities required for the Schanuel–Street walking
adjunction:

1. **Top/bottom duality (`Δ_topᵒᵖ ≅ Δ_bot`)**:
   `TauCeti.SimplexCategory.lastPreservingOpToZeroPreserving` and
   `TauCeti.SimplexCategory.zeroPreservingToLastPreservingOp`, given by `OrderHom.leftAdjoint` and
   `OrderHom.rightAdjoint` on endpoint-preserving monotone maps between finite ordinals, are strict
   mutual inverses and package as `TauCeti.SimplexCategory.lastPreservingOpIsoZeroPreserving :`
   `Cat.of LastPreservingᵒᵖ ≅ Cat.of ZeroPreserving`.
2. **Finite-ordinal cut duality (`Δ₊ᵒᵖ ≅ Δ_∂`)**: sending the ordinal with `n` elements (`∅` in
   `AugmentedSimplexCategory`, or `⦋k⦌` of cardinality `k + 1`) to its chain of `n + 1` cuts `⦋n⦌`
   (`⦋0⦌`, or `⦋k + 1⦌`) and a monotone map `α` to the cut-counting map
   `x ↦ #{i | (α i).castSucc < x}` factors `SimplexCategory.II.leftOp : Δᵒᵖ ⥤ Δ` through
   `TauCeti.SimplexCategory.iiOpToBoundary : Δᵒᵖ ⥤ Boundary`, extends to
   `TauCeti.SimplexCategory.augmentedOpToBoundary : AugmentedSimplexCategoryᵒᵖ ⥤ Boundary`, and
   admits a strict inverse
   `TauCeti.SimplexCategory.boundaryToAugmentedOp : Boundary ⥤ AugmentedSimplexCategoryᵒᵖ` via
   right adjoints, packaging as `TauCeti.SimplexCategory.augmentedOpIsoBoundary :`
   `Cat.of AugmentedSimplexCategoryᵒᵖ ≅ Cat.of Boundary`.

## References

* S. Schanuel and R. Street, *The free adjunction*, Cahiers de Topologie et Géométrie
  Différentielle Catégoriques **27** (1986), 81–83.
* E. Riehl and D. Verity, *Elements of ∞-Category Theory*, Proposition 3.3.4, Observation 3.3.6,
  and Remark 3.3.8.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

namespace TauCeti.SimplexCategory

open _root_.SimplexCategory

/-! ### Endpoint-preserving morphism properties -/

/-- The property of a morphism in `SimplexCategory` preserving the initial vertex `0`. -/
def preservesZero : MorphismProperty _root_.SimplexCategory :=
  fun {_ _} f ↦ f.toOrderHom 0 = 0

/-- The property of a morphism in `SimplexCategory` preserving the final vertex `Fin.last`. -/
def preservesLast : MorphismProperty _root_.SimplexCategory :=
  fun {x y} f ↦ f.toOrderHom (Fin.last x.len) = Fin.last y.len

/-- The property of a morphism in `SimplexCategory` preserving both endpoints `0` and
`Fin.last`. -/
def preservesEndpoints : MorphismProperty _root_.SimplexCategory :=
  fun _ _ f ↦ preservesZero f ∧ preservesLast f

theorem preservesZero_iff {x y : _root_.SimplexCategory} (f : x ⟶ y) :
    preservesZero f ↔ f.toOrderHom 0 = 0 :=
  Iff.rfl

theorem preservesLast_iff {x y : _root_.SimplexCategory} (f : x ⟶ y) :
    preservesLast f ↔ f.toOrderHom (Fin.last x.len) = Fin.last y.len :=
  Iff.rfl

theorem preservesEndpoints_iff {x y : _root_.SimplexCategory} (f : x ⟶ y) :
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
  simp only [preservesZero_iff, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact ⟨fun h hi ↦ by simp [hi] at h, fun hi ↦ Fin.succAbove_ne_zero_zero hi⟩

@[simp]
theorem preservesLast_δ_iff {n : ℕ} (i : Fin (n + 2)) :
    preservesLast (δ i) ↔ i ≠ Fin.last (n + 1) := by
  simp only [preservesLast_iff, δ, mkHom, Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, len_mk]
  exact ⟨fun h hi ↦ by simp [hi, Fin.ext_iff] at h, fun hi ↦ Fin.succAbove_ne_last_last hi⟩

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

theorem preservesZero_const_zero (x y : _root_.SimplexCategory) :
    preservesZero (const x y 0) :=
  rfl

theorem preservesLast_const_last (x y : _root_.SimplexCategory) :
    preservesLast (const x y (Fin.last y.len)) :=
  rfl

@[simp]
theorem preservesEndpoints_const_to_zero (x : _root_.SimplexCategory) :
    preservesEndpoints (const x ⦋0⦌ 0) :=
  ⟨rfl, Subsingleton.elim (α := Fin 1) _ _⟩

@[simp]
theorem preservesZero_rev_map_iff {x y : _root_.SimplexCategory} (f : x ⟶ y) :
    preservesZero (rev.map f) ↔ preservesLast f := by
  simp only [preservesZero_iff, preservesLast_iff, rev_map_apply, rev_obj, ← Fin.rev_last,
    Fin.rev_rev, Fin.rev_inj]

@[simp]
theorem preservesLast_rev_map_iff {x y : _root_.SimplexCategory} (f : x ⟶ y) :
    preservesLast (rev.map f) ↔ preservesZero f := by
  simp only [preservesLast_iff, preservesZero_iff, rev_map_apply, rev_obj, ← Fin.rev_zero,
    Fin.rev_rev, Fin.rev_inj]

@[simp]
theorem preservesEndpoints_rev_map_iff {x y : _root_.SimplexCategory} (f : x ⟶ y) :
    preservesEndpoints (rev.map f) ↔ preservesEndpoints f := by
  rw [preservesEndpoints_iff, preservesEndpoints_iff, ← preservesZero_iff, ← preservesLast_iff,
    ← preservesZero_iff, ← preservesLast_iff, preservesZero_rev_map_iff,
    preservesLast_rev_map_iff, and_comm]

/-! ### Endpoint wide subcategories -/

/-- The wide subcategory `Δ_top` of `SimplexCategory` whose morphisms preserve the greatest
element `Fin.last`. -/
abbrev LastPreserving : Type := WideSubcategory preservesLast

/-- The wide subcategory `Δ_bot` of `SimplexCategory` whose morphisms preserve the least element
`0`. -/
abbrev ZeroPreserving : Type := WideSubcategory preservesZero

/-- The wide subcategory `Δ_∂` of `SimplexCategory` (including `⦋0⦌`) whose morphisms preserve both
endpoints `0` and `Fin.last`. -/
abbrev Boundary : Type := WideSubcategory preservesEndpoints

namespace LastPreserving

/-- Construct a morphism in `LastPreserving` from a morphism in `SimplexCategory` preserving the
greatest element. -/
def homMk {x y : LastPreserving} (f : x.obj ⟶ y.obj)
    (hf : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) : x ⟶ y :=
  ⟨f, hf⟩

@[simp]
theorem homMk_hom {x y : LastPreserving} (f : x.obj ⟶ y.obj)
    (hf : f.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len) :
    (homMk f hf).hom = f :=
  rfl

@[simp]
theorem toOrderHom_last {x y : LastPreserving} (f : x ⟶ y) :
    f.hom.toOrderHom (Fin.last x.obj.len) = Fin.last y.obj.len :=
  f.property

/-- Restricted coface maps `δ i.castSucc : ⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ_top`, omitting a non-last
vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n⦌⟩ : LastPreserving) ⟶ ⟨⦋n + 1⦌⟩ :=
  ⟨_root_.SimplexCategory.δ i.castSucc,
    (preservesLast_δ_iff i.castSucc).mpr (Fin.castSucc_lt_last i).ne⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_top`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : LastPreserving) ⟶ ⟨⦋n⦌⟩ :=
  ⟨_root_.SimplexCategory.σ i, preservesLast_σ i⟩

@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (LastPreserving.δ i).hom = _root_.SimplexCategory.δ i.castSucc :=
  rfl

@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (LastPreserving.σ i).hom = _root_.SimplexCategory.σ i :=
  rfl

/-- `⟨⦋0⦌⟩` is terminal in `LastPreserving`. -/
instance {x : LastPreserving} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := ⟨const x.obj ⦋0⦌ 0, Subsingleton.elim (α := Fin 1) _ _⟩
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

/-- `LastPreserving.δ 0` sends `0` to `1 ≠ 0`, witnessing that `Δ_∂` is strictly contained in
`Δ_top`. -/
theorem δ_zero_hom_zero : (LastPreserving.δ (0 : Fin 1)).hom.toOrderHom 0 = 1 :=
  rfl

/-- In `Δ_top`, the unique coface map `⦋0⦌ ⟶ ⦋1⦌` is a section of `σ 0`. -/
theorem δ_zero_comp_σ_zero : LastPreserving.δ (0 : Fin 1) ≫ LastPreserving.σ 0 = 𝟙 _ :=
  WideSubcategory.hom_ext _ (δ_comp_σ_self (i := (0 : Fin 1)))

end LastPreserving

namespace ZeroPreserving

/-- Construct a morphism in `ZeroPreserving` from a morphism in `SimplexCategory` preserving
`0`. -/
def homMk {x y : ZeroPreserving} (f : x.obj ⟶ y.obj) (hf : f.toOrderHom 0 = 0) : x ⟶ y :=
  ⟨f, hf⟩

@[simp]
theorem homMk_hom {x y : ZeroPreserving} (f : x.obj ⟶ y.obj) (hf : f.toOrderHom 0 = 0) :
    (homMk f hf).hom = f :=
  rfl

@[simp]
theorem toOrderHom_zero {x y : ZeroPreserving} (f : x ⟶ y) : f.hom.toOrderHom 0 = 0 :=
  f.property

/-- Restricted coface maps `δ i.succ : ⦋n⦌ ⟶ ⦋n + 1⦌` in `Δ_bot`, omitting a nonzero vertex. -/
def δ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n⦌⟩ : ZeroPreserving) ⟶ ⟨⦋n + 1⦌⟩ :=
  ⟨_root_.SimplexCategory.δ i.succ, (preservesZero_δ_iff i.succ).mpr (Fin.succ_ne_zero i)⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_bot`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : ZeroPreserving) ⟶ ⟨⦋n⦌⟩ :=
  ⟨_root_.SimplexCategory.σ i, preservesZero_σ i⟩

@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (ZeroPreserving.δ i).hom = _root_.SimplexCategory.δ i.succ :=
  rfl

@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (ZeroPreserving.σ i).hom = _root_.SimplexCategory.σ i :=
  rfl

/-- `⟨⦋0⦌⟩` is terminal in `ZeroPreserving`. -/
instance {x : ZeroPreserving} : Unique (x ⟶ ⟨⦋0⦌⟩) where
  default := ⟨const x.obj ⦋0⦌ 0, rfl⟩
  uniq f := WideSubcategory.hom_ext _ (eq_const_to_zero f.hom)

/-- In `Δ_bot`, the unique coface map `⦋0⦌ ⟶ ⦋1⦌` is a section of `σ 0`. -/
theorem δ_zero_comp_σ_zero : ZeroPreserving.δ (0 : Fin 1) ≫ ZeroPreserving.σ 0 = 𝟙 _ :=
  WideSubcategory.hom_ext _ (δ_comp_σ_succ (i := (0 : Fin 1)))

end ZeroPreserving

namespace Boundary

/-- The faithful inclusion `Δ_∂ ⥤ Δ_top`. -/
def toLastPreserving : Boundary ⥤ LastPreserving where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom, f.property.2⟩

instance : toLastPreserving.Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) h)

@[simp]
theorem toLastPreserving_obj (x : Boundary) : toLastPreserving.obj x = ⟨x.obj⟩ := rfl

@[simp]
theorem toLastPreserving_map_hom {x y : Boundary} (f : x ⟶ y) :
    (toLastPreserving.map f).hom = f.hom := rfl

theorem toLastPreserving_comp_inclusion :
    toLastPreserving ⋙ wideSubcategoryInclusion preservesLast =
      wideSubcategoryInclusion preservesEndpoints := rfl

/-- The faithful inclusion `Δ_∂ ⥤ Δ_bot`. -/
def toZeroPreserving : Boundary ⥤ ZeroPreserving where
  obj x := ⟨x.obj⟩
  map f := ⟨f.hom, f.property.1⟩

instance : toZeroPreserving.Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg (fun g ↦ g.hom) h)

@[simp]
theorem toZeroPreserving_obj (x : Boundary) : toZeroPreserving.obj x = ⟨x.obj⟩ := rfl

@[simp]
theorem toZeroPreserving_map_hom {x y : Boundary} (f : x ⟶ y) :
    (toZeroPreserving.map f).hom = f.hom := rfl

theorem toZeroPreserving_comp_inclusion :
    toZeroPreserving ⋙ wideSubcategoryInclusion preservesZero =
      wideSubcategoryInclusion preservesEndpoints := rfl

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
  ⟨_root_.SimplexCategory.δ i.succ.castSucc, (preservesEndpoints_δ_iff i.succ.castSucc).mpr
    ⟨Fin.castSucc_ne_zero_iff.mpr (Fin.succ_ne_zero i),
      (Fin.castSucc_lt_last i.succ).ne⟩⟩

/-- Restricted codegeneracy maps `σ i : ⦋n + 1⦌ ⟶ ⦋n⦌` in `Δ_∂`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋n⦌⟩ :=
  ⟨_root_.SimplexCategory.σ i, preservesEndpoints_σ i⟩

@[simp]
theorem δ_hom {n : ℕ} (i : Fin (n + 1)) :
    (Boundary.δ i).hom = _root_.SimplexCategory.δ i.succ.castSucc :=
  rfl

@[simp]
theorem σ_hom {n : ℕ} (i : Fin (n + 1)) :
    (Boundary.σ i).hom = _root_.SimplexCategory.σ i :=
  rfl

/-- The unique morphism to the terminal object `⟨⦋0⦌⟩` in `Boundary`. -/
def constToZero (x : _root_.SimplexCategory) : (⟨x⟩ : Boundary) ⟶ ⟨⦋0⦌⟩ :=
  ⟨const x ⦋0⦌ 0, preservesEndpoints_const_to_zero x⟩

@[simp]
theorem constToZero_hom (x : _root_.SimplexCategory) : (constToZero x).hom = const x ⦋0⦌ 0 :=
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
def lastPreservingOpToZeroPreserving : LastPreservingᵒᵖ ⥤ ZeroPreserving where
  obj x := ⟨x.unop.obj⟩
  map f := ZeroPreserving.homMk (Hom.mk (f.unop.hom.toOrderHom.leftAdjoint f.unop.property))
    (f.unop.hom.toOrderHom.leftAdjoint_bot f.unop.property)
  map_id _ := WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by simp [OrderHom.leftAdjoint_id]
  map_comp f g := WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp [WideSubcategory.comp_def, comp_toOrderHom, ZeroPreserving.homMk, Hom.toOrderHom_mk,
      OrderHom.leftAdjoint_comp g.unop.property f.unop.property]

/-- The duality functor `Δ_bot ⥤ Δ_topᵒᵖ` taking each bottom-preserving map to its right
adjoint. -/
def zeroPreservingToLastPreservingOp : ZeroPreserving ⥤ LastPreservingᵒᵖ where
  obj x := op ⟨x.obj⟩
  map f := Quiver.Hom.op <| LastPreserving.homMk
    (Hom.mk (f.hom.toOrderHom.rightAdjoint f.property))
    (f.hom.toOrderHom.rightAdjoint_top f.property)
  map_id _ := Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp [OrderHom.rightAdjoint_id]
  map_comp f g := Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <| by
    simp [WideSubcategory.comp_def, comp_toOrderHom, LastPreserving.homMk, Hom.toOrderHom_mk,
      OrderHom.rightAdjoint_comp f.property g.property]

@[simp]
theorem lastPreservingOpToZeroPreserving_obj (x : LastPreservingᵒᵖ) :
    lastPreservingOpToZeroPreserving.obj x = ⟨x.unop.obj⟩ := (rfl)

@[simp]
theorem zeroPreservingToLastPreservingOp_obj (x : ZeroPreserving) :
    zeroPreservingToLastPreservingOp.obj x = op ⟨x.obj⟩ := (rfl)

@[simp]
theorem lastPreservingOpToZeroPreserving_map_toOrderHom {x y : LastPreservingᵒᵖ} (f : x ⟶ y) :
    (lastPreservingOpToZeroPreserving.map f).hom.toOrderHom =
      f.unop.hom.toOrderHom.leftAdjoint f.unop.property :=
  rfl

@[simp]
theorem zeroPreservingToLastPreservingOp_map_toOrderHom {x y : ZeroPreserving} (f : x ⟶ y) :
    (zeroPreservingToLastPreservingOp.map f).unop.hom.toOrderHom =
      f.hom.toOrderHom.rightAdjoint f.property :=
  rfl

@[simp]
theorem lastPreservingOpToZeroPreserving_map_δ {n : ℕ} (i : Fin (n + 1)) :
    lastPreservingOpToZeroPreserving.map (LastPreserving.δ i).op = ZeroPreserving.σ i :=
  WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.leftAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_predAbove_castSucc_succAbove i)

@[simp]
theorem lastPreservingOpToZeroPreserving_map_σ {n : ℕ} (i : Fin (n + 1)) :
    lastPreservingOpToZeroPreserving.map (LastPreserving.σ i).op = ZeroPreserving.δ i :=
  WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.leftAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_succ_succAbove_predAbove i)

@[simp]
theorem zeroPreservingToLastPreservingOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    zeroPreservingToLastPreservingOp.map (ZeroPreserving.δ i) = (LastPreserving.σ i).op :=
  Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.rightAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_succ_succAbove_predAbove i)

@[simp]
theorem zeroPreservingToLastPreservingOp_map_σ {n : ℕ} (i : Fin (n + 1)) :
    zeroPreservingToLastPreservingOp.map (ZeroPreserving.σ i) = (LastPreserving.δ i).op :=
  Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
    OrderHom.rightAdjoint_eq_of_galoisConnection _
      (Fin.galoisConnection_predAbove_castSucc_succAbove i)

/-- `lastPreservingOpToZeroPreserving` and `zeroPreservingToLastPreservingOp` are strict
left/right inverses on `Δ_topᵒᵖ`. -/
@[simp]
theorem lastPreservingOpToZeroPreserving_comp_zeroPreservingToLastPreservingOp :
    lastPreservingOpToZeroPreserving ⋙ zeroPreservingToLastPreservingOp =
      𝟭 LastPreservingᵒᵖ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    Quiver.Hom.unop_inj <| WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
      OrderHom.rightAdjoint_leftAdjoint f.unop.hom.toOrderHom f.unop.property

/-- `zeroPreservingToLastPreservingOp` and `lastPreservingOpToZeroPreserving` are strict
left/right inverses on `Δ_bot`. -/
@[simp]
theorem zeroPreservingToLastPreservingOp_comp_lastPreservingOpToZeroPreserving :
    zeroPreservingToLastPreservingOp ⋙ lastPreservingOpToZeroPreserving =
      𝟭 ZeroPreserving :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) fun _ _ f ↦ heq_of_eq <|
    WideSubcategory.hom_ext _ <| Hom.ext _ _ <|
      OrderHom.leftAdjoint_rightAdjoint f.hom.toOrderHom f.property

/-- Strict isomorphism of categories `Δ_topᵒᵖ ≅ Δ_bot`. -/
def lastPreservingOpIsoZeroPreserving :
    Cat.of LastPreservingᵒᵖ ≅ Cat.of ZeroPreserving where
  hom := lastPreservingOpToZeroPreserving.toCatHom
  inv := zeroPreservingToLastPreservingOp.toCatHom
  hom_inv_id := Cat.ext lastPreservingOpToZeroPreserving_comp_zeroPreservingToLastPreservingOp
  inv_hom_id := Cat.ext zeroPreservingToLastPreservingOp_comp_lastPreservingOpToZeroPreserving

@[simp]
theorem lastPreservingOpIsoZeroPreserving_hom_toFunctor :
    lastPreservingOpIsoZeroPreserving.hom.toFunctor = lastPreservingOpToZeroPreserving :=
  rfl

@[simp]
theorem lastPreservingOpIsoZeroPreserving_inv_toFunctor :
    lastPreservingOpIsoZeroPreserving.inv.toFunctor = zeroPreservingToLastPreservingOp :=
  rfl

/-! ### Factorization of `SimplexCategory.II` through `Boundary` -/

/-- Factorization of `SimplexCategory.II.leftOp : Δᵒᵖ ⥤ Δ` through the boundary subcategory
`Boundary`. -/
def iiOpToBoundary : _root_.SimplexCategoryᵒᵖ ⥤ Boundary where
  obj x := ⟨⦋x.unop.len + 1⦌⟩
  map f := Boundary.homMk (II.map f.unop).unop (II.map'_zero _) (II.map'_last _)
  map_id x := WideSubcategory.hom_ext _ <| congrArg Quiver.Hom.unop (II.map_id x.unop)
  map_comp f g := WideSubcategory.hom_ext _ <| congrArg Quiver.Hom.unop (II.map_comp g.unop f.unop)

@[simp]
theorem iiOpToBoundary_obj (x : _root_.SimplexCategoryᵒᵖ) :
    iiOpToBoundary.obj x = ⟨⦋x.unop.len + 1⦌⟩ :=
  (rfl)

@[simp]
theorem iiOpToBoundary_map_hom {x y : _root_.SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    (iiOpToBoundary.map f).hom = (II.map f.unop).unop :=
  rfl

@[simp]
theorem iiOpToBoundary_comp_inclusion :
    iiOpToBoundary ⋙ wideSubcategoryInclusion preservesEndpoints = II.leftOp :=
  rfl

@[simp]
theorem iiOpToBoundary_map_δ {n : ℕ} (i : Fin (n + 2)) :
    iiOpToBoundary.map (_root_.SimplexCategory.δ i).op = Boundary.σ i :=
  WideSubcategory.hom_ext _ (congrArg Quiver.Hom.unop (II_δ i))

@[simp]
theorem iiOpToBoundary_map_σ {n : ℕ} (i : Fin (n + 1)) :
    iiOpToBoundary.map (_root_.SimplexCategory.σ i).op = Boundary.δ i :=
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
theorem augmentedOpToBoundary_obj_of (x : _root_.SimplexCategory) :
    augmentedOpToBoundary.obj (op (WithInitial.of x)) = ⟨⦋x.len + 1⦌⟩ :=
  (rfl)

@[simp]
theorem augmentedOpToBoundary_map_of {x y : _root_.SimplexCategory} (f : y ⟶ x) :
    augmentedOpToBoundary.map (AugmentedSimplexCategory.inclusion.map f).op =
      iiOpToBoundary.map f.op :=
  rfl

@[simp]
theorem inclusion_op_comp_augmentedOpToBoundary :
    AugmentedSimplexCategory.inclusion.op ⋙ augmentedOpToBoundary = iiOpToBoundary :=
  rfl

theorem augmentedOpToBoundary_map_homTo (x : _root_.SimplexCategory) :
    augmentedOpToBoundary.map (WithInitial.homTo x).op =
      Boundary.constToZero ⦋x.len + 1⦌ :=
  rfl

theorem augmentedOpToBoundary_map_δ {n : ℕ} (i : Fin (n + 2)) :
    augmentedOpToBoundary.map
        (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.δ i)).op =
      Boundary.σ i :=
  (augmentedOpToBoundary_map_of _).trans (iiOpToBoundary_map_δ i)

theorem augmentedOpToBoundary_map_σ {n : ℕ} (i : Fin (n + 1)) :
    augmentedOpToBoundary.map
        (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.σ i)).op =
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

/-- Embedding `Boundary.cutInv g y` via `Fin.castSucc` recovers the right adjoint of `g` at
`y.castSucc`. -/
@[simp]
theorem Boundary.castSucc_cutInv_apply {n m : ℕ}
    (g : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩) (y : Fin (m + 1)) :
    ((Boundary.cutInv g).toOrderHom y).castSucc =
      g.hom.toOrderHom.rightAdjoint g.property.1 y.castSucc :=
  Fin.castSucc_castPred _ fun h ↦
    (Fin.castSucc_lt_last y).not_ge <| by
      rw [← Boundary.toOrderHom_last g]
      exact (OrderHom.le_rightAdjoint_iff _ _).mp h.symm.le

/-- Galois characterization of `Boundary.cutInv g`:
`x ≤ (Boundary.cutInv g).toOrderHom y ↔ g.hom.toOrderHom x.castSucc ≤ y.castSucc`. -/
@[simp]
theorem Boundary.le_cutInv_iff {n m : ℕ} (g : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩)
    (x : Fin (n + 1)) (y : Fin (m + 1)) :
    x ≤ (Boundary.cutInv g).toOrderHom y ↔ g.hom.toOrderHom x.castSucc ≤ y.castSucc :=
  Fin.castSucc_le_castSucc_iff.symm.trans <|
    (Boundary.castSucc_cutInv_apply g y).symm ▸
      (g.hom.toOrderHom.galoisConnection_rightAdjoint g.property.1 x.castSucc y.castSucc).symm

/-- Applying `SimplexCategory.II` to `Boundary.cutInv g` recovers `g`. -/
@[simp]
theorem Boundary.ii_cutInv {n m : ℕ} (g : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩) :
    (II.map (Boundary.cutInv g)).unop = g.hom := by
  refine Hom.ext _ _ (OrderHom.ext _ _ (funext fun (x : Fin (n + 2)) ↦ ?_))
  dsimp only [II, Quiver.Hom.unop_op, Hom.toOrderHom_mk, OrderHom.coe_mk]
  apply le_antisymm
  · by_contra! hlt
    obtain ⟨y, hy⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hlt)
    have hle1 : ((Boundary.cutInv g).toOrderHom y).castSucc ≥ x :=
      (Boundary.castSucc_cutInv_apply g y).symm ▸
        (OrderHom.le_rightAdjoint_iff _ _).mpr hy.symm.le
    have hle2 : II.map' (Boundary.cutInv g).toOrderHom x ≤ y.castSucc :=
      (II.map'_le_castSucc_iff (Boundary.cutInv g).toOrderHom x y).mpr hle1
    exact hlt.not_ge (hy ▸ hle2)
  · by_contra! hlt
    obtain ⟨y, hy⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hlt)
    have hle1 : x ≤ ((Boundary.cutInv g).toOrderHom y).castSucc :=
      (II.map'_le_castSucc_iff (Boundary.cutInv g).toOrderHom x y).mp hy.symm.le
    have hle2 : g.hom.toOrderHom x ≤ y.castSucc :=
      (OrderHom.le_rightAdjoint_iff _ _).mp ((Boundary.castSucc_cutInv_apply g y) ▸ hle1)
    exact hlt.not_ge (hy ▸ hle2)

/-- `Boundary.cutInv` is left inverse to `SimplexCategory.II`. -/
@[simp]
theorem Boundary.cutInv_ii {n m : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    Boundary.cutInv (Boundary.homMk (II.map α).unop (II.map'_zero _) (II.map'_last _)) = α := by
  refine Hom.ext _ _ (OrderHom.ext _ _ (funext fun (y : Fin (m + 1)) ↦ ?_))
  apply le_antisymm
  · by_contra! hlt
    have hsucc : (α.toOrderHom y).succ ≤
        ((Boundary.cutInv (Boundary.homMk (II.map α).unop
          (II.map'_zero _) (II.map'_last _))).toOrderHom y).castSucc :=
      Fin.le_def.mpr (Nat.succ_le_of_lt (Fin.lt_def.mp hlt))
    have hle1 : (II.map α).unop.toOrderHom (α.toOrderHom y).succ ≤ y.castSucc :=
      (OrderHom.le_rightAdjoint_iff _ _).mp
        ((Boundary.castSucc_cutInv_apply
          (Boundary.homMk (II.map α).unop (II.map'_zero _) (II.map'_last _)) y) ▸ hsucc)
    dsimp only [II, Quiver.Hom.unop_op, Hom.toOrderHom_mk, OrderHom.coe_mk] at hle1
    have hle2 : (α.toOrderHom y).succ ≤ (α.toOrderHom y).castSucc :=
      (II.map'_le_castSucc_iff α.toOrderHom (α.toOrderHom y).succ y).mp hle1
    exact (Fin.castSucc_lt_succ (i := α.toOrderHom y)).not_ge hle2
  · rw [Boundary.le_cutInv_iff]
    dsimp only [Boundary.homMk, II, Quiver.Hom.unop_op, Hom.toOrderHom_mk, OrderHom.coe_mk]
    exact (II.map'_le_castSucc_iff α.toOrderHom (α.toOrderHom y).castSucc y).mpr le_rfl

@[simp]
theorem Boundary.cutInv_id (n : ℕ) :
    Boundary.cutInv (𝟙 (⟨⦋n + 1⦌⟩ : Boundary)) = 𝟙 ⦋n⦌ := by
  have h : 𝟙 (⟨⦋n + 1⦌⟩ : Boundary) =
      Boundary.homMk (II.map (𝟙 ⦋n⦌)).unop (II.map'_zero _) (II.map'_last _) :=
    WideSubcategory.hom_ext _ (congrArg Quiver.Hom.unop (II.map_id ⦋n⦌)).symm
  rw [h]
  exact Boundary.cutInv_ii (𝟙 ⦋n⦌)

@[simp]
theorem Boundary.cutInv_comp {n m p : ℕ} (f : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩)
    (g : (⟨⦋m + 1⦌⟩ : Boundary) ⟶ ⟨⦋p + 1⦌⟩) :
    Boundary.cutInv (f ≫ g) = Boundary.cutInv g ≫ Boundary.cutInv f := by
  have h : f ≫ g = iiOpToBoundary.map (Boundary.cutInv g ≫ Boundary.cutInv f).op :=
    WideSubcategory.hom_ext _ <|
      (WideSubcategory.comp_def _ f g).trans <|
        (congrArg₂ (· ≫ ·) (Boundary.ii_cutInv f).symm (Boundary.ii_cutInv g).symm).trans <|
          (CategoryTheory.unop_comp).symm.trans <|
            (congrArg Quiver.Hom.unop (II.map_comp _ _).symm).trans
              (iiOpToBoundary_map_hom _).symm
  rw [h]
  exact Boundary.cutInv_ii (Boundary.cutInv g ≫ Boundary.cutInv f)

@[simp]
theorem Boundary.cutInv_δ {n : ℕ} (i : Fin (n + 1)) :
    Boundary.cutInv (Boundary.δ i) = _root_.SimplexCategory.σ i := by
  rw [← iiOpToBoundary_map_σ]
  exact Boundary.cutInv_ii (_root_.SimplexCategory.σ i)

@[simp]
theorem Boundary.cutInv_σ {n : ℕ} (i : Fin (n + 2)) :
    Boundary.cutInv (Boundary.σ i) = _root_.SimplexCategory.δ i := by
  rw [← iiOpToBoundary_map_δ]
  exact Boundary.cutInv_ii (_root_.SimplexCategory.δ i)

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

@[simp]
theorem boundaryToAugmentedOp_map_succ {n m : ℕ}
    (f : (⟨⦋n + 1⦌⟩ : Boundary) ⟶ ⟨⦋m + 1⦌⟩) :
    boundaryToAugmentedOp.map f = (Boundary.cutInv f).op :=
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

/-- `iiOpToBoundary` is full. -/
instance : iiOpToBoundary.Full where
  map_surjective {x y} g := by
    obtain ⟨⟨n⟩⟩ := x
    obtain ⟨⟨m⟩⟩ := y
    exact ⟨(Boundary.cutInv g).op, WideSubcategory.hom_ext _ (Boundary.ii_cutInv g)⟩

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

theorem boundaryToAugmentedOp_map_δ {n : ℕ} (i : Fin (n + 1)) :
    boundaryToAugmentedOp.map (Boundary.δ i) =
      (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.σ i)).op := by
  rw [← iiOpToBoundary_map_σ]
  exact Quiver.Hom.unop_inj (Boundary.cutInv_ii (_root_.SimplexCategory.σ i))

theorem boundaryToAugmentedOp_map_σ {n : ℕ} (i : Fin (n + 2)) :
    boundaryToAugmentedOp.map (Boundary.σ i) =
      (AugmentedSimplexCategory.inclusion.map (_root_.SimplexCategory.δ i)).op := by
  rw [← iiOpToBoundary_map_δ]
  exact Quiver.Hom.unop_inj (Boundary.cutInv_ii (_root_.SimplexCategory.δ i))

end TauCeti.SimplexCategory
