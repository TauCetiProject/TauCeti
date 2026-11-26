/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Closed.Braided
public import TauCeti.Topology.Convenient.GeneratedBy
public import TauCeti.Topology.Convenient.HomSpace
import Mathlib.CategoryTheory.Elementwise

/-!
# Cartesian closed structure on categories of generated spaces

Given a family of topological spaces `G : ι → Type u`, Mathlib defines the full subcategory
`GeneratedByTopCat G` of `G`-generated spaces in `TopCat` and the equivalent Escardó–Lawson–Simpson
category `ContinuousGeneratedByCat G` of all spaces and `G`-continuous maps
(`ContinuousMapGeneratedBy G Y Z`).

This file equips both categories with chosen finite products (`CartesianMonoidalCategory` and
`BraidedCategory`) and, when each `G i` is locally compact and each `G i × G j` is `G`-generated,
with the `MonoidalClosed` structure induced by `Topology.ContinuousMapGeneratedBy.curryEquiv`:

* In `ContinuousGeneratedByCat G`, the product is `Y × Z` and `(ihom Y).obj Z` is
  `ContinuousMapGeneratedBy G Y Z`.
* In `GeneratedByTopCat G`, the product is `WithGeneratedByTopology G (Y × Z)` and `(ihom Y).obj Z`
  is `WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z)`. When `Y × Z` is `G`-generated
  (in particular when one factor is locally compact under the closedness hypotheses on `G`),
  `GeneratedByTopCat.toTopCat` preserves the binary product
  (`GeneratedByTopCat.preservesLimit_pair_toTopCat`).
* For arbitrary `Y, Z, T : GeneratedByTopCat G`, `(ihom Y).obj T` is canonically isomorphic to the
  `G`-generated refinement `WithGeneratedByTopology G C(Y, T)` of the compact-open mapping space
  (`GeneratedByTopCat.ihomIsoCompactOpen`), yielding the compact-open exponential law
  `GeneratedByTopCat.compactOpenCurryIso`.

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Topology

universe v t u

namespace ContinuousGeneratedByCat

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]

/-- `PUnit` is terminal in `ContinuousGeneratedByCat G`. -/
@[expose]
def isTerminalPUnit : IsTerminal (of (X := G) PUnit.{v + 1}) :=
  have : ∀ Y : ContinuousGeneratedByCat.{v} G, Unique (Y ⟶ of (X := G) PUnit.{v + 1}) := fun _ ↦
    ⟨⟨homMk (fun _ ↦ PUnit.unit) continuous_const.continuousGeneratedBy⟩, fun _ ↦ by ext⟩
  IsTerminal.ofUnique _

/-- First projection from the binary product in `ContinuousGeneratedByCat G`. -/
@[expose]
def prodFst (Y Z : ContinuousGeneratedByCat.{v} G) : of (X := G) (Y × Z) ⟶ Y :=
  homMk Prod.fst continuous_fst.continuousGeneratedBy

/-- Second projection from the binary product in `ContinuousGeneratedByCat G`. -/
@[expose]
def prodSnd (Y Z : ContinuousGeneratedByCat.{v} G) : of (X := G) (Y × Z) ⟶ Z :=
  homMk Prod.snd continuous_snd.continuousGeneratedBy

/-- The explicit binary product fan in `ContinuousGeneratedByCat G`, whose point is `Y × Z` with
the ordinary product topology. -/
@[expose]
def prodBinaryFan (Y Z : ContinuousGeneratedByCat.{v} G) : BinaryFan Y Z :=
  BinaryFan.mk (prodFst Y Z) (prodSnd Y Z)

/-- The ordinary product `Y × Z` is a categorical binary product in `ContinuousGeneratedByCat G`. -/
@[expose]
def prodBinaryFanIsLimit (Y Z : ContinuousGeneratedByCat.{v} G) :
    IsLimit (prodBinaryFan Y Z) where
  lift := fun S : BinaryFan Y Z ↦ homMk (fun s ↦ (S.fst s, S.snd s))
    fun _ p ↦ (S.fst.hom.prop p).prodMk (S.snd.hom.prop p)
  fac := by rintro S (_ | _) <;> rfl
  uniq S m hm := by
    ext s
    exact Prod.ext (ConcreteCategory.congr_hom (hm ⟨WalkingPair.left⟩) s)
      (ConcreteCategory.congr_hom (hm ⟨WalkingPair.right⟩) s)

instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory (ContinuousGeneratedByCat.{v} G) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩

instance instBraidedCategory : BraidedCategory (ContinuousGeneratedByCat.{v} G) :=
  .ofCartesianMonoidalCategory

@[simp]
theorem tensor_apply {W X Y Z : ContinuousGeneratedByCat.{v} G} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : ↑(W ⊗ Y)) : (f ⊗ₘ g) p = (f p.1, g p.2) := rfl

@[simp]
theorem whiskerLeft_apply (X : ContinuousGeneratedByCat.{v} G)
    {Y Z : ContinuousGeneratedByCat.{v} G} (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (p.1, f p.2) := rfl

@[simp]
theorem whiskerRight_apply {Y Z : ContinuousGeneratedByCat.{v} G} (f : Y ⟶ Z)
    (X : ContinuousGeneratedByCat.{v} G) (p : ↑(Y ⊗ X)) : (f ▷ X) p = (f p.1, p.2) := rfl

@[simp]
theorem fst_apply (X Y : ContinuousGeneratedByCat.{v} G) (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.fst X Y p = p.1 := rfl

@[simp]
theorem snd_apply (X Y : ContinuousGeneratedByCat.{v} G) (p : ↑(X ⊗ Y)) :
    CartesianMonoidalCategory.snd X Y p = p.2 := rfl

@[simp]
protected theorem lift_apply {X Y Z : ContinuousGeneratedByCat.{v} G} (f : X ⟶ Y) (g : X ⟶ Z)
    (x : X) : CartesianMonoidalCategory.lift f g x = (f x, g x) := rfl

@[simp]
theorem braiding_hom_apply {Y Z : ContinuousGeneratedByCat.{v} G} (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = p.swap := rfl

@[simp]
theorem braiding_inv_apply {Y Z : ContinuousGeneratedByCat.{v} G} (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = p.swap := rfl

@[simp]
theorem associator_hom_apply {W Y Z : ContinuousGeneratedByCat.{v} G} (p : ↑((W ⊗ Y) ⊗ Z)) :
    (α_ W Y Z).hom p = (p.1.1, (p.1.2, p.2)) := rfl

@[simp]
theorem associator_inv_apply {W Y Z : ContinuousGeneratedByCat.{v} G} (p : ↑(W ⊗ (Y ⊗ Z))) :
    (α_ W Y Z).inv p = ((p.1, p.2.1), p.2.2) := rfl

section Closed

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]

/-- The internal hom functor on `ContinuousGeneratedByCat G`, sending `Z` to the `G`-probed
mapping space `ContinuousMapGeneratedBy G Y Z`. -/
@[expose, simps]
def ihomFunctor (Y : ContinuousGeneratedByCat.{v} G) :
    ContinuousGeneratedByCat.{v} G ⥤ ContinuousGeneratedByCat.{v} G where
  obj Z := of (ContinuousMapGeneratedBy G Y Z)
  map p := ConcreteCategory.ofHom p.hom.postcomp

instance instFunLikeIhomFunctor (Y Z : ContinuousGeneratedByCat.{v} G) :
    FunLike ↑((ihomFunctor Y).obj Z) Y Z :=
  inferInstanceAs (FunLike (ContinuousMapGeneratedBy G Y Z) Y Z)

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in
`ContinuousGeneratedByCat G`. -/
def curryEquiv (Y Z T : ContinuousGeneratedByCat.{v} G) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T) where
  toFun f := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv f.hom)
  invFun g := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv.symm g.hom)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp]
theorem curryEquiv_apply_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (f : Y ⊗ Z ⟶ T)
    (z : Z) (y : Y) : (curryEquiv Y Z T f z) y = f (y, z) := (rfl)

@[simp]
theorem curryEquiv_symm_apply {Y Z T : ContinuousGeneratedByCat.{v} G}
    (g : Z ⟶ (ihomFunctor Y).obj T) (p : ↑(Y ⊗ Z)) :
    (curryEquiv Y Z T).symm g p = g p.2 p.1 := (rfl)

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `ContinuousGeneratedByCat G`. -/
def tensorLeftAdjunction (Y : ContinuousGeneratedByCat.{v} G) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm _ _ := by ext ⟨_, _⟩; rfl
      homEquiv_naturality_right _ _ := by ext; rfl }

instance instMonoidalClosed : MonoidalClosed (ContinuousGeneratedByCat.{v} G) where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

instance instFunLikeIhom (Y Z : ContinuousGeneratedByCat.{v} G) :
    FunLike ↑((ihom Y).obj Z) Y Z :=
  inferInstanceAs (FunLike (ContinuousMapGeneratedBy G Y Z) Y Z)

instance instFunLikeTensorLeftCompIhom (Y Z : ContinuousGeneratedByCat.{v} G) :
    FunLike ↑((tensorLeft Y ⋙ ihom Y).obj Z) Y ↑(Y ⊗ Z) :=
  inferInstanceAs (FunLike ↑((ihom Y).obj (Y ⊗ Z)) Y ↑(Y ⊗ Z))

@[simp]
theorem ihom_map_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (p : Z ⟶ T)
    (g : ↑((ihom Y).obj Z)) (y : Y) : ((ihom Y).map p g) y = p (g y) := rfl

/-- The hom-set bijection of the internal-hom adjunction on `ContinuousGeneratedByCat G` is
`curryEquiv`. -/
theorem ihom_adjunction_homEquiv (Y Z T : ContinuousGeneratedByCat.{v} G) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem curry_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (MonoidalClosed.curry f z) y = f (y, z) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, ihom_adjunction_homEquiv]
  exact curryEquiv_apply_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : ContinuousGeneratedByCat.{v} G} (g : Z ⟶ (ihom Y).obj T)
    (p : ↑(Y ⊗ Z)) : MonoidalClosed.uncurry g p = g p.2 p.1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, ihom_adjunction_homEquiv]
  exact curryEquiv_symm_apply g p

@[simp]
theorem ihom_ev_app_apply (Y Z : ContinuousGeneratedByCat.{v} G) (p : ↑(Y ⊗ (ihom Y).obj Z)) :
    dsimp% only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj, Functor.id_obj]
      ((ihom.ev Y).app Z p) = p.2 p.1 := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]; rfl

@[simp]
theorem ihom_coev_app_apply (Y Z : ContinuousGeneratedByCat.{v} G) (z : Z) (y : Y) :
    dsimp% only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj, Functor.id_obj]
      (((ihom.coev Y).app Z z) y) = (y, z) := by
  rw [← MonoidalClosed.curry_id_eq_coev]; exact curry_apply (𝟙 _) z y

@[simp]
theorem pre_app_apply {Y₁ Y₂ T : ContinuousGeneratedByCat.{v} G} (f : Y₂ ⟶ Y₁)
    (g : ↑((ihom Y₁).obj T)) (y₂ : Y₂) :
    ((MonoidalClosed.pre f).app T g) y₂ = g (f y₂) := by
  let p : ↑(Y₂ ⊗ (ihom Y₁).obj T) := (y₂, g)
  let fp : ↑(Y₁ ⊗ (ihom Y₁).obj T) := (f y₂, g)
  have h := uncurry_apply ((MonoidalClosed.pre f).app T) p
  rw [MonoidalClosed.uncurry_pre, CategoryTheory.comp_apply, whiskerRight_apply] at h
  exact h.symm.trans (ihom_ev_app_apply Y₁ T fp)

@[simp]
theorem ihomTensorIso_hom_apply (Y Z T : ContinuousGeneratedByCat.{v} G)
    (g : ↑((ihom (Y ⊗ Z)).obj T)) (y : Y) (z : Z) :
    (((ihomTensorIso Y Z T).hom g) y) z = g (y, z) := by
  let h : ↑((ihom (Z ⊗ Y)).obj T) := (MonoidalClosed.pre (β_ Z Y).hom).app T g
  let yh : ↑(Y ⊗ (ihom (Z ⊗ Y)).obj T) := (y, h)
  let zyh : ↑(Z ⊗ (Y ⊗ (ihom (Z ⊗ Y)).obj T)) := (z, yh)
  let zy_h : ↑((Z ⊗ Y) ⊗ (ihom (Z ⊗ Y)).obj T) := ((z, y), h)
  let zy : ↑(Z ⊗ Y) := (z, y)
  calc
    (((ihomTensorIso Y Z T).hom g) y) z = ((ihomCurry Z Y T h) y) z := by
      rw [MonoidalClosed.ihomTensorIso_hom, CategoryTheory.comp_apply]
    _ = MonoidalClosed.uncurry (MonoidalClosed.uncurry (ihomCurry Z Y T)) zyh := by
      rw [uncurry_apply, uncurry_apply]
    _ = ((α_ Z Y _).inv ≫ (ihom.ev (Z ⊗ Y)).app T) zyh := by
      rw [MonoidalClosed.uncurry_uncurry_ihomCurry]
    _ = (ihom.ev (Z ⊗ Y)).app T zy_h := by
      rw [CategoryTheory.comp_apply]
      exact congrArg ((ihom.ev (Z ⊗ Y)).app T) (associator_inv_apply zyh)
    _ = h zy := ihom_ev_app_apply (Z ⊗ Y) T zy_h
    _ = g (y, z) := by rw [pre_app_apply]; exact congrArg g (braiding_hom_apply zy)

@[simp]
theorem ihomTensorIso_inv_apply (Y Z T : ContinuousGeneratedByCat.{v} G)
    (h : ↑((ihom Y).obj ((ihom Z).obj T))) (p : ↑(Y ⊗ Z)) :
    ((ihomTensorIso Y Z T).inv h) p = (h p.1) p.2 := by
  rcases p with ⟨y, z⟩
  simpa [Iso.inv_hom_id_apply] using
    (ihomTensorIso_hom_apply Y Z T ((ihomTensorIso Y Z T).inv h) y z).symm

end Closed

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

variable {ι : Type t} {G : ι → Type u} [∀ i, TopologicalSpace (G i)]

/-- `PUnit` is terminal in `GeneratedByTopCat G`. -/
@[expose]
def isTerminalPUnit : IsTerminal (of (X := G) PUnit.{v + 1}) :=
  have : ∀ Y : GeneratedByTopCat.{v} G, Unique (Y ⟶ of (X := G) PUnit.{v + 1}) := fun _ ↦
    ⟨⟨ObjectProperty.homMk (TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)⟩, fun _ ↦ by ext⟩
  IsTerminal.ofUnique _

/-- First projection from the convenient product `WithGeneratedByTopology G (Y × Z)`. -/
@[expose]
def prodFst (Y Z : GeneratedByTopCat.{v} G) :
    of (X := G) (WithGeneratedByTopology G (Y × Z)) ⟶ Y :=
  ObjectProperty.homMk (TopCat.ofHom ⟨fun p ↦ (WithGeneratedByTopology.equiv p).1,
    continuous_fst.comp WithGeneratedByTopology.continuous_equiv⟩)

/-- Second projection from the convenient product `WithGeneratedByTopology G (Y × Z)`. -/
@[expose]
def prodSnd (Y Z : GeneratedByTopCat.{v} G) :
    of (X := G) (WithGeneratedByTopology G (Y × Z)) ⟶ Z :=
  ObjectProperty.homMk (TopCat.ofHom ⟨fun p ↦ (WithGeneratedByTopology.equiv p).2,
    continuous_snd.comp WithGeneratedByTopology.continuous_equiv⟩)

@[simp]
theorem prodFst_apply (Y Z : GeneratedByTopCat.{v} G) (p : WithGeneratedByTopology G (Y × Z)) :
    prodFst Y Z p = (WithGeneratedByTopology.equiv p).1 := rfl

@[simp]
theorem prodSnd_apply (Y Z : GeneratedByTopCat.{v} G) (p : WithGeneratedByTopology G (Y × Z)) :
    prodSnd Y Z p = (WithGeneratedByTopology.equiv p).2 := rfl

/-- The explicit binary product fan in `GeneratedByTopCat G`, whose point is the generated
refinement `WithGeneratedByTopology G (Y × Z)` of the ordinary topological product. -/
@[expose]
def prodBinaryFan (Y Z : GeneratedByTopCat.{v} G) : BinaryFan Y Z :=
  BinaryFan.mk (prodFst Y Z) (prodSnd Y Z)

/-- The generated refinement `WithGeneratedByTopology G (Y × Z)` is a categorical binary product in
`GeneratedByTopCat G`. -/
@[expose]
def prodBinaryFanIsLimit (Y Z : GeneratedByTopCat.{v} G) : IsLimit (prodBinaryFan Y Z) where
  lift := fun S : BinaryFan Y Z ↦ ObjectProperty.homMk (TopCat.ofHom
    ⟨fun s ↦ WithGeneratedByTopology.equiv.symm (S.fst.hom.hom s, S.snd.hom.hom s),
      (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := G)
        (fun s : S.pt ↦ (S.fst.hom.hom s, S.snd.hom.hom s))).2
        (S.fst.hom.hom.continuous.prodMk S.snd.hom.hom.continuous)⟩)
  fac := by rintro S (_ | _) <;> rfl
  uniq S m hm := by
    ext x
    apply (WithGeneratedByTopology.equiv (X := G)).injective
    exact Prod.ext
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (hm ⟨WalkingPair.left⟩)) x)
      (ConcreteCategory.congr_hom (congrArg InducedCategory.Hom.hom (hm ⟨WalkingPair.right⟩)) x)

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (GeneratedByTopCat.{v} G) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩

instance instBraidedCategory : BraidedCategory (GeneratedByTopCat.{v} G) :=
  .ofCartesianMonoidalCategory

/-- The canonical bijection identifying points of `Y ⊗ Z` in `GeneratedByTopCat G` with `Y × Z`. -/
def tensorEquiv (Y Z : GeneratedByTopCat.{v} G) : ↑(Y ⊗ Z) ≃ Y × Z :=
  WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)

@[continuity, fun_prop]
theorem continuous_tensorEquiv (Y Z : GeneratedByTopCat.{v} G) : Continuous (tensorEquiv Y Z) :=
  WithGeneratedByTopology.continuous_equiv

instance instT2SpaceTensor (Y Z : GeneratedByTopCat.{v} G) [T2Space Y] [T2Space Z] :
    T2Space ↑(Y ⊗ Z) := inferInstanceAs (T2Space (WithGeneratedByTopology G (Y × Z)))

instance instNontrivialTensorLeft (Y Z : GeneratedByTopCat.{v} G) [Nontrivial Y] [Nonempty Z] :
    Nontrivial ↑(Y ⊗ Z) := (tensorEquiv Y Z).nontrivial

instance instNontrivialTensorRight (Y Z : GeneratedByTopCat.{v} G) [Nonempty Y] [Nontrivial Z] :
    Nontrivial ↑(Y ⊗ Z) := (tensorEquiv Y Z).nontrivial

@[ext]
theorem tensor_ext {Y Z : GeneratedByTopCat.{v} G} {p q : ↑(Y ⊗ Z)}
    (h : tensorEquiv Y Z p = tensorEquiv Y Z q) : p = q :=
  (tensorEquiv Y Z).injective h

@[simp]
theorem whiskerLeft_apply (X : GeneratedByTopCat.{v} G) {Y Z : GeneratedByTopCat.{v} G}
    (f : Y ⟶ Z) (p : ↑(X ⊗ Y)) :
    (X ◁ f) p = (tensorEquiv X Z).symm ((tensorEquiv X Y p).1, f (tensorEquiv X Y p).2) := (rfl)

@[simp]
theorem fst_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ Z)) :
    CartesianMonoidalCategory.fst Y Z p = (tensorEquiv Y Z p).1 := (rfl)

@[simp]
theorem snd_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ Z)) :
    CartesianMonoidalCategory.snd Y Z p = (tensorEquiv Y Z p).2 := (rfl)

@[simp]
protected theorem lift_apply {X Y Z : GeneratedByTopCat.{v} G} (f : X ⟶ Y) (g : X ⟶ Z) (x : X) :
    CartesianMonoidalCategory.lift f g x = (tensorEquiv Y Z).symm (f x, g x) := (rfl)

private theorem eq_tensorEquiv_symm {Y Z : GeneratedByTopCat.{v} G} {p : ↑(Y ⊗ Z)} {y : Y} {z : Z}
    (h₁ : CartesianMonoidalCategory.fst Y Z p = y)
    (h₂ : CartesianMonoidalCategory.snd Y Z p = z) :
    p = (tensorEquiv Y Z).symm (y, z) :=
  (tensorEquiv Y Z).injective <| (Prod.ext h₁ h₂).trans ((tensorEquiv Y Z).apply_symm_apply _).symm

@[simp]
theorem tensor_apply {W₁ W₂ Y Z : GeneratedByTopCat.{v} G} (f : W₁ ⟶ Y) (g : W₂ ⟶ Z)
    (p : ↑(W₁ ⊗ W₂)) :
    (f ⊗ₘ g) p = (tensorEquiv Y Z).symm (f (tensorEquiv W₁ W₂ p).1, g (tensorEquiv W₁ W₂ p).2) :=
  eq_tensorEquiv_symm congr($(tensorHom_fst f g) p) congr($(tensorHom_snd f g) p)

@[simp]
theorem whiskerRight_apply {Y₁ Y₂ : GeneratedByTopCat.{v} G} (f : Y₁ ⟶ Y₂)
    (Z : GeneratedByTopCat.{v} G) (p : ↑(Y₁ ⊗ Z)) :
    (f ▷ Z) p = (tensorEquiv Y₂ Z).symm (f (tensorEquiv Y₁ Z p).1, (tensorEquiv Y₁ Z p).2) :=
  eq_tensorEquiv_symm congr($(whiskerRight_fst f Z) p) congr($(whiskerRight_snd f Z) p)

@[simp]
theorem braiding_hom_apply {Y Z : GeneratedByTopCat.{v} G} (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (tensorEquiv Z Y).symm (tensorEquiv Y Z p).swap :=
  eq_tensorEquiv_symm congr($(braiding_hom_fst Y Z) p) congr($(braiding_hom_snd Y Z) p)

@[simp]
theorem braiding_inv_apply {Y Z : GeneratedByTopCat.{v} G} (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = (tensorEquiv Y Z).symm (tensorEquiv Z Y p).swap :=
  eq_tensorEquiv_symm congr($(braiding_inv_fst Y Z) p) congr($(braiding_inv_snd Y Z) p)

@[simp]
theorem associator_hom_apply {W Y Z : GeneratedByTopCat.{v} G} (p : ↑((W ⊗ Y) ⊗ Z)) :
    (α_ W Y Z).hom p = (tensorEquiv W (Y ⊗ Z)).symm ((tensorEquiv W Y (tensorEquiv _ Z p).1).1,
      (tensorEquiv Y Z).symm ((tensorEquiv W Y (tensorEquiv _ Z p).1).2, (tensorEquiv _ Z p).2)) :=
  eq_tensorEquiv_symm congr($(associator_hom_fst W Y Z) p)
    (eq_tensorEquiv_symm congr($(associator_hom_snd_fst W Y Z) p)
      congr($(associator_hom_snd_snd W Y Z) p))

@[simp]
theorem associator_inv_apply {W Y Z : GeneratedByTopCat.{v} G} (p : ↑(W ⊗ (Y ⊗ Z))) :
    (α_ W Y Z).inv p = (tensorEquiv (W ⊗ Y) Z).symm ((tensorEquiv W Y).symm
      ((tensorEquiv W _ p).1, (tensorEquiv Y Z (tensorEquiv W _ p).2).1),
      (tensorEquiv Y Z (tensorEquiv W _ p).2).2) :=
  eq_tensorEquiv_symm (eq_tensorEquiv_symm congr($(associator_inv_fst_fst W Y Z) p)
    congr($(associator_inv_fst_snd W Y Z) p)) congr($(associator_inv_snd W Y Z) p)

@[simp]
theorem prodComparison_toTopCat_apply (Y Z : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ Z)) :
    dsimp% CartesianMonoidalCategory.prodComparison (toTopCat (X := G)) Y Z p =
      tensorEquiv Y Z p :=
  Prod.ext congr($(CartesianMonoidalCategory.prodComparison_fst (toTopCat (X := G)) Y Z) p)
    congr($(CartesianMonoidalCategory.prodComparison_snd (toTopCat (X := G)) Y Z) p)

/-- Whenever the ordinary product `Y × Z` is already `G`-generated, the forgetful functor
`GeneratedByTopCat.toTopCat` preserves the binary product of `Y` and `Z`. -/
instance preservesLimit_pair_toTopCat (Y Z : GeneratedByTopCat.{v} G) [IsGeneratedBy G (Y × Z)] :
    PreservesLimit (pair Y Z) (toTopCat (X := G)) := by
  have h : CartesianMonoidalCategory.prodComparison (toTopCat (X := G)) Y Z =
      (TopCat.isoOfHomeo (IsGeneratedBy.homeomorph (X := G) (Y := Y × Z))).hom :=
    TopCat.ext (prodComparison_toTopCat_apply Y Z)
  have : IsIso (CartesianMonoidalCategory.prodComparison (toTopCat (X := G)) Y Z) :=
    h ▸ inferInstance
  exact preservesLimit_pair_of_isIso_prodComparison (toTopCat (X := G)) Y Z

@[simp]
theorem prodComparisonIso_toTopCat_inv_apply (Y Z : GeneratedByTopCat.{v} G)
    [PreservesLimit (pair Y Z) (toTopCat (X := G))] (p : Y × Z) :
    dsimp% (CartesianMonoidalCategory.prodComparisonIso (toTopCat (X := G)) Y Z).inv p =
      (tensorEquiv Y Z).symm p := by
  apply (tensorEquiv Y Z).injective
  rw [Equiv.apply_symm_apply, ← prodComparison_toTopCat_apply]
  exact congr($((CartesianMonoidalCategory.prodComparisonIso (toTopCat (X := G)) Y Z).inv_hom_id) p)

section Closed

variable [∀ i, LocallyCompactSpace (G i)] [∀ i j, IsGeneratedBy G (G i × G j)]

instance preservesLimit_pair_toTopCat_of_locallyCompactSpace_left
    (Y Z : GeneratedByTopCat.{v} G) [LocallyCompactSpace Y] :
    PreservesLimit (pair Y Z) (toTopCat (X := G)) :=
  have := IsGeneratedBy.prod_of_locallyCompactSpace_left (G := G) (Y := Y) (Z := Z)
  inferInstance

instance preservesLimit_pair_toTopCat_of_locallyCompactSpace_right
    (Y Z : GeneratedByTopCat.{v} G) [LocallyCompactSpace Z] :
    PreservesLimit (pair Y Z) (toTopCat (X := G)) :=
  have := IsGeneratedBy.prod_of_locallyCompactSpace_right (G := G) (Y := Y) (Z := Z)
  inferInstance

/-- The internal hom functor on `GeneratedByTopCat G`, sending `Z` to the `G`-generated refinement
of `ContinuousMapGeneratedBy G Y Z`. -/
@[expose, simps! obj]
def ihomFunctor (Y : GeneratedByTopCat.{v} G) :
    GeneratedByTopCat.{v} G ⥤ GeneratedByTopCat.{v} G where
  obj Z := of (WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y Z))
  map p := ObjectProperty.homMk (TopCat.ofHom
    ((p.hom.hom.toContinuousMapGeneratedBy G).postcomp (Y := Y)).prop.continuousMap)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem ihomFunctor_map_apply {Y Z T : GeneratedByTopCat.{v} G} (p : Z ⟶ T)
    (g : ↑((ihomFunctor Y).obj Z)) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
      ((ihomFunctor Y).map p g)) y =
      p ((WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y Z) g) y) := rfl

/-- Currying a morphism `Y ⊗ Z ⟶ T` in `GeneratedByTopCat G`. -/
def curryHom {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) : Z ⟶ (ihomFunctor Y).obj T :=
  let c := (ContinuousMapGeneratedBy.curryEquiv (X := G)
    { toFun p := f.hom.hom ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm p)
      prop := fun _ q ↦ f.hom.hom.continuous.comp
        ((IsGeneratedBy.equiv_symm_comp_continuous_iff (X := G) q).2 q.continuous) })
    |>.toContinuousMap
  ObjectProperty.homMk <| TopCat.ofHom
    ⟨(WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)).symm ∘ c,
      (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := G) c).2 c.continuous⟩

/-- Uncurrying a morphism `Z ⟶ (ihomFunctor Y).obj T` in `GeneratedByTopCat G`. -/
def uncurryHom {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihomFunctor Y).obj T) : Y ⊗ Z ⟶ T :=
  let g₀ : C(Z, ContinuousMapGeneratedBy G Y T) :=
    ⟨WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T) ∘ g.hom.hom,
      WithGeneratedByTopology.continuous_equiv.comp g.hom.hom.continuous⟩
  let u := ContinuousMapGeneratedBy.curryEquiv.symm (g₀.toContinuousMapGeneratedBy G)
  ObjectProperty.homMk <| TopCat.ofHom
    ⟨WithGeneratedByTopology.equiv (X := G) (Y := T) ∘ u.prop.continuousMap,
      WithGeneratedByTopology.continuous_equiv.comp u.prop.continuousMap.continuous⟩

@[simp]
theorem equiv_curryHom_apply {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
      (curryHom f z)) y =
      f ((WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z)) := (rfl)

@[simp]
theorem uncurryHom_apply {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihomFunctor Y).obj T)
    (p : ↑(Y ⊗ Z)) :
    uncurryHom g p =
      (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
        (g (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).2))
        (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z) p).1 := (rfl)

/-- Currying equivalence `(Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T)` in `GeneratedByTopCat G`. -/
def curryEquiv (Y Z T : GeneratedByTopCat.{v} G) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ihomFunctor Y).obj T) where
  toFun := curryHom
  invFun := uncurryHom
  left_inv _ := by ext; rfl
  right_inv g := by
    ext z
    apply (WithGeneratedByTopology.equiv (X := G)
      (Y := ContinuousMapGeneratedBy G Y T)).injective
    ext y
    exact equiv_curryHom_apply (uncurryHom g) z y

@[simp]
theorem curryEquiv_apply {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) :
    curryEquiv Y Z T f = curryHom f := (rfl)

@[simp]
theorem curryEquiv_symm_apply {Y Z T : GeneratedByTopCat.{v} G}
    (g : Z ⟶ (ihomFunctor Y).obj T) :
    (curryEquiv Y Z T).symm g = uncurryHom g := (rfl)

/-- Naturality of `curryEquiv.symm` in the source: precomposing with `f` corresponds to
precomposing with `Y ◁ f`. -/
theorem curryEquiv_symm_comp {Y Z' Z T : GeneratedByTopCat.{v} G} (f : Z' ⟶ Z)
    (g : Z ⟶ (ihomFunctor Y).obj T) :
    (curryEquiv Y Z' T).symm (f ≫ g) = Y ◁ f ≫ (curryEquiv Y Z T).symm g := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ ?_
  let q : ↑(Y ⊗ Z) := (tensorEquiv Y Z).symm ((tensorEquiv Y Z' p).1, f (tensorEquiv Y Z' p).2)
  calc
    (curryEquiv Y Z' T).symm (f ≫ g) p
      = (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
          (g (f (tensorEquiv Y Z' p).2))) (tensorEquiv Y Z' p).1 := by
        rw [curryEquiv_symm_apply, uncurryHom_apply, CategoryTheory.comp_apply]; rfl
    _ = (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T)
          (g (tensorEquiv Y Z q).2)) (tensorEquiv Y Z q).1 := by
        rw [Equiv.apply_symm_apply]
    _ = uncurryHom g q := (uncurryHom_apply g q).symm
    _ = (Y ◁ f ≫ (curryEquiv Y Z T).symm g) p := by
        rw [CategoryTheory.comp_apply, curryEquiv_symm_apply, whiskerLeft_apply]

/-- Naturality of `curryEquiv` in the target: postcomposing with `g` corresponds to postcomposing
with `(ihomFunctor Y).map g`. -/
theorem curryEquiv_comp {Y Z T T' : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) (g : T ⟶ T') :
    curryEquiv Y Z T' (f ≫ g) = curryEquiv Y Z T f ≫ (ihomFunctor Y).map g := by
  refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
  apply (WithGeneratedByTopology.equiv (X := G)
    (Y := ContinuousMapGeneratedBy G Y T')).injective
  refine DFunLike.ext _ _ fun y ↦ ?_
  let p : ↑(Y ⊗ Z) := (WithGeneratedByTopology.equiv (X := G) (Y := Y × Z)).symm (y, z)
  calc
    (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T')
        (curryEquiv Y Z T' (f ≫ g) z)) y
      = (f ≫ g) p := by rw [curryEquiv_apply, equiv_curryHom_apply]
    _ = g (f p) := CategoryTheory.comp_apply f g p
    _ = (WithGeneratedByTopology.equiv (X := G) (Y := ContinuousMapGeneratedBy G Y T')
          ((curryEquiv Y Z T f ≫ (ihomFunctor Y).map g) z)) y := by
        rw [CategoryTheory.comp_apply, ihomFunctor_map_apply, curryEquiv_apply,
          equiv_curryHom_apply]

/-- `Y ⊗ -` is left adjoint to `ihomFunctor Y` in `GeneratedByTopCat G`. -/
def tensorLeftAdjunction (Y : GeneratedByTopCat.{v} G) : tensorLeft Y ⊣ ihomFunctor Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv := curryEquiv Y
      homEquiv_naturality_left_symm := curryEquiv_symm_comp
      homEquiv_naturality_right := curryEquiv_comp }

instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} G) where
  closed Y := { rightAdj := ihomFunctor Y, adj := tensorLeftAdjunction Y }

/-- The canonical bijection identifying points of `(ihom Y).obj T` in `GeneratedByTopCat G` with
`G`-continuous maps `Y → T`. -/
def ihomEquiv (Y T : GeneratedByTopCat.{v} G) :
    ↑((ihom Y).obj T) ≃ ContinuousMapGeneratedBy G Y T :=
  WithGeneratedByTopology.equiv (X := G)

instance instNontrivialIhom (Y T : GeneratedByTopCat.{v} G) [Nonempty Y] [Nontrivial T] :
    Nontrivial ↑((ihom Y).obj T) :=
  inferInstanceAs (Nontrivial (WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y T)))

@[ext]
theorem ihom_obj_ext {Y T : GeneratedByTopCat.{v} G} {f g : ↑((ihom Y).obj T)}
    (h : ∀ y, ihomEquiv Y T f y = ihomEquiv Y T g y) : f = g :=
  (ihomEquiv Y T).injective (DFunLike.ext _ _ h)

@[simp]
theorem ihom_map_apply {Y Z T : GeneratedByTopCat.{v} G} (p : Z ⟶ T)
    (g : ↑((ihom Y).obj Z)) (y : Y) :
    ihomEquiv Y T ((ihom Y).map p g) y = p (ihomEquiv Y Z g y) := (rfl)

/-- The hom-set bijection of the internal-hom adjunction on `GeneratedByTopCat G` is
`curryEquiv`. -/
theorem ihom_adjunction_homEquiv (Y Z T : GeneratedByTopCat.{v} G) :
    (ihom.adjunction Y).homEquiv Z T = curryEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem equiv_curry_apply {Y Z T : GeneratedByTopCat.{v} G} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    ihomEquiv Y T (MonoidalClosed.curry f z) y = f ((tensorEquiv Y Z).symm (y, z)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, ihom_adjunction_homEquiv]
  exact equiv_curryHom_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : GeneratedByTopCat.{v} G} (g : Z ⟶ (ihom Y).obj T)
    (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p = ihomEquiv Y T (g (tensorEquiv Y Z p).2) (tensorEquiv Y Z p).1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, ihom_adjunction_homEquiv]
  exact uncurryHom_apply g p

@[simp]
theorem ihom_ev_app_apply (Y T : GeneratedByTopCat.{v} G) (p : ↑(Y ⊗ (ihom Y).obj T)) :
    dsimp% (ihom.ev Y).app T p = ihomEquiv Y T (tensorEquiv Y _ p).2 (tensorEquiv Y _ p).1 := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply, CategoryTheory.id_apply]

@[simp]
theorem ihom_coev_app_apply (Y Z : GeneratedByTopCat.{v} G) (z : Z) (y : Y) :
    dsimp% ihomEquiv Y (Y ⊗ Z) ((ihom.coev Y).app Z z) y = (tensorEquiv Y Z).symm (y, z) := by
  rw [← MonoidalClosed.curry_id_eq_coev]
  exact (equiv_curry_apply (𝟙 (Y ⊗ Z)) z y).trans rfl

@[simp]
theorem pre_app_apply {Y₁ Y₂ T : GeneratedByTopCat.{v} G} (f : Y₂ ⟶ Y₁)
    (g : ↑((ihom Y₁).obj T)) (y₂ : Y₂) :
    ihomEquiv Y₂ T ((MonoidalClosed.pre f).app T g) y₂ = ihomEquiv Y₁ T g (f y₂) := by
  have h := uncurry_apply ((MonoidalClosed.pre f).app T) ((tensorEquiv Y₂ _).symm (y₂, g))
  simpa [MonoidalClosed.uncurry_pre, CategoryTheory.comp_apply] using h.symm

@[simp]
theorem ihomCurry_apply (Z Y T : GeneratedByTopCat.{v} G)
    (g : ↑((ihom (Z ⊗ Y)).obj T)) (y : Y) (z : Z) :
    ihomEquiv Z T (ihomEquiv Y ((ihom Z).obj T) (ihomCurry Z Y T g) y) z =
      ihomEquiv (Z ⊗ Y) T g ((tensorEquiv Z Y).symm (z, y)) := by
  have h := congr($(MonoidalClosed.uncurry_uncurry_ihomCurry Z Y T)
    ((tensorEquiv Z (Y ⊗ (ihom (Z ⊗ Y)).obj T)).symm
      (z, (tensorEquiv Y ((ihom (Z ⊗ Y)).obj T)).symm (y, g))))
  simp only [uncurry_apply, CategoryTheory.comp_apply, associator_inv_apply,
    Equiv.apply_symm_apply] at h
  exact h.trans ((ihom_ev_app_apply (Z ⊗ Y) T _).trans (by simp))

@[simp]
theorem ihomTensorIso_hom_apply (Y Z T : GeneratedByTopCat.{v} G)
    (g : ↑((ihom (Y ⊗ Z)).obj T)) (y : Y) (z : Z) :
    ihomEquiv Z T (ihomEquiv Y ((ihom Z).obj T) ((ihomTensorIso Y Z T).hom g) y) z =
      ihomEquiv (Y ⊗ Z) T g ((tensorEquiv Y Z).symm (y, z)) := by
  simp [MonoidalClosed.ihomTensorIso_hom, CategoryTheory.comp_apply]

@[simp]
theorem ihomTensorIso_inv_apply (Y Z T : GeneratedByTopCat.{v} G)
    (h : ↑((ihom Y).obj ((ihom Z).obj T))) (p : ↑(Y ⊗ Z)) :
    ihomEquiv (Y ⊗ Z) T ((ihomTensorIso Y Z T).inv h) p =
      ihomEquiv Z T (ihomEquiv Y ((ihom Z).obj T) h (tensorEquiv Y Z p).1)
        (tensorEquiv Y Z p).2 := by
  simpa [Iso.inv_hom_id_apply] using (ihomTensorIso_hom_apply Y Z T
    ((ihomTensorIso Y Z T).inv h) (tensorEquiv Y Z p).1 (tensorEquiv Y Z p).2).symm

/-- Suppose `[∀ i, LocallyCompactSpace (G i)]` and `[∀ i j, IsGeneratedBy G (G i × G j)]`. For
every `Y, T : GeneratedByTopCat G`, `(ihom Y).obj T` is canonically isomorphic to the `G`-generated
refinement of the compact-open mapping space `C(Y, T)`. -/
def ihomIsoCompactOpen (Y T : GeneratedByTopCat.{v} G) :
    (ihom Y).obj T ≅ of (X := G) (WithGeneratedByTopology G C(Y, T)) :=
  ObjectProperty.isoMk (TopCat.generatedBy G)
    (TopCat.isoOfHomeo (ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap (G := G)
      (Y := Y) (Z := T)))

@[simp]
theorem ihomIsoCompactOpen_hom_apply (Y T : GeneratedByTopCat.{v} G)
    (g : ↑((ihom Y).obj T)) (y : Y) :
    dsimp% WithGeneratedByTopology.equiv (X := G) (Y := C(Y, T))
      ((ihomIsoCompactOpen Y T).hom g) y = ihomEquiv Y T g y :=
  let g' : WithGeneratedByTopology G (ContinuousMapGeneratedBy G Y T) := g
  (congrArg (fun h : C(Y, T) ↦ h y)
    (ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap_apply (G := G) g')).trans
    (ContinuousMapGeneratedBy.toContinuousMap_apply _ y)

@[simp]
theorem ihomIsoCompactOpen_inv_apply (Y T : GeneratedByTopCat.{v} G)
    (f : WithGeneratedByTopology G C(Y, T)) (y : Y) :
    ihomEquiv Y T (dsimp% (ihomIsoCompactOpen Y T).inv f) y =
      WithGeneratedByTopology.equiv (X := G) (Y := C(Y, T)) f y :=
  congr($(ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap_symm_apply
    (G := G) (Y := Y) (Z := T) f) y).trans (ContinuousMap.toContinuousMapGeneratedBy_apply _ y)

/-- Suppose `[∀ i, LocallyCompactSpace (G i)]` and `[∀ i j, IsGeneratedBy G (G i × G j)]`. For
arbitrary `Y, Z, T : GeneratedByTopCat G`, the `G`-generated refinement of `C(↑(Y ⊗ Z), T)` is
canonically isomorphic to the `G`-generated refinement of
`C(Y, WithGeneratedByTopology G C(Z, T))`. -/
def compactOpenCurryIso (Y Z T : GeneratedByTopCat.{v} G) :
    of (X := G) (WithGeneratedByTopology G C(↑(Y ⊗ Z), T)) ≅
      of (X := G) (WithGeneratedByTopology G C(Y, WithGeneratedByTopology G C(Z, T))) :=
  (ihomIsoCompactOpen (Y ⊗ Z) T).symm ≪≫ ihomTensorIso Y Z T ≪≫
    (ihom Y).mapIso (ihomIsoCompactOpen Z T) ≪≫ ihomIsoCompactOpen Y _

@[simp]
theorem compactOpenCurryIso_hom_apply (Y Z T : GeneratedByTopCat.{v} G)
    (f : WithGeneratedByTopology G C(↑(Y ⊗ Z), T)) (y : Y) (z : Z) :
    dsimp% WithGeneratedByTopology.equiv (X := G) (Y := C(Z, T))
      (WithGeneratedByTopology.equiv (X := G) (Y := C(Y, WithGeneratedByTopology G C(Z, T)))
        ((compactOpenCurryIso Y Z T).hom f) y) z =
      WithGeneratedByTopology.equiv (X := G) (Y := C(↑(Y ⊗ Z), T)) f
        ((tensorEquiv Y Z).symm (y, z)) := by
  simp only [compactOpenCurryIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    CategoryTheory.comp_apply]
  refine (congrArg
    (fun h : WithGeneratedByTopology G C(Z, T) ↦
      WithGeneratedByTopology.equiv (X := G) (Y := C(Z, T)) h z)
    ((ihomIsoCompactOpen_hom_apply Y _ _ y).trans
      (ihom_map_apply (ihomIsoCompactOpen Z T).hom _ y))).trans ?_
  simp

@[simp]
theorem compactOpenCurryIso_inv_apply (Y Z T : GeneratedByTopCat.{v} G)
    (g : WithGeneratedByTopology G C(Y, WithGeneratedByTopology G C(Z, T))) (p : ↑(Y ⊗ Z)) :
    dsimp% WithGeneratedByTopology.equiv (X := G) (Y := C(↑(Y ⊗ Z), T))
      ((compactOpenCurryIso Y Z T).inv g) p =
      WithGeneratedByTopology.equiv (X := G) (Y := C(Z, T))
        (WithGeneratedByTopology.equiv (X := G)
          (Y := C(Y, WithGeneratedByTopology G C(Z, T))) g (tensorEquiv Y Z p).1)
        (tensorEquiv Y Z p).2 := by
  simpa [Iso.inv_hom_id_apply] using (compactOpenCurryIso_hom_apply Y Z T
    ((compactOpenCurryIso Y Z T).inv g) (tensorEquiv Y Z p).1 (tensorEquiv Y Z p).2).symm

end Closed

end GeneratedByTopCat

end
