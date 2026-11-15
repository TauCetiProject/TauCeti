/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.Convenient.Product

/-!
# Cartesian monoidal closed categories of generated spaces

Let `X : ι → Type u` be a family of topological spaces. Mathlib introduces two equivalent
categories associated to `X`:

* `ContinuousGeneratedByCat.{v} X`, whose objects are all topological spaces in `Type v` and whose
  morphisms are `X`-continuous maps (`Topology.ContinuousMapGeneratedBy X Y Z`);
* `GeneratedByTopCat.{v} X`, the full subcategory of `TopCat.{v}` spanned by `X`-generated spaces.

In `ContinuousGeneratedByCat.{v} X`, a map into an ordinary topological product `Y × Z` is
`X`-continuous if and only if its two coordinate projections are `X`-continuous, so `PUnit` and
the ordinary product `Y × Z` give chosen finite products without any hypothesis on `X`. Across the
coreflective equivalence `ContinuousGeneratedByCat.equivalence`, finite products in
`GeneratedByTopCat.{v} X` refine the ordinary product topology to the convenient product
`WithGeneratedByTopology X (Y × Z)`.

When every test space `X i` is locally compact and every pairwise product `X i × X j` is
`X`-generated, Mathlib's currying bijection `Topology.ContinuousMapGeneratedBy.curryEquiv` upgrades
both `ContinuousGeneratedByCat.{v} X` and `GeneratedByTopCat.{v} X` to cartesian monoidal closed
categories:

* In `ContinuousGeneratedByCat.{v} X`, the internal hom from `Y` to `T` is
  `ContinuousMapGeneratedBy X Y T` with the topology induced by precomposition along all test maps
  `C(X i, Y)` into the compact-open spaces `C(X i, T)`.
* In `GeneratedByTopCat.{v} X`, the internal hom from `Y` to `T` is its `X`-generated refinement
  `WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)`.

## Main declarations

* `ContinuousGeneratedByCat.instCartesianMonoidalCategory` and
  `ContinuousGeneratedByCat.instMonoidalClosed`: the cartesian closed structure on `X`-continuous
  spaces and maps.
* `GeneratedByTopCat.instCartesianMonoidalCategory` and
  `GeneratedByTopCat.instMonoidalClosed`: the cartesian closed structure on `X`-generated spaces,
  with convenient product `WithGeneratedByTopology X (Y × Z)` and internal hom
  `WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)`.
* `GeneratedByTopCat.tensorEquiv` and `GeneratedByTopCat.ihomEquiv`: canonical bijections
  identifying points of `Y ⊗ Z` with `Y × Z` and points of `(ihom Y).obj T` with
  `ContinuousMapGeneratedBy X Y T`.
* `GeneratedByTopCat.curry_apply`, `GeneratedByTopCat.uncurry_apply`, and
  `GeneratedByTopCat.ihom_ev_app_apply`: explicit pointwise formulas for currying, uncurrying, and
  evaluation.

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson and A. Simpson, *Comparing Cartesian closed categories of (core) compactly
  generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

noncomputable section

universe v t u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

namespace ContinuousGeneratedByCat

/-- `PUnit` is terminal in `ContinuousGeneratedByCat X`. -/
def isTerminalPUnit : IsTerminal (of (X := X) PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ homMk (fun _ ↦ PUnit.unit) continuous_const.continuousGeneratedBy)
    (fun _ _ ↦ by ext)

/-- The first projection `Y × Z ⟶ Y` in `ContinuousGeneratedByCat X`. -/
@[expose]
def prodFst {Y Z : ContinuousGeneratedByCat.{v} X} : of (X := X) (Y × Z) ⟶ Y :=
  homMk Prod.fst continuous_fst.continuousGeneratedBy

/-- The second projection `Y × Z ⟶ Z` in `ContinuousGeneratedByCat X`. -/
@[expose]
def prodSnd {Y Z : ContinuousGeneratedByCat.{v} X} : of (X := X) (Y × Z) ⟶ Z :=
  homMk Prod.snd continuous_snd.continuousGeneratedBy

/-- The binary product fan of `Y` and `Z` in `ContinuousGeneratedByCat X`, given by the ordinary
product `Y × Z`.

Exposed so that `↑(Y ⊗ Z)` reduces to `↑Y × ↑Z` when applying morphisms to pairs. -/
@[expose]
def prodBinaryFan (Y Z : ContinuousGeneratedByCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk prodFst prodSnd

/-- The ordinary product `Y × Z` is a binary product in `ContinuousGeneratedByCat X`, because a
map into `Y × Z` is `X`-continuous if and only if both coordinate projections are. -/
@[expose]
def prodBinaryFanIsLimit (Y Z : ContinuousGeneratedByCat.{v} X) :
    IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {W} f g ↦ homMk (Z := of (X := X) (Y × Z)) (fun w ↦ (f w, g w)) <| by
      rw [continuousGeneratedBy_def]
      intro i p
      exact (f.hom.prop p).prodMk (g.hom.prop p))
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun {W} f g m h₁ h₂ ↦ by
      ext w
      exact Prod.ext (congr($h₁ w).trans rfl) (congr($h₂ w).trans rfl))

/-- Chosen finite products on `ContinuousGeneratedByCat X`, with unit `PUnit` and binary product
`Y × Z`. -/
instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory (ContinuousGeneratedByCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩)

instance instBraidedCategory : BraidedCategory (ContinuousGeneratedByCat.{v} X) :=
  .ofCartesianMonoidalCategory

section Closed

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- The internal hom functor on `ContinuousGeneratedByCat X` sending `T` to
`ContinuousMapGeneratedBy X Y T` and acting on morphisms by postcomposition.

The body is exposed so that elements of `(ihom Y).obj T` can be evaluated as `X`-continuous maps
`Y → T`. -/
@[expose]
protected def ihom (Y : ContinuousGeneratedByCat.{v} X) :
    ContinuousGeneratedByCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj T := of (X := X) (ContinuousMapGeneratedBy X Y T)
  map p := ConcreteCategory.ofHom p.hom.postcomp

/-- Currying in `ContinuousGeneratedByCat X`: `X`-continuous maps `Y × Z → T` correspond to
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T`. -/
def tensorHomEquiv (Y Z T : ContinuousGeneratedByCat.{v} X) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (ContinuousGeneratedByCat.ihom Y).obj T) where
  toFun f := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv f.hom)
  invFun g := ConcreteCategory.ofHom (ContinuousMapGeneratedBy.curryEquiv.symm g.hom)
  left_inv _ := by ext; rfl
  right_inv _ := by
    ext z
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

@[simp]
theorem tensorHomEquiv_apply_apply
    {Y Z T : ContinuousGeneratedByCat.{v} X} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    (tensorHomEquiv Y Z T f z).toFun y = f (y, z) :=
  (rfl)

@[simp]
theorem tensorHomEquiv_symm_apply
    {Y Z T : ContinuousGeneratedByCat.{v} X}
    (g : Z ⟶ (ContinuousGeneratedByCat.ihom Y).obj T) (y : Y) (z : Z) :
    (tensorHomEquiv Y Z T).symm g (y, z) = (g z).toFun y :=
  (rfl)

/-- When every `X i` is locally compact and every `X i × X j` is `X`-generated,
`ContinuousGeneratedByCat X` is cartesian monoidal closed. -/
instance instMonoidalClosed : MonoidalClosed (ContinuousGeneratedByCat.{v} X) where
  closed Y :=
    { rightAdj := ContinuousGeneratedByCat.ihom Y
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := tensorHomEquiv Y
          homEquiv_naturality_left_symm _ _ := by ext ⟨_, _⟩; rfl
          homEquiv_naturality_right _ _ := by
            ext z
            exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl) } }

end Closed

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

/-- `PUnit` is terminal in `GeneratedByTopCat X`. -/
def isTerminalPUnit : IsTerminal (of (X := X) PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ ObjectProperty.homMk (TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩))
    (fun _ _ ↦ by ext)

/-- The first projection `WithGeneratedByTopology X (Y × Z) ⟶ Y` in `GeneratedByTopCat X`. -/
@[expose]
def prodFst {Y Z : GeneratedByTopCat.{v} X} :
    of (X := X) (WithGeneratedByTopology X (Y × Z)) ⟶ Y :=
  ObjectProperty.homMk <| TopCat.ofHom
    ⟨Prod.fst ∘ WithGeneratedByTopology.equiv (X := X),
      continuous_fst.comp WithGeneratedByTopology.continuous_equiv⟩

/-- The second projection `WithGeneratedByTopology X (Y × Z) ⟶ Z` in `GeneratedByTopCat X`. -/
@[expose]
def prodSnd {Y Z : GeneratedByTopCat.{v} X} :
    of (X := X) (WithGeneratedByTopology X (Y × Z)) ⟶ Z :=
  ObjectProperty.homMk <| TopCat.ofHom
    ⟨Prod.snd ∘ WithGeneratedByTopology.equiv (X := X),
      continuous_snd.comp WithGeneratedByTopology.continuous_equiv⟩

/-- The binary product fan of `Y` and `Z` in `GeneratedByTopCat X`, given by the convenient
product `WithGeneratedByTopology X (Y × Z)`.

Exposed so that `↑(Y ⊗ Z)` reduces to `WithGeneratedByTopology X (Y × Z)`. -/
@[expose]
def prodBinaryFan (Y Z : GeneratedByTopCat.{v} X) : BinaryFan Y Z :=
  BinaryFan.mk prodFst prodSnd

/-- The convenient product `WithGeneratedByTopology X (Y × Z)` is a binary product in
`GeneratedByTopCat X`: any pair of continuous maps from an `X`-generated space `W` into `Y` and
`Z` defines a continuous map `W → Y × Z`, which lifts uniquely through the `X`-generated counit. -/
@[expose]
def prodBinaryFanIsLimit (Y Z : GeneratedByTopCat.{v} X) :
    IsLimit (prodBinaryFan Y Z) :=
  BinaryFan.IsLimit.mk _
    (fun {W} f g ↦ ObjectProperty.homMk
      (Y := of (X := X) (WithGeneratedByTopology X (Y × Z))) <| TopCat.ofHom
      ⟨fun w ↦ (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).symm (f w, g w),
        (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) _).2
          (f.hom.hom.continuous.prodMk g.hom.hom.continuous)⟩)
    (fun _ _ ↦ by ext; rfl)
    (fun _ _ ↦ by ext; rfl)
    (fun {W} f g m h₁ h₂ ↦ by
      ext w
      apply (WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)).injective
      exact Prod.ext (congr($h₁ w)) (congr($h₂ w)))

/-- Chosen finite products on `GeneratedByTopCat X`, with unit `PUnit` and binary product
`WithGeneratedByTopology X (Y × Z)`. -/
instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory (GeneratedByTopCat.{v} X) :=
  .ofChosenFiniteProducts ⟨_, isTerminalPUnit⟩
    (fun Y Z ↦ ⟨prodBinaryFan Y Z, prodBinaryFanIsLimit Y Z⟩)

instance instBraidedCategory : BraidedCategory (GeneratedByTopCat.{v} X) :=
  .ofCartesianMonoidalCategory

theorem tensorObj_def (Y Z : GeneratedByTopCat.{v} X) :
    Y ⊗ Z = of (X := X) (WithGeneratedByTopology X (Y × Z)) :=
  (rfl)

theorem tensorUnit_def :
    𝟙_ (GeneratedByTopCat.{v} X) = of (X := X) PUnit.{v + 1} :=
  (rfl)

/-- The canonical bijection identifying points of the convenient product `Y ⊗ Z` in
`GeneratedByTopCat X` with pairs in `Y × Z`. -/
@[expose]
def tensorEquiv (Y Z : GeneratedByTopCat.{v} X) : ↑(Y ⊗ Z) ≃ Y × Z :=
  WithGeneratedByTopology.equiv (X := X) (Y := Y × Z)

@[ext]
theorem tensor_ext {Y Z : GeneratedByTopCat.{v} X} {p q : ↑(Y ⊗ Z)}
    (h : tensorEquiv Y Z p = tensorEquiv Y Z q) : p = q :=
  (tensorEquiv Y Z).injective h

@[simp]
theorem fst_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    fst Y Z p = (tensorEquiv Y Z p).1 :=
  (rfl)

@[simp]
theorem snd_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    snd Y Z p = (tensorEquiv Y Z p).2 :=
  (rfl)

private theorem eq_tensorEquiv_symm {Y Z : GeneratedByTopCat.{v} X} {p : ↑(Y ⊗ Z)} {y : Y} {z : Z}
    (h₁ : fst Y Z p = y) (h₂ : snd Y Z p = z) :
    p = (tensorEquiv Y Z).symm (y, z) :=
  (tensorEquiv Y Z).injective <|
    (Prod.ext h₁ h₂).trans ((tensorEquiv Y Z).apply_symm_apply _).symm

@[simp]
theorem lift_apply {W Y Z : GeneratedByTopCat.{v} X} (f : W ⟶ Y) (g : W ⟶ Z) (w : W) :
    CartesianMonoidalCategory.lift f g w = (tensorEquiv Y Z).symm (f w, g w) :=
  eq_tensorEquiv_symm congr($(lift_fst f g) w) congr($(lift_snd f g) w)

@[simp]
theorem tensor_apply {W₁ W₂ Y Z : GeneratedByTopCat.{v} X}
    (f : W₁ ⟶ Y) (g : W₂ ⟶ Z) (p : ↑(W₁ ⊗ W₂)) :
    (f ⊗ₘ g) p =
      (tensorEquiv Y Z).symm (f (tensorEquiv W₁ W₂ p).1, g (tensorEquiv W₁ W₂ p).2) :=
  eq_tensorEquiv_symm congr($(tensorHom_fst f g) p) congr($(tensorHom_snd f g) p)

@[simp]
theorem whiskerLeft_apply (Y : GeneratedByTopCat.{v} X) {Z₁ Z₂ : GeneratedByTopCat.{v} X}
    (g : Z₁ ⟶ Z₂) (p : ↑(Y ⊗ Z₁)) :
    (Y ◁ g) p =
      (tensorEquiv Y Z₂).symm ((tensorEquiv Y Z₁ p).1, g (tensorEquiv Y Z₁ p).2) :=
  eq_tensorEquiv_symm congr($(whiskerLeft_fst Y g) p) congr($(whiskerLeft_snd Y g) p)

@[simp]
theorem whiskerRight_apply {Y₁ Y₂ : GeneratedByTopCat.{v} X} (f : Y₁ ⟶ Y₂)
    (Z : GeneratedByTopCat.{v} X) (p : ↑(Y₁ ⊗ Z)) :
    (f ▷ Z) p =
      (tensorEquiv Y₂ Z).symm (f (tensorEquiv Y₁ Z p).1, (tensorEquiv Y₁ Z p).2) :=
  eq_tensorEquiv_symm congr($(whiskerRight_fst f Z) p) congr($(whiskerRight_snd f Z) p)

@[simp]
theorem braiding_hom_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    (β_ Y Z).hom p = (tensorEquiv Z Y).symm (tensorEquiv Y Z p).swap :=
  eq_tensorEquiv_symm congr($(braiding_hom_fst Y Z) p) congr($(braiding_hom_snd Y Z) p)

@[simp]
theorem braiding_inv_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Z ⊗ Y)) :
    (β_ Y Z).inv p = (tensorEquiv Y Z).symm (tensorEquiv Z Y p).swap :=
  eq_tensorEquiv_symm congr($(braiding_inv_fst Y Z) p) congr($(braiding_inv_snd Y Z) p)

@[simp]
theorem leftUnitor_hom_apply {Y : GeneratedByTopCat.{v} X}
    (p : ↑(𝟙_ (GeneratedByTopCat.{v} X) ⊗ Y)) :
    (λ_ Y).hom p = (tensorEquiv _ Y p).2 :=
  (rfl)

@[simp]
theorem leftUnitor_inv_apply {Y : GeneratedByTopCat.{v} X} (y : Y) :
    (λ_ Y).inv y = (tensorEquiv _ Y).symm (PUnit.unit, y) :=
  eq_tensorEquiv_symm (PUnit.ext _ _) congr($(Iso.inv_hom_id (λ_ Y)) y)

@[simp]
theorem rightUnitor_hom_apply {Y : GeneratedByTopCat.{v} X}
    (p : ↑(Y ⊗ 𝟙_ (GeneratedByTopCat.{v} X))) :
    (ρ_ Y).hom p = (tensorEquiv Y _ p).1 :=
  (rfl)

@[simp]
theorem rightUnitor_inv_apply {Y : GeneratedByTopCat.{v} X} (y : Y) :
    (ρ_ Y).inv y = (tensorEquiv Y _).symm (y, PUnit.unit) :=
  eq_tensorEquiv_symm congr($(Iso.inv_hom_id (ρ_ Y)) y) (PUnit.ext _ _)

/-- The canonical comparison morphism `(Y ⊗ Z).obj ⟶ Y.obj ⊗ Z.obj` in `TopCat`, given on points
by `tensorEquiv Y Z`. -/
@[expose]
def prodComparisonHom (Y Z : GeneratedByTopCat.{v} X) :
    (Y ⊗ Z).obj ⟶ Y.obj ⊗ Z.obj :=
  TopCat.ofHom (WithGeneratedByTopology.counit X (Y × Z))

@[simp]
theorem prodComparisonHom_apply {Y Z : GeneratedByTopCat.{v} X} (p : ↑(Y ⊗ Z)) :
    prodComparisonHom Y Z p = tensorEquiv Y Z p :=
  WithGeneratedByTopology.counit_apply X (X := Y × Z) p

/-- Turn a morphism `Y ⊗ Z ⟶ T` in `GeneratedByTopCat X` into an `X`-continuous map `Y × Z → T`. -/
def homToContinuousMapGeneratedBy {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T) :
    ContinuousMapGeneratedBy X (Y × Z) T where
  toFun p := f ((tensorEquiv Y Z).symm p)
  prop := by
    rw [continuousGeneratedBy_def]
    intro i r
    exact f.hom.hom.continuous.comp
      ((IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) r).2 r.continuous)

@[simp]
theorem homToContinuousMapGeneratedBy_apply
    {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T) (p : Y × Z) :
    homToContinuousMapGeneratedBy f p = f ((tensorEquiv Y Z).symm p) :=
  (rfl)

/-- Turn an `X`-continuous map `Y × Z → T` into a morphism `Y ⊗ Z ⟶ T` in `GeneratedByTopCat X`. -/
def continuousMapGeneratedByToHom {Y Z T : GeneratedByTopCat.{v} X}
    (g : ContinuousMapGeneratedBy X (Y × Z) T) : Y ⊗ Z ⟶ T :=
  ObjectProperty.homMk (X := Y ⊗ Z) <| TopCat.ofHom
    ⟨g ∘ tensorEquiv Y Z,
      (WithGeneratedByTopology.continuous_from_iff _).2 fun _ r ↦ g.prop r⟩

@[simp]
theorem continuousMapGeneratedByToHom_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : ContinuousMapGeneratedBy X (Y × Z) T) (p : ↑(Y ⊗ Z)) :
    continuousMapGeneratedByToHom g p = g (tensorEquiv Y Z p) :=
  (rfl)

section Closed

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

/-- When `Y` is locally compact, the convenient product `Y ⊗ Z` in `GeneratedByTopCat X` has the
ordinary product topology in `TopCat`. -/
def prodComparisonIsoOfLocallyCompactLeft (Y Z : GeneratedByTopCat.{v} X)
    [LocallyCompactSpace Y] :
    (Y ⊗ Z).obj ≅ Y.obj ⊗ Z.obj :=
  TopCat.isoOfHomeo (WithGeneratedByTopology.prodHomeomorphOfLocallyCompactLeft X Y Z)

@[simp]
theorem prodComparisonIsoOfLocallyCompactLeft_hom (Y Z : GeneratedByTopCat.{v} X)
    [LocallyCompactSpace Y] :
    (prodComparisonIsoOfLocallyCompactLeft Y Z).hom = prodComparisonHom Y Z :=
  TopCat.ext fun p ↦
    (WithGeneratedByTopology.prodHomeomorphOfLocallyCompactLeft_apply X
      (Y := Y) (Z := Z) p).trans
      (WithGeneratedByTopology.counit_apply X (X := Y × Z) p).symm

/-- When `Z` is locally compact, the convenient product `Y ⊗ Z` in `GeneratedByTopCat X` has the
ordinary product topology in `TopCat`. -/
def prodComparisonIsoOfLocallyCompactRight (Y Z : GeneratedByTopCat.{v} X)
    [LocallyCompactSpace Z] :
    (Y ⊗ Z).obj ≅ Y.obj ⊗ Z.obj :=
  TopCat.isoOfHomeo (WithGeneratedByTopology.prodHomeomorphOfLocallyCompactRight X Y Z)

@[simp]
theorem prodComparisonIsoOfLocallyCompactRight_hom (Y Z : GeneratedByTopCat.{v} X)
    [LocallyCompactSpace Z] :
    (prodComparisonIsoOfLocallyCompactRight Y Z).hom = prodComparisonHom Y Z :=
  TopCat.ext fun p ↦
    (WithGeneratedByTopology.prodHomeomorphOfLocallyCompactRight_apply X
      (Y := Y) (Z := Z) p).trans
      (WithGeneratedByTopology.counit_apply X (X := Y × Z) p).symm

/-- The internal hom functor on `GeneratedByTopCat X`, sending `T` to
`WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)` and acting on morphisms by
postcomposition.

The body is exposed so that elements of `(ihom Y).obj T` can be unwrapped via `ihomEquiv` and
evaluated on points of `Y`. -/
@[expose]
protected def ihom (Y : GeneratedByTopCat.{v} X) :
    GeneratedByTopCat.{v} X ⥤ GeneratedByTopCat.{v} X where
  obj T := of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T))
  map {T T'} p := ObjectProperty.homMk
    (X := of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)))
    (Y := of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T'))) <|
    TopCat.ofHom ((ContinuousMapGeneratedBy.mk p.hom.hom
      p.hom.hom.continuous.continuousGeneratedBy).postcomp.prop.continuousMap)
  map_id T := by
    ext g
    apply (WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)).injective
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)
  map_comp {T₁ T₂ T₃} _ _ := by
    ext g
    apply (WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T₃)).injective
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

/-- Currying in `GeneratedByTopCat X`: morphisms `Y ⊗ Z ⟶ T` correspond to morphisms
`Z ⟶ (GeneratedByTopCat.ihom Y).obj T`. -/
def tensorHomEquiv (Y Z T : GeneratedByTopCat.{v} X) :
    (Y ⊗ Z ⟶ T) ≃ (Z ⟶ (GeneratedByTopCat.ihom Y).obj T) where
  toFun f := ObjectProperty.homMk (Y := (GeneratedByTopCat.ihom Y).obj T) <| TopCat.ofHom
    ⟨fun z ↦ (WithGeneratedByTopology.equiv (X := X)
        (Y := ContinuousMapGeneratedBy X Y T)).symm
        (ContinuousMapGeneratedBy.curryEquiv (homToContinuousMapGeneratedBy f) z),
      (IsGeneratedBy.equiv_symm_comp_continuous_iff (X := X) _).2 <|
        (IsGeneratedBy.continuous_iff X _).2
          (ContinuousMapGeneratedBy.curryEquiv (homToContinuousMapGeneratedBy f)).prop⟩
  invFun g := continuousMapGeneratedByToHom <|
    ContinuousMapGeneratedBy.curryEquiv.symm
      ⟨fun z ↦ WithGeneratedByTopology.equiv (X := X)
          (Y := ContinuousMapGeneratedBy X Y T) (g z),
        ((WithGeneratedByTopology.continuous_equiv (X := X)
          (Y := ContinuousMapGeneratedBy X Y T)).comp
          g.hom.hom.continuous).continuousGeneratedBy⟩
  left_inv f := by
    ext p
    exact congrArg f ((tensorEquiv Y Z).symm_apply_apply p)
  right_inv g := by
    ext z
    apply (WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)).injective
    exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

theorem tensorHomEquiv_symm_comp {Y Z Z' T : GeneratedByTopCat.{v} X}
    (f : Z' ⟶ Z) (g : Z ⟶ (GeneratedByTopCat.ihom Y).obj T) :
    (tensorHomEquiv Y Z' T).symm (f ≫ g) = Y ◁ f ≫ (tensorHomEquiv Y Z T).symm g := by
  ext p
  change WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)
      (g (f (tensorEquiv Y Z' p).2)) (tensorEquiv Y Z' p).1 =
    WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)
      (g (tensorEquiv Y Z ((Y ◁ f) p)).2) (tensorEquiv Y Z ((Y ◁ f) p)).1
  rw [whiskerLeft_apply, Equiv.apply_symm_apply]

theorem tensorHomEquiv_comp {Y Z T T' : GeneratedByTopCat.{v} X}
    (f : Y ⊗ Z ⟶ T) (g : T ⟶ T') :
    tensorHomEquiv Y Z T' (f ≫ g) =
      tensorHomEquiv Y Z T f ≫ (GeneratedByTopCat.ihom Y).map g := by
  ext z
  apply (WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T')).injective
  exact ContinuousMapGeneratedBy.ext (funext fun _ ↦ rfl)

/-- **Cartesian closedness of `GeneratedByTopCat X`.**
When every test space `X i` is locally compact and every pairwise product `X i × X j` is
`X`-generated, the category `GeneratedByTopCat X` of `X`-generated spaces is cartesian monoidal
closed. -/
instance instMonoidalClosed : MonoidalClosed (GeneratedByTopCat.{v} X) where
  closed Y :=
    { rightAdj := GeneratedByTopCat.ihom Y
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := tensorHomEquiv Y
          homEquiv_naturality_left_symm := tensorHomEquiv_symm_comp
          homEquiv_naturality_right := tensorHomEquiv_comp } }

theorem homEquiv_def (Y Z T : GeneratedByTopCat.{v} X) :
    (ihom.adjunction Y).homEquiv Z T = tensorHomEquiv Y Z T :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

theorem ihom_obj_def (Y T : GeneratedByTopCat.{v} X) :
    (ihom Y).obj T =
      of (X := X) (WithGeneratedByTopology X (ContinuousMapGeneratedBy X Y T)) :=
  (rfl)

theorem ihom_map_def {Y T T' : GeneratedByTopCat.{v} X} (p : T ⟶ T') :
    (ihom Y).map p = (GeneratedByTopCat.ihom Y).map p :=
  (rfl)

/-- The canonical bijection identifying points of the internal hom `(ihom Y).obj T` in
`GeneratedByTopCat X` with `X`-continuous maps `Y → T`. -/
@[expose]
def ihomEquiv (Y T : GeneratedByTopCat.{v} X) :
    ↑((ihom Y).obj T) ≃ ContinuousMapGeneratedBy X Y T :=
  WithGeneratedByTopology.equiv (X := X) (Y := ContinuousMapGeneratedBy X Y T)

@[ext]
theorem ihom_obj_ext {Y T : GeneratedByTopCat.{v} X} {f g : ↑((ihom Y).obj T)}
    (h : ∀ y, ihomEquiv Y T f y = ihomEquiv Y T g y) : f = g :=
  (ihomEquiv Y T).injective (DFunLike.ext _ _ h)

@[simp]
theorem ihom_map_apply {Y T T' : GeneratedByTopCat.{v} X} (p : T ⟶ T')
    (g : ↑((ihom Y).obj T)) (y : Y) :
    ihomEquiv Y T' ((ihom Y).map p g) y = p (ihomEquiv Y T g y) :=
  (rfl)

@[simp]
theorem tensorHomEquiv_apply_apply {Y Z T : GeneratedByTopCat.{v} X}
    (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    ihomEquiv Y T (tensorHomEquiv Y Z T f z) y = f ((tensorEquiv Y Z).symm (y, z)) :=
  (rfl)

@[simp]
theorem tensorHomEquiv_symm_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ (GeneratedByTopCat.ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    (tensorHomEquiv Y Z T).symm g p =
      ihomEquiv Y T (g (tensorEquiv Y Z p).2) (tensorEquiv Y Z p).1 :=
  (rfl)

@[simp]
theorem curry_apply {Y Z T : GeneratedByTopCat.{v} X} (f : Y ⊗ Z ⟶ T) (z : Z) (y : Y) :
    ihomEquiv Y T (MonoidalClosed.curry f z) y = f ((tensorEquiv Y Z).symm (y, z)) := by
  rw [← MonoidalClosed.homEquiv_apply_eq, homEquiv_def]
  exact tensorHomEquiv_apply_apply f z y

@[simp]
theorem uncurry_apply {Y Z T : GeneratedByTopCat.{v} X}
    (g : Z ⟶ (ihom Y).obj T) (p : ↑(Y ⊗ Z)) :
    MonoidalClosed.uncurry g p =
      ihomEquiv Y T (g (tensorEquiv Y Z p).2) (tensorEquiv Y Z p).1 := by
  rw [← MonoidalClosed.homEquiv_symm_apply_eq, homEquiv_def]
  exact tensorHomEquiv_symm_apply g p

/-- Evaluation `Y ⊗ (ihom Y).obj T ⟶ T` in `GeneratedByTopCat X` evaluates the unwrapped
map on the point of `Y`. -/
@[simp]
theorem ihom_ev_app_apply {Y T : GeneratedByTopCat.{v} X}
    (p : ↑(Y ⊗ (ihom Y).obj T)) :
    dsimp% (ihom.ev Y).app T p =
      ihomEquiv Y T (tensorEquiv Y _ p).2 (tensorEquiv Y _ p).1 := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_apply]
  rfl

/-- Coevaluation `Z ⟶ (ihom Y).obj (Y ⊗ Z)` in `GeneratedByTopCat X` sends `z` to
`y ↦ (y, z)`. -/
@[simp]
theorem ihom_coev_app_apply {Y Z : GeneratedByTopCat.{v} X} (z : Z) (y : Y) :
    dsimp% ihomEquiv Y (Y ⊗ Z) ((ihom.coev Y).app Z z) y = (tensorEquiv Y Z).symm (y, z) := by
  rw [ihom.coev, ← Adjunction.homEquiv_id, homEquiv_def]
  exact tensorHomEquiv_apply_apply (𝟙 _) z y

/-- For every `Y, T : GeneratedByTopCat X`, `(ihom Y).obj T` is canonically isomorphic to the
`X`-generated refinement of the ordinary compact-open mapping space `C(Y, T)`. -/
def ihomIsoCompactOpen (Y T : GeneratedByTopCat.{v} X) :
    (ihom Y).obj T ≅ of (X := X) (WithGeneratedByTopology X C(Y, T)) :=
  (fullyFaithfulToTopCat X).preimageIso
    (TopCat.isoOfHomeo ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap)

@[simp]
theorem ihomIsoCompactOpen_hom_apply (Y T : GeneratedByTopCat.{v} X)
    (g : ↑((ihom Y).obj T)) (y : Y) :
    WithGeneratedByTopology.equiv (X := X) (Y := C(Y, T))
        ((ihomIsoCompactOpen Y T).hom g) y =
      ihomEquiv Y T g y :=
  congr($(ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap_apply (X := X) g) y).trans
    (ContinuousMapGeneratedBy.toContinuousMap_apply _ y)

@[simp]
theorem ihomIsoCompactOpen_inv_apply (Y T : GeneratedByTopCat.{v} X)
    (f : WithGeneratedByTopology X C(Y, T)) (y : Y) :
    ihomEquiv Y T ((ihomIsoCompactOpen Y T).inv f) y =
      WithGeneratedByTopology.equiv (X := X) (Y := C(Y, T)) f y :=
  congr($(ContinuousMapGeneratedBy.generatedByHomeomorphContinuousMap_symm_apply
      (X := X) f) y).trans
    (ContinuousMap.toContinuousMapGeneratedBy_apply _ y)

end Closed

end GeneratedByTopCat

end
