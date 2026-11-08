/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Maps and homotopies out of pushouts in `TopCat`

Let `P = Z ∪_a Y` be a pushout square in `TopCat`, with maps `i : B → Y`, `a : B → Z`,
`j : Y → P` and `k : Z → P`. Continuous maps out of `P` are determined by their restrictions to
`Y` and to `Z`. Since the unit interval `I` is locally compact, the cylinder `I × P` is again a
pushout: a map out of `I × P` is glued from maps out of `I × Y` and `I × Z` which agree along `a`,
as the uncurried form of the map `P → C(I, W)` glued from the curried ones. In particular,
homotopies between maps out of `P` are glued from homotopies on `Y` and on `Z`.

## Main declarations

* `CategoryTheory.IsPushout.continuousMap_ext`: continuous maps out of a pushout agree when they
  agree on both legs.
* `CategoryTheory.IsPushout.cylinderDesc`: the map out of the cylinder `I × P` glued from
  compatible maps out of `I × Y` and `I × Z`.
* `CategoryTheory.IsPushout.homotopyDesc`: the homotopy between maps out of `P` glued from
  compatible homotopies of their restrictions to `Y` and to `Z`.
-/

public section

noncomputable section

open unitInterval ContinuousMap

namespace CategoryTheory.IsPushout

universe u

variable {B Y Z P : TopCat.{u}} {i : B ⟶ Y} {a : B ⟶ Z} {j : Y ⟶ P} {k : Z ⟶ P}
  {W : Type u} [TopologicalSpace W]

/-- The pointwise form of the commutativity of a pushout square in `TopCat`. -/
theorem w_apply (h : IsPushout i a j k) (b : B) : j (i b) = k (a b) := by
  simpa using ConcreteCategory.congr_hom h.w b

/-- Two continuous maps out of a pushout in `TopCat` agree as soon as they agree on both legs. -/
theorem continuousMap_ext (h : IsPushout i a j k) {f g : C(P, W)}
    (hj : ∀ y, f (j y) = g (j y)) (hk : ∀ z, f (k z) = g (k z)) : f = g := by
  have : TopCat.ofHom (X := P) (Y := TopCat.of W) f = TopCat.ofHom g :=
    h.hom_ext (by ext y; exact hj y) (by ext z; exact hk z)
  exact congrArg TopCat.Hom.hom this

/-- The map `P → C(I, W)` glued from the curried maps `F` and `G`. -/
private def cylinderCurry (h : IsPushout i a j k) (F : C(I × Y, W)) (G : C(I × Z, W))
    (hFG : ∀ t b, F (t, i b) = G (t, a b)) : P ⟶ TopCat.of C(I, W) :=
  h.desc (TopCat.ofHom (F.comp ContinuousMap.prodSwap).curry)
    (TopCat.ofHom (G.comp ContinuousMap.prodSwap).curry) (by ext b t; exact hFG t b)

/-- The map out of the cylinder `I × P` on a pushout `P = Z ∪_a Y` glued from maps
`F : I × Y → W` and `G : I × Z → W` which agree along the attaching map. Since `I` is locally
compact, it is the uncurried map out of `P` glued from the curried maps into `C(I, W)`; this is the
form in which homotopies are glued on `P`. -/
def cylinderDesc (h : IsPushout i a j k) (F : C(I × Y, W)) (G : C(I × Z, W))
    (hFG : ∀ t b, F (t, i b) = G (t, a b)) : C(I × P, W) :=
  (h.cylinderCurry F G hFG).hom.uncurry.comp ContinuousMap.prodSwap

variable (h : IsPushout i a j k) (F : C(I × Y, W)) (G : C(I × Z, W))
  (hFG : ∀ t b, F (t, i b) = G (t, a b))

/-- On the cylinder over `Y`, the glued map `CategoryTheory.IsPushout.cylinderDesc` is `F`. -/
@[simp]
theorem cylinderDesc_inl (t : I) (y : Y) : h.cylinderDesc F G hFG (t, j y) = F (t, y) := by
  have hy : h.cylinderCurry F G hFG (j y) = (F.comp ContinuousMap.prodSwap).curry y :=
    ConcreteCategory.congr_hom (h.inl_desc _ _ _) y
  exact congrArg (fun g : C(I, W) ↦ g t) hy

/-- On the cylinder over `Z`, the glued map `CategoryTheory.IsPushout.cylinderDesc` is `G`. -/
@[simp]
theorem cylinderDesc_inr (t : I) (z : Z) : h.cylinderDesc F G hFG (t, k z) = G (t, z) := by
  have hz : h.cylinderCurry F G hFG (k z) = (G.comp ContinuousMap.prodSwap).curry z :=
    ConcreteCategory.congr_hom (h.inr_desc _ _ _) z
  exact congrArg (fun g : C(I, W) ↦ g t) hz

/-- A slice of the glued map `CategoryTheory.IsPushout.cylinderDesc` is the map out of `P` which
agrees with the corresponding slices of `F` and `G` on both legs. -/
theorem cylinderDesc_apply_eq (t : I) {w : C(P, W)} (hY : ∀ y, F (t, y) = w (j y))
    (hZ : ∀ z, G (t, z) = w (k z)) (p : P) : h.cylinderDesc F G hFG (t, p) = w p :=
  congrArg (fun g : C(P, W) ↦ g p)
    (h.continuousMap_ext (f := ⟨fun p ↦ h.cylinderDesc F G hFG (t, p), by fun_prop⟩)
      (fun y ↦ by simpa using hY y) (fun z ↦ by simpa using hZ z))

omit hFG in
/-- The homotopy between two maps out of a pushout `P = Z ∪_a Y` glued from homotopies of their
restrictions to `Y` and to `Z` which agree along the attaching map. -/
def homotopyDesc {f g : C(P, W)} (HY : (f.comp j.hom).Homotopy (g.comp j.hom))
    (HZ : (f.comp k.hom).Homotopy (g.comp k.hom)) (hYZ : ∀ t b, HY (t, i b) = HZ (t, a b)) :
    f.Homotopy g where
  toContinuousMap := h.cylinderDesc HY.toContinuousMap HZ.toContinuousMap hYZ
  map_zero_left := h.cylinderDesc_apply_eq _ _ hYZ 0 (by simp) (by simp)
  map_one_left := h.cylinderDesc_apply_eq _ _ hYZ 1 (by simp) (by simp)

omit hFG in
/-- On `Y`, the glued homotopy `CategoryTheory.IsPushout.homotopyDesc` is `HY`. -/
@[simp]
theorem homotopyDesc_apply_inl {f g : C(P, W)} (HY : (f.comp j.hom).Homotopy (g.comp j.hom))
    (HZ : (f.comp k.hom).Homotopy (g.comp k.hom)) (hYZ : ∀ t b, HY (t, i b) = HZ (t, a b))
    (t : I) (y : Y) : h.homotopyDesc HY HZ hYZ (t, j y) = HY (t, y) :=
  h.cylinderDesc_inl _ _ hYZ t y

omit hFG in
/-- On `Z`, the glued homotopy `CategoryTheory.IsPushout.homotopyDesc` is `HZ`. -/
@[simp]
theorem homotopyDesc_apply_inr {f g : C(P, W)} (HY : (f.comp j.hom).Homotopy (g.comp j.hom))
    (HZ : (f.comp k.hom).Homotopy (g.comp k.hom)) (hYZ : ∀ t b, HY (t, i b) = HZ (t, a b))
    (t : I) (z : Z) : h.homotopyDesc HY HZ hYZ (t, k z) = HZ (t, z) :=
  h.cylinderDesc_inr _ _ hYZ t z

end CategoryTheory.IsPushout
