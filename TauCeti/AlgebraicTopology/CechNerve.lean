/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

import TauCeti.Data.Fin.Basic

/-!
# Homotopies between maps of Čech nerves, and maps into a Čech nerve

Let `F G : f ⟶ g` be two morphisms of arrows with the same component `F.right = G.right` on the
targets. The induced maps of Čech nerves `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` are
simplicially homotopic. In degree `n` the `i`-th component of the homotopy
`f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌` repeats the `i`-th factor of the wide pullback and
applies `F.left` to the factors in positions `≤ i` and `G.left` to the others.

Applied to the Čech nerve of a family of objects over a terminal object, this says that the map
induced on Čech nerves by a refinement of covers does not depend on the chosen refinement map, up
to homotopy. This is the input for `TauCeti.CategoryTheory.cechComplexMapHomotopy`, which shows
that the maps induced on Čech complexes by two refinement maps are homotopic.

For an object `T`, the morphisms from `T` into the Čech nerve of `f` form an augmented simplicial
set over the morphisms `T ⟶ f.right` which lift along `f.hom`. It has an extra degeneracy, which
inserts a chosen lift of the base as a new first factor; this is Mathlib's extra degeneracy of the
Čech nerve of a split epimorphism, `Arrow.AugmentedCechNerve.extraDegeneracy`, with the section
chosen separately over each morphism. For the map from the disjoint union of a family of open sets
and `T` a topological simplex, it shows that the rows of the Čech--singular double complex resolve
the singular chains subordinate to the family.

## Main definitions

* `CategoryTheory.Arrow.mapCechNerveHomotopy`: the simplicial homotopy between
  `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` for `F.right = G.right`.
* `CategoryTheory.Arrow.augmentedCechNerveMapsFrom`: the morphisms from `T` into the Čech nerve,
  augmented over the morphisms which lift along `f.hom`.
* `CategoryTheory.Arrow.AugmentedCechNerveMapsFrom.extraDegeneracy`: its extra degeneracy.

## References

* R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977,
  Exercise III.4.4, for the independence of the map induced on Čech cohomology by a refinement
  from the refinement map.
-/

public section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] {f g : Arrow C}
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom]
  [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) ↦ g.left) fun _ ↦ g.hom]

/-- The `i`-th component `f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌` of the homotopy between
`mapCechNerve F` and `mapCechNerve G`: its `j`-th factor is the `i.predAbove j`-th factor of the
source followed by `F.left` if `j ≤ i` and by `G.left` otherwise. -/
private noncomputable def mapCechNerveHomotopyApp (F G : f ⟶ g) (h : F.right = G.right) {n : ℕ}
    (i : Fin (n + 1)) : f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌ :=
  WidePullback.lift (WidePullback.base _ ≫ F.right)
    (fun j ↦ WidePullback.π _ (i.predAbove j) ≫ if j ≤ i.castSucc then F.left else G.left)
    (fun j ↦ by split_ifs <;> simp [h])

variable (F G : f ⟶ g) (h : F.right = G.right)

@[reassoc (attr := simp)]
private theorem mapCechNerveHomotopyApp_π {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    mapCechNerveHomotopyApp F G h i ≫ WidePullback.π _ j =
      WidePullback.π _ (i.predAbove j) ≫ if j ≤ i.castSucc then F.left else G.left :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem mapCechNerveHomotopyApp_base {n : ℕ} (i : Fin (n + 1)) :
    mapCechNerveHomotopyApp F G h i ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right :=
  WidePullback.lift_base _ _ _ _

omit [∀ n : ℕ, HasWidePullback g.right (fun _ : Fin (n + 1) ↦ g.left) fun _ ↦ g.hom] in
/-- Two composites `π a ≫ (if p then F.left else G.left)` out of a wide pullback agree when the
factors `a`, `b` and the conditions `p`, `q` do. -/
private theorem π_comp_ite_congr {n : ℕ} {a b : Fin (n + 1)} {p q : Prop} [Decidable p]
    [Decidable q] (hab : a = b) (hpq : p ↔ q) :
    (WidePullback.π (fun _ : Fin (n + 1) ↦ f.hom) a ≫ if p then F.left else G.left) =
      WidePullback.π (fun _ : Fin (n + 1) ↦ f.hom) b ≫ if q then F.left else G.left := by
  subst hab
  simp only [hpq]

/-- Proves an identity between two maps into a Čech nerve built from face maps, degeneracy maps
and `mapCechNerveHomotopyApp`: both sides are compared factor by factor, which reduces the identity
to arithmetic of the indices. -/
local macro "cech_nerve_homotopy_ext" : tactic => `(tactic| (
  apply WidePullback.hom_ext
  · intro k
    simp only [SimplicialObject.δ, SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ,
      SimplexCategory.mkHom, cechNerve_map, Quiver.Hom.unop_op, SimplexCategory.Hom.toOrderHom_mk,
      OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.predAboveOrderHom_coe,
      Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, mapCechNerveHomotopyApp_π]
    refine π_comp_ite_congr _ _ ?_ ?_ <;>
      simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
        Fin.val_castSucc, Fin.val_succ] at * <;>
      split_ifs at * <;> omega
  · simp [SimplicialObject.δ, SimplicialObject.σ]))

/-- **Morphisms of arrows with the same target component induce homotopic maps of Čech
nerves.** If `F.right = G.right`, then `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` are
simplicially homotopic. -/
noncomputable def mapCechNerveHomotopy :
    SimplicialObject.Homotopy (mapCechNerve F) (mapCechNerve G) where
  h i := mapCechNerveHomotopyApp F G h i
  h_zero_comp_δ_zero n := by
    apply WidePullback.hom_ext
    · intro j
      simp [SimplicialObject.δ, SimplexCategory.δ]
    · simp [SimplicialObject.δ, h]
  h_last_comp_δ_last n := by
    apply WidePullback.hom_ext
    · intro j
      simp [SimplicialObject.δ, SimplexCategory.δ, Fin.le_last]
    · simp [SimplicialObject.δ]
  h_succ_comp_δ_castSucc_of_lt i j hij := by cech_nerve_homotopy_ext
  h_succ_comp_δ_castSucc_succ j := by cech_nerve_homotopy_ext
  h_castSucc_comp_δ_succ_of_lt i j hji := by cech_nerve_homotopy_ext
  h_comp_σ_castSucc_of_le i j hij := by cech_nerve_homotopy_ext
  h_comp_σ_succ_of_lt i j hji := by cech_nerve_homotopy_ext

/-- The `j`-th factor of the `i`-th component of `mapCechNerveHomotopy F G h` is the
`i.predAbove j`-th factor of the source followed by `F.left` if `j ≤ i` and by `G.left`
otherwise. -/
@[reassoc (attr := simp)]
theorem mapCechNerveHomotopy_h_π {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (mapCechNerveHomotopy F G h).h i ≫ WidePullback.π _ j =
      WidePullback.π _ (i.predAbove j) ≫ if j ≤ i.castSucc then F.left else G.left :=
  mapCechNerveHomotopyApp_π F G h i j

/-- Every component of `mapCechNerveHomotopy F G h` lies over `F.right = G.right`. -/
@[reassoc (attr := simp)]
theorem mapCechNerveHomotopy_h_base {n : ℕ} (i : Fin (n + 1)) :
    (mapCechNerveHomotopy F G h).h i ≫ WidePullback.base _ = WidePullback.base _ ≫ F.right :=
  mapCechNerveHomotopyApp_base F G h i

end CategoryTheory.Arrow

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom]

/-- The morphisms from `T` into the Čech nerve of `f`, augmented over the morphisms
`T ⟶ f.right` which lift along `f.hom`. The augmentation composes with the projection
`WidePullback.base`. -/
@[expose] noncomputable def augmentedCechNerveMapsFrom (T : C) :
    SimplicialObject.Augmented (Type v) where
  left := f.cechNerve ⋙ coyoneda.obj (op T)
  right := {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}
  hom :=
    { app n := ↾fun σ ↦ ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩
      naturality n m θ := by
        ext σ
        simp }

/-- The simplicial operators act on maps into the Čech nerve by postcomposition. -/
@[simp]
theorem augmentedCechNerveMapsFrom_left_map (T : C) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (σ : T ⟶ f.cechNerve.obj n) :
    (f.augmentedCechNerveMapsFrom T).left.map θ σ = σ ≫ f.cechNerve.map θ :=
  (rfl)

/-- The augmentation sends a map into the Čech nerve to its composite with the base.

The source and target of `ConcreteCategory.hom` are given explicitly, as `left.obj n` and
`right`, so that the left-hand side is in simp normal form: elaborated directly they would be
`(𝟭 _).obj left` and `(const.obj right).obj n`, which simp rewrites first. -/
@[simp]
theorem augmentedCechNerveMapsFrom_hom_app_coe (T : C) (n : SimplexCategoryᵒᵖ)
    (σ : T ⟶ f.cechNerve.obj n) :
    Subtype.val (ConcreteCategory.hom (X := (f.augmentedCechNerveMapsFrom T).left.obj n)
      (Y := (f.augmentedCechNerveMapsFrom T).right) ((f.augmentedCechNerveMapsFrom T).hom.app n)
      σ) = σ ≫ WidePullback.base _ :=
  (rfl)

namespace AugmentedCechNerveMapsFrom

variable {f} {T : C}

omit [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom] in
/-- A chosen lift along `f.hom` of a morphism which admits one. -/
private noncomputable def lift (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    T ⟶ f.left :=
  g.2.choose

omit [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) ↦ f.left) fun _ ↦ f.hom] in
@[reassoc (attr := simp)]
private theorem lift_comp (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    lift g ≫ f.hom = g.1 :=
  g.2.choose_spec

/-- The section of the augmentation in degree `0`: a liftable morphism goes to its chosen lift. -/
private noncomputable def sectionFun (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    T ⟶ f.cechNerve _⦋0⦌ :=
  WidePullback.lift g.1 (fun _ ↦ lift g) (by simp)

/-- The extra degeneracy on maps into the Čech nerve: it inserts the chosen lift of the base
as the new `0`-th factor. -/
private noncomputable def sFun {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) : T ⟶ f.cechNerve _⦋n + 1⦌ :=
  WidePullback.lift (σ ≫ WidePullback.base _)
    (Fin.cases (lift ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩)
      fun i ↦ σ ≫ WidePullback.π _ i)
    fun i ↦ by cases i using Fin.cases <;> simp

@[reassoc (attr := simp)]
private theorem sectionFun_π (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g})
    (i : Fin 1) :
    sectionFun g ≫ WidePullback.π _ i = lift g :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem sectionFun_base (g : {g : T ⟶ f.right // ∃ l : T ⟶ f.left, l ≫ f.hom = g}) :
    sectionFun g ≫ WidePullback.base _ = g.1 :=
  WidePullback.lift_base _ _ _ _

@[reassoc (attr := simp)]
private theorem sFun_π_zero {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ WidePullback.π _ 0 =
      lift ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩ :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem sFun_π_succ {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) (i : Fin (n + 1)) :
    sFun σ ≫ WidePullback.π _ i.succ = σ ≫ WidePullback.π _ i :=
  WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
private theorem sFun_base {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ WidePullback.base _ = σ ≫ WidePullback.base _ :=
  WidePullback.lift_base _ _ _ _

private theorem sFun_zero_comp_δ_one (σ : T ⟶ f.cechNerve _⦋0⦌) :
    sFun σ ≫ f.cechNerve.δ 1 =
      sectionFun ⟨σ ≫ WidePullback.base _, σ ≫ WidePullback.π _ 0, by simp⟩ := by
  apply WidePullback.hom_ext
  · intro j
    fin_cases j
    simp [SimplicialObject.δ, SimplexCategory.δ]
  · simp [SimplicialObject.δ]

private theorem sFun_comp_δ_zero {n : ℕ} (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ f.cechNerve.δ 0 = σ := by
  apply WidePullback.hom_ext
  · intro j
    simp [SimplicialObject.δ, SimplexCategory.δ]
  · simp [SimplicialObject.δ]

private theorem sFun_comp_δ_succ {n : ℕ} (i : Fin (n + 2)) (σ : T ⟶ f.cechNerve _⦋n + 1⦌) :
    sFun σ ≫ f.cechNerve.δ i.succ = sFun (σ ≫ f.cechNerve.δ i) := by
  apply WidePullback.hom_ext
  · intro j
    induction j using Fin.cases <;> simp [SimplicialObject.δ, SimplexCategory.δ]
  · simp [SimplicialObject.δ]

private theorem sFun_comp_σ_succ {n : ℕ} (i : Fin (n + 1)) (σ : T ⟶ f.cechNerve _⦋n⦌) :
    sFun σ ≫ f.cechNerve.σ i.succ = sFun (σ ≫ f.cechNerve.σ i) := by
  apply WidePullback.hom_ext
  · intro j
    induction j using Fin.cases <;> simp [SimplicialObject.σ, SimplexCategory.σ]
  · simp [SimplicialObject.σ]

end AugmentedCechNerveMapsFrom

open AugmentedCechNerveMapsFrom in
/-- **Maps into a Čech nerve over liftable maps have an extra degeneracy.** -/
noncomputable def AugmentedCechNerveMapsFrom.extraDegeneracy (T : C) :
    SimplicialObject.Augmented.ExtraDegeneracy (f.augmentedCechNerveMapsFrom T) where
  s' := ↾sectionFun
  s _ := ↾sFun
  -- The simplices of `f.augmentedCechNerveMapsFrom T` are morphisms into the Čech nerve and its
  -- simplicial operators act by postcomposition, so each identity is the corresponding identity
  -- for morphisms into the Čech nerve.
  s'_comp_ε := by
    ext g
    exact Subtype.ext (sectionFun_base g)
  s₀_comp_δ₁ := by
    ext σ
    exact sFun_zero_comp_δ_one σ
  s_comp_δ₀ n := by
    ext σ
    exact sFun_comp_δ_zero σ
  s_comp_δ n i := by
    ext σ
    exact sFun_comp_δ_succ i σ
  s_comp_σ n i := by
    ext σ
    exact sFun_comp_σ_succ i σ

end CategoryTheory.Arrow
