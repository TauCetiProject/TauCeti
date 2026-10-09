/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy

import TauCeti.Data.Fin.Basic

/-!
# Homotopies between maps of Čech nerves

Let `F G : f ⟶ g` be two morphisms of arrows with the same component `F.right = G.right` on the
targets. The induced maps of Čech nerves `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` are
simplicially homotopic. In degree `n` the `i`-th component of the homotopy
`f.cechNerve _⦋n⦌ ⟶ g.cechNerve _⦋n + 1⦌` repeats the `i`-th factor of the wide pullback and
applies `F.left` to the factors in positions `≤ i` and `G.left` to the others.

Applied to the Čech nerve of a family of objects over a terminal object, this says that the map
induced on Čech nerves by a refinement of covers does not depend on the chosen refinement map, up
to homotopy. This is the input for `TauCeti.CategoryTheory.cechComplexMapHomotopy`, which shows
that the maps induced on Čech complexes by two refinement maps are homotopic.

## Main definitions

* `CategoryTheory.Arrow.mapCechNerveHomotopy`: the simplicial homotopy between
  `Arrow.mapCechNerve F` and `Arrow.mapCechNerve G` for `F.right = G.right`.

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
