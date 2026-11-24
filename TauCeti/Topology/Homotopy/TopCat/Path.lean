/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.TopCat.Path
public import TauCeti.Topology.Category.TopCat.Interval

/-!
# Paths as morphisms out of `TopCat.I`

Mathlib's `TopCat.pathEquiv` identifies a path `γ` in `X : TopCat` with a morphism
`(TopCat.pathEquiv.symm γ).hom : TopCat.I ⟶ X`, which sends `t` to `γ (TopCat.I.homeomorph t)`
(`TopCat.pathEquiv_symm_hom_apply`). Along the reparametrizations `TopCat.I.firstHalf` and
`TopCat.I.secondHalf` of the two halves of the interval, the morphism of a concatenation `γ.trans δ`
restricts to the morphisms of `γ` and of `δ`, and it sends `TopCat.I.midpoint` to the point at
which they meet.
-/

public section

open CategoryTheory

universe u

namespace TopCat

variable {X : TopCat.{u}} {x₀ x₁ x₂ : X}

/-- The morphism `TopCat.I ⟶ X` of a path `γ` sends `t` to `γ (TopCat.I.homeomorph t)`. -/
@[simp]
lemma pathEquiv_symm_hom_apply (γ : _root_.Path x₀ x₁) (t : I.{u}) :
    (pathEquiv.symm γ).hom t = γ (I.homeomorph t) :=
  (rfl)

/-- The morphism `TopCat.I ⟶ Y` of the image of a path `γ` under `g : X ⟶ Y` is the morphism of `γ`
followed by `g`. -/
@[simp]
lemma pathEquiv_symm_map_hom {Y : TopCat.{u}} (γ : _root_.Path x₀ x₁) (g : X ⟶ Y) :
    (pathEquiv.symm (γ.map g.hom.continuous)).hom = (pathEquiv.symm γ).hom ≫ g := by
  ext t
  rw [ConcreteCategory.comp_apply, pathEquiv_symm_hom_apply, pathEquiv_symm_hom_apply,
    Path.map_coe, Function.comp_apply]

/-- The concatenation of two paths passes through their common end point at the midpoint. -/
lemma pathEquiv_symm_trans_hom_midpoint (γ : _root_.Path x₀ x₁) (δ : _root_.Path x₁ x₂) :
    (pathEquiv.symm (γ.trans δ)).hom I.midpoint = x₁ := by
  rw [pathEquiv_symm_hom_apply, ← Path.extend_extends', I.coe_homeomorph_midpoint,
    Path.extend_trans_of_le_half _ _ le_rfl, mul_one_div_cancel two_ne_zero, Path.extend_one]

/-- On the first half of the interval, the concatenation of two paths is the first path. -/
lemma firstHalf_comp_pathEquiv_symm_trans_hom (γ : _root_.Path x₀ x₁) (δ : _root_.Path x₁ x₂) :
    I.firstHalf ≫ (pathEquiv.symm (γ.trans δ)).hom = (pathEquiv.symm γ).hom := by
  ext t
  rw [ConcreteCategory.comp_apply, pathEquiv_symm_hom_apply, pathEquiv_symm_hom_apply,
    ← Path.extend_extends', ← Path.extend_extends', I.coe_homeomorph_firstHalf_apply,
    Path.extend_trans_of_le_half _ _ (by linarith [(I.homeomorph t).property.2]),
    mul_div_cancel₀ _ two_ne_zero]

/-- On the second half of the interval, the concatenation of two paths is the second path. -/
lemma secondHalf_comp_pathEquiv_symm_trans_hom (γ : _root_.Path x₀ x₁) (δ : _root_.Path x₁ x₂) :
    I.secondHalf ≫ (pathEquiv.symm (γ.trans δ)).hom = (pathEquiv.symm δ).hom := by
  ext t
  rw [ConcreteCategory.comp_apply, pathEquiv_symm_hom_apply, pathEquiv_symm_hom_apply,
    ← Path.extend_extends', ← Path.extend_extends', I.coe_homeomorph_secondHalf_apply,
    Path.extend_trans_of_half_le _ _ (by linarith [(I.homeomorph t).property.1]),
    mul_div_cancel₀ _ two_ne_zero, add_sub_cancel_right]

end TopCat
