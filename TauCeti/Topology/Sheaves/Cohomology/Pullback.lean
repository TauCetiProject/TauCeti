/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import TauCeti.Topology.Sheaves.Functors

/-!
# Inverse image on the cohomology of abelian sheaves

Let `f : X ⟶ Y` be a continuous map and `F` a sheaf of abelian groups on `Y`. The inverse image
functor `f⁻¹` from abelian sheaves on `Y` to abelian sheaves on `X` is exact, and it carries the
constant sheaf `ℤ` on `Y` to the constant sheaf `ℤ` on `X` (`TopCat.Hom.pullbackConstantSheafIso`,
in `TauCeti.Topology.Sheaves.Functors`). Since `Hⁿ(Y, F)` is `Extⁿ(ℤ, F)` (Mathlib's
`CategoryTheory.Sheaf.H`), applying `f⁻¹` to extensions gives the canonical map

`f.cohomologyPullback F n : Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)`.

It is natural in `F`, commutes with the connecting maps of short exact sequences, and in degree
zero it is the map on global sections given by the unit `F ⟶ f_* f⁻¹ F` of the adjunction. These
three properties make it a morphism of cohomological δ-functors. Composed with a comparison map
`f⁻¹ F ⟶ G`, it gives the pullback maps on the cohomology of sheaves of modules on schemes.

## Main declarations

* `TopCat.Hom.cohomologyPullback`: the map `Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)`;
* `TopCat.Hom.cohomologyPullback_map`: its naturality in `F`;
* `TopCat.Hom.cohomologyPullback_δ`: its compatibility with connecting maps;
* `TopCat.Hom.cohomologyPullback_zero`: its description in degree zero.

## References

* R. Hartshorne, *Algebraic Geometry*, Section III.1 (universal δ-functors) and Exercise III.8.1.
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Hom

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The inverse image map `Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)` on sheaf cohomology along a continuous map
`f : X ⟶ Y`: the exact functor `f⁻¹` applied to `Extⁿ(ℤ, F)`, followed by the identification
`f⁻¹ ℤ ≅ ℤ` of `pullbackConstantSheafIso`. -/
def cohomologyPullback (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F n →+
      CategoryTheory.Sheaf.H.{u} (((Opens.map f).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj F) n where
  toFun x := (Ext.mk₀ (f.pullbackConstantSheafIso _).inv).comp
    (x.mapExactFunctor ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _)) (zero_add n)
  map_zero' := by rw [Ext.mapExactFunctor_zero]; exact Ext.comp_zero _ _ _ _ _
  map_add' x y := by rw [Ext.mapExactFunctor_add]; exact Ext.comp_add _ _ _ _

/-- The defining formula of `cohomologyPullback`. -/
lemma cohomologyPullback_apply
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) {n : ℕ}
    (x : CategoryTheory.Sheaf.H.{u} F n) :
    f.cohomologyPullback F n x = (Ext.mk₀ (f.pullbackConstantSheafIso _).inv).comp
      (x.mapExactFunctor ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _)) (zero_add n) :=
  (rfl)

/-- The inverse image map on cohomology is natural in the coefficient sheaf. -/
lemma cohomologyPullback_map
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (α : F ⟶ G) {n : ℕ} (x : CategoryTheory.Sheaf.H.{u} F n) :
    f.cohomologyPullback G n (CategoryTheory.Sheaf.H.map α n x) =
      CategoryTheory.Sheaf.H.map (((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _).map α) n
        (f.cohomologyPullback F n x) := by
  rw [cohomologyPullback_apply, cohomologyPullback_apply, CategoryTheory.Sheaf.H.map_apply,
    CategoryTheory.Sheaf.H.map_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- The inverse image map on cohomology commutes with the connecting maps of a short exact
sequence of sheaves and of its (exact) inverse image. -/
lemma cohomologyPullback_δ
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (x : CategoryTheory.Sheaf.H.{u} S.X₃ n₀) :
    f.cohomologyPullback S.X₁ n₁ (CategoryTheory.Sheaf.H.δ hS n₀ n₁ h x) =
      CategoryTheory.Sheaf.H.δ
        (hS.map_of_exact ((Opens.map f).sheafPullback AddCommGrpCat.{u} _ _)) n₀ n₁ h
        (f.cohomologyPullback S.X₃ n₀ x) := by
  simp only [cohomologyPullback_apply, CategoryTheory.Sheaf.H.δ, AddMonoidHom.flip_apply,
    Ext.bilinearComp_apply_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) h (by omega)).symm

/-- In degree zero, under the identifications of `H⁰` with global sections, the inverse image map
on cohomology is the unit `F ⟶ f_* f⁻¹ F` on global sections. -/
lemma cohomologyPullback_zero
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (x : CategoryTheory.Sheaf.H.{u} F 0) :
    CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop (f.cohomologyPullback F 0 x) =
      (((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app F).hom.app (op ⊤)
        (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop x) := by
  obtain ⟨a, rfl⟩ : ∃ a, Ext.mk₀ a = x := ⟨Ext.addEquiv₀ x, Ext.mk₀_addEquiv₀_apply x⟩
  rw [cohomologyPullback_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  simp only [CategoryTheory.Sheaf.H.equiv₀, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, Adjunction.homAddEquiv_apply,
    constantSheafAdj_homEquiv_pullbackConstantSheafIso_inv]
  -- `uliftZMultiplesAddEquiv` evaluates a map out of `ℤ` at `1`, so on the left it evaluates the
  -- composite `a' ≫ unit` at `1`, which is by definition the unit applied to `a'` evaluated at `1`.
  rfl

end

end TopCat.Hom
