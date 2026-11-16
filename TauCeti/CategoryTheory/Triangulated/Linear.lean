/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Linear Hom modules in triangulated categories

This file collects two general facts about Hom modules in an `R`-linear pretriangulated category
`C`:

* **Finiteness across distinguished triangles**: if `T` is a distinguished triangle in `C` and `Z`
  is an object such that `Z ⟶ T.obj₁` is a finite `R`-module and `Z ⟶ T.obj₃` is a Noetherian
  `R`-module, then `Z ⟶ T.obj₂` is a finite `R`-module
  (`CategoryTheory.Pretriangulated.moduleFinite_hom_of_distTriang_right`), and dually in the
  contravariant variable (`CategoryTheory.Pretriangulated.moduleFinite_hom_of_distTriang_left`).
* **Truncation equivalences for t-structures**: for a t-structure `t` on `C`, precomposition with
  `(t.truncGEπ n).app X` identifies `(t.truncGE n).obj X ⟶ Y` with `X ⟶ Y` linearly whenever
  `t.IsGE Y n` (`CategoryTheory.Triangulated.TStructure.homTruncGELinearEquiv`), and dually
  postcomposition with `(t.truncLEι n).app Y` identifies `X ⟶ (t.truncLE n).obj Y` with `X ⟶ Y`
  whenever `t.IsLE X n` (`CategoryTheory.Triangulated.TStructure.homTruncLELinearEquiv`).
-/

public section

open CategoryTheory Limits

universe t' v u

namespace CategoryTheory.Pretriangulated

variable {R : Type t'} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear R C]

private theorem moduleFinite_of_exact {M N P : Type*} [AddCommMonoid M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) [Module.Finite R M] (hg : (LinearMap.range g).FG) :
    Module.Finite R N := by
  classical
  obtain ⟨sM, hsM⟩ := Module.Finite.fg_top (R := R) (M := M)
  obtain ⟨sP, hsP⟩ := hg
  have hmem : ∀ p : sP, ∃ n : N, g n = p.1 := fun p ↦ by
    have : p.1 ∈ LinearMap.range g := hsP ▸ Submodule.subset_span (Finset.mem_coe.mpr p.2)
    exact this
  choose lift hlift using hmem
  let T : Finset N := sM.image f ∪ sP.attach.image lift
  refine ⟨⟨T, eq_top_iff.mpr fun x _ ↦ ?_⟩⟩
  have hgx : g x ∈ Submodule.span R (sP : Set P) := hsP.symm ▸ LinearMap.mem_range_self g x
  obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp hgx
  let y : N := ∑ p ∈ sP.attach, c p.1 • lift p
  have hy_span : y ∈ Submodule.span R (T : Set N) :=
    Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ <|
      Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ p))))
  have hgy : g y = g x := by
    rw [← hc]
    simpa [y, map_sum, map_smul, hlift] using
      (Finset.sum_attach sP (fun p ↦ c p • p))
  have hsub : g (x - y) = 0 := by rw [map_sub, hgy, sub_self]
  obtain ⟨m, hm⟩ := (hfg (x - y)).mp hsub
  have hm_span : m ∈ Submodule.span R (sM : Set M) := by rw [hsM]; trivial
  have hfm_span : f m ∈ Submodule.span R (T : Set N) := by
    have h1 : f m ∈ (Submodule.span R (sM : Set M)).map f := Submodule.mem_map_of_mem hm_span
    rw [Submodule.map_span, ← Finset.coe_image] at h1
    exact Submodule.span_mono (Finset.coe_subset.mpr Finset.subset_union_left) h1
  have hx : x = f m + y := by rw [hm, sub_add_cancel]
  rw [hx]
  exact Submodule.add_mem _ hfm_span hy_span

/-- If `T` is a distinguished triangle in an `R`-linear pretriangulated category, `Z ⟶ T.obj₁` is
a finite `R`-module and `Z ⟶ T.obj₃` is a Noetherian `R`-module, then `Z ⟶ T.obj₂` is a finite
`R`-module. -/
theorem moduleFinite_hom_of_distTriang_right {T : Triangle C} (hT : T ∈ distTriang C) (Z : C)
    [Module.Finite R (Z ⟶ T.obj₁)] [IsNoetherian R (Z ⟶ T.obj₃)] :
    Module.Finite R (Z ⟶ T.obj₂) := by
  let f : (Z ⟶ T.obj₁) →ₗ[R] (Z ⟶ T.obj₂) := Linear.rightComp R Z T.mor₁
  let g : (Z ⟶ T.obj₂) →ₗ[R] (Z ⟶ T.obj₃) := Linear.rightComp R Z T.mor₂
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, f, g, Linear.rightComp_apply]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
    · obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ T hT x hx
      exact ⟨y, hy.symm⟩
    · rw [← hy, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  exact moduleFinite_of_exact hfg (IsNoetherian.noetherian _)

/-- If `T` is a distinguished triangle in an `R`-linear pretriangulated category, `T.obj₃ ⟶ Z` is
a finite `R`-module and `T.obj₁ ⟶ Z` is a Noetherian `R`-module, then `T.obj₂ ⟶ Z` is a finite
`R`-module. -/
theorem moduleFinite_hom_of_distTriang_left {T : Triangle C} (hT : T ∈ distTriang C) (Z : C)
    [Module.Finite R (T.obj₃ ⟶ Z)] [IsNoetherian R (T.obj₁ ⟶ Z)] :
    Module.Finite R (T.obj₂ ⟶ Z) := by
  let f : (T.obj₃ ⟶ Z) →ₗ[R] (T.obj₂ ⟶ Z) := Linear.leftComp R Z T.mor₂
  let g : (T.obj₂ ⟶ Z) →ₗ[R] (T.obj₁ ⟶ Z) := Linear.leftComp R Z T.mor₁
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, f, g, Linear.leftComp_apply]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
    · obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT x hx
      exact ⟨y, hy.symm⟩
    · rw [← hy, ← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  exact moduleFinite_of_exact hfg (IsNoetherian.noetherian _)

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated.TStructure

open Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)
  (R : Type t') [Semiring R] [Linear R C]

/-- Precomposition with `(t.truncGEπ n).app X` gives an `R`-linear equivalence
`((t.truncGE n).obj X ⟶ Y) ≃ₗ[R] (X ⟶ Y)` whenever `t.IsGE Y n`. -/
noncomputable def homTruncGELinearEquiv (X Y : C) (n : ℤ) [t.IsGE Y n] :
    ((t.truncGE n).obj X ⟶ Y) ≃ₗ[R] (X ⟶ Y) where
  toFun f := (t.truncGEπ n).app X ≫ f
  invFun g := t.descTruncGE g n
  left_inv f := t.from_truncGE_obj_ext (by simp)
  right_inv g := t.π_descTruncGE g n
  map_add' f₁ f₂ := Preadditive.comp_add _ _ _ _ _ _
  map_smul' r f := by simp

/-- Applying `homTruncGELinearEquiv` precomposes with `(t.truncGEπ n).app X`. -/
@[simp]
theorem homTruncGELinearEquiv_apply (X Y : C) (n : ℤ) [t.IsGE Y n]
    (f : (t.truncGE n).obj X ⟶ Y) :
    t.homTruncGELinearEquiv R X Y n f = (t.truncGEπ n).app X ≫ f :=
  (rfl)

/-- The inverse of `homTruncGELinearEquiv` is `TStructure.descTruncGE`. -/
@[simp]
theorem homTruncGELinearEquiv_symm_apply (X Y : C) (n : ℤ) [t.IsGE Y n] (g : X ⟶ Y) :
    (t.homTruncGELinearEquiv R X Y n).symm g = t.descTruncGE g n :=
  (rfl)

/-- Postcomposition with `(t.truncLEι n).app Y` gives an `R`-linear equivalence
`(X ⟶ (t.truncLE n).obj Y) ≃ₗ[R] (X ⟶ Y)` whenever `t.IsLE X n`. -/
noncomputable def homTruncLELinearEquiv (X Y : C) (n : ℤ) [t.IsLE X n] :
    (X ⟶ (t.truncLE n).obj Y) ≃ₗ[R] (X ⟶ Y) where
  toFun f := f ≫ (t.truncLEι n).app Y
  invFun g := t.liftTruncLE g n
  left_inv f := t.to_truncLE_obj_ext (by simp)
  right_inv g := t.liftTruncLE_ι g n
  map_add' f₁ f₂ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' r f := by simp

/-- Applying `homTruncLELinearEquiv` postcomposes with `(t.truncLEι n).app Y`. -/
@[simp]
theorem homTruncLELinearEquiv_apply (X Y : C) (n : ℤ) [t.IsLE X n]
    (f : X ⟶ (t.truncLE n).obj Y) :
    t.homTruncLELinearEquiv R X Y n f = f ≫ (t.truncLEι n).app Y :=
  (rfl)

/-- The inverse of `homTruncLELinearEquiv` is `TStructure.liftTruncLE`. -/
@[simp]
theorem homTruncLELinearEquiv_symm_apply (X Y : C) (n : ℤ) [t.IsLE X n] (g : X ⟶ Y) :
    (t.homTruncLELinearEquiv R X Y n).symm g = t.liftTruncLE g n :=
  (rfl)

end CategoryTheory.Triangulated.TStructure
