/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing sections of sheaves

This file provides general gluing lemmas for sections of sheaves:

1. Two-open gluing along a commutative square of sheaf morphisms valued in a concrete category with
   zero morphisms (`TopCat.Sheaf.app_apply_eq_of_le_sup`): if `π₁ ≫ ζ = φ ≫ π₂`, `W ≤ U ⊔ V`,
   both `φ` and `ζ` vanish on `V`, and a section `g` over `W` lifts `z|_U` along `π₁` after
   restriction to `U`, then `π₂(φ(g)) = ζ(z)` over `W`.
2. Locally finite sums of sections of an abelian sheaf (`TopCat.Sheaf.exists_gluing_finset_sum`):
   given a family of sections `a i` of an abelian sheaf `G` over an open subset `U` such that each
   `a i` vanishes on all opens inside an open `V i`, and an open cover `N k ≤ U` of `U` on each
   member of which only finitely many `i ∈ S k` fail to satisfy `N k ≤ V i`, the finite sums
   `∑ i ∈ S k, a i|_{N k}` are compatible on overlaps and glue to a section of `G` over `U`.

## Main results

* `TopCat.Sheaf.app_apply_eq_of_le_sup`: two-open gluing of an intertwining equality `π₂(φ(g)) =
  ζ(z)` when `φ` and `ζ` vanish on the second open.
* `TopCat.Sheaf.exists_gluing_finset_sum`: gluing of locally finite sums of sections of an abelian
  sheaf over an open subset `U`.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

/-- If `π₁ ≫ ζ = φ ≫ π₂` is a commutative square of sheaf morphisms valued in a concrete category
with zero morphisms, `U` and `V` are open subsets of `W` covering `W` (`W ≤ U ⊔ V`), both `φ` and
`ζ` vanish on `V`, and a section `g` of `G₁` over `W` lifts `z|_U` along `π₁` after restriction to
`U`, then `π₂(φ(g)) = ζ(z)` over `W`. -/
theorem app_apply_eq_of_le_sup {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasZeroMorphisms C] [HasLimitsOfSize.{u, u} C]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
    {X : TopCat.{u}} {G₁ G₂ Z₁ Z₂ : X.Sheaf C}
    (π₁ : G₁ ⟶ Z₁) (π₂ : G₂ ⟶ Z₂) (φ : G₁ ⟶ G₂) (ζ : Z₁ ⟶ Z₂)
    (hcomm : π₁ ≫ ζ = φ ≫ π₂)
    {U V W : Opens X} (hUW : U ≤ W) (hVW : V ≤ W) (hcover : W ≤ U ⊔ V)
    (hφ : φ.hom.app (op V) = 0) (hζ : ζ.hom.app (op V) = 0)
    (g : ToType (G₁.obj.obj (op W))) (z : ToType (Z₁.obj.obj (op W)))
    (hg : π₁.hom.app (op U) (G₁.obj.map (homOfLE hUW).op g) = Z₁.obj.map (homOfLE hUW).op z) :
    π₂.hom.app (op W) (φ.hom.app (op W) g) = ζ.hom.app (op W) z := by
  have hcommU (x : ToType (G₁.obj.obj (op U))) :
      π₂.hom.app (op U) (φ.hom.app (op U) x) = ζ.hom.app (op U) (π₁.hom.app (op U) x) := by
    have hU : φ.hom.app (op U) ≫ π₂.hom.app (op U) = π₁.hom.app (op U) ≫ ζ.hom.app (op U) := by
      rw [← TopCat.Sheaf.comp_app, ← TopCat.Sheaf.comp_app, hcomm]
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hU x
  have hzeroV (x : ToType (G₁.obj.obj (op V))) (y : ToType (Z₁.obj.obj (op V))) :
      π₂.hom.app (op V) (φ.hom.app (op V) x) = ζ.hom.app (op V) y := by
    have : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, u, u} C
    have : PreservesLimitsOfSize.{0, 0} (CategoryTheory.forget C) :=
      preservesSmallestLimits_of_preservesLimits (CategoryTheory.forget C)
    have hL : φ.hom.app (op V) ≫ π₂.hom.app (op V) =
        (0 : G₁.obj.obj (op V) ⟶ ⊤_ C) ≫ (0 : ⊤_ C ⟶ Z₂.obj.obj (op V)) := by
      rw [hφ, zero_comp, zero_comp]
    have hR : ζ.hom.app (op V) =
        (0 : Z₁.obj.obj (op V) ⟶ ⊤_ C) ≫ (0 : ⊤_ C ⟶ Z₂.obj.obj (op V)) := by
      rw [hζ, zero_comp]
    have hLx := ConcreteCategory.congr_hom hL x
    have hRy := ConcreteCategory.congr_hom hR y
    simp only [ConcreteCategory.comp_apply] at hLx hRy
    rw [hLx, hRy]
    exact congrArg _ (Subsingleton.elim _ _)
  refine Z₂.eq_of_locally_eq₂ (homOfLE hUW) (homOfLE hVW) hcover _ _ ?_ ?_
  · simp only [← NatTrans.naturality_apply, hcommU, hg]
  · simp only [← NatTrans.naturality_apply]
    exact hzeroV _ _

/-- Gluing a locally finite sum of sections of an abelian sheaf `G` over `U`: if each `a i`
vanishes on opens inside `V i`, and `N` covers `U` with `N k ≤ V i` for all `i ∉ S k`, then the
finite sums `∑ i ∈ S k, a i|_{N k}` glue to a section `b` over `U`. -/
theorem exists_gluing_finset_sum {X : TopCat.{u}} (G : X.Sheaf AddCommGrpCat.{u}) {U : Opens X}
    {ι κ : Type*} (V : ι → Opens X) (a : ι → G.obj.obj (op U))
    (ha : ∀ i ⦃W : Opens X⦄ (hWU : W ≤ U), W ≤ V i → G.obj.map (homOfLE hWU).op (a i) = 0)
    (N : κ → Opens X) (hNU : ∀ k, N k ≤ U) (hN : U ≤ ⨆ k, N k) (S : κ → Finset ι)
    (hSV : ∀ k i, i ∉ S k → N k ≤ V i) :
    ∃ b : G.obj.obj (op U), ∀ k,
      G.obj.map (homOfLE (hNU k)).op b =
        ∑ i ∈ S k, G.obj.map (homOfLE (hNU k)).op (a i) := by
  classical
  let sf : ∀ k : κ, G.obj.obj (op (N k)) :=
    fun k ↦ ∑ i ∈ S k, G.obj.map (homOfLE (hNU k)).op (a i)
  have hcompat : TopCat.Presheaf.IsCompatible G.obj N sf := by
    intro k₁ k₂
    let W := N k₁ ⊓ N k₂
    have hWU : W ≤ U := inf_le_left.trans (hNU k₁)
    have hrestrict (k : κ) (hWN : W ≤ N k) (hs : S k ⊆ S k₁ ∪ S k₂) :
        G.obj.map (homOfLE hWN).op (sf k) =
          ∑ i ∈ S k₁ ∪ S k₂, G.obj.map (homOfLE hWU).op (a i) := by
      simp only [sf, map_sum]
      have hterm (i : ι) :
          G.obj.map (homOfLE hWN).op (G.obj.map (homOfLE (hNU k)).op (a i)) =
            G.obj.map (homOfLE hWU).op (a i) := by
        rw [← Functor.map_comp_apply]
        exact congrArg (fun f : W ⟶ U ↦ G.obj.map f.op (a i)) (Subsingleton.elim _ _)
      simp_rw [hterm]
      exact Finset.sum_subset hs fun i _ hi ↦ ha i hWU (hWN.trans (hSV k i hi))
    exact (hrestrict k₁ inf_le_left Finset.subset_union_left).trans
      (hrestrict k₂ inf_le_right Finset.subset_union_right).symm
  obtain ⟨b, hb, -⟩ := G.existsUnique_gluing' N U (fun k ↦ homOfLE (hNU k)) hN sf hcompat
  exact ⟨b, hb⟩

end TopCat.Sheaf
