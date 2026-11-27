/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.WeakLimits.WeakCokernels
public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic

import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Flatness and left exactness

An additive functor is flat if it takes weak cokernels to exact pairs, provided
the source has finite biproducts and weak cokernels. In the presence of cokernels,
this is equivalent to preservation of finite limits by the contravariant functor.

The weak cokernel criterion is the equational form of Crawley-Boevey's
*Locally finitely presented additive categories*, §1.2, Lemma 2 and §1.3.
For the finite limit characterization, see Oberst and Röhrl,
*Flat and coherent functors*, Corollary 3.4.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C] {F : ModCat.{w} C}

/-- A flat module takes a weak cokernel pair to an exact sequence of abelian groups. -/
theorem Flat.exact_of_isWeakCokernel [F.Flat] {X Y Z : C} {f : X ⟶ Y} {q : Y ⟶ Z}
    (hq : IsWeakCokernel f q) :
    Function.Exact (F.obj.map q.op) (F.obj.map f.op) := by
  intro y
  constructor
  · intro hy
    have hr : ∑ _ : Fin 1, F.obj.map f.op y = 0 := by simpa using hy
    obtain ⟨m, W, z, α, hy', hα⟩ :=
      isTrivialRelation_def.mp (Flat.isTrivialRelation (fun _ : Fin 1 ↦ f) (fun _ ↦ y) hr)
    have h (i : Fin m) : f ≫ α i 0 = 0 := by simpa using hα i
    choose l hl using fun i ↦ hq.exists_desc (α i 0) (h i)
    refine ⟨∑ i, F.obj.map (l i).op (z i), ?_⟩
    simpa only [map_sum, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, hl] using (hy' 0).symm
  · rintro ⟨z, rfl⟩
    have h : q.op ≫ f.op = 0 := by simp [← op_comp, hq.comp_eq_zero]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, h, Functor.map_zero,
      AddCommGrpCat.zero_apply]

/-- A module over a category with finite biproducts is flat if every arrow extends to a pair
with zero composite that the module sends to an exact sequence. -/
theorem Flat.of_exists_exact [HasFiniteBiproducts C]
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ∃ (Z : C) (q : Y ⟶ Z), f ≫ q = 0 ∧
      Function.Exact (F.obj.map q.op) (F.obj.map f.op)) : F.Flat where
  isTrivialRelation {X n Y} β y hy := by
    classical
    -- Assemble the row and all its coefficients into a relation at the biproduct.
    let f : X ⟶ ⨁ Y := biproduct.lift β
    let t : F.obj.obj (op (⨁ Y)) := ∑ j, F.obj.map (biproduct.π Y j).op (y j)
    have ht : F.obj.map f.op t = 0 := by
      simpa only [t, map_sum, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, f,
        biproduct.lift_π] using hy
    obtain ⟨Z, q, hq, hq'⟩ := h f
    obtain ⟨z, hz⟩ := (hq' t).mp ht
    refine isTrivialRelation_def.mpr ⟨1, fun _ ↦ Z, fun _ ↦ z,
      fun _ j ↦ biproduct.ι Y j ≫ q, ?_, ?_⟩
    · intro j
      -- Restriction along the jth inclusion recovers the jth coefficient.
      rw [Fin.sum_univ_one, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hz]
      dsimp only [t]
      rw [map_sum, Finset.sum_eq_single j]
      · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          biproduct.ι_π_self, op_id, F.obj.map_id, ConcreteCategory.id_apply]
      · intro k _ hkj
        simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
          biproduct.ι_π_ne Y (Ne.symm hkj), op_zero, Functor.map_zero, AddCommGrpCat.zero_apply]
      · simp
    · intro _
      simpa only [← Category.assoc, ← Preadditive.sum_comp, ← biproduct.lift_eq] using hq

/-- Flatness is equivalent to the existence of a weak cokernel for each arrow whose image under
the module is exact, provided the source has finite biproducts and weak cokernels. -/
theorem flat_iff_exists_isWeakCokernel_exact [HasFiniteBiproducts C] [HasWeakKernels Cᵒᵖ]
    (F : ModCat.{w} C) :
    F.Flat ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ∃ (Z : C) (q : Y ⟶ Z), IsWeakCokernel f q ∧
      Function.Exact (F.obj.map q.op) (F.obj.map f.op) := by
  refine ⟨?_, fun h ↦ Flat.of_exists_exact fun _ _ f ↦ ?_⟩
  · intro hF X Y f
    obtain ⟨Z, q, hq⟩ := exists_isWeakCokernel f
    exact ⟨Z, q, hq, Flat.exact_of_isWeakCokernel hq⟩
  · obtain ⟨Z, q, hq, he⟩ := h f
    exact ⟨Z, q, hq.comp_eq_zero, he⟩

/-- Over an additive category with weak cokernels, a module is flat exactly when it maps
every weak cokernel pair to an exact sequence. -/
theorem flat_iff_exact_of_isWeakCokernel [HasFiniteBiproducts C] [HasWeakKernels Cᵒᵖ]
    (F : ModCat.{w} C) :
    F.Flat ↔ ∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (q : Y ⟶ Z), IsWeakCokernel f q →
      Function.Exact (F.obj.map q.op) (F.obj.map f.op) := by
  refine ⟨fun _ _ _ _ _ _ hq ↦ Flat.exact_of_isWeakCokernel hq, fun h ↦ ?_⟩
  apply (flat_iff_exists_isWeakCokernel_exact F).mpr
  intro X Y f
  obtain ⟨Z, q, hq⟩ := exists_isWeakCokernel f
  exact ⟨Z, q, hq, h f q hq⟩

/-- A flat module preserves monomorphisms in the opposite category. -/
theorem Flat.map_mono [F.Flat] {X Y : Cᵒᵖ} (f : X ⟶ Y) [Mono f] :
    Mono (F.obj.map f) := by
  have hq := IsWeakCokernel.zero_of_epi f.unop
  refine (AddCommGrpCat.mono_iff_injective _).mpr ((injective_iff_map_eq_zero _).mpr ?_)
  intro x hx
  obtain ⟨y, hy⟩ := (Flat.exact_of_isWeakCokernel (F := F) hq x).mp (by simpa using hx)
  simpa only [op_zero, Functor.map_zero, AddCommGrpCat.zero_apply] using hy.symm

/-- A flat module preserves every existing kernel in the opposite category. -/
theorem Flat.preservesLimit_parallelPair_zero [F.Flat] {X Y : Cᵒᵖ} (f : X ⟶ Y) [HasKernel f] :
    PreservesLimit (parallelPair f 0) F.obj := by
  let S := (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).map F.obj
  have hq := IsWeakCokernel.of_isLimit (h := kernel.condition f) (kernelIsKernel f)
  have he : S.Exact := S.ab_exact_iff_function_exact.mpr (Flat.exact_of_isWeakCokernel hq)
  have : Mono S.f := Flat.map_mono (kernel.ι f)
  exact preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    ((isLimitMapConeForkEquiv' F.obj (kernel.condition f)).symm he.fIsKernel)

/-- Over an additive category with cokernels, flatness is equivalent to preservation of finite
limits by the contravariant functor. -/
theorem flat_iff_preservesFiniteLimits [HasFiniteBiproducts C] [HasCokernels C] (F : ModCat.{w} C) :
    F.Flat ↔ PreservesFiniteLimits F.obj := by
  let : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let : HasBinaryBiproducts Cᵒᵖ := .of_hasBinaryProducts
    let {X Y : Cᵒᵖ} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F.obj :=
      Flat.preservesLimit_parallelPair_zero f
    exact F.obj.preservesFiniteLimits_of_preservesKernels
  · apply (flat_iff_exists_isWeakCokernel_exact F).mpr
    intro X Y f
    let S := (ShortComplex.mk (kernel.ι f.op) f.op (kernel.condition f.op)).map F.obj
    have he : S.Exact := S.exact_of_f_is_kernel (isLimitOfHasKernelOfPreservesLimit F.obj f.op)
    exact ⟨_, _, IsWeakCokernel.of_isLimit (h := kernel.condition f.op) (kernelIsKernel f.op),
      S.ab_exact_iff_function_exact.mp he⟩

end TauCeti.ModCat
