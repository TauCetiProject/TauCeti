/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Triangulation

/-!
# Completing morphisms of stable triangles

A commutative square on the first arrow of distinguished stable triangles extends to a
morphism of triangles. This is the morphism axiom for the Happel triangulation, proved without
assuming a pretriangulated structure on the stable category.

Completion holds both for the standard triangles arising from conflations and for all
distinguished stable triangles, giving the morphism-of-triangles axiom (TR3).

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.ExactStructure.IsFrobenius

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)

/-- A square on the first arrow of stable conflation triangles extends to a morphism
of triangles. -/
private theorem complete_stableConflationTriangle_morphism {S T : ShortComplex C}
    (hS : E.Conflation S) (hT : E.Conflation T) :
    letI := hE.stableHasShift
    ∀ (a : (hE.stableConflationTriangle S hS).obj₁ ⟶
        (hE.stableConflationTriangle T hT).obj₁)
      (b : (hE.stableConflationTriangle S hS).obj₂ ⟶
        (hE.stableConflationTriangle T hT).obj₂),
      (hE.stableConflationTriangle S hS).mor₁ ≫ b =
        a ≫ (hE.stableConflationTriangle T hT).mor₁ →
      ∃ c : (hE.stableConflationTriangle S hS).obj₃ ⟶
          (hE.stableConflationTriangle T hT).obj₃,
        (hE.stableConflationTriangle S hS).mor₂ ≫ c =
          b ≫ (hE.stableConflationTriangle T hT).mor₂ ∧
        (hE.stableConflationTriangle S hS).mor₃ ≫ a⟦1⟧' =
          c ≫ (hE.stableConflationTriangle T hT).mor₃ := by
  let := hE.stableHasShift
  rw [hE.stableConflationTriangle_eq_mk S hS, hE.stableConflationTriangle_eq_mk T hT]
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
    Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃]
  intro a b hab
  obtain ⟨c, hc, hδ⟩ := hE.exists_stable_connecting_square hS hT a b hab
  refine ⟨c, hc, ?_⟩
  -- Naturality of the comparison transports the suspension square to the integer shift.
  simp only [Category.assoc]
  rw [← hE.stableShiftFunctorOneIso.inv.naturality a]
  simpa only [Category.assoc] using congrArg
      (fun f => f ≫ hE.stableShiftFunctorOneIso.inv.app
        (E.projectiveStableFunctor.obj T.X₁)) hδ

/-- The morphism axiom for distinguished stable triangles: every commutative square on their
first arrows extends to a morphism of triangles. No triangulated structure is assumed. -/
theorem complete_stable_distinguished_triangle_morphism :
    letI := hE.stableHasShift
    ∀ (T₁ T₂ : Triangle E.ProjectiveStableCategory)
      (_ : T₁ ∈ hE.stableDistinguishedTriangles)
      (_ : T₂ ∈ hE.stableDistinguishedTriangles)
      (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
      T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
      ∃ c : T₁.obj₃ ⟶ T₂.obj₃,
        T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  let := hE.stableHasShift
  intro T₁ T₂ h₁ h₂ a b hab
  obtain ⟨S, hS, ⟨e⟩⟩ := (hE.mem_stableDistinguishedTriangles_iff T₁).1 h₁
  obtain ⟨T, hT, ⟨f⟩⟩ := (hE.mem_stableDistinguishedTriangles_iff T₂).1 h₂
  have hab' : (hE.stableConflationTriangle S hS).mor₁ ≫
      (e.inv.hom₂ ≫ b ≫ f.hom.hom₂) =
      (e.inv.hom₁ ≫ a ≫ f.hom.hom₁) ≫ (hE.stableConflationTriangle T hT).mor₁ := by
    simp only [Category.assoc, e.inv.comm₁_assoc, reassoc_of% hab, f.hom.comm₁]
  obtain ⟨c, hc₂, hc₃⟩ := hE.complete_stableConflationTriangle_morphism hS hT
    (e.inv.hom₁ ≫ a ≫ f.hom.hom₁) (e.inv.hom₂ ≫ b ≫ f.hom.hom₂) hab'
  let φ : T₁ ⟶ T₂ := e.hom ≫ Triangle.homMk _ _ _ _ c hab' hc₂ hc₃ ≫ f.inv
  have hφ₁ : φ.hom₁ = a := by simp [φ, Category.assoc]
  have hφ₂ : φ.hom₂ = b := by simp [φ, Category.assoc]
  exact ⟨φ.hom₃, by simpa only [hφ₂] using φ.comm₂,
    by simpa only [hφ₁] using φ.comm₃⟩

end TauCeti.ExactStructure.IsFrobenius
