/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finitely presented modules over filtered ring colimits

A finitely presented module over a filtered colimit of commutative rings is the scalar
extension of a finitely presented module over one stage. A finite relation matrix descends
to that stage, and right exactness identifies the scalar extension of its cokernel.
This supplies affine models for descent of finitely presented sheaves.
-/

public section

universe u v w w₁

noncomputable section

open CategoryTheory Limits

open scoped ChangeOfRings

namespace ModuleCat

private theorem exists_stage_finite_relation_cokernel
    {ι : Type u} [Category.{u} ι] [IsFiltered ι]
    (D : ι ⥤ CommRingCat.{u}) (n m : ℕ)
    (r : (Fin m → (colimit D : CommRingCat.{u})) →ₗ[(colimit D : CommRingCat.{u})]
      (Fin n → (colimit D : CommRingCat.{u}))) :
    ∃ (i₀ : ι) (rᵢ : (Fin m → D.obj i₀) →ₗ[D.obj i₀] (Fin n → D.obj i₀)),
      Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι D i₀))).obj
        (ModuleCat.of (D.obj i₀) (ULift.{v} ((Fin n → D.obj i₀) ⧸ LinearMap.range rᵢ))) ≅
        ModuleCat.of (colimit D : CommRingCat.{u})
          (ULift.{v} ((Fin n → (colimit D : CommRingCat.{u})) ⧸ LinearMap.range r))) := by
  obtain ⟨i₀, rᵢ, hqi⟩ := TauCeti.CommRingCat.exists_stage_finite_relation_matrix D n m r
  exact ⟨i₀, rᵢ, (colimit.ι D i₀).hom.nonempty_extendScalars_cokernel_pi_iso n m r rᵢ hqi⟩

/-- A finitely presented module over a filtered ring colimit is extended from a stage. -/
theorem exists_finitePresentation_model
    {ι : Type u} [Category.{u} ι] [IsFiltered ι] (D : ι ⥤ CommRingCat.{u})
    (M : ModuleCat.{max u v} (colimit D : CommRingCat.{u}))
    [Module.FinitePresentation (colimit D : CommRingCat.{u}) M] :
    ∃ (i₀ : ι) (Mᵢ : ModuleCat.{max u v} (D.obj i₀)),
      Module.FinitePresentation (D.obj i₀) Mᵢ ∧
      Nonempty ((extendScalars (colimit.ι D i₀).hom).obj Mᵢ ≅ M) := by
  classical
  obtain ⟨n, m, presentationMap, r, hp, hqp⟩ :=
    Module.FinitePresentation.exists_fin' (colimit D : CommRingCat.{u}) M
  obtain ⟨i₀, rᵢ, ⟨e⟩⟩ := exists_stage_finite_relation_cokernel D n m r
  let Q := (Fin n → D.obj i₀) ⧸ LinearMap.range rᵢ
  let Mᵢ := ModuleCat.of (D.obj i₀) (ULift.{v} Q)
  have hQ : Module.FinitePresentation (D.obj i₀) Q :=
    Module.finitePresentation_of_surjective (LinearMap.range rᵢ).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range rᵢ)
  have instQ : Module.FinitePresentation (D.obj i₀) Q := hQ
  have hM : Module.FinitePresentation (D.obj i₀) Mᵢ :=
    Module.FinitePresentation.of_equiv
      (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[D.obj i₀] Q).symm
  let eN : ModuleCat.of (colimit D : CommRingCat.{u})
      (ULift.{v} ((Fin n → (colimit D : CommRingCat.{u})) ⧸ LinearMap.range r)) ≅ M :=
    ((ULift.moduleEquiv :
      ULift.{v} ((Fin n → (colimit D : CommRingCat.{u})) ⧸ LinearMap.range r) ≃ₗ[_]
        ((Fin n → (colimit D : CommRingCat.{u})) ⧸ LinearMap.range r)).trans
      ((Submodule.quotEquivOfEq (LinearMap.range r) (LinearMap.ker presentationMap)
        (LinearMap.exact_iff.mp hqp).symm).trans
        (LinearMap.quotKerEquivOfSurjective presentationMap hp))).toModuleIso
  exact ⟨i₀, Mᵢ, hM, ⟨e.trans eN⟩⟩

end ModuleCat
