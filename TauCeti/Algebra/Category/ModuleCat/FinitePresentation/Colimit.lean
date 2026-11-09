/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
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

private theorem exists_stage_finite_relation_matrix
    {ι : Type u} [Category.{u} ι] [IsFiltered ι]
    (D : ι ⥤ CommRingCat.{u}) (n m : ℕ)
    (r : (Fin m → (colimit D : CommRingCat.{u})) →ₗ[(colimit D : CommRingCat.{u})]
      (Fin n → (colimit D : CommRingCat.{u}))) :
    ∃ (j : ι) (rᵢ : (Fin m → D.obj j) →ₗ[D.obj j] (Fin n → D.obj j)),
      ∀ (row : Fin n) (col : Fin m),
        (colimit.ι D j).hom (rᵢ (Pi.single col 1) row) = r (Pi.single col 1) row := by
  classical
  have reps (a : Fin n × Fin m) :=
    Concrete.colimit_exists_rep D (r (Pi.single a.2 1) a.1)
  choose j x ha using reps
  obtain ⟨row, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (a : Fin n × Fin m) : j a ⟶ row :=
    (hj (Finset.mem_image_of_mem j (Finset.mem_univ a))).some
  let entry (a : Fin n × Fin m) : D.obj row := D.map (f a) (x a)
  have hb (a : Fin n × Fin m) :
      (colimit.ι D row).hom (entry a) = r (Pi.single a.2 1) a.1 := by
    exact (ConcreteCategory.congr_hom (colimit.w D (f a)) (x a)).trans (ha a)
  refine ⟨row, Matrix.toLin' (Matrix.of
    (fun rowIndex columnIndex ↦ entry (rowIndex, columnIndex))), ?_⟩
  intro rowIndex columnIndex
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact hb (rowIndex, columnIndex)

private theorem finite_relation_quotient_comparison
    {ι : Type u} [Category.{u} ι]
    (D : ι ⥤ CommRingCat.{u}) (n m : ℕ)
    (r : (Fin m → (colimit D : CommRingCat.{u})) →ₗ[(colimit D : CommRingCat.{u})]
      (Fin n → (colimit D : CommRingCat.{u})))
    (i₀ : ι) (rᵢ : (Fin m → D.obj i₀) →ₗ[D.obj i₀] (Fin n → D.obj i₀))
    (hcoeff : ∀ (row : Fin n) (col : Fin m),
      (colimit.ι D i₀).hom (rᵢ (Pi.single col 1) row) = r (Pi.single col 1) row) :
    Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι D i₀))).obj
        (ModuleCat.of (D.obj i₀) (ULift.{v} ((Fin n → D.obj i₀) ⧸ LinearMap.range rᵢ))) ≅
        ModuleCat.of (colimit D : CommRingCat.{u})
          (ULift.{v} ((Fin n → (colimit D : CommRingCat.{u})) ⧸ LinearMap.range r))) := by
  classical
  let R := D.obj i₀
  let S := (colimit D : CommRingCat.{u})
  let φ : R →+* S := (colimit.ι D i₀).hom
  let := φ.toAlgebra
  let eₙ := TensorProduct.piScalarRight R S S (Fin n)
  let eₘ := TensorProduct.piScalarRight R S S (Fin m)
  have hcoord (x : Fin m → R) (row : Fin n) :
      φ (rᵢ x row) = r (fun col ↦ φ (x col)) row := by
    have hx : x = ∑ col : Fin m, x col • Pi.single col (1 : R) := by
      ext col
      simp [Pi.single_apply]
    have hy : (fun col ↦ φ (x col)) = ∑ col : Fin m, φ (x col) • Pi.single col (1 : S) := by
      ext col
      simp [Pi.single_apply]
    have hqi : rᵢ x = ∑ col : Fin m, x col • rᵢ (Pi.single col 1) := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul]
    rw [hqi, hy]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      LinearMap.map_smul]
    apply Finset.sum_congr rfl
    intro col _
    rw [show φ (rᵢ (Pi.single col 1) row) = r (Pi.single col 1) row from hcoeff row col]
  have hmatrix : eₙ.toLinearMap ∘ₗ rᵢ.baseChange S = r ∘ₗ eₘ.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro scalar x
    ext row
    change eₙ (scalar ⊗ₜ[R] rᵢ x) row = r (eₘ (scalar ⊗ₜ[R] x)) row
    simp only [eₙ, eₘ, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    change φ (rᵢ x row) * scalar = r (fun col ↦ φ (x col) * scalar) row
    have hy : (fun col ↦ φ (x col) * scalar) = scalar • (fun col ↦ φ (x col)) := by
      ext col
      simp [mul_comm]
    rw [hy, map_smul, Pi.smul_apply, smul_eq_mul, hcoord]
    exact mul_comm _ _
  have hrange : LinearMap.range (rᵢ.baseChange S) =
      LinearMap.range ((LinearMap.range rᵢ).subtype.baseChange S) := by
    have hf : rᵢ = (LinearMap.range rᵢ).subtype ∘ₗ rᵢ.rangeRestrict := rfl
    nth_rewrite 1 [hf]
    rw [LinearMap.baseChange_comp]
    apply LinearMap.range_comp_of_range_eq_top
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.baseChange_surjective S rᵢ.surjective_rangeRestrict
  have hmap : (LinearMap.range ((LinearMap.range rᵢ).subtype.baseChange S)).map
      eₙ.toLinearMap = LinearMap.range r := by
    rw [← hrange, ← LinearMap.range_comp, hmatrix]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr eₘ.surjective)
  let eQ := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := R) S R S
    (LinearMap.range rᵢ)
  let eR := Submodule.Quotient.equiv _ _ eₙ hmap
  let eU := (ULift.moduleEquiv : ULift.{v} ((Fin n → R) ⧸ LinearMap.range rᵢ) ≃ₗ[R]
    ((Fin n → R) ⧸ LinearMap.range rᵢ)).baseChange R S _ _
  let e := eU.trans (eQ.trans (eR.trans ULift.moduleEquiv.symm))
  exact ⟨e.toModuleIso⟩

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
  obtain ⟨i₀, rᵢ, hqi⟩ := exists_stage_finite_relation_matrix D n m r
  exact ⟨i₀, rᵢ, finite_relation_quotient_comparison D n m r i₀ rᵢ hqi⟩

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
