/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.InnerProductSpace.Comass
import Mathlib.Algebra.Module.TransferInstance

/-!
# Covectors with the Gram norm

`TauCeti.Covector V k` wraps continuous alternating real-valued forms. On a finite-dimensional
real inner product space it carries the Hilbert norm transported from the exterior power via
`TauCeti.alternatingFormEquiv`. Its native-form equivalence compares this norm with the operator
norm, while its musical isometry identifies it with the exterior power. This supplies Hilbert
fibres for spaces of square-integrable differential forms.

The wrapper and algebraic transport follow Mathlib's `WithLp` construction.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

namespace TauCeti

section Normed

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ)

/-- Continuous alternating real-valued forms, with a separate carrier for the Gram norm. -/
structure Covector where
  /-- Wrap a continuous alternating form as a covector. -/
  toCovector ::
  /-- The underlying continuous alternating form. -/
  ofCovector : V [⋀^Fin k]→L[ℝ] ℝ

namespace Covector

instance : AddCommGroup (Covector V k) :=
  ({ toFun := ofCovector
     invFun := toCovector
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } : Covector V k ≃ (V [⋀^Fin k]→L[ℝ] ℝ)).addCommGroup

instance : SMul ℝ (Covector V k) where
  smul c α := toCovector (c • α.ofCovector)

instance : Module ℝ (Covector V k) :=
  ({ toFun := ofCovector
     invFun := toCovector
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl
     map_add' := fun _ _ ↦ rfl } :
      Covector V k ≃+ (V [⋀^Fin k]→L[ℝ] ℝ)).module ℝ

variable {V k}

@[simp] theorem ofCovector_toCovector (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    (toCovector α).ofCovector = α := (rfl)

@[simp] theorem toCovector_ofCovector (α : Covector V k) :
    toCovector α.ofCovector = α := (rfl)

@[ext] theorem ext {α β : Covector V k} (h : α.ofCovector = β.ofCovector) : α = β := by
  cases α
  cases β
  cases h
  rfl

@[simp] theorem ofCovector_zero : (0 : Covector V k).ofCovector = 0 := (rfl)

@[simp] theorem ofCovector_add (α β : Covector V k) :
    (α + β).ofCovector = α.ofCovector + β.ofCovector := (rfl)

@[simp] theorem ofCovector_smul (c : ℝ) (α : Covector V k) :
    (c • α).ofCovector = c • α.ofCovector := (rfl)

@[simp] theorem ofCovector_neg (α : Covector V k) :
    (-α).ofCovector = -α.ofCovector := (rfl)

@[simp] theorem ofCovector_sub (α β : Covector V k) :
    (α - β).ofCovector = α.ofCovector - β.ofCovector := (rfl)

@[simp] theorem toCovector_zero : toCovector (0 : V [⋀^Fin k]→L[ℝ] ℝ) = 0 := (rfl)

@[simp] theorem toCovector_add (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    toCovector (α + β) = toCovector α + toCovector β := (rfl)

@[simp] theorem toCovector_smul (c : ℝ) (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    toCovector (c • α) = c • toCovector α := (rfl)

@[simp] theorem toCovector_neg (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    toCovector (-α) = -toCovector α := (rfl)

@[simp] theorem toCovector_sub (α β : V [⋀^Fin k]→L[ℝ] ℝ) :
    toCovector (α - β) = toCovector α - toCovector β := (rfl)

variable (V k)

/-- Forgetting the wrapper is a linear equivalence with the native continuous forms. -/
def ofCovectorₗ : Covector V k ≃ₗ[ℝ] (V [⋀^Fin k]→L[ℝ] ℝ) where
  toFun := ofCovector
  invFun := toCovector
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp] theorem ofCovectorₗ_apply (α : Covector V k) :
    ofCovectorₗ V k α = α.ofCovector := by
  simp [ofCovectorₗ]

@[simp] theorem ofCovectorₗ_symm_apply (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    (ofCovectorₗ V k).symm α = toCovector α := by
  simp [ofCovectorₗ]

end Covector
end Normed

namespace Covector

section Hilbert

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (k : ℕ)

/-- The Gram norm is induced by the musical identification with the exterior power. -/
instance : NormedAddCommGroup (Covector V k) :=
  NormedAddCommGroup.induced _ _
    ((ofCovectorₗ V k).trans (alternatingFormEquiv V k).symm)
    ((ofCovectorₗ V k).trans (alternatingFormEquiv V k).symm).injective

instance : NormedSpace ℝ (Covector V k) := by
  exact NormedSpace.induced ℝ _ _ ((ofCovectorₗ V k).trans (alternatingFormEquiv V k).symm)

/-- The inner product of covectors is the Gram inner product of alternating forms. -/
instance : InnerProductSpace ℝ (Covector V k) := by
  exact InnerProductSpace.induced ((ofCovectorₗ V k).trans (alternatingFormEquiv V k).symm)

instance : FiniteDimensional ℝ (Covector V k) :=
  ((ofCovectorₗ V k).trans (alternatingFormEquiv V k).symm).symm.finiteDimensional

/-- The musical identification of covectors with the exterior power, as a surjective isometry. -/
def toExteriorPower : Covector V k ≃ₗᵢ[ℝ] ⋀[ℝ]^k V where
  __ := (ofCovectorₗ V k).trans (alternatingFormEquiv V k).symm
  norm_map' _ := (rfl)

@[simp] theorem toExteriorPower_apply (α : Covector V k) :
    toExteriorPower V k α = (alternatingFormEquiv V k).symm α.ofCovector := by
  simp [toExteriorPower]

@[simp] theorem toExteriorPower_symm_apply (α : ⋀[ℝ]^k V) :
    (toExteriorPower V k).symm α = toCovector (alternatingFormEquiv V k α) := by
  apply (toExteriorPower V k).injective
  rw [LinearIsometryEquiv.apply_symm_apply, toExteriorPower_apply, ofCovector_toCovector,
    LinearEquiv.symm_apply_apply]

variable {V k}

/-- The Hilbert inner product is the pointwise Gram inner product of the native forms. -/
theorem inner_eq_alternatingFormInner (α β : Covector V k) :
    ⟪α, β⟫ = alternatingFormInner V k α.ofCovector β.ofCovector := by
  rw [← (toExteriorPower V k).inner_map_map, toExteriorPower_apply, toExteriorPower_apply,
    alternatingFormInner_apply]

/-- The Hilbert norm is the square root of the Gram quadratic form. -/
theorem norm_eq_sqrt_alternatingFormInner (α : Covector V k) :
    ‖α‖ = √(alternatingFormInner V k α.ofCovector α.ofCovector) := by
  rw [← (toExteriorPower V k).norm_map, toExteriorPower_apply]
  exact α.ofCovector.sqrt_alternatingFormInner_self.symm

/-- The operator norm of the underlying form is bounded by its Hilbert norm. -/
theorem norm_ofCovector_le (α : Covector V k) : ‖α.ofCovector‖ ≤ ‖α‖ := by
  rw [norm_eq_sqrt_alternatingFormInner]
  exact α.ofCovector.norm_le_sqrt_alternatingFormInner_self

/-- The Hilbert norm is bounded by `√(dim V choose k)` times the operator norm. -/
theorem norm_le_sqrt_choose_mul_norm_ofCovector (α : Covector V k) :
    ‖α‖ ≤ √((finrank ℝ V).choose k) * ‖α.ofCovector‖ := by
  rw [norm_eq_sqrt_alternatingFormInner]
  exact α.ofCovector.sqrt_alternatingFormInner_self_le

variable (V k)

/-- Forgetting the wrapper is a continuous linear equivalence for the Gram and operator norms. -/
def ofCovectorL : Covector V k ≃L[ℝ] (V [⋀^Fin k]→L[ℝ] ℝ) :=
  (ofCovectorₗ V k).toContinuousLinearEquiv

@[simp] theorem ofCovectorL_apply (α : Covector V k) :
    ofCovectorL V k α = α.ofCovector := by
  simp [ofCovectorL]

@[simp] theorem ofCovectorL_symm_apply (α : V [⋀^Fin k]→L[ℝ] ℝ) :
    (ofCovectorL V k).symm α = toCovector α := by
  simp [ofCovectorL]

variable {V k}

/-- In an orthonormal basis the Gram inner product is the sum of products of coefficients. -/
theorem inner_eq_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ V) (α β : Covector V k) :
    ⟪α, β⟫ = ∑ s : powersetCard ι k,
      α.ofCovector (b ∘ powersetCard.ofFinEmbEquiv.symm s) *
        β.ofCovector (b ∘ powersetCard.ofFinEmbEquiv.symm s) := by
  rw [inner_eq_alternatingFormInner]
  exact alternatingFormInner_eq_sum b _ _

end Hilbert

section Pullback

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] (k : ℕ)

/-- Pullback by a linear isometric equivalence acts isometrically on the Gram norm. -/
def pullback (e : V ≃ₗᵢ[ℝ] W) : Covector W k ≃ₗᵢ[ℝ] Covector V k :=
  (toExteriorPower W k).trans
    (((e.symm.toLinearEquiv.exteriorPower k).isometryOfInner
      (fun x y ↦ exteriorPower.inner_map_map e.symm.toLinearIsometry x y)).trans
        (toExteriorPower V k).symm)

/-- Musical identification sends pullback to the exterior power of the inverse isometry. -/
theorem toExteriorPower_pullback (e : V ≃ₗᵢ[ℝ] W) (α : Covector W k) :
    toExteriorPower V k (pullback k e α) =
      exteriorPower.map k e.symm.toLinearMap (toExteriorPower W k α) := by
  simp [pullback, LinearEquiv.exteriorPower]

/-- Pullback of a covector is precomposition of its native form with the isometry. -/
@[simp] theorem ofCovector_pullback (e : V ≃ₗᵢ[ℝ] W) (α : Covector W k) :
    (pullback k e α).ofCovector =
      α.ofCovector.compContinuousLinearMap e.toContinuousLinearMap := by
  have h := e.symm.toLinearIsometry.alternatingFormEquiv_map (toExteriorPower W k α)
  have hα : alternatingFormEquiv W k (toExteriorPower W k α) = α.ofCovector := by
    simp
  have he : e.symm.toLinearIsometry.toLinearMap = e.symm.toLinearMap := by
    ext x
    rfl
  rw [hα, he, ← toExteriorPower_pullback] at h
  simp only [toExteriorPower_apply, LinearEquiv.apply_symm_apply] at h
  ext v
  have hv := DFunLike.congr_fun h (e ∘ v)
  simpa [Function.comp_def] using hv

end Pullback
end Covector
end TauCeti
