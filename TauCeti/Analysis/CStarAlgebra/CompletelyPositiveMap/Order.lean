/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import TauCeti.Analysis.CStarAlgebra.MatrixOrder
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Cone operations, compression, and the completely positive order on `A₁ →CP A₂`

Completely positive maps between C⋆-algebras are closed under addition, `ℝ≥0`-scaling, identity,
composition, and operator compression `conjAdjoint V : T ↦ V† ∘L T ∘L V`. Equipping `A₁ →CP A₂`
with the *completely positive order* `ψ ≤ φ ↔ ∃ θ : A₁ →CP A₂, φ = ψ + θ` makes it a partially
ordered cancellative `ℝ≥0`-cone with bottom element `0`, used in Arveson's Radon–Nikodym theorem.

## References

* W. B. Arveson, *Subalgebras of C⋆-algebras*, Acta Math. 123 (1969), §1.4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3.
-/

public section

open scoped CStarAlgebra NNReal InnerProductSpace ComplexOrder

namespace CompletelyPositiveMap

section General

variable {A₁ A₂ A₃ : Type*}
  [NonUnitalCStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [NonUnitalCStarAlgebra A₃] [PartialOrder A₃] [StarOrderedRing A₃]

@[ext]
theorem ext {φ ψ : A₁ →CP A₂} (h : ∀ a, φ a = ψ a) : φ = ψ := DFunLike.ext φ ψ h

@[simp] theorem coe_toLinearMap (φ : A₁ →CP A₂) : ⇑φ.toLinearMap = φ := (rfl)

@[simp] theorem coe_mk (f : A₁ →ₗ[ℂ] A₂) (hf) : ⇑(mk f hf) = f := (rfl)

theorem toLinearMap_injective : Function.Injective (toLinearMap : (A₁ →CP A₂) → A₁ →ₗ[ℂ] A₂) :=
  fun _ _ h => ext fun a => congr($h a)

/-- Reinterpret a completely positive map as a positive linear map. -/
def toPositiveLinearMap (φ : A₁ →CP A₂) : A₁ →ₚ[ℂ] A₂ := .ofClass φ

@[simp] theorem coe_toPositiveLinearMap (φ : A₁ →CP A₂) : ⇑φ.toPositiveLinearMap = φ := (rfl)

/-- Reinterpret a completely positive map as a continuous linear map. -/
noncomputable def toContinuousLinearMap (φ : A₁ →CP A₂) : A₁ →L[ℂ] A₂ :=
  ⟨φ.toLinearMap, map_continuous φ⟩

@[simp] theorem coe_toContinuousLinearMap (φ : A₁ →CP A₂) : ⇑φ.toContinuousLinearMap = φ := (rfl)

@[simp] theorem toContinuousLinearMap_apply (φ : A₁ →CP A₂) (a : A₁) :
    φ.toContinuousLinearMap a = φ a := (rfl)

instance instZero : Zero (A₁ →CP A₂) where
  zero := ⟨0, fun _ M _ => by convert le_rfl; ext; simp⟩

@[simp] theorem toLinearMap_zero : (0 : A₁ →CP A₂).toLinearMap = 0 := (rfl)

instance : IsZeroApply (A₁ →CP A₂) where

instance instAdd : Add (A₁ →CP A₂) where
  add φ ψ := ⟨φ.toLinearMap + ψ.toLinearMap, fun _ M hM => by
    convert add_nonneg (φ.map_cstarMatrix_nonneg M hM) (ψ.map_cstarMatrix_nonneg M hM); ext; simp⟩

@[simp] theorem toLinearMap_add (φ ψ : A₁ →CP A₂) :
    (φ + ψ).toLinearMap = φ.toLinearMap + ψ.toLinearMap := (rfl)

instance : IsAddApply (A₁ →CP A₂) where

instance instSMulNat : SMul ℕ (A₁ →CP A₂) where
  smul n φ := ⟨n • φ.toLinearMap, fun _ M hM => by
    convert nsmul_nonneg (φ.map_cstarMatrix_nonneg M hM) n; ext; simp⟩

@[simp] theorem toLinearMap_nsmul (n : ℕ) (φ : A₁ →CP A₂) :
    (n • φ).toLinearMap = n • φ.toLinearMap := (rfl)

instance : IsSMulApply ℕ (A₁ →CP A₂) where

instance instAddCommMonoid : AddCommMonoid (A₁ →CP A₂) :=
  toLinearMap_injective.addCommMonoid toLinearMap toLinearMap_zero toLinearMap_add
    fun φ n => toLinearMap_nsmul n φ

instance : IsLeftCancelAdd (A₁ →CP A₂) where
  add_left_cancel _ _ _ h := toLinearMap_injective <| add_left_cancel <| by
    simpa only [toLinearMap_add] using congrArg toLinearMap h

instance : IsCancelAdd (A₁ →CP A₂) := AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _

noncomputable instance instSMulNNReal : SMul ℝ≥0 (A₁ →CP A₂) where
  smul c φ := ⟨c • φ.toLinearMap, fun _ M hM => by
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun x => ?_
    simpa [NNReal.smul_def, Finset.smul_sum, mul_smul_comm, smul_mul_assoc] using
      smul_nonneg c.2 (CStarMatrix.nonneg_iff_forall_sum_nonneg.mp
        (φ.map_cstarMatrix_nonneg M hM) x)⟩

@[simp] theorem toLinearMap_smul (c : ℝ≥0) (φ : A₁ →CP A₂) :
    (c • φ).toLinearMap = c • φ.toLinearMap := (rfl)

instance : IsSMulApply ℝ≥0 (A₁ →CP A₂) where

noncomputable instance instModuleNNReal : Module ℝ≥0 (A₁ →CP A₂) :=
  toLinearMap_injective.module ℝ≥0
    { toFun := toLinearMap, map_zero' := toLinearMap_zero, map_add' := toLinearMap_add }
    toLinearMap_smul

variable (A₁) in
/-- The identity completely positive map on a C⋆-algebra. -/
protected def id : A₁ →CP A₁ :=
  ⟨LinearMap.id, fun _ M hM => by convert hM; ext; rfl⟩

@[simp] theorem id_apply (a : A₁) : CompletelyPositiveMap.id A₁ a = a := (rfl)

@[simp] theorem toLinearMap_id : (CompletelyPositiveMap.id A₁).toLinearMap = LinearMap.id := (rfl)

/-- Composition of completely positive maps. -/
def comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) : A₁ →CP A₃ :=
  ⟨ψ.toLinearMap.comp φ.toLinearMap, fun _ M hM => by
    convert ψ.map_cstarMatrix_nonneg _ (φ.map_cstarMatrix_nonneg M hM); ext; rfl⟩

@[simp] theorem comp_apply (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) (a : A₁) :
    (ψ.comp φ) a = ψ (φ a) := (rfl)

@[simp] theorem toLinearMap_comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) :
    (ψ.comp φ).toLinearMap = ψ.toLinearMap.comp φ.toLinearMap := (rfl)

/-- The *completely positive order* on `A₁ →CP A₂`: `ψ ≤ φ` means `φ = ψ + θ` for some
`θ : A₁ →CP A₂`. -/
instance instPartialOrder : PartialOrder (A₁ →CP A₂) where
  le ψ φ := ∃ θ : A₁ →CP A₂, φ = ψ + θ
  le_refl φ := ⟨0, (add_zero φ).symm⟩
  le_trans χ _ _ := by rintro ⟨θ₁, rfl⟩ ⟨θ₂, rfl⟩; exact ⟨θ₁ + θ₂, add_assoc χ θ₁ θ₂⟩
  le_antisymm ψ φ := by
    rintro ⟨θ₁, rfl⟩ ⟨θ₂, h₂⟩
    have hsum (a : A₁) : θ₁ a + θ₂ a = 0 :=
      add_left_cancel (a := ψ a) (by simpa [add_assoc] using congrArg (· a) h₂.symm)
    have h0 : ∀ a ∈ {x : A₁ | 0 ≤ x}, θ₁.toLinearMap a = 0 := fun a ha =>
      le_antisymm (by simpa [hsum a] using add_le_add_right (map_nonneg θ₂ ha) (θ₁ a))
        (map_nonneg θ₁ ha)
    have hθ₁ : θ₁ = 0 := toLinearMap_injective <|
      LinearMap.ext_on CStarAlgebra.span_nonneg fun a ha => by simp [h0 a ha]
    rw [hθ₁, add_zero]

theorem le_def {ψ φ : A₁ →CP A₂} : ψ ≤ φ ↔ ∃ θ : A₁ →CP A₂, φ = ψ + θ := Iff.rfl

theorem le_iff_exists_forall_add {ψ φ : A₁ →CP A₂} :
    ψ ≤ φ ↔ ∃ θ : A₁ →CP A₂, ∀ a, φ a = ψ a + θ a := by simp [le_def, CompletelyPositiveMap.ext_iff]

instance instOrderBot : OrderBot (A₁ →CP A₂) where
  bot := 0
  bot_le φ := ⟨φ, (zero_add φ).symm⟩

@[simp] theorem bot_eq_zero : (⊥ : A₁ →CP A₂) = 0 := (rfl)

theorem zero_le (φ : A₁ →CP A₂) : 0 ≤ φ := bot_le

instance : IsOrderedAddMonoid (A₁ →CP A₂) where
  add_le_add_left ψ _ h χ := by obtain ⟨θ, rfl⟩ := h; exact ⟨θ, add_right_comm ψ θ χ⟩

end General

section Hilbert

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Operator compression `T ↦ V† ∘L T ∘L V` as a completely positive map
`(K →L[ℂ] K) →CP (H →L[ℂ] H)`. -/
noncomputable def conjAdjoint (V : H →L[ℂ] K) : (K →L[ℂ] K) →CP (H →L[ℂ] H) where
  toLinearMap :=
    { toFun T := V.adjoint.comp (T.comp V)
      map_add' S T := by ext; simp
      map_smul' c T := by ext; simp }
  map_cstarMatrix_nonneg' _ M hM := by
    refine CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.mpr fun ξ => ?_
    simpa only [CStarMatrix.map_apply, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] using
      (CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.mp hM) fun i => V (ξ i)

@[simp] theorem conjAdjoint_apply (V : H →L[ℂ] K) (T : K →L[ℂ] K) :
    conjAdjoint V T = V.adjoint.comp (T.comp V) := (rfl)

end Hilbert

end CompletelyPositiveMap
