/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.Matrix.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Cone operations, compression, and the completely positive order on `A₁ →CP A₂`

Completely positive maps between C⋆-algebras are closed under addition, `ℝ≥0`-scaling, identity,
composition, algebra conjugation `CompletelyPositiveMap.conj` (`a ↦ star b * a * b`), and operator
compression `ContinuousLinearMap.conjAdjoint` (`V.conjAdjoint : T ↦ V† ∘L T ∘L V`). Every positive
linear functional is completely positive (`PositiveLinearMap.toCompletelyPositiveMap`), and so is
`a ↦ ω a • 1` into any unital C⋆-algebra (`PositiveLinearMap.toCompletelyPositiveMapOfId`).
Every completely positive map is a nonnegative multiple of a completely positive contraction
(`CompletelyPositiveMap.exists_norm_apply_le_and_eq_smul`).
Equipping `A₁ →CP A₂` with the *completely positive order* `ψ ≤ φ ↔ ∃ θ : A₁ →CP A₂, φ = ψ + θ`
makes it a partially ordered cancellative `ℝ≥0`-cone with bottom element `0`, used in Arveson's
Radon–Nikodym theorem.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955), Thm. 3.
* W. B. Arveson, *Subalgebras of C⋆-algebras*, Acta Math. 123 (1969), §1.4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3.
-/

public section

open scoped CStarAlgebra NNReal InnerProductSpace ComplexOrder

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
  [CompletelyPositiveMapClass F A₁ A₂]

@[simp] theorem coe_toCompletelyPositiveLinearMap (f : F) :
    ⇑(toCompletelyPositiveLinearMap (A₁ := A₁) (A₂ := A₂) f) = f := (rfl)

end CompletelyPositiveMapClass

namespace CompletelyPositiveMap

section General

variable {A₁ A₂ A₃ : Type*}
  [NonUnitalCStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [NonUnitalCStarAlgebra A₃] [PartialOrder A₃] [StarOrderedRing A₃]

@[ext]
theorem ext {φ ψ : A₁ →CP A₂} (h : ∀ a, φ a = ψ a) : φ = ψ := DFunLike.ext φ ψ h

@[simp] theorem coe_mk (f : A₁ →ₗ[ℂ] A₂) (hf) : ⇑(mk f hf) = f := (rfl)

theorem toLinearMap_injective : Function.Injective (toLinearMap : (A₁ →CP A₂) → A₁ →ₗ[ℂ] A₂) :=
  fun _ _ h => ext fun a => congr($h a)

/-- Reinterpret a completely positive map as a positive linear map. -/
def toPositiveLinearMap (φ : A₁ →CP A₂) : A₁ →ₚ[ℂ] A₂ := .ofClass φ

@[simp] theorem coe_toPositiveLinearMap (φ : A₁ →CP A₂) : ⇑φ.toPositiveLinearMap = φ := (rfl)

/-- A completely positive map preserves adjoints. -/
@[simp] protected theorem map_star (φ : A₁ →CP A₂) (a : A₁) : φ (star a) = star (φ a) := by
  simpa only [coe_toPositiveLinearMap] using map_star φ.toPositiveLinearMap a

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
      smul_nonneg c.property (CStarMatrix.nonneg_iff_forall_sum_nonneg.mp
        (φ.map_cstarMatrix_nonneg M hM) x)⟩

@[simp] theorem toLinearMap_smul (c : ℝ≥0) (φ : A₁ →CP A₂) :
    (c • φ).toLinearMap = c • φ.toLinearMap := (rfl)

instance : IsSMulApply ℝ≥0 (A₁ →CP A₂) where

noncomputable instance instModuleNNReal : Module ℝ≥0 (A₁ →CP A₂) :=
  toLinearMap_injective.module ℝ≥0
    { toFun := toLinearMap, map_zero' := toLinearMap_zero, map_add' := toLinearMap_add }
    toLinearMap_smul

/-- Every completely positive map is a nonnegative multiple `K • ψ'` of a completely positive
contraction `ψ'`, since positive maps between C⋆-algebras are bounded. -/
theorem exists_norm_apply_le_and_eq_smul (ψ : A₁ →CP A₂) :
    ∃ (K : ℝ≥0) (ψ' : A₁ →CP A₂), (∀ a, ‖ψ' a‖ ≤ ‖a‖) ∧ ψ = K • ψ' := by
  obtain ⟨K, hK⟩ := PositiveLinearMap.exists_norm_apply_le (.ofClass ψ)
  have hK₁ : (0 : ℝ) < (K + 1 : ℝ≥0) := by positivity
  refine ⟨K + 1, (K + 1)⁻¹ • ψ, fun a ↦ ?_, ?_⟩
  · rw [smul_apply, NNReal.smul_def, norm_smul_of_nonneg (by positivity), NNReal.coe_inv,
      inv_mul_le_iff₀ hK₁]
    calc ‖ψ a‖ ≤ K * ‖a‖ := hK a
      _ ≤ ((K + 1 : ℝ≥0) : ℝ) * ‖a‖ := by gcongr; simp
  · rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

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

@[simp] theorem comp_id (φ : A₁ →CP A₂) : φ.comp (CompletelyPositiveMap.id A₁) = φ :=
  ext fun _ ↦ rfl

@[simp] theorem id_comp (φ : A₁ →CP A₂) : (CompletelyPositiveMap.id A₂).comp φ = φ :=
  ext fun _ ↦ rfl

/-- The amplification of the identity is the identity. -/
@[simp] theorem mapCStarMatrix_id (n : Type*) [Fintype n] :
    (CompletelyPositiveMap.id A₁).mapCStarMatrix n = CompletelyPositiveMap.id _ := by
  ext x i j
  simp

/-- The amplification of a composite is the composite of the amplifications. -/
@[simp] theorem mapCStarMatrix_comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) (n : Type*) [Fintype n] :
    (ψ.comp φ).mapCStarMatrix n = (ψ.mapCStarMatrix n).comp (φ.mapCStarMatrix n) := by
  ext x i j
  simp

/-- Converting a composite of non-unital star algebra homomorphisms to a completely positive map
composes the converted maps. -/
@[simp] theorem _root_.CompletelyPositiveMapClass.toCompletelyPositiveLinearMap_comp
    (ψ : A₂ →⋆ₙₐ[ℂ] A₃) (φ : A₁ →⋆ₙₐ[ℂ] A₂) :
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (ψ.comp φ) =
      (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ψ).comp
        (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap φ) :=
  ext fun _ ↦ rfl

/-- Composition is compatible with `ℝ≥0`-scaling on the left factor. -/
@[simp] theorem smul_comp (c : ℝ≥0) (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) :
    (c • ψ).comp φ = c • ψ.comp φ :=
  ext fun _ ↦ rfl

/-- Composition is compatible with `ℝ≥0`-scaling on the right factor. -/
@[simp] theorem comp_smul (c : ℝ≥0) (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) :
    ψ.comp (c • φ) = c • ψ.comp φ :=
  ext fun a ↦ LinearMapClass.map_smul_of_tower ψ c (φ a)

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

/-- Conjugation `a ↦ star b * a * b` on a C⋆-algebra as a completely positive map. -/
def conj (b : A₁) : A₁ →CP A₁ where
  toLinearMap := LinearMap.mulLeftRight ℂ (star b, b)
  map_cstarMatrix_nonneg' k M hM := by
    let d := CStarMatrix.diagonalNonUnitalStarAlgHom ℂ (Fin k) A₁
    have hD : M.map (LinearMap.mulLeftRight ℂ (star b, b)) = star (d b) * M * d b := by
      apply CStarMatrix.ofMatrix.symm.injective
      have hd (x : A₁) : CStarMatrix.ofMatrix.symm (d x) = Matrix.diagonal fun _ => x := by
        ext i j
        simp [d, Matrix.diagonal_apply]
      rw [← map_star, CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_mul, hd, hd]
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hD ▸ star_left_conjugate_nonneg hM (d b)

@[simp] theorem conj_apply (b a : A₁) : conj b a = star b * a * b := (rfl)

@[simp] theorem toLinearMap_conj (b : A₁) :
    (conj b).toLinearMap = LinearMap.mulLeftRight ℂ (star b, b) := (rfl)

end General

section UnitalDomain

/-- A completely positive map from a unital C⋆-algebra attains its operator norm at `1`:
`‖φ.toContinuousLinearMap‖ = ‖φ 1‖`. -/
@[simp] theorem norm_toContinuousLinearMap {D A₂ : Type*}
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
    (φ : D →CP A₂) : ‖φ.toContinuousLinearMap‖ = ‖φ 1‖ :=
  (φ.isNPositive 2).opNorm_eq_norm_map_one

end UnitalDomain

end CompletelyPositiveMap

namespace ContinuousLinearMap

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
    V.conjAdjoint T = V.adjoint.comp (T.comp V) := (rfl)

end ContinuousLinearMap

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every positive linear functional `ω : A →ₚ[ℂ] ℂ` is completely positive
(Stinespring 1955, Theorem 3). -/
noncomputable def toCompletelyPositiveMap (ω : A →ₚ[ℂ] ℂ) : A →CP ℂ where
  toLinearMap := ω.toLinearMap
  map_cstarMatrix_nonneg' _ M hM := by
    obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => ?_
    have hsum : (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j) =
        ∑ l, ω (star (∑ i, z i • R l i) * ∑ j, z j • R l j) := by
      have hLHS : (∑ i, ∑ j, star (z i) * (star R * R).map ω.toLinearMap i j * z j) =
          ∑ l, ∑ i, ∑ j, (star (z i) * z j) * ω (star (R l i) * R l j) := by
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
          ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm)
        simp only [CStarMatrix.map_apply, PositiveLinearMap.coe_toLinearMap, CStarMatrix.mul_apply,
          CStarMatrix.star_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hLHS]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [star_smul, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]; ring
    exact hsum ▸ Finset.sum_nonneg fun _ _ => map_nonneg ω (star_mul_self_nonneg _)

@[simp] theorem toCompletelyPositiveMap_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMap a = ω a := (rfl)

variable (B : Type*) [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] in
/-- A positive linear functional `ω : A →ₚ[ℂ] ℂ` viewed as a completely positive map
`a ↦ ω a • 1` into a unital C⋆-algebra `B`, i.e. `ω` followed by `StarAlgHom.ofId ℂ B`. -/
noncomputable def toCompletelyPositiveMapOfId (ω : A →ₚ[ℂ] ℂ) : A →CP B :=
  CompletelyPositiveMap.comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.ofId ℂ B))
    ω.toCompletelyPositiveMap

section OfId

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- `ω.toCompletelyPositiveMapOfId B a` is `ω a` times the identity of `B`. -/
@[simp] theorem toCompletelyPositiveMapOfId_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMapOfId B a = ω a • (1 : B) := by
  rw [toCompletelyPositiveMapOfId, CompletelyPositiveMap.comp_apply,
    CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap, toCompletelyPositiveMap_apply,
    StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one]

/-- The norm of `ω.toCompletelyPositiveMapOfId B a` is `‖ω a‖`. -/
theorem norm_toCompletelyPositiveMapOfId_apply [NormOneClass B] (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ‖ω.toCompletelyPositiveMapOfId B a‖ = ‖ω a‖ := by
  rw [toCompletelyPositiveMapOfId_apply, norm_smul, norm_one, mul_one]

end OfId

end PositiveLinearMap
