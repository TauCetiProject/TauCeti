/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
import TauCeti.Data.Int.MulPred

/-!
# The indefinite odd unimodular plane and its hyperbolic two-neighbors

`indefiniteUnitPlane` on `ℚ²` has Gram matrix `diag(1, -1)` (`⟨1⟩ ⊕ ⟨-1⟩`), signature `(1, 0, 1)`,
and isotropic characteristic vector `![1, 1]`. Both of its even Kneser two-neighbors are isometric
to `hyperbolicPlane`, and orthogonal sums with an even lattice preserve `evenSublattice` and
Kneser `p`-neighbors.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §2.
-/

public section

open Module

namespace TauCeti.IntegralLattice

private abbrev indefiniteUnitPlaneMatrix : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal ![1, -1]

/-- The indefinite odd unimodular plane on `ℚ²`, with Gram matrix `diag(1, -1)`. -/
noncomputable def indefiniteUnitPlane : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix (Matrix.isSymm_diagonal _)

/-- The standard coordinate integral basis of `indefiniteUnitPlane`. -/
noncomputable def indefiniteUnitPlaneBasis : Basis (Fin 2) ℤ indefiniteUnitPlane :=
  ofGramMatrix.basis (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix (Matrix.isSymm_diagonal _)

/-- Ambient coercion of `indefiniteUnitPlaneBasis`. -/
@[simp] theorem coe_indefiniteUnitPlaneBasis (i : Fin 2) :
    (indefiniteUnitPlaneBasis i : Fin 2 → ℚ) = Pi.single i 1 :=
  (ofGramMatrix.coe_basis (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix
    (Matrix.isSymm_diagonal _) i).trans (Pi.basisFun_apply ℚ (Fin 2) i)

/-- The Gram matrix of `indefiniteUnitPlane` in `indefiniteUnitPlaneBasis` is `diag(1, -1)`. -/
@[simp] theorem gramMatrix_indefiniteUnitPlaneBasis :
    indefiniteUnitPlane.gramMatrix indefiniteUnitPlaneBasis = !![1, 0; 0, -1] := by
  rw [show indefiniteUnitPlane.gramMatrix indefiniteUnitPlaneBasis = indefiniteUnitPlaneMatrix from
    gramMatrix_ofGramMatrix (Pi.basisFun ℚ (Fin 2)) indefiniteUnitPlaneMatrix _]
  ext i j; fin_cases i <;> fin_cases j <;> simp [indefiniteUnitPlaneMatrix]

/-- A vector belongs to `indefiniteUnitPlane` precisely when both coordinates are integers. -/
@[simp] theorem mem_indefiniteUnitPlane_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ indefiniteUnitPlane.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical rw [indefiniteUnitPlane, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

/-- The bilinear form of `indefiniteUnitPlane` is `x₀ y₀ - x₁ y₁`. -/
@[simp] theorem indefiniteUnitPlane_form_apply (x y : Fin 2 → ℚ) :
    indefiniteUnitPlane.form x y = x 0 * y 0 - x 1 * y 1 := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [indefiniteUnitPlane, ofGramMatrix_form, Matrix.toBilin_apply]
  simp [Fin.sum_univ_two, indefiniteUnitPlaneMatrix]; ring

/-- The quadratic norm on `indefiniteUnitPlane` is `x₀² - x₁²`. -/
@[simp] theorem indefiniteUnitPlane_norm_apply (x : Fin 2 → ℚ) :
    indefiniteUnitPlane.norm x = x 0 ^ 2 - x 1 ^ 2 := by
  rw [norm_apply, indefiniteUnitPlane_form_apply]; ring

/-- `indefiniteUnitPlane` has rank two. -/
@[simp] theorem finrank_indefiniteUnitPlane : Module.finrank ℤ indefiniteUnitPlane = 2 := by
  rw [indefiniteUnitPlane.finrank_carrier]; simp

/-- `indefiniteUnitPlane` has signed determinant `-1`. -/
@[simp] theorem indefiniteUnitPlane_determinant : indefiniteUnitPlane.determinant = -1 := by
  rw [indefiniteUnitPlane, determinant_ofGramMatrix]; simp [indefiniteUnitPlaneMatrix]

/-- `indefiniteUnitPlane` has discriminant `1`. -/
@[simp] theorem indefiniteUnitPlane_discriminant : indefiniteUnitPlane.discriminant = 1 := by
  rw [indefiniteUnitPlane, discriminant_ofGramMatrix]; simp [indefiniteUnitPlaneMatrix]

/-- `indefiniteUnitPlane` is nondegenerate. -/
instance instIsNondegenerateIndefiniteUnitPlane : indefiniteUnitPlane.IsNondegenerate :=
  ⟨indefiniteUnitPlane.determinant_ne_zero_iff.mp (by simp)⟩

/-- `indefiniteUnitPlane` is unimodular. -/
theorem isUnimodular_indefiniteUnitPlane : indefiniteUnitPlane.IsUnimodular :=
  indefiniteUnitPlane.isUnimodular_iff_discriminant_eq_one.mpr indefiniteUnitPlane_discriminant

/-- `indefiniteUnitPlane` is an odd integral lattice. -/
theorem not_isEven_indefiniteUnitPlane : ¬ indefiniteUnitPlane.IsEven := by
  rw [indefiniteUnitPlane, isEven_ofGramMatrix_iff]; rintro h; obtain ⟨k, hk⟩ := h 0
  have : (1 : ℤ) = k + k := by simpa [indefiniteUnitPlaneMatrix] using hk
  omega

/-- The canonical isometry `(rankOne 1).orthogonalSum (rankOne (-1)) ≅ indefiniteUnitPlane`. -/
noncomputable def rankOneOrthogonalSumIsometryIndefiniteUnitPlane :
    Isometry ((rankOne 1).orthogonalSum (rankOne (-1))) indefiniteUnitPlane where
  toLinearEquiv := (LinearEquiv.finTwoArrow ℚ ℚ).symm
  map_app' p q := by
    change indefiniteUnitPlane.form ![p.1, p.2] ![q.1, q.2] = _
    simp [indefiniteUnitPlane_form_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply]; ring
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, orthogonalSum_carrier, Submodule.mem_prod,
      mem_rankOne_carrier_iff, mem_rankOne_carrier_iff, mem_indefiniteUnitPlane_carrier_iff,
      Fin.forall_fin_two]; rfl

/-- `rankOneOrthogonalSumIsometryIndefiniteUnitPlane` sends `(a, b)` to `![a, b]`. -/
@[simp] theorem rankOneOrthogonalSumIsometryIndefiniteUnitPlane_apply (p : ℚ × ℚ) :
    rankOneOrthogonalSumIsometryIndefiniteUnitPlane p = ![p.1, p.2] := (rfl)

/-- `indefiniteUnitPlane` has signature `(1, 0, 1)`. -/
@[simp] theorem indefiniteUnitPlane_signature : indefiniteUnitPlane.signature = (1, 0, 1) := by
  have hp := rankOne_signature_of_pos (a := 1) zero_lt_one
  have hn := rankOne_signature_of_neg (a := -1) (by decide)
  rw [← rankOneOrthogonalSumIsometryIndefiniteUnitPlane.signature_eq, signature_orthogonalSum]
  simp only [signature, Prod.mk.injEq] at hp hn ⊢; omega

/-- The isotropic characteristic vector `![1, 1]` of `indefiniteUnitPlane`. -/
def indefiniteUnitPlaneCharacteristicVector : indefiniteUnitPlane :=
  ⟨![1, 1], (mem_indefiniteUnitPlane_carrier_iff _).mpr fun i ↦ by fin_cases i <;> exact ⟨1, rfl⟩⟩

/-- Ambient coercion of `indefiniteUnitPlaneCharacteristicVector`. -/
@[simp] theorem coe_indefiniteUnitPlaneCharacteristicVector :
    (indefiniteUnitPlaneCharacteristicVector : Fin 2 → ℚ) = ![1, 1] := (rfl)

/-- `![1, 1]` is a characteristic vector of `indefiniteUnitPlane`. -/
theorem isCharacteristicVector_indefiniteUnitPlaneCharacteristicVector :
    indefiniteUnitPlane.IsCharacteristicVector indefiniteUnitPlaneCharacteristicVector := by
  rw [indefiniteUnitPlane.isCharacteristicVector_iff]; intro y
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ :=
    Fin.forall_fin_two.mp ((mem_indefiniteUnitPlane_carrier_iff y).mp y.2)
  have hsub : indefiniteUnitPlane.integralNorm y -
      indefiniteUnitPlane.integralForm indefiniteUnitPlaneCharacteristicVector y =
      (z₀ ^ 2 - z₀) - (z₁ ^ 2 - z₁) := Int.cast_injective (α := ℚ) (by
    simp [integralNorm_cast, integralForm_cast, ← hz₀, ← hz₁]; ring)
  exact Int.modEq_iff_dvd.mpr (hsub ▸
    dvd_sub (Int.two_dvd_sq_sub_self z₀) (Int.two_dvd_sq_sub_self z₁))

/-- `indefiniteUnitPlaneCharacteristicVector` has integral norm zero. -/
@[simp] theorem integralNorm_indefiniteUnitPlaneCharacteristicVector :
    indefiniteUnitPlane.integralNorm indefiniteUnitPlaneCharacteristicVector = 0 :=
  Int.cast_injective (α := ℚ) (by simp [integralNorm_cast])

/-- The standard unit-norm vector `![1, 0]` of `indefiniteUnitPlane`. -/
def indefiniteUnitPlaneOddVector : indefiniteUnitPlane :=
  ⟨![1, 0], (mem_indefiniteUnitPlane_carrier_iff _).mpr
    (Fin.forall_fin_two.mpr ⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩)⟩

/-- Ambient coercion of `indefiniteUnitPlaneOddVector`. -/
@[simp] theorem coe_indefiniteUnitPlaneOddVector :
    (indefiniteUnitPlaneOddVector : Fin 2 → ℚ) = ![1, 0] := (rfl)

/-- `indefiniteUnitPlaneOddVector` has integral norm `1`. -/
@[simp] theorem integralNorm_indefiniteUnitPlaneOddVector :
    indefiniteUnitPlane.integralNorm indefiniteUnitPlaneOddVector = 1 :=
  Int.cast_injective (α := ℚ) (by simp [integralNorm_cast])

/-- `indefiniteUnitPlaneOddVector` has odd integral norm. -/
theorem odd_integralNorm_indefiniteUnitPlaneOddVector :
    Odd (indefiniteUnitPlane.integralNorm indefiniteUnitPlaneOddVector) :=
  integralNorm_indefiniteUnitPlaneOddVector ▸ odd_one

private theorem mem_evenSublattice_carrier_iff_norm {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : IntegralLattice V) (x : V) :
    x ∈ L.evenSublattice.carrier ↔ x ∈ L.carrier ∧ ∃ k : ℤ, L.norm x = 2 * k :=
  ⟨fun h ↦ ⟨L.evenSublattice_carrier_le h,
    (L.even_integralNorm_iff ⟨x, L.evenSublattice_carrier_le h⟩).mp
      ((L.mem_evenSublattice_carrier_iff ⟨x, L.evenSublattice_carrier_le h⟩).mp h)⟩,
   fun ⟨hx, hk⟩ ↦ (L.mem_evenSublattice_carrier_iff ⟨x, hx⟩).mpr
    ((L.even_integralNorm_iff ⟨x, hx⟩).mpr hk)⟩

/-- Membership in `indefiniteUnitPlane.evenSublattice` means integral coordinates with even sum. -/
theorem mem_evenSublattice_indefiniteUnitPlane_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ indefiniteUnitPlane.evenSublattice.carrier ↔
      (∀ i, ∃ z : ℤ, (z : ℚ) = x i) ∧ ∃ k : ℤ, x 0 + x 1 = 2 * k := by
  have hev (a : ℤ) : (∃ k : ℤ, (a : ℚ) = 2 * k) ↔ Even a :=
    ⟨fun ⟨k, hk⟩ ↦ ⟨k, Int.cast_injective (α := ℚ) (by push_cast; linarith)⟩,
      fun ⟨k, hk⟩ ↦ ⟨k, by exact_mod_cast (by omega : a = 2 * k)⟩⟩
  rw [mem_evenSublattice_carrier_iff_norm, mem_indefiniteUnitPlane_carrier_iff]
  refine and_congr_right fun hxZ ↦ ?_
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ := Fin.forall_fin_two.mp hxZ
  rw [indefiniteUnitPlane_norm_apply, ← hz₀, ← hz₁, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_sub,
    ← Int.cast_add, hev, hev]
  simp [Int.even_sub, Int.even_add, Int.even_pow]

/-- The first even unimodular Kneser two-neighbor of `indefiniteUnitPlane`. -/
noncomputable def indefiniteUnitPlaneFirstNeighbor : IntegralLattice (Fin 2 → ℚ) :=
  indefiniteUnitPlane.halfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    isCharacteristicVector_indefiniteUnitPlaneCharacteristicVector (by simp)

/-- The second even unimodular Kneser two-neighbor of `indefiniteUnitPlane`. -/
noncomputable def indefiniteUnitPlaneSecondNeighbor : IntegralLattice (Fin 2 → ℚ) :=
  indefiniteUnitPlane.shiftedHalfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    isCharacteristicVector_indefiniteUnitPlaneCharacteristicVector (by simp)
    indefiniteUnitPlaneOddVector

/-- `indefiniteUnitPlaneFirstNeighbor` is even. -/
theorem isEven_indefiniteUnitPlaneFirstNeighbor : indefiniteUnitPlaneFirstNeighbor.IsEven :=
  indefiniteUnitPlane.isEven_halfCharacteristicOverlattice _ _ _

/-- `indefiniteUnitPlaneFirstNeighbor` is unimodular. -/
theorem isUnimodular_indefiniteUnitPlaneFirstNeighbor :
    indefiniteUnitPlaneFirstNeighbor.IsUnimodular :=
  indefiniteUnitPlane.isUnimodular_halfCharacteristicOverlattice _ _ _

/-- `indefiniteUnitPlaneFirstNeighbor` is a Kneser two-neighbor of `indefiniteUnitPlane`. -/
theorem isNeighbor_indefiniteUnitPlaneFirstNeighbor :
    indefiniteUnitPlane.IsNeighbor indefiniteUnitPlaneFirstNeighbor 2 :=
  indefiniteUnitPlane.isNeighbor_halfCharacteristicOverlattice isUnimodular_indefiniteUnitPlane
    not_isEven_indefiniteUnitPlane _ _

/-- `indefiniteUnitPlaneSecondNeighbor` is even. -/
theorem isEven_indefiniteUnitPlaneSecondNeighbor : indefiniteUnitPlaneSecondNeighbor.IsEven :=
  indefiniteUnitPlane.isEven_shiftedHalfCharacteristicOverlattice _ _ _ _

/-- `indefiniteUnitPlaneSecondNeighbor` is unimodular. -/
theorem isUnimodular_indefiniteUnitPlaneSecondNeighbor :
    indefiniteUnitPlaneSecondNeighbor.IsUnimodular :=
  indefiniteUnitPlane.isUnimodular_shiftedHalfCharacteristicOverlattice _ _ _ _

/-- `indefiniteUnitPlaneSecondNeighbor` is a Kneser two-neighbor of `indefiniteUnitPlane`. -/
theorem isNeighbor_indefiniteUnitPlaneSecondNeighbor :
    indefiniteUnitPlane.IsNeighbor indefiniteUnitPlaneSecondNeighbor 2 :=
  indefiniteUnitPlane.isNeighbor_shiftedHalfCharacteristicOverlattice
    isUnimodular_indefiniteUnitPlane not_isEven_indefiniteUnitPlane _ _ _

/-- Explicit isometry `hyperbolicPlane ≅ indefiniteUnitPlaneFirstNeighbor`. -/
noncomputable def hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor :
    Isometry hyperbolicPlane indefiniteUnitPlaneFirstNeighbor where
  toLinearEquiv :=
    { toFun := fun u ↦ ![u 0 / 2 + u 1, u 0 / 2 - u 1]
      invFun := fun x ↦ ![x 0 + x 1, (x 0 - x 1) / 2]
      map_add' := fun _ _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩)
      map_smul' := fun _ _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩)
      left_inv := fun _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)
      right_inv := fun _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩) }
  map_app' u v := by
    rw [isNeighbor_indefiniteUnitPlaneFirstNeighbor.form_eq.symm, indefiniteUnitPlane_form_apply,
      hyperbolicPlane_form_apply]; simp; ring
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, indefiniteUnitPlaneFirstNeighbor,
      indefiniteUnitPlane.mem_halfCharacteristicOverlattice_carrier_iff,
      mem_evenSublattice_indefiniteUnitPlane_carrier_iff,
      mem_evenSublattice_indefiniteUnitPlane_carrier_iff, mem_hyperbolicPlane_carrier_iff]
    simp only [Fin.forall_fin_two, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.coe_symm_mk,
      coe_indefiniteUnitPlaneCharacteristicVector, Pi.sub_apply, Pi.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    refine ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ?_, ?_⟩
    · rcases Int.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> [left; right] <;>
        exact ⟨⟨⟨m + b, by push_cast at ha ⊢; linarith⟩,
          ⟨m - b, by push_cast at ha ⊢; linarith⟩⟩, m, by push_cast at ha ⊢; linarith⟩
    · rintro (⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩ | ⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩)
      · exact ⟨⟨z₀ + z₁, by push_cast; linarith⟩, ⟨z₀ - k, by push_cast; linarith⟩⟩
      · exact ⟨⟨z₀ + z₁ + 1, by push_cast; linarith⟩, ⟨z₀ - k, by push_cast; linarith⟩⟩

/-- `hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor` sends `u` to
`![u 0 / 2 + u 1, u 0 / 2 - u 1]`. -/
@[simp] theorem hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor_apply (u : Fin 2 → ℚ) :
    hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor u =
      ![u 0 / 2 + u 1, u 0 / 2 - u 1] := (rfl)

/-- Explicit isometry `hyperbolicPlane ≅ indefiniteUnitPlaneSecondNeighbor`. -/
noncomputable def hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor :
    Isometry hyperbolicPlane indefiniteUnitPlaneSecondNeighbor where
  toLinearEquiv :=
    { toFun := fun u ↦ ![u 0 / 2 + u 1, -u 0 / 2 + u 1]
      invFun := fun x ↦ ![x 0 - x 1, (x 0 + x 1) / 2]
      map_add' := fun _ _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩)
      map_smul' := fun _ _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩)
      left_inv := fun _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩)
      right_inv := fun _ ↦ funext (Fin.forall_fin_two.mpr ⟨by simp; ring, by simp; ring⟩) }
  map_app' u v := by
    rw [isNeighbor_indefiniteUnitPlaneSecondNeighbor.form_eq.symm, indefiniteUnitPlane_form_apply,
      hyperbolicPlane_form_apply]; simp; ring
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, indefiniteUnitPlaneSecondNeighbor,
      indefiniteUnitPlane.mem_shiftedHalfCharacteristicOverlattice_carrier_iff,
      mem_evenSublattice_indefiniteUnitPlane_carrier_iff,
      mem_evenSublattice_indefiniteUnitPlane_carrier_iff, mem_hyperbolicPlane_carrier_iff]
    simp only [Fin.forall_fin_two, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.coe_symm_mk,
      coe_indefiniteUnitPlaneOddVector, coe_indefiniteUnitPlaneCharacteristicVector, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    refine ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ?_, ?_⟩
    · rcases Int.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left; exact ⟨⟨⟨m + b, by push_cast at ha ⊢; linarith⟩,
          ⟨-m + b, by push_cast at ha ⊢; linarith⟩⟩, b, by linarith⟩
      · right; exact ⟨⟨⟨m + b - 1, by push_cast at ha ⊢; linarith⟩,
          ⟨-m + b - 1, by push_cast at ha ⊢; linarith⟩⟩, b - 1, by push_cast; linarith⟩
    · rintro (⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩ | ⟨⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩, k, hk⟩)
      · exact ⟨⟨z₀ - z₁, by push_cast; linarith⟩, ⟨k, by linarith⟩⟩
      · exact ⟨⟨z₀ - z₁ + 1, by push_cast; linarith⟩, ⟨k + 1, by push_cast; linarith⟩⟩

/-- `hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor` sends `u` to
`![u 0 / 2 + u 1, -u 0 / 2 + u 1]`. -/
@[simp] theorem hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor_apply (u : Fin 2 → ℚ) :
    hyperbolicPlaneIsometryIndefiniteUnitPlaneSecondNeighbor u =
      ![u 0 / 2 + u 1, -u 0 / 2 + u 1] := (rfl)

universe u v
variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

private theorem orthogonalSum_transport_prodComm (A : IntegralLattice V) (B : IntegralLattice W) :
    (B.orthogonalSum A).transport (LinearEquiv.prodComm ℚ W V) = A.orthogonalSum B :=
  IntegralLattice.ext (Submodule.ext fun x ↦ by
    rw [transport_carrier, Submodule.mem_map_equiv]
    simp [orthogonalSum_carrier, Submodule.mem_prod, and_comm])
    (LinearMap.BilinForm.ext fun x y ↦ by
      simp [transport_form, orthogonalSum_form, LinearMap.BilinForm.prod_apply, add_comm])

/-- `evenSublattice` commutes with transporting an integral lattice along a linear equivalence. -/
@[simp] theorem evenSublattice_transport (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) :
    (L.transport e).evenSublattice = L.evenSublattice.transport e :=
  IntegralLattice.ext (Submodule.ext fun y ↦ by
    rw [mem_evenSublattice_carrier_iff_norm, transport_carrier, Submodule.mem_map_equiv,
      transport_carrier, Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply,
      mem_evenSublattice_carrier_iff_norm]
    simp [norm_apply, transport_form]) (by simp)

/-- **Orthogonal sum with an even lattice commutes with `evenSublattice`.** -/
theorem evenSublattice_orthogonalSum_of_isEven_left {Y : IntegralLattice V} (hY : Y.IsEven)
    (M : IntegralLattice W) :
    (Y.orthogonalSum M).evenSublattice = Y.orthogonalSum M.evenSublattice := by
  refine IntegralLattice.ext (Submodule.ext fun p ↦ ?_) (by simp)
  rw [mem_evenSublattice_carrier_iff_norm, orthogonalSum_carrier, Submodule.mem_prod,
    orthogonalSum_carrier, Submodule.mem_prod, mem_evenSublattice_carrier_iff_norm,
    norm_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply, ← Y.norm_apply, ← M.norm_apply]
  refine ⟨fun ⟨⟨hp1, hp2⟩, k, hk⟩ ↦ ?_, fun ⟨hp1, hp2, k, hk⟩ ↦ ?_⟩ <;>
    obtain ⟨m, hm⟩ := Y.isEven_iff_forall_norm.mp hY ⟨p.1, hp1⟩
  · exact ⟨hp1, hp2, k - m, by push_cast; linarith⟩
  · exact ⟨⟨hp1, hp2⟩, m + k, by push_cast; linarith⟩

/-- Right-hand companion to `evenSublattice_orthogonalSum_of_isEven_left`. -/
theorem evenSublattice_orthogonalSum_of_isEven_right (M : IntegralLattice V)
    {Y : IntegralLattice W} (hY : Y.IsEven) :
    (M.orthogonalSum Y).evenSublattice = M.evenSublattice.orthogonalSum Y := by
  rw [← orthogonalSum_transport_prodComm M Y, evenSublattice_transport,
    evenSublattice_orthogonalSum_of_isEven_left hY M, orthogonalSum_transport_prodComm]

/-- **Kneser `p`-neighbors are preserved by left orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_left (Y : IntegralLattice V) {M N : IntegralLattice W} {p : ℕ}
    (h : M.IsNeighbor N p) : (Y.orthogonalSum M).IsNeighbor (Y.orthogonalSum N) p := by
  have hrel (B : Submodule ℤ W) : (Y.carrier.prod (M.carrier ⊓ N.carrier)).toAddSubgroup.relIndex
      (Y.carrier.prod B).toAddSubgroup =
      (M.carrier ⊓ N.carrier).toAddSubgroup.relIndex B.toAddSubgroup := by
    let proj : (Y.carrier.prod B).toAddSubgroup →+ B.toAddSubgroup :=
      ⟨⟨fun q ↦ ⟨q.1.2, q.2.2⟩, rfl⟩, fun _ _ ↦ rfl⟩
    have hcomap : ((M.carrier ⊓ N.carrier).toAddSubgroup.addSubgroupOf B.toAddSubgroup).comap proj =
        (Y.carrier.prod (M.carrier ⊓ N.carrier)).toAddSubgroup.addSubgroupOf
          (Y.carrier.prod B).toAddSubgroup :=
      AddSubgroup.ext fun q ↦ ⟨fun hq ↦ ⟨q.2.1, hq⟩, fun hq ↦ hq.2⟩
    rw [AddSubgroup.relIndex, ← hcomap, AddSubgroup.index_comap_of_surjective _
      (fun b ↦ ⟨⟨(0, b.1), ⟨Y.carrier.zero_mem, b.2⟩⟩, rfl⟩), ← AddSubgroup.relIndex]
  have hinf : (Y.orthogonalSum M).carrier ⊓ (Y.orthogonalSum N).carrier =
      Y.carrier.prod (M.carrier ⊓ N.carrier) := Submodule.ext fun x ↦ by
    simp only [Submodule.mem_inf, orthogonalSum_carrier, Submodule.mem_prod]; tauto
  exact ⟨by simp [h.form_eq], by rw [hinf, orthogonalSum_carrier, hrel]; exact h.relIndex_inf_left,
    by rw [hinf, orthogonalSum_carrier, hrel]; exact h.relIndex_inf_right⟩

/-- **Kneser `p`-neighbors are preserved by right orthogonal direct sums.** -/
theorem IsNeighbor.orthogonalSum_right {M N : IntegralLattice V} {p : ℕ}
    (h : M.IsNeighbor N p) (Y : IntegralLattice W) :
    (M.orthogonalSum Y).IsNeighbor (N.orthogonalSum Y) p := by
  have hswap := (h.orthogonalSum_left Y).transport (LinearEquiv.prodComm ℚ W V)
  rwa [orthogonalSum_transport_prodComm, orthogonalSum_transport_prodComm] at hswap

/-- **For any even lattice `Y`, `Y ⊕ hyperbolicPlane` is isometric to an explicit even Kneser
two-neighbor of `Y ⊕ indefiniteUnitPlane`.** -/
theorem exists_isNeighbor_orthogonalSum_indefiniteUnitPlane {Y : IntegralLattice V}
    (hY : Y.IsEven) :
    ∃ K : IntegralLattice (V × (Fin 2 → ℚ)),
      (Y.orthogonalSum indefiniteUnitPlane).IsNeighbor K 2 ∧
        K.IsEven ∧ Nonempty (Isometry (Y.orthogonalSum hyperbolicPlane) K) :=
  ⟨Y.orthogonalSum indefiniteUnitPlaneFirstNeighbor,
    isNeighbor_indefiniteUnitPlaneFirstNeighbor.orthogonalSum_left Y,
    (isEven_orthogonalSum_iff _ _).mpr ⟨hY, isEven_indefiniteUnitPlaneFirstNeighbor⟩,
    ⟨(Isometry.refl Y).orthogonalSum hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor⟩⟩

end TauCeti.IntegralLattice
