/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.MatrixOrder
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite Kraus families

Rectangular complex matrices `V k : Matrix n m ℂ` define the completely positive map
`a ↦ ∑ k, (V k)ᴴ * a * V k`. Its value at one is the Kraus normalization sum.
The trace dual is `ρ ↦ ∑ k, V k * ρ * (V k)ᴴ`; it preserves trace exactly when
that normalization sum is one. Isometric changes of Kraus family preserve the map.

The normalization criterion connects the Heisenberg and Schrödinger pictures of
a finite-dimensional quantum channel.

The construction uses Mathlib's `CompletelyPositiveMap` and `Matrix.PosSemidef`,
with the spectral order transported by `CStarMatrix.nonneg_iff_posSemidef`.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*,
  Linear Algebra and its Applications 10 (1975), 285–290.
-/

public section

open scoped CStarAlgebra ComplexOrder
open CStarMatrix

namespace Matrix

variable {n m ι κ : Type*} [Fintype n] [Fintype m] [Fintype ι] [Fintype κ]

/-- Conjugation by a rectangular matrix is completely positive. -/
noncomputable def conjugateCP (V : Matrix n m ℂ) :
    CStarMatrix n n ℂ →CP CStarMatrix m m ℂ where
  toFun a := ofMatrix (Vᴴ * ofMatrix.symm a * V)
  map_add' a b := by
    -- Use the linear equivalence to transport addition across the matrix wrapper.
    change ofMatrix (Vᴴ * (ofMatrixₗ (R := ℂ)).symm (a + b) * V) = _
    simp only [map_add, Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' c a := by
    -- Use the linear equivalence to transport scalar multiplication across the wrapper.
    change ofMatrix (Vᴴ * (ofMatrixₗ (R := ℂ)).symm (c • a) * V) = _
    simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    rfl
  map_cstarMatrix_nonneg' k M hM := by
    classical
    let : NonUnitalContinuousFunctionalCalculus ℝ
        (CStarMatrix (Fin k) (Fin k) (CStarMatrix n n ℂ)) IsSelfAdjoint :=
      IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    let : NonnegSpectrumClass ℝ
        (CStarMatrix (Fin k) (Fin k) (CStarMatrix n n ℂ)) :=
      CStarAlgebra.instNonnegSpectrumClass'
    obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    apply nonneg_iff_forall_sum_nonneg.mpr
    intro x
    apply CStarMatrix.nonneg_iff_posSemidef.mpr
    let B (l : Fin k) : Matrix n m ℂ :=
      ∑ i, ofMatrix.symm (R l i) * V * ofMatrix.symm (x i)
    have hB : (∑ l, (B l)ᴴ * B l).PosSemidef :=
      Matrix.posSemidef_sum _ fun l _ => Matrix.posSemidef_conjTranspose_mul_self (B l)
    convert hB using 1
    simp only [B, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.sum_mul, Matrix.mul_sum]
    -- Expand the block product through the canonical matrix wrapper.
    change (∑ i, ∑ j, (ofMatrix.symm (x i))ᴴ *
      (Vᴴ * (∑ l, (ofMatrix.symm (R l i))ᴴ * ofMatrix.symm (R l j)) * V) *
      ofMatrix.symm (x j)) = _
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1
    funext l
    rw [Finset.sum_comm]

/-- The conjugation map evaluates to the usual matrix formula. -/
@[simp] theorem conjugateCP_apply (V : Matrix n m ℂ) (a : CStarMatrix n n ℂ) :
    conjugateCP V a = ofMatrix (Vᴴ * ofMatrix.symm a * V) := (rfl)

/-- The completely positive map associated to a finite Kraus family. -/
noncomputable def krausMap (V : ι → Matrix n m ℂ) :
    CStarMatrix n n ℂ →CP CStarMatrix m m ℂ where
  toLinearMap := ∑ i, (conjugateCP (V i)).toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have h (i : ι) := (conjugateCP (V i)).map_cstarMatrix_nonneg M hM
    convert Finset.sum_nonneg (s := Finset.univ) (fun i _ => h i) using 1
    -- Evaluation at four indices is additive, so it commutes with the finite sum.
    let ev (i j : Fin k) (p q : m) :
        CStarMatrix (Fin k) (Fin k) (CStarMatrix m m ℂ) →+ ℂ :=
      { toFun := fun A => A i j p q
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    ext i j p q
    rw [← show (ev i j p q) (∑ d, M.map (conjugateCP (V d))) =
        (∑ d, M.map (conjugateCP (V d))) i j p q from rfl, map_sum]
    simp only [CStarMatrix.map, LinearMap.sum_apply]
    -- Evaluate the sum of linear maps, then the sum of its matrix entries.
    change (∑ d, (conjugateCP (V d)).toLinearMap (M i j)) p q = _
    let entry : CStarMatrix m m ℂ →+ ℂ :=
      { toFun := fun A => A p q
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact map_sum entry _ _


/-- Evaluation of a Kraus map. -/
@[simp] theorem krausMap_apply (V : ι → Matrix n m ℂ) (a : CStarMatrix n n ℂ) :
    krausMap V a = ofMatrix (∑ i, (V i)ᴴ * ofMatrix.symm a * V i) := by
  -- Evaluation commutes with the sum of linear maps.
  change (∑ i, (conjugateCP (V i)).toLinearMap) a = _
  simp only [LinearMap.sum_apply]
  rfl

/-- A Kraus map is unital precisely when its normalization sum is one. -/
theorem krausMap_unital_iff [DecidableEq n] [DecidableEq m]
    (V : ι → Matrix n m ℂ) :
    krausMap V 1 = 1 ↔ ∑ i, (V i)ᴴ * V i = 1 := by
  rw [krausMap_apply]
  -- The unit is transported by the canonical ring equivalence.
  change ofMatrix (∑ i, (V i)ᴴ * (1 : Matrix n n ℂ) * V i) = ofMatrix 1 ↔ _
  simp only [Matrix.mul_one, ofMatrix.injective.eq_iff]

/-- The trace dual of a finite Kraus family. -/
noncomputable def krausTraceDual (V : ι → Matrix n m ℂ) :
    Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun ρ := ∑ i, V i * ρ * (V i)ᴴ
  map_add' ρ σ := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c ρ := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

omit [Fintype n] in
/-- Evaluation of the trace dual. -/
@[simp] theorem krausTraceDual_apply (V : ι → Matrix n m ℂ) (ρ : Matrix m m ℂ) :
    krausTraceDual V ρ = ∑ i, V i * ρ * (V i)ᴴ := (rfl)

/-- The two Kraus formulas are dual for the bilinear trace pairing. -/
theorem trace_krausTraceDual_mul (V : ι → Matrix n m ℂ)
    (ρ : Matrix m m ℂ) (a : CStarMatrix n n ℂ) :
    trace (krausTraceDual V ρ * ofMatrix.symm a) =
      trace (ρ * ofMatrix.symm (krausMap V a)) := by
  simp only [krausTraceDual_apply, krausMap_apply, Equiv.symm_apply_apply,
    Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- Trace preservation is equivalent to Kraus normalization. -/
theorem krausTraceDual_trace_preserving_iff [DecidableEq m]
    (V : ι → Matrix n m ℂ) :
    (∀ ρ, trace (krausTraceDual V ρ) = trace ρ) ↔ ∑ i, (V i)ᴴ * V i = 1 := by
  have htrace (ρ : Matrix m m ℂ) :
      trace (krausTraceDual V ρ) = trace (ρ * ∑ i, (V i)ᴴ * V i) := by
    simp only [krausTraceDual_apply, trace_sum, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (trace_mul_cycle _ _ _).trans (trace_mul_comm _ _)
  simp_rw [htrace]
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro ρ
    simpa using h ρ
  · intro h ρ
    simp [h]

/-- The trace dual preserves trace exactly when the Kraus map is unital. -/
theorem krausTraceDual_trace_preserving_iff_unital [DecidableEq n] [DecidableEq m]
    (V : ι → Matrix n m ℂ) :
    (∀ ρ, trace (krausTraceDual V ρ) = trace ρ) ↔ krausMap V 1 = 1 := by
  rw [krausTraceDual_trace_preserving_iff, krausMap_unital_iff]

/-- An isometric change of the indexing family preserves its Kraus map. -/
theorem krausMap_isometry [DecidableEq ι] (V : ι → Matrix n m ℂ)
    (u : Matrix κ ι ℂ) (hu : uᴴ * u = 1) (a : CStarMatrix n n ℂ) :
    krausMap (fun j => ∑ i, u j i • V i) a = krausMap V a := by
  have hu' (i l : ι) : ∑ j, star (u j i) * u j l = if i = l then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg (fun M => M i l) hu
  simp only [krausMap_apply]
  congr 1
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [mul_comm (u _ _), ← Finset.sum_smul, hu']
  simp

/-- A unitary change of Kraus family preserves the associated map. -/
theorem krausMap_unitary [DecidableEq ι] (V : ι → Matrix n m ℂ)
    (u : unitary (Matrix ι ι ℂ)) (a : CStarMatrix n n ℂ) :
    krausMap (fun j => ∑ i, (u : Matrix ι ι ℂ) j i • V i) a = krausMap V a :=
  krausMap_isometry V (u : Matrix ι ι ℂ) (Unitary.coe_star_mul_self u) a

end Matrix
