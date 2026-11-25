/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import TauCeti.Analysis.CStarAlgebra.Matrix.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Finite Kraus families

Rectangular complex matrices `V k : Matrix n m ℂ` define the completely positive map
`a ↦ ∑ k, (V k)ᴴ * a * V k`. Its value at one is the Kraus normalization sum.
The trace dual is `ρ ↦ ∑ k, V k * ρ * (V k)ᴴ`; it preserves trace exactly when
that normalization sum is one. Isometric changes of Kraus family preserve the map.

The normalization criterion connects the Heisenberg and Schrödinger pictures of
a finite-dimensional quantum channel.

The construction uses Mathlib's `CompletelyPositiveMap` and derives complete positivity of
matrix conjugation from `CompletelyPositiveMap.conj` via `CStarMatrix.map_fromBlocks_inl_nonneg`
and `CStarMatrix.map_toBlocks₂₂_nonneg`.

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
    let M' : CStarMatrix (Fin k) (Fin k) (CStarMatrix (n ⊕ m) (n ⊕ m) ℂ) :=
      M.map fun A => ofMatrix (Matrix.fromBlocks (ofMatrix.symm A) 0 0 0)
    have hM' : 0 ≤ M' := CStarMatrix.map_fromBlocks_inl_nonneg hM
    let B : CStarMatrix (n ⊕ m) (n ⊕ m) ℂ := ofMatrix (Matrix.fromBlocks 0 V 0 0)
    have hconj : 0 ≤ M.map fun A =>
        ofMatrix (Matrix.fromBlocks 0 0 0 (Vᴴ * ofMatrix.symm A * V) :
          Matrix (n ⊕ m) (n ⊕ m) ℂ) := by
      convert (CompletelyPositiveMap.conj B).map_cstarMatrix_nonneg M' hM' using 1
      refine CStarMatrix.ext fun i j => ofMatrix.symm.injective ?_
      simp [B, M', Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    convert CStarMatrix.map_toBlocks₂₂_nonneg hconj using 1
    ext i j p q
    simp [Matrix.toBlocks₂₂]

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
    ext i j p q
    -- Unfold the Kraus map's linear-map coercion and read the block sum in `Matrix`.
    change M.map (⇑(∑ d, (conjugateCP (V d)).toLinearMap)) i j p q =
      (∑ d, ofMatrix.symm (M.map (conjugateCP (V d)))) i j p q
    simp only [CStarMatrix.map_apply, LinearMap.sum_apply, Matrix.sum_apply, ofMatrix_symm_apply]
    -- Read both sums of blocks in `Matrix` to evaluate their scalar entries.
    change (∑ d, ofMatrix.symm ((conjugateCP (V d)).toLinearMap (M i j))) p q =
      (∑ d, ofMatrix.symm (conjugateCP (V d) (M i j))) p q
    simp only [Matrix.sum_apply, ofMatrix_symm_apply]
    -- A completely positive map and its underlying linear map have the same `toFun`.
    rfl


/-- Evaluation of a Kraus map. It is not `@[simp]`, so that unitality `krausMap V 1 = 1` stays the
simp normal form recorded by `krausMap_unital_iff`; evaluate with `simp [krausMap_apply]`. -/
theorem krausMap_apply (V : ι → Matrix n m ℂ) (a : CStarMatrix n n ℂ) :
    krausMap V a = ofMatrix (∑ i, (V i)ᴴ * ofMatrix.symm a * V i) := by
  -- Representation equality: `krausMap V` is built from
  -- `toLinearMap := ∑ i, (conjugateCP (V i)).toLinearMap`, and a `CompletelyPositiveMap`
  -- coerces to a function through its `toLinearMap`, so this application is definitionally
  -- that of the sum of linear maps. `change` states it; `LinearMap.sum_apply` and
  -- `conjugateCP_apply` evaluate it.
  change (∑ i, (conjugateCP (V i)).toLinearMap) a = _
  simp only [LinearMap.sum_apply]
  rfl

/-- A Kraus map is unital precisely when its normalization sum is one. -/
@[simp] theorem krausMap_unital_iff [DecidableEq n] [DecidableEq m]
    (V : ι → Matrix n m ℂ) :
    krausMap V 1 = 1 ↔ ∑ i, (V i)ᴴ * V i = 1 := by
  rw [krausMap_apply]
  -- `ofMatrix` is `Equiv.refl _`, so `ofMatrix.symm 1` is the identity matrix and the unit of
  -- `CStarMatrix m m ℂ` is `ofMatrix 1`. `change` records both; `ofMatrix.injective` then compares
  -- the underlying matrices.
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

/-- Trace preservation is equivalent to Kraus normalization. It is not `@[simp]`: the simp
lemma `krausTraceDual_apply` already rewrites its left-hand side, so that side is not a simp
normal form. -/
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

/-- The trace dual preserves trace exactly when the Kraus map is unital. Like
`krausTraceDual_trace_preserving_iff`, whose left-hand side it shares, it is not `@[simp]`. -/
theorem krausTraceDual_trace_preserving_iff_unital [DecidableEq n] [DecidableEq m]
    (V : ι → Matrix n m ℂ) :
    (∀ ρ, trace (krausTraceDual V ρ) = trace ρ) ↔ krausMap V 1 = 1 := by
  rw [krausTraceDual_trace_preserving_iff, krausMap_unital_iff]

/-- An isometric change of the indexing family preserves its Kraus map. -/
theorem krausMap_apply_eq_of_isometry [DecidableEq ι] (V : ι → Matrix n m ℂ)
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
theorem krausMap_apply_eq_of_unitary [DecidableEq ι] (V : ι → Matrix n m ℂ)
    (u : unitary (Matrix ι ι ℂ)) (a : CStarMatrix n n ℂ) :
    krausMap (fun j => ∑ i, (u : Matrix ι ι ℂ) j i • V i) a = krausMap V a :=
  krausMap_apply_eq_of_isometry V (u : Matrix ι ι ℂ) (Unitary.coe_star_mul_self u) a

end Matrix
