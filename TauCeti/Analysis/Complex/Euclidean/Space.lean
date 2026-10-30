/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Real coordinates of complex vectors

`complexToRealEuclidean` identifies a finite complex vector with its real and imaginary
coordinate blocks as a real continuous linear equivalence. It uses the product topology
on complex vectors and the Euclidean topology on the real coordinates, so both directions
are measurable for the Borel structures.
-/

public section

namespace TauCeti

variable (ι : Type*) [Fintype ι]

/-- Split a complex vector into its real and imaginary coordinate blocks, as a real
continuous linear equivalence. -/
noncomputable def complexToRealEuclidean : (ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (ι ⊕ ι) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z ↦ WithLp.toLp 2 (Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im))
      invFun := fun x i ↦ (x (Sum.inl i) : ℂ) + (x (Sum.inr i) : ℂ) * Complex.I
      left_inv := by intro z; ext i; simp
      right_inv := by intro x; ext j; cases j <;> simp
      map_add' := by intro z w; ext j; cases j <;> simp
      map_smul' := by intro r z; ext j; cases j <;> simp }

@[simp]
theorem complexToRealEuclidean_apply (z : ι → ℂ) (k : ι ⊕ ι) :
    complexToRealEuclidean ι z k =
      Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im) k := (rfl)

/-- Recombine the two real coordinate blocks into a complex vector. -/
theorem complexToRealEuclidean_symm_apply (x : EuclideanSpace ℝ (ι ⊕ ι)) (i : ι) :
    (complexToRealEuclidean ι).symm x i =
      (x (Sum.inl i) : ℂ) + (x (Sum.inr i) : ℂ) * Complex.I := (rfl)

@[simp]
theorem complexToRealEuclidean_symm_apply_re (x : EuclideanSpace ℝ (ι ⊕ ι)) (i : ι) :
    ((complexToRealEuclidean ι).symm x i).re = x (Sum.inl i) := by
  simp [complexToRealEuclidean_symm_apply]

@[simp]
theorem complexToRealEuclidean_symm_apply_im (x : EuclideanSpace ℝ (ι ⊕ ι)) (i : ι) :
    ((complexToRealEuclidean ι).symm x i).im = x (Sum.inr i) := by
  simp [complexToRealEuclidean_symm_apply]

end TauCeti
