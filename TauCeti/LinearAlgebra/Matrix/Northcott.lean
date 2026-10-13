/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Order.Northcott
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Nondegeneracy from Northcott finiteness

A symmetric real matrix whose quadratic form has finite sublevel sets on the integer lattice
has nonzero determinant. A real null direction would give infinitely many integer vectors of
bounded quadratic value by rounding its multiples. This criterion applies to Gram matrices of
height pairings, where finiteness is supplied by Northcott's theorem.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

namespace Matrix

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A symmetric real matrix has nonzero determinant if its quadratic form has the Northcott
property on the integer lattice. No rationality assumption on its entries is needed. -/
theorem IsSymm.det_ne_zero_of_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    [Northcott (fun z : ι → ℤ ↦ (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ)))] :
    A.det ≠ 0 := by
  classical
  let q : (ι → ℝ) → ℝ := fun x ↦ x ⬝ᵥ A *ᵥ x
  have hcont : Continuous q := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : ι ↦ (-1 : ℝ)) 0)).bddAbove_image hcont.continuousOn
  have hs : Set.Finite {z : ι → ℤ | q (fun i ↦ (z i : ℝ)) ≤ C} :=
    Northcott.finite_le C
  have hker : ∀ x : ι → ℝ, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    let r : ℝ → ι → ℤ := fun t i ↦ ⌊t * x i⌋
    -- Rounding leaves an error in the compact cube [-1, 0]^ι. The null direction
    -- contributes neither a square term nor a cross term, by symmetry.
    have hr : ∀ t, r t ∈ {z : ι → ℤ | q (fun i ↦ (z i : ℝ)) ≤ C} := by
      intro t
      let e : ι → ℝ := (fun i ↦ (r t i : ℝ)) - t • x
      have he : e ∈ Set.Icc (fun _ : ι ↦ (-1 : ℝ)) 0 := by
        constructor <;> intro i
        · have := Int.lt_floor_add_one (t * x i)
          dsimp [e, r]
          linarith
        · exact sub_nonpos.mpr (Int.floor_le (t * x i))
      have hcross : x ⬝ᵥ A *ᵥ (fun i ↦ (r t i : ℝ)) = 0 := by
        rw [hA.dotProduct_mulVec_comm, hx, dotProduct_zero]
      have hq : q e = q (fun i ↦ (r t i : ℝ)) := by
        dsimp only [q, e]
        rw [mulVec_sub, mulVec_smul, hx, smul_zero, sub_zero, sub_dotProduct,
          smul_dotProduct, hcross, smul_zero, sub_zero]
      simpa only [Set.mem_ofPred_eq, hq] using hC (Set.mem_image_of_mem q he)
    ext i
    by_contra hi
    -- If a null vector has a nonzero coordinate, its rounded multiples attain every
    -- integer in that coordinate, contradicting the finite quadratic sublevel set.
    apply Set.infinite_univ (α := ℤ)
    refine (hs.image (fun z ↦ z i)).subset ?_
    intro z _
    refine ⟨r ((z : ℝ) / x i), hr _, ?_⟩
    simp [r, div_mul_cancel₀ _ hi]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have h := hker (x - y) (by rw [mulVec_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  exact (A.isUnit_iff_isUnit_det.mp (mulVec_injective_iff_isUnit.mp hinj)).ne_zero

end Matrix
