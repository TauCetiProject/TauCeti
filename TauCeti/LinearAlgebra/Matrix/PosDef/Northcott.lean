/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Order.Northcott
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Positive definiteness from Northcott finiteness

A symmetric real matrix whose quadratic form has finite sublevel sets on the integer lattice
is positive definite. A negative direction contradicts finiteness by scaling integer vectors
and density of rational vectors; a real null direction gives infinitely many integer vectors
of bounded quadratic value by rounding its multiples. This criterion applies to Gram matrices of
height pairings, where finiteness is supplied by Northcott's theorem.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

namespace Matrix

open scoped Matrix

variable {ι : Type*} [Fintype ι]

/-- A symmetric real matrix is positive semidefinite if its quadratic form has the Northcott
property on the integer lattice. -/
theorem IsSymm.posSemidef_of_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hN : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ)))) : A.PosSemidef := by
  classical
  let := hN
  let q : (ι → ℝ) → ℝ := fun x ↦ x ⬝ᵥ A *ᵥ x
  have hcont : Continuous q := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  have hsmul (t : ℝ) (x : ι → ℝ) : q (t • x) = t ^ 2 * q x := by
    simp [q, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two,
      mul_assoc]
  have hint (z : ι → ℤ) : 0 ≤ q (fun i ↦ (z i : ℝ)) := by
    by_contra hz
    have hzneg := lt_of_not_ge hz
    have hzne : z ≠ 0 := by
      intro h
      simp [h, q] at hzneg
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hzne
    have hfinite : (Set.univ : Set ℤ).Finite := by
      refine (Northcott.finite_le (h := fun z : ι → ℤ ↦ q (fun i ↦ (z i : ℝ))) 0).of_injOn
        (f := fun n : ℤ ↦ n • z) ?_ ?_
      · intro n _
        have heq : (fun i ↦ ((n • z) i : ℝ)) = (n : ℝ) • (fun i ↦ (z i : ℝ)) := by
          ext i
          simp
        simp only [Set.mem_ofPred_eq]
        rw [heq, hsmul]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hzneg.le
      · intro n _ m _ h
        exact mul_right_cancel₀ hi (by simpa using congrFun h i)
    exact Set.infinite_univ hfinite
  have hnonneg (x : ι → ℝ) : 0 ≤ q x := by
    refine (DenseRange.piMap (fun _ : ι ↦ Rat.denseRange_cast)).induction_on x
      (isClosed_le continuous_const hcont) ?_
    intro y
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors ℤ) y
    choose z hz using hd
    have heq : (fun i ↦ (z i : ℝ)) = (d : ℤ) • (fun i ↦ (y i : ℝ)) := by
      ext i
      simpa [Algebra.smul_def] using congrArg (fun r : ℚ ↦ (r : ℝ)) (hz i)
    have h := hint z
    rw [heq, ← Int.cast_smul_eq_zsmul ℝ, hsmul] at h
    exact nonneg_of_mul_nonneg_right h
      (sq_pos_of_ne_zero (by exact_mod_cast (nonZeroDivisors.ne_zero d.property)))
  refine PosSemidef.of_dotProduct_mulVec_nonneg (by simpa using hA) ?_
  simpa [q] using hnonneg

/-- A symmetric real matrix whose quadratic form has the Northcott property on the integer
lattice has no nonzero real null vector. -/
theorem IsSymm.eq_zero_of_mulVec_eq_zero_of_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hN : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ))))
    {x : ι → ℝ} (hx : A *ᵥ x = 0) : x = 0 := by
  classical
  let := hN
  let q : (ι → ℝ) → ℝ := fun x ↦ x ⬝ᵥ A *ᵥ x
  have hcont : Continuous q := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : ι ↦ (-1 : ℝ)) 0)).bddAbove_image hcont.continuousOn
  have hs : Set.Finite {z : ι → ℤ | q (fun i ↦ (z i : ℝ)) ≤ C} :=
    Northcott.finite_le C
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
      simp [q, e, mulVec_sub, mulVec_smul, hx, sub_dotProduct, smul_dotProduct, hcross]
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

/-- A symmetric real matrix is positive definite if its quadratic form has the Northcott
property on the integer lattice. No rationality assumption on its entries is needed. -/
theorem IsSymm.posDef_of_northcott {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (hN : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ A *ᵥ (fun i ↦ (z i : ℝ)))) : A.PosDef := by
  classical
  apply (hA.posSemidef_of_northcott hN).posDef_iff_det_ne_zero.mpr
  intro hdet
  obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  exact hv (hA.eq_zero_of_mulVec_eq_zero_of_northcott hN hAv)

end Matrix
