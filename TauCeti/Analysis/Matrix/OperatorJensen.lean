/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import TauCeti.Analysis.Matrix.FunctionalCalculus

/-!
# Jensen's operator inequality for isometries

Let `V` be an isometry, a rectangular matrix with `Vᴴ * V = 1`, and let `f` be operator concave:
`A ↦ cfc f A` is concave on a set `S` of square matrices closed under unitary conjugation. Then
compressing by `V` lowers the functional calculus,

`Vᴴ * cfc f A * V ≤ cfc f (Vᴴ * A * V)` for Hermitian `A ∈ S`,

`Matrix.conjTranspose_mul_cfc_mul_le_cfc_conjTranspose_mul_mul`. For the logarithm, which Mathlib
proves operator concave on the strictly positive elements (`CFC.concaveOn_log`), this is the
compression inequality `-log (Vᴴ * A * V) ≤ Vᴴ * (-log A) * V` for positive definite `A`,
`Matrix.PosDef.conjTranspose_mul_log_mul_le_log`. Applied to the partial-trace isometry and the
relative modular operator, this compression inequality is the operator inequality behind the
monotonicity of the relative entropy under partial traces, and so behind the strong subadditivity
of the von Neumann entropy.

## The argument

Let `P = V * Vᴴ` be the projection onto the range of `V` and `U = 2 • P - 1` the reflection
across it, a self-adjoint unitary with `U * V = V`. The pinching `C = (A + U * A * U) / 2` of `A`
is `P * A * P + (1 - P) * A * (1 - P)`, so the range of `V` is invariant,
`C * V = V * (Vᴴ * A * V)`. The functional calculus preserves intertwiners
(`Matrix.IsHermitian.cfc_mul_eq_mul_cfc`), hence `Vᴴ * cfc f C * V = cfc f (Vᴴ * A * V)` and
`cfc f (U * A * U) = U * cfc f A * U`. Concavity at the midpoint gives
`(cfc f A + U * cfc f A * U) / 2 ≤ cfc f C`, and compressing both sides by `V` gives the
inequality, since `U * V = V`.

## References

* F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*, Math. Ann.
  **258** (1982), 229–241.
* F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, Bull. London Math. Soc. **35**
  (2003), 553–564.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Section V.2
  (operator convex functions and Jensen's inequality for compressions).
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **Jensen's operator inequality for isometries.** Let `f` be operator concave on a set `S` of
matrices closed under unitary conjugation, in the sense that `A ↦ cfc f A` is concave on `S`. For
a Hermitian `A ∈ S` and an isometry `V`, that is `Vᴴ * V = 1`, compressing by `V` lowers the
functional calculus: `Vᴴ * cfc f A * V ≤ cfc f (Vᴴ * A * V)`. -/
theorem conjTranspose_mul_cfc_mul_le_cfc_conjTranspose_mul_mul {f : ℝ → ℝ}
    {S : Set (Matrix m m 𝕜)} (hf : ConcaveOn ℝ S (cfc f))
    (hS : ∀ a ∈ S, ∀ u ∈ unitary (Matrix m m 𝕜), u * a * star u ∈ S)
    {A : Matrix m m 𝕜} (hAS : A ∈ S) (hA : A.IsHermitian) {V : Matrix m n 𝕜}
    (hV : Vᴴ * V = 1) :
    Vᴴ * cfc f A * V ≤ cfc f (Vᴴ * A * V) := by
  -- the reflection `U = 2 P - 1` across the range of `V`, where `P = V Vᴴ`
  set U : Matrix m m 𝕜 := 2 • (V * Vᴴ) - 1 with hU_def
  have hUh : Uᴴ = U := by
    rw [hU_def, conjTranspose_sub, conjTranspose_nsmul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_one]
  have hUV : U * V = V := by
    simp only [hU_def, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, hV, Matrix.mul_one,
      Matrix.one_mul]
    module
  have hVU : Vᴴ * U = Vᴴ := by simpa [hUh] using congrArg conjTranspose hUV
  -- `P = V Vᴴ` is idempotent
  have hP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  have hUU : U * U = 1 := by
    simp only [hU_def, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hP,
      Matrix.one_mul, Matrix.mul_one]
    module
  -- the reflected matrix `B = U A U` and the pinching `C = (A + B) / 2`
  set B := U * A * U with hB_def
  have hBS : B ∈ S := by
    simpa [star_eq_conjTranspose, hUh] using
      hS A hAS U (Unitary.mem_iff.mpr (by rw [star_eq_conjTranspose, hUh, hUU, and_self]))
  have hB : B.IsHermitian := by simpa only [hUh] using isHermitian_conjTranspose_mul_mul U hA
  set C := (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B with hC_def
  have hC : C.IsHermitian := (hA.smul (IsSelfAdjoint.all _)).add (hB.smul (IsSelfAdjoint.all _))
  -- `U` intertwines `A` with `B`, and `V` intertwines `Vᴴ A V` with `C`
  have hBU : cfc f B * U = U * cfc f A :=
    hB.cfc_mul_eq_mul_cfc hA (by rw [hB_def, Matrix.mul_assoc, hUU, Matrix.mul_one]) f
  have hCV : cfc f C * V = V * cfc f (Vᴴ * A * V) := by
    refine hC.cfc_mul_eq_mul_cfc (isHermitian_conjTranspose_mul_mul V hA) ?_ f
    have hBV : B * V = 2 • (V * (Vᴴ * A * V)) - A * V := by
      rw [hB_def, Matrix.mul_assoc, hUV, hU_def]
      simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hC_def, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hBV, two_nsmul]
    module
  -- compress both sides of concavity at the midpoint by `V`
  have hBcomp : Vᴴ * cfc f B * V = Vᴴ * cfc f A * V := by
    have h : Vᴴ * cfc f B * V = Vᴴ * (cfc f B * U) * V := by
      rw [← Matrix.mul_assoc Vᴴ (cfc f B) U, Matrix.mul_assoc (Vᴴ * cfc f B) U V, hUV]
    rw [h, hBU, ← Matrix.mul_assoc, hVU]
  have hCcomp : Vᴴ * cfc f C * V = cfc f (Vᴴ * A * V) := by
    rw [Matrix.mul_assoc, hCV, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hconc : (1 / 2 : ℝ) • cfc f A + (1 / 2 : ℝ) • cfc f B ≤ cfc f C :=
    hf.2 hAS hBS (by norm_num) (by norm_num) (by norm_num)
  have hcomp := (le_iff.mp hconc).conjTranspose_mul_mul_same V
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hBcomp, hCcomp] at hcomp
  exact le_iff.mpr (by convert hcomp using 2; module)

-- the C⋆-algebra structure of `Matrix m m ℂ`, needed for `CFC.concaveOn_log`, is scoped
open scoped Matrix.Norms.L2Operator in
/-- **The compression inequality for the logarithm.** For a positive definite complex matrix `A`
and an isometry `V`, that is `Vᴴ * V = 1`, `Vᴴ * log A * V ≤ log (Vᴴ * A * V)`; equivalently,
`-log (Vᴴ * A * V) ≤ Vᴴ * (-log A) * V`. -/
theorem PosDef.conjTranspose_mul_log_mul_le_log {A : Matrix m m ℂ} (hA : A.PosDef)
    {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) :
    Vᴴ * CFC.log A * V ≤ CFC.log (Vᴴ * A * V) :=
  conjTranspose_mul_cfc_mul_le_cfc_conjTranspose_mul_mul CFC.concaveOn_log
    (fun _ ha _ hu ↦
      (Unitary.isUnit_coe (U := ⟨_, hu⟩)).isStrictlyPositive_star_right_conjugate_iff.mpr ha)
    hA.isStrictlyPositive hA.isHermitian hV

end Matrix
