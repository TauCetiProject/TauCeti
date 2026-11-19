/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Basic lemmas on bundled `C^n` maps

This file evaluates Mathlib's constant `C^n` map `ContMDiffMap.const` pointwise
(`ContMDiffMap.const_apply`), and defines the `C^n` function `e^{t f}` of a real `C^n` function `f`
(`ContMDiffMap.expMul`), with inverse `e^{-t f}` (`ContMDiffMap.expMul_mul_expMul_neg`).
-/

public section

open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞}

/-- The constant `C^n` map with value `y` takes the value `y` at every point. -/
@[simp]
theorem const_apply (y : M') (x : M) : (const y : C^n⟮I, M; I', M'⟯) x = y :=
  rfl

section Exp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

/-- The `C^n` function `e^{t f}` of a real `C^n` function `f`. -/
noncomputable def expMul (f : C^n⟮I, M; ℝ⟯) (t : ℝ) : C^n⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ Real.exp (t * f x),
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).comp_contMDiff f.contMDiff :)⟩

/-- The value of `e^{t f}` at `x` is `Real.exp (t * f x)`. -/
@[simp]
theorem expMul_apply (f : C^n⟮I, M; ℝ⟯) (t : ℝ) (x : M) :
    expMul f t x = Real.exp (t * f x) :=
  (rfl)

/-- `e^{t f} e^{-t f} = 1`. -/
theorem expMul_mul_expMul_neg (f : C^n⟮I, M; ℝ⟯) (t : ℝ) (x : M) :
    expMul f t x * expMul f (-t) x = 1 := by
  rw [expMul_apply, expMul_apply, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]

end Exp

end ContMDiffMap
