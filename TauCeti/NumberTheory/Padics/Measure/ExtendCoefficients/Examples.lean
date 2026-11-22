/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.BaseChange
import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Clopen
import TauCeti.NumberTheory.Padics.Measure.IntegralUnitBall

/-!
# Arithmetic examples of coefficient extension

These examples compute extensions of integral Dirac measures, their restrictions on a two-point
space, and the coefficient extension, character evaluation, and Amice transform of pure tensors.

For the Amice-transform identity, use `ext n <;> simp` to simplify each power series coefficient.
This uses `AbstractMeasure.amiceTransform_extendScalars` and
`AbstractMeasure.amiceTransform_extendCoefficients_algebraMap`. The source coefficient ring is
finite free over `ℤ_[p]`, the target is a complete ultrametric normed field, and both actions of
`ℤ_[p]` are continuous. The coefficient map is a `ℤ_[p]`-algebra map with image in the closed
unit ball. For the coefficient map `algebraMap O L`, the same calculation uses the compatible
scalar tower `ℤ_[p] → O → L`.
-/

noncomputable section

open AbstractMeasure ContinuousMap TopologicalSpace
open scoped PowerSeries TensorProduct

variable {p : ℕ} [Fact p.Prime]

/- The arithmetic case: coefficients extended from `ℤ_p` to `ℚ_p`. The extension of a Dirac measure
evaluates test functions at its point, and it does not forget multiplicities. -/

example (x : ℤ_[p]) (f : C(ℤ_[p], ℚ_[p])) :
    extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
      (dirac ℤ_[p] x) f = f x := by
  simp

example (x : ℤ_[p]) :
    extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
        (dirac ℤ_[p] x + dirac ℤ_[p] x) ≠
      extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
        (dirac ℤ_[p] x) := by
  intro h
  have := congrArg (fun ν : D(ℤ_[p], ℚ_[p]) ↦ ν 1) h
  norm_num at this

-- On the two-point space the restriction keeps the coefficient at zero
-- and discards the atom outside the clopen.
example :
    let s : Clopens (Fin 2) := ⟨{0}, isClopen_discrete {0}⟩
    restrictClopen s
        (extendCoefficients PadicInt.Coe.ringHom (by simpa using PadicInt.norm_le_one)
          (2 • dirac ℤ_[p] (0 : Fin 2) - 3 • dirac ℤ_[p] 1)) =
      2 • dirac ℚ_[p] ⟨0, by simp⟩ := by
  dsimp only
  let s : Clopens (Fin 2) := ⟨{0}, isClopen_discrete {0}⟩
  change restrictClopen s _ = _
  have h0 : (0 : Fin 2) ∈ s := by simp [s]
  have h1 : (1 : Fin 2) ∉ s := by simp [s]
  rw [← extendCoefficients_restrictClopen]
  simp only [map_sub, map_nsmul, restrictClopen_dirac_mem s h0,
    restrictClopen_dirac_not_mem s h1, nsmul_zero, sub_zero, extendCoefficients_dirac]

variable {O : Type*} [NormedCommRing O] [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O]
  [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

variable {K : Type*} [NormedCommRing K] [CompleteSpace K] [IsUltrametricDist K] {B : ℝ}

example (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) (a : O) (x : ℤ_[p]) :
    extendCoefficients j hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a • dirac K x := by
  simp

example {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
    (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ B) (a : O) (x : G) :
    χ.extendedCharacterRingHom j hj (baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a * χ x := by
  simp

example {L : Type*} [NormedField L] [CompleteSpace L] [IsUltrametricDist L]
    [Algebra ℤ_[p] L] [ContinuousSMul ℤ_[p] L] (j : O →ₐ[ℤ_[p]] L) (hj : ∀ a, ‖j a‖ ≤ 1)
    (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    (extendCoefficients (j : O →+* L) hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] μ))).amiceTransform =
      j a • PowerSeries.map (algebraMap ℤ_[p] L) μ.amiceTransform := by
  ext n
  simp
