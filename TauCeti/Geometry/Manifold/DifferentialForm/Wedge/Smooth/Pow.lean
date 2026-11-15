/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Wedge powers of smooth differential forms

For a smooth real differential form `φ` of degree `k`, the wedge power
`TauCeti.SmoothForm.wedgePow φ m` is the smooth form `φ ∧ ⋯ ∧ φ` of degree `k * m`, with `m`
factors. The empty power is the constant function `1`, and `φ ^ (m + 1) = φ ^ m ∧ φ`. At every
point it is the wedge power `ContinuousAlternatingMap.wedgePow` of the value of `φ`
(`TauCeti.SmoothForm.wedgePow_apply`), so the pointwise identities for wedge powers apply to it.
The symplectic volume form `σⁿ / n!` is built from the top power of a symplectic form
(`TauCeti.SmoothTwoForm.volumeForm`).

## Main definitions

* `TauCeti.SmoothForm.wedgePow φ m`: the `m`-th wedge power of a smooth real form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  {k : ℕ}

/-- The `m`-th wedge power `φ ∧ ⋯ ∧ φ` of a smooth real form `φ` of degree `k`, a smooth form of
degree `k * m`. The empty power is the constant function `1`, and `φ ^ (m + 1) = φ ^ m ∧ φ`. -/
def wedgePow (φ : SmoothForm I M ℝ k) : (m : ℕ) → SmoothForm I M ℝ (k * m)
  | 0 => ⟨RoughForm.ofFunction I fun _ ↦ (1 : ℝ),
      (isSmoothForm_ofFunction_iff.mpr contMDiff_const).mem_smoothBundleForms⟩
  | m + 1 => wedge (wedgePow φ m) φ

/-- The successor wedge power is the previous power wedged with the form. -/
theorem wedgePow_succ (φ : SmoothForm I M ℝ k) (m : ℕ) :
    φ.wedgePow (m + 1) = wedge (φ.wedgePow m) φ := (rfl)

/-- A wedge power of a smooth form is, at every point, the wedge power of its value. -/
@[simp]
theorem wedgePow_apply (φ : SmoothForm I M ℝ k) (m : ℕ) (x : M) :
    (φ.wedgePow m).1 x = (φ.1 x).wedgePow m := by
  induction m with
  | zero =>
    ext v
    exact (RoughForm.ofFunction_apply _ x v).trans
      (ContinuousAlternatingMap.wedgePow_zero_apply (φ.1 x) v).symm
  | succ m ih =>
    rw [wedgePow_succ, coe_wedge, RoughForm.wedge_def, RoughForm.wedgeWith_apply', ih,
      ContinuousAlternatingMap.wedgePow_succ]

end SmoothForm

end TauCeti
