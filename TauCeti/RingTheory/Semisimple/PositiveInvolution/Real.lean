/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.RingTheory.Semisimple.PositiveInvolution

/-!
# Positivity of an involution after extension of scalars to `ℝ`

Let `B` be a finite-dimensional `ℚ`-algebra with an involution `x ↦ x*` (a `StarRing` structure).
The involution extends `ℝ`-linearly to `B_ℝ = ℝ ⊗[ℚ] B` (`r ⊗ x ↦ r ⊗ x*`, Mathlib's `StarRing`
instance on tensor products of algebras), and the reduced trace `Trd_{B/ℚ}` extends to the
`ℝ`-linear functional `Trd_ℝ (r ⊗ x) = r Trd(x)` on `B_ℝ`, Mathlib's
`Module.Dual.baseChange ℝ (semisimpleReducedTrace ℚ B)`.

The involution is positive, `Trd(x x*) > 0` for every nonzero `x ∈ B`, exactly when its
extension is positive on `B_ℝ`: `Trd_ℝ(v v*) > 0` for every nonzero `v ∈ B_ℝ`
(`TauCeti.PositiveInvolution.iff_real`). Both conditions are positive definiteness of a quadratic
form, `x ↦ Trd(x x*)` on `B` and its real extension on `B_ℝ`
(`TauCeti.Algebra.semisimpleReducedTraceStarForm_baseChange_apply`), and positive definiteness of a
rational form is preserved and reflected by extension of scalars to `ℝ`
(`LinearMap.BilinForm.posDef_toQuadraticMap_baseChange_iff`). The form need not be symmetric.

## Main declarations

* `TauCeti.Algebra.semisimpleReducedTraceStarForm`: the `ℚ`-bilinear form `(x, y) ↦ Trd(x y*)`.
* `TauCeti.Algebra.semisimpleReducedTraceStarForm_baseChange_apply`: the real extension of the form
  is `(v, w) ↦ Trd_ℝ(v w*)`.
* `TauCeti.PositiveInvolution.iff_real`: positivity of the involution is positivity of its real
  extension.
* `TauCeti.PositiveInvolution.baseChange_semisimpleReducedTrace_mul_star_pos`,
  `TauCeti.PositiveInvolution.ofReal`: the two directions for bundled positive involutions.

## References

* J. S. Milne, *Introduction to Shimura varieties*, Proposition 8.10 and Definition 8.11.
-/

public section

namespace TauCeti

open TensorProduct

variable (B : Type*) [Ring B] [Algebra ℚ B]

namespace Algebra

variable [StarRing B]

/-- The `ℚ`-bilinear trace form `(x, y) ↦ Trd(x y*)` of an involution. -/
noncomputable def semisimpleReducedTraceStarForm : LinearMap.BilinForm ℚ B :=
  LinearMap.mk₂ ℚ (fun x y ↦ semisimpleReducedTrace ℚ B (x * star y))
    (fun x x' y ↦ by rw [add_mul, map_add])
    (fun c x y ↦ by rw [smul_mul_assoc, map_smul])
    (fun x y y' ↦ by rw [star_add, mul_add, map_add])
    (fun c x y ↦ by rw [star_rat_smul, mul_smul_comm, map_smul])

variable {B}

@[simp]
theorem semisimpleReducedTraceStarForm_apply (x y : B) :
    semisimpleReducedTraceStarForm B x y = semisimpleReducedTrace ℚ B (x * star y) :=
  (rfl)

/-- The real extension of the trace form is `(v, w) ↦ Trd_ℝ(v w*)`, for the real extension of the
involution. -/
@[simp]
theorem semisimpleReducedTraceStarForm_baseChange_apply (v w : ℝ ⊗[ℚ] B) :
    (semisimpleReducedTraceStarForm B).baseChange ℝ v w =
      Module.Dual.baseChange ℝ (semisimpleReducedTrace ℚ B) (v * star w) := by
  induction v using TensorProduct.inductionOn with
  | add v v' hv hv' => simp [hv, hv', add_mul]
  | tmul r x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp [hw, hw', mul_add]
    | tmul s y =>
      simp [LinearMap.BilinForm.baseChange_tmul, Rat.smul_def]

end Algebra

namespace PositiveInvolution

variable {B} [StarRing B] [FiniteDimensional ℚ B]

/-- **Positivity after extension to `ℝ`.** An involution of a finite-dimensional `ℚ`-algebra is
positive, `Trd(x x*) > 0` for every nonzero `x ∈ B`, exactly when its `ℝ`-linear extension is
positive on `ℝ ⊗[ℚ] B`: `Trd_ℝ(v v*) > 0` for every nonzero `v`. -/
theorem iff_real :
    (∀ x : B, x ≠ 0 → 0 < Algebra.semisimpleReducedTrace ℚ B (x * star x)) ↔
      ∀ v : ℝ ⊗[ℚ] B, v ≠ 0 →
        0 < Module.Dual.baseChange ℝ (Algebra.semisimpleReducedTrace ℚ B) (v * star v) := by
  have h := (Algebra.semisimpleReducedTraceStarForm B).posDef_toQuadraticMap_baseChange_iff (K := ℝ)
  simp only [QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply,
    Algebra.semisimpleReducedTraceStarForm_baseChange_apply,
    Algebra.semisimpleReducedTraceStarForm_apply] at h
  exact h.symm

end PositiveInvolution

variable {B} [FiniteDimensional ℚ B]

/-- **A positive involution is positive on `ℝ ⊗[ℚ] B`.** -/
theorem PositiveInvolution.baseChange_semisimpleReducedTrace_mul_star_pos (P : PositiveInvolution B)
    {v : ℝ ⊗[ℚ] B} (hv : v ≠ 0) :
    letI := P.toStarRing
    0 < Module.Dual.baseChange ℝ (Algebra.semisimpleReducedTrace ℚ B) (v * star v) := by
  let := P.toStarRing
  exact iff_real.1 P.semisimpleReducedTrace_mul_star_pos v hv

/-- **An involution positive on `ℝ ⊗[ℚ] B` is a positive involution.** -/
def PositiveInvolution.ofReal [StarRing B]
    (h : ∀ v : ℝ ⊗[ℚ] B, v ≠ 0 →
      0 < Module.Dual.baseChange ℝ (Algebra.semisimpleReducedTrace ℚ B) (v * star v)) :
    PositiveInvolution B :=
  .ofStarRing (iff_real.2 h)

@[simp]
theorem PositiveInvolution.ofReal_toStarRing [inst : StarRing B]
    (h : ∀ v : ℝ ⊗[ℚ] B, v ≠ 0 →
      0 < Module.Dual.baseChange ℝ (Algebra.semisimpleReducedTrace ℚ B) (v * star v)) :
    (PositiveInvolution.ofReal h).toStarRing = inst :=
  (rfl)

end TauCeti
