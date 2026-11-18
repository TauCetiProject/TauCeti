/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Bundling families of continuous maps into `PiLp`

Since `PiLp p E` carries the product topology for any index type `ι` and exponent `p : ℝ≥0∞`, a
family of continuous maps `f : ∀ i, C(X, E i)` bundles into a continuous map
`ContinuousMap.piLp p f : C(X, PiLp p E)` via `WithLp.toLp p`. Coordinate projection gives the
inverse map, identifying `(∀ i, C(X, E i))` with `C(X, PiLp p E)` (`ContinuousMap.piLpEquiv`), and
`ContinuousMap.piLp` commutes with pointwise `0`, `+`, `-`, subtraction, and scalar multiplication
whenever `PiLp p E` and the coordinate spaces carry the corresponding continuous operations.

## Main declarations

* `ContinuousMap.piLp`: bundle `∀ i, C(X, E i)` into `C(X, PiLp p E)`.
* `ContinuousMap.piLpEquiv`: the equivalence `(∀ i, C(X, E i)) ≃ C(X, PiLp p E)`.
-/

public section

open scoped ENNReal

namespace ContinuousMap

variable {X ι : Type*} [TopologicalSpace X] {E : ι → Type*} [∀ i, TopologicalSpace (E i)]

/-- Bundle a family of continuous maps `∀ i, C(X, E i)` into a continuous map into `PiLp p E`. -/
def piLp (p : ℝ≥0∞) (f : ∀ i, C(X, E i)) : C(X, PiLp p E) where
  toFun x := WithLp.toLp p fun i ↦ f i x
  continuous_toFun := (PiLp.continuous_toLp p E).comp (ContinuousMap.pi f).continuous

/-- Evaluating `ContinuousMap.piLp` collects the pointwise values in `PiLp`. -/
@[simp]
theorem piLp_apply (p : ℝ≥0∞) (f : ∀ i, C(X, E i)) (x : X) :
    piLp p f x = WithLp.toLp p fun i ↦ f i x :=
  (rfl)

/-- Bundling a family of continuous maps `∀ i, C(X, E i)` into `C(X, PiLp p E)` as an
equivalence. -/
def piLpEquiv (p : ℝ≥0∞) : (∀ i, C(X, E i)) ≃ C(X, PiLp p E) where
  toFun := piLp p
  invFun g i := ⟨fun x ↦ g x i, (PiLp.continuous_apply p E i).comp g.continuous⟩
  left_inv _ := funext fun _ ↦ ContinuousMap.ext fun _ ↦ rfl
  right_inv _ := ContinuousMap.ext fun _ ↦ PiLp.ext fun _ ↦ rfl

/-- Applying `ContinuousMap.piLpEquiv` applies `ContinuousMap.piLp`. -/
@[simp]
theorem piLpEquiv_apply (p : ℝ≥0∞) (f : ∀ i, C(X, E i)) :
    piLpEquiv p f = piLp p f :=
  (rfl)

/-- Evaluating `(ContinuousMap.piLpEquiv p).symm` projects onto the `i`-th coordinate. -/
@[simp]
theorem piLpEquiv_symm_apply (p : ℝ≥0∞) (g : C(X, PiLp p E)) (i : ι) (x : X) :
    (piLpEquiv p).symm g i x = g x i :=
  (rfl)

/-- `ContinuousMap.piLp` sends the zero family to `0`. -/
@[simp]
theorem piLp_zero (p : ℝ≥0∞) [∀ i, AddCommGroup (E i)] :
    piLp p (0 : ∀ i, C(X, E i)) = 0 :=
  ContinuousMap.ext fun _ ↦ rfl

/-- `ContinuousMap.piLp` preserves addition. -/
@[simp]
theorem piLp_add (p : ℝ≥0∞) [∀ i, AddCommGroup (E i)] [∀ i, ContinuousAdd (E i)]
    [ContinuousAdd (PiLp p E)] (f g : ∀ i, C(X, E i)) :
    piLp p (f + g) = piLp p f + piLp p g :=
  ContinuousMap.ext fun _ ↦ rfl

/-- `ContinuousMap.piLp` commutes with negation. -/
@[simp]
theorem piLp_neg (p : ℝ≥0∞) [∀ i, AddCommGroup (E i)] [∀ i, ContinuousNeg (E i)]
    [ContinuousNeg (PiLp p E)] (f : ∀ i, C(X, E i)) :
    piLp p (-f) = -piLp p f :=
  ContinuousMap.ext fun _ ↦ rfl

/-- `ContinuousMap.piLp` preserves subtraction. -/
@[simp]
theorem piLp_sub (p : ℝ≥0∞) [∀ i, AddCommGroup (E i)] [∀ i, ContinuousSub (E i)]
    [ContinuousSub (PiLp p E)] (f g : ∀ i, C(X, E i)) :
    piLp p (f - g) = piLp p f - piLp p g :=
  ContinuousMap.ext fun _ ↦ rfl

/-- `ContinuousMap.piLp` commutes with scalar multiplication. -/
@[simp]
theorem piLp_smul {R : Type*} (p : ℝ≥0∞) [∀ i, SMul R (E i)] [∀ i, ContinuousConstSMul R (E i)]
    [ContinuousConstSMul R (PiLp p E)] (c : R) (f : ∀ i, C(X, E i)) :
    piLp p (c • f) = c • piLp p f :=
  ContinuousMap.ext fun _ ↦ rfl

end ContinuousMap
