/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic

/-!
# Weighting measures by continuous functions

For a continuous function `g : C(X, R)` and a measure `μ` on `X` (Mathlib's `AbstractMeasure`,
an `R`-linear functional on `C(X, R)`), the *weighted measure* `weight g μ` integrates `f` to
`μ (g * f)`; informally, `d(weight g μ) = g dμ`. This is an operator on the existing measure
carrier, not a new kind of measure. Weighting by the coordinate function `x` on `ℤ_p` is the
operation whose Amice transform is the Mahler derivation, and weighting by the characteristic
function of a clopen set is restriction to that set followed by extension by zero.

Weighting needs multiplication on `C(X, R)` to be continuous for the compact-open topology, which
the hypothesis `[ContinuousMul C(X, R)]` records; instance search supplies it when `X` is locally
compact and `R` is a topological ring, and also when `X` is compact and `R` is a normed ring.

## Main definitions

* `AbstractMeasure.weight g`: the `R`-linear operator `μ ↦ (f ↦ μ (g * f))`.

## Main results

* `AbstractMeasure.weight_mul`: `weight (g * h) = weight g ∘ weight h`.
* `AbstractMeasure.weight_dirac`: `weight g δ_x = g x • δ_x`.
* `AbstractMeasure.map_weight`: weighting is natural for pushforward.
* `AbstractMeasure.iterate_weight_apply`: the `k`-th iterate of `weight g` integrates `f` to
  `μ (g ^ k * f)`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.2.
-/

public noncomputable section

open scoped AbstractMeasure

namespace AbstractMeasure

variable {X Y R E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module R E] [ContinuousSMul R E]
  [ContinuousMul C(X, R)]

/-- The measure `μ` weighted by the continuous function `g`, which integrates `f` to
`μ (g * f)`. -/
def weight (g : C(X, R)) : AbstractMeasure X R E →ₗ[R] AbstractMeasure X R E where
  toFun μ := μ ∘L
    { toLinearMap := LinearMap.mulLeft R g, cont := continuous_const.mul continuous_id }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem weight_apply (g : C(X, R)) (μ : AbstractMeasure X R E) (f : C(X, R)) :
    weight g μ f = μ (g * f) := (rfl)

@[simp]
theorem weight_one (μ : AbstractMeasure X R E) : weight 1 μ = μ := by
  ext; simp

theorem weight_mul (g h : C(X, R)) (μ : AbstractMeasure X R E) :
    weight (g * h) μ = weight g (weight h μ) := by
  ext f; simp [mul_left_comm, mul_assoc]

theorem weight_add (g h : C(X, R)) (μ : AbstractMeasure X R E) :
    weight (g + h) μ = weight g μ + weight h μ := by
  ext f; simp [add_mul]

/-- Weighting by a constant function is scalar multiplication. -/
@[simp]
theorem weight_const (r : R) (μ : AbstractMeasure X R E) :
    weight (ContinuousMap.const X r) μ = r • μ := by
  ext f
  have hf : ContinuousMap.const X r * f = r • f := by ext; simp
  simp [hf]

@[simp]
theorem weight_zero (μ : AbstractMeasure X R E) : weight 0 μ = 0 := by
  simpa using weight_const (X := X) (0 : R) μ

@[simp]
theorem weight_dirac (g : C(X, R)) (x : X) : weight g (dirac R x) = g x • dirac R x := by
  ext f; simp

/-- The `k`-th iterate of weighting by `g` is weighting by `g ^ k`, evaluated on test
functions. -/
theorem iterate_weight_apply (g : C(X, R)) (k : ℕ) (μ : AbstractMeasure X R E) (f : C(X, R)) :
    ((weight g)^[k] μ) f = μ (g ^ k * f) := by
  induction k generalizing μ with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, weight_apply, pow_succ', mul_assoc]

/-- Weighting is natural for pushforward: pushing forward `μ` weighted by `g ∘ h` along `h` is
the pushforward of `μ` weighted by `g`. -/
theorem map_weight [ContinuousMul C(Y, R)] (h : C(X, Y)) (g : C(Y, R))
    (μ : AbstractMeasure X R E) :
    map h (weight (g.comp h) μ) = weight g (map h μ) := by
  ext f; simp

end AbstractMeasure
