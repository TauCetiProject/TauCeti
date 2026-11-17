/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Algebraic lemmas on spaces of continuous maps

When a bundled continuous map `f : C(X, M₀)` into a topological monoid with zero is a unit,
evaluating `f⁻¹ʳ` at `x : X` agrees with `(f x)⁻¹ʳ` (`ContinuousMap.ringInverse_apply`). Without
`IsUnit f`, `f⁻¹ʳ` vanishes globally even at points where `f x` is individually invertible.

In addition, if a zero-preserving functional on `C(α, A)` does not vanish at `1`, the domain `α`
must be nonempty (`ContinuousMap.nonempty_of_map_one_ne_zero`), and on scalar-valued continuous
maps `C(α, R)` every linear map sends `const α c = c • 1` to `c • φ 1`
(`ContinuousMap.map_const_eq_smul_map_one`).
-/

public section

open scoped Ring

namespace ContinuousMap

/-- Evaluating `f⁻¹ʳ` at a point `x` gives `(f x)⁻¹ʳ` whenever `f : C(X, M₀)` is a unit. -/
theorem ringInverse_apply {X M₀ : Type*} [TopologicalSpace X] [MonoidWithZero M₀]
    [TopologicalSpace M₀] [ContinuousMul M₀] {f : C(X, M₀)} (hf : IsUnit f) (x : X) :
    f⁻¹ʳ x = (f x)⁻¹ʳ :=
  hf.map_ringInverse ((Pi.evalMonoidHom (fun _ ↦ M₀) x).comp coeFnMonoidHom)

/-- If a zero-preserving map on `C(α, A)` does not vanish at `1`, then `α` is nonempty. -/
theorem nonempty_of_map_one_ne_zero {α A B Φ : Type*} [TopologicalSpace α] [TopologicalSpace A]
    [Zero A] [One A] [Zero B] [FunLike Φ C(α, A) B] [ZeroHomClass Φ C(α, A) B] (φ : Φ)
    (hφ : φ 1 ≠ 0) : Nonempty α := by
  by_contra! h
  have h10 : (1 : C(α, A)) = 0 := ext fun x => isEmptyElim x
  exact hφ (by rw [h10, map_zero])

/-- A linear map on `C(α, R)` evaluates at the constant function `c` to `c • φ 1`. -/
theorem map_const_eq_smul_map_one {α R B Φ : Type*} [TopologicalSpace α] [Semiring R]
    [TopologicalSpace R] [ContinuousAdd R] [ContinuousConstSMul R R] [AddCommMonoid B] [Module R B]
    [FunLike Φ C(α, R) B] [LinearMapClass Φ R C(α, R) B] (φ : Φ) (c : R) :
    φ (const α c) = c • φ 1 := by
  have hc : const α c = c • (1 : C(α, R)) := by ext; simp
  rw [hc, map_smul]

end ContinuousMap
