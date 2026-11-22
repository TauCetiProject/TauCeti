/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Positive functionals from finite atomic models

For nonnegative weights `p : ι → ℂ` on a finite linearly ordered alphabet and a real nonzero
parameter `q : ℂˣ`, the finite atomic trace `TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n` is
bundled as a `StarPositiveFunctional` (`TauCeti.TypeAHeckeAlgebra.atomicPositiveFunctional`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.atomicPositiveFunctional`: the complex finite atomic trace bundled as
  a `StarPositiveFunctional`.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TypeAHeckeAlgebra

variable {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]

/-- The complex atomic trace on `n` strands bundled as a `StarPositiveFunctional`. -/
noncomputable def atomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := atomicTrace pos q p n
  square_nonneg := atomicTrace_star_mul_self_nonneg pos q p hp

/-- Forgetting positivity recovers the underlying atomic trace. -/
@[simp]
theorem toLinearMap_atomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) :
    (atomicPositiveFunctional pos q hp n).toLinearMap = atomicTrace pos q p n := (rfl)

/-- Evaluating `atomicPositiveFunctional` at an element recovers `atomicTrace`. -/
@[simp]
theorem atomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] [Finite ι]
    {p : ι → ℂ} (hp : ∀ a, 0 ≤ p a) (n : ℕ) (x : TypeAHeckeAlgebra ℂ q n) :
    atomicPositiveFunctional pos q hp n x = atomicTrace pos q p n x := (rfl)

end TauCeti.TypeAHeckeAlgebra
