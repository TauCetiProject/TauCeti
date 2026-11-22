/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Positivity
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Positive functionals from countable atomic models

For nonnegative summable weights `p : ι → ℂ` on a linearly ordered alphabet and a real nonzero
parameter `q : ℂˣ`, the countable atomic trace
`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace pos q p hp n` is bundled as a
`StarPositiveFunctional` (`TauCeti.TypeAHeckeAlgebra.countableAtomicPositiveFunctional`).

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.countableAtomicPositiveFunctional`: the complex countable atomic trace
  bundled as a `StarPositiveFunctional`.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TypeAHeckeAlgebra

variable {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]

/-- The complex countable atomic trace on `n` strands bundled as a `StarPositiveFunctional`. -/
noncomputable def countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    StarPositiveFunctional (TypeAHeckeAlgebra ℂ q n) where
  toLinearMap := countableAtomicTrace pos q p hp n
  square_nonneg := countableAtomicTrace_star_mul_self_nonneg pos q hp hp0

/-- Forgetting positivity recovers the underlying countable atomic trace. -/
@[simp]
theorem toLinearMap_countableAtomicPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ) :
    (countableAtomicPositiveFunctional pos q hp hp0 n).toLinearMap =
      countableAtomicTrace pos q p hp n := (rfl)

/-- Evaluating `countableAtomicPositiveFunctional` at an element recovers `countableAtomicTrace`. -/
@[simp]
theorem countableAtomicPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))]
    {p : ι → ℂ} (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) (n : ℕ)
    (x : TypeAHeckeAlgebra ℂ q n) :
    countableAtomicPositiveFunctional pos q hp hp0 n x =
      countableAtomicTrace pos q p hp n x := (rfl)

end TauCeti.TypeAHeckeAlgebra
