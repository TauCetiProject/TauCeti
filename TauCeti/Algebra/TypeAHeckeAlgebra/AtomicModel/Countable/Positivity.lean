/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Positivity.Basic

/-!
# Star compatibility and positivity of countable atomic models

Exhaustion by finite sub-alphabets passes star compatibility
(`TauCeti.TypeAHeckeAlgebra.star_countableAtomicTrace`,
`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star`) and `⋆`-positivity for nonnegative weights
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg`) from finite atomic traces
to countable atomic traces.

## Main results

* `TauCeti.TypeAHeckeAlgebra.star_countableAtomicTrace` and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star`: star compatibility of countable atomic
  traces.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg`: positivity of countable
  atomic traces with nonnegative weights.
-/

public section

open Filter

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {ι : Type*} [LinearOrder ι]
  (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)

/-- **Positivity of countable atomic traces** for nonnegative weights over a complete normed
`StarOrderedRing` with `OrderClosedTopology`. -/
theorem countableAtomicTrace_star_mul_self_nonneg [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [OrderClosedTopology R] [Fact (IsSelfAdjoint (q : R))] {p : ι → R}
    (hp : Summable fun a ↦ ‖p a‖) (hp0 : ∀ a, 0 ≤ p a) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    0 ≤ countableAtomicTrace pos q p hp n (star x * x) :=
  ge_of_tendsto (tendsto_atomicTrace_finset pos q p hp n (star x * x)) <|
    Eventually.of_forall fun s ↦
      atomicTrace_star_mul_self_nonneg (fun a : s ↦ pos a) q (fun a : s ↦ p a)
        (fun a : s ↦ hp0 a) x

/-- Conjugating `countableAtomicTrace` conjugates both the weights and the argument. -/
theorem star_countableAtomicTrace [StarRing R] [NormedStarGroup R]
    [Fact (IsSelfAdjoint (q : R))] (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    star (countableAtomicTrace pos q p hp n x) =
      countableAtomicTrace pos q (star ∘ p) (hp.congr fun _ ↦ (norm_star _).symm) n (star x) :=
  tendsto_nhds_unique
    ((continuous_star.tendsto _).comp (tendsto_atomicTrace_finset pos q p hp n x)) <|
    (tendsto_atomicTrace_finset pos q (star ∘ p) (hp.congr fun _ ↦ (norm_star _).symm) n
      (star x)).congr fun s ↦ (star_atomicTrace (fun a : s ↦ pos a) q (fun a : s ↦ p a) x).symm

/-- For self-adjoint weights, `countableAtomicTrace` commutes with `star`. -/
@[simp]
theorem countableAtomicTrace_star [StarRing R] [ContinuousStar R]
    [Fact (IsSelfAdjoint (q : R))] {p : ι → R} (hp_sum : Summable fun a ↦ ‖p a‖)
    (hp : ∀ a, IsSelfAdjoint (p a)) {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp_sum n (star x) =
      star (countableAtomicTrace pos q p hp_sum n x) :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp_sum n (star x)) <|
    ((continuous_star.tendsto _).comp (tendsto_atomicTrace_finset pos q p hp_sum n x)).congr
      fun s ↦ (atomicTrace_star (fun a : s ↦ pos a) q (fun a : s ↦ p a)
        (fun a : s ↦ hp a) x).symm

end TauCeti.TypeAHeckeAlgebra
