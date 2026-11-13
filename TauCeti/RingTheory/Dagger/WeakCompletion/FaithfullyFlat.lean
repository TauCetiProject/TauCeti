/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Flat.Basic
public import TauCeti.RingTheory.Dagger.WeakCompletion.Completion
public import TauCeti.RingTheory.Dagger.WeakCompletion.Noetherian
import TauCeti.RingTheory.Dagger.WeakCompletion.Jacobson

/-!
# Faithful flatness of the adic completion over the weak completion

Let `O` be a commutative ring, `π : O`, and `S` a finitely generated `O`-algebra whose weak
completion `S†` is noetherian (for instance, when `O` is the noetherian valuation unit ball `K°`
of a complete ultrametric field `K` and `0 < ‖π‖ < 1`). Then the canonical inclusion `S† → S^∧`
into the `π`-adic completion is faithfully flat.

The proof combines three ingredients:
1. The `π`-adic completion of `S†` is isomorphic to `S^∧` as an `S†`-algebra
   (`adicCompletionAlgEquiv`), without any noetherian hypothesis.
2. Because `S†` is noetherian, its `π`-adic completion is flat over `S†`.
3. Because `π` lies in the Jacobson radical of `S†` (`algebraMap_mem_jacobson`), flatness upgrades
   to faithful flatness (`AdicCompletion.faithfullyFlat_of_le_jacobson`).

As an immediate consequence, flatness of `S†` over `O` is equivalent to flatness of `S^∧` over `O`,
and when `O` is noetherian, flatness of `S` over `O` implies flatness of `S†` over `O`.

## Main results

* `TauCeti.Dagger.weakCompletion.faithfullyFlat_piAdicCompletion`: `S^∧` is faithfully flat over
  `S†` whenever `S†` is noetherian.
* `TauCeti.Dagger.weakCompletion.flat_iff_flat_piAdicCompletion`: `S†` is flat over `O` iff `S^∧`
  is flat over `O`.
* `TauCeti.Dagger.weakCompletion.flat_of_flat`: if `O` and `S†` are noetherian and `S` is flat
  over `O`, then `S†` is flat over `O`.
* `TauCeti.Dagger.weakCompletion.faithfullyFlat_piAdicCompletion_of_unitClosedBall` and
  `TauCeti.Dagger.weakCompletion.flat_of_flat_unitClosedBall`: specializations over a noetherian
  valuation unit ball `K°`.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2, Theorem 2.2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2, (2.1.3).
* H. Matsumura, *Commutative Ring Theory*, Theorem 8.14 (faithful flatness of adic completion
  along an ideal in the Jacobson radical).
-/

public section

namespace TauCeti.Dagger.weakCompletion

section General

variable {O : Type*} [CommRing O] (π : O) (S : Type*) [CommRing S] [Algebra O S]
  [Algebra.FiniteType O S]

/-- When the weak completion `S†` is noetherian, the ambient `π`-adic completion `S^∧` is
faithfully flat over `S†`. -/
instance faithfullyFlat_piAdicCompletion [IsNoetherianRing (weakCompletion π S)] :
    Module.FaithfullyFlat (weakCompletion π S) (piAdicCompletion π S) := by
  have hJ : Ideal.span {algebraMap O (weakCompletion π S) π} ≤
      (⊥ : Ideal (weakCompletion π S)).jacobson := by
    rw [Ideal.jacobson_bot]
    exact span_algebraMap_le_jacobson π S
  have : Module.FaithfullyFlat (weakCompletion π S) (piAdicCompletion π (weakCompletion π S)) :=
    AdicCompletion.faithfullyFlat_of_le_jacobson hJ
  exact Module.FaithfullyFlat.of_linearEquiv (weakCompletion π S)
    (piAdicCompletion π (weakCompletion π S)) (adicCompletionAlgEquiv π S).symm.toLinearEquiv

/-- When `S†` is noetherian, flatness of `S†` over `O` is equivalent to flatness of the `π`-adic
completion `S^∧` over `O`. -/
theorem flat_iff_flat_piAdicCompletion [IsNoetherianRing (weakCompletion π S)] :
    Module.Flat O (weakCompletion π S) ↔ Module.Flat O (piAdicCompletion π S) :=
  Module.Flat.iff_of_faithfullyFlat O (weakCompletion π S) (piAdicCompletion π S)

/-- If both `O` and `S†` are noetherian and `S` is flat over `O`, then `S†` is flat over `O`. -/
theorem flat_of_flat [IsNoetherianRing O] [IsNoetherianRing (weakCompletion π S)]
    [Module.Flat O S] : Module.Flat O (weakCompletion π S) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing O S
  have : Module.Flat O (piAdicCompletion π S) := .trans O S (piAdicCompletion π S)
  exact (flat_iff_flat_piAdicCompletion π S).mpr inferInstance

end General

section UnitClosedBall

variable {K S : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing S] [Algebra (Subring.unitClosedBall K) S]
  [Algebra.FiniteType (Subring.unitClosedBall K) S]

local notation "O" => Subring.unitClosedBall K

/-- Over a noetherian valuation unit ball `K°` of a complete ultrametric field, the `π`-adic
completion `S^∧` of any finitely generated `K°`-algebra `S` is faithfully flat over its weak
completion `S†`. -/
theorem faithfullyFlat_piAdicCompletion_of_unitClosedBall [IsNoetherianRing O] {π : O}
    (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    Module.FaithfullyFlat (weakCompletion π S) (piAdicCompletion π S) := by
  have := isNoetherianRing (S := S) hπ hπ1
  infer_instance

/-- Over a noetherian valuation unit ball `K°` of a complete ultrametric field, the weak completion
of a flat finitely generated `K°`-algebra is flat over `K°`. -/
theorem flat_of_flat_unitClosedBall [IsNoetherianRing O] [Module.Flat O S] {π : O}
    (hπ : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    Module.Flat O (weakCompletion π S) := by
  have := isNoetherianRing (S := S) hπ hπ1
  exact flat_of_flat π S

end UnitClosedBall

end TauCeti.Dagger.weakCompletion
