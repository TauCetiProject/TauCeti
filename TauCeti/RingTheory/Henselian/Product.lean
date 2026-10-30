/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Eval.Pi
public import TauCeti.RingTheory.Henselian.Basic
import Mathlib.Algebra.Group.Pi.Units

/-!
# Products of henselian pairs

A product of pairs `(Rᵢ, Iᵢ)` is henselian if and only if every factor is henselian.
The ideal in the product is Mathlib's `Ideal.pi I`. The index set need not be finite,
and may be empty. Thus the theorem applies both to finite disconnected bases and to
infinite products without Noetherian or completeness assumptions.

The forward construction lifts a simple root coordinatewise. For the converse, a
polynomial in one factor is extended to a polynomial in the product which is `X`
in every other factor. This polynomial need not be monic, so the converse uses
`Polynomial.exists_isRoot_sub_mem`, the nonmonic form of Hensel's lemma.

## References

* The Stacks Project, Section 15.11 (09XD), Henselian pairs.
-/

public section

open Polynomial

namespace Ideal

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i))

/-- Products of henselian pairs are henselian, including infinite and empty products. -/
instance henselianRing_pi [∀ i, HenselianRing (R i) (I i)] :
    HenselianRing (∀ i, R i) (pi I) := by
  have hjac : pi I ≤ jacobson ⊥ := by
    intro x hx
    rw [mem_jacobson_bot]
    intro y
    rw [Pi.isUnit_iff]
    intro i
    exact mem_jacobson_bot.1 (HenselianRing.jac (hx i)) (y i)
  refine ⟨hjac, ?_⟩
  intro f hf a₀ ha hu
  classical
  have := isLocalHom_of_le_jacobson_bot (pi I) hjac
  have hunit : IsUnit (f.derivative.eval a₀) := isUnit_of_map_unit _ _ hu
  have hcoord (i : ι) :
      ∃ a : R i, (f.map (Pi.evalRingHom R i)).IsRoot a ∧ a - a₀ i ∈ I i := by
    have hu' := (hunit.map (Pi.evalRingHom R i)).map (Quotient.mk (I i))
    apply HenselianRing.is_henselian (f.map (Pi.evalRingHom R i)) (hf.map _) (a₀ i)
    · simpa only [eval_map_evalRingHom] using ha i
    · simpa only [derivative_map, eval_map_evalRingHom, Pi.evalRingHom_apply] using hu'
  choose a hroot hmem using hcoord
  refine ⟨a, ?_, hmem⟩
  exact funext fun i ↦ by
    simpa only [IsRoot, eval_map_evalRingHom, Pi.zero_apply] using hroot i

/-- Each factor of a henselian product pair is henselian. This is not an instance,
since the converse instance `henselianRing_pi` would create an instance-search loop. -/
theorem henselianRing_of_pi [HenselianRing (∀ i, R i) (pi I)] (i : ι) :
    HenselianRing (R i) (I i) := by
  classical
  have hjac : I i ≤ jacobson ⊥ := by
    intro x hx
    rw [mem_jacobson_bot]
    intro y
    have hsingle : Pi.single i x ∈ pi I := single_mem_pi hx
    have hu := (mem_jacobson_bot.1 (HenselianRing.jac hsingle)
      (Pi.single i y)).map (Pi.evalRingHom R i)
    simpa using hu
  refine ⟨hjac, fun f _ a₀ ha hu ↦ ?_⟩
  have := isLocalHom_of_le_jacobson_bot (I i) hjac
  have hunit : IsUnit (f.derivative.eval a₀) := isUnit_of_map_unit _ _ hu
  -- Lift the coefficients, then use the coordinate idempotent to replace every other
  -- coordinate polynomial by X. There is no bound on the number of other coordinates.
  obtain ⟨g, hg⟩ := Polynomial.map_surjective (Pi.evalRingHom R i)
    (fun x ↦ ⟨Pi.single i x, by simp⟩) f
  let e : ∀ j, R j := Pi.single i 1
  let q : (∀ j, R j)[X] := C e * g + C (1 - e) * X
  have hqi : q.map (Pi.evalRingHom R i) = f := by
    simp [q, e, hg]
  have hqj (j : ι) (hji : j ≠ i) : q.map (Pi.evalRingHom R j) = X := by
    simp [q, e, hji]
  have heval : q.eval (Pi.single i a₀) ∈ pi I := by
    intro j
    rcases eq_or_ne j i with rfl | hji
    · simpa only [← eval_map_evalRingHom, hqi, Pi.single_eq_same] using ha
    · simp [← eval_map_evalRingHom, hqj j hji, hji]
  have hderiv : IsUnit (q.derivative.eval (Pi.single i a₀)) := by
    rw [Pi.isUnit_iff]
    intro j
    rcases eq_or_ne j i with rfl | hji
    · simpa only [← eval_map_evalRingHom, ← derivative_map, hqi, Pi.single_eq_same]
        using hunit
    · simp [← eval_map_evalRingHom, ← derivative_map, hqj j hji]
  -- The assembled polynomial is not necessarily monic, but its root is simple in every
  -- factor. The nonmonic Hensel lemma therefore applies to the product pair.
  obtain ⟨a, hroot, hmem⟩ := q.exists_isRoot_sub_mem heval (hderiv.map (Quotient.mk (pi I)))
  refine ⟨a i, ?_, ?_⟩
  · have hr := congrFun hroot i
    rw [← eval_map_evalRingHom, hqi] at hr
    simpa only [IsRoot, Pi.zero_apply] using hr
  · simpa using hmem i

/-- A product pair is henselian exactly when each of its factors is henselian.
No finiteness assumption on the index set is required. -/
theorem henselianRing_pi_iff :
    HenselianRing (∀ i, R i) (pi I) ↔ ∀ i, HenselianRing (R i) (I i) :=
  ⟨fun _ ↦ henselianRing_of_pi I, fun h ↦ by let := h; infer_instance⟩

end Ideal
