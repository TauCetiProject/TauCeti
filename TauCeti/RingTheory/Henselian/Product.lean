/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
    HenselianRing (∀ i, R i) (pi I) where
  jac x hx := by
    rw [mem_jacobson_bot]
    intro y
    rw [Pi.isUnit_iff]
    intro i
    exact mem_jacobson_bot.1 (HenselianRing.jac (hx i)) (y i)
  is_henselian f hf a₀ ha hu := by
    classical
    have hcoord (i : ι) :
        ∃ a : R i, (f.map (Pi.evalRingHom R i)).IsRoot a ∧ a - a₀ i ∈ I i := by
      have hu' := hu.map (quotientMap (I := pi I) (I i) (Pi.evalRingHom R i)
        (fun _ hx ↦ hx i))
      -- The quotient-map formula uses the quotient Ring instance; IsUnit.map elaborates
      -- through its Semiring instance. Unfold those instance projections for this rewrite.
      erw [quotientMap_mk] at hu'
      simp only [Pi.evalRingHom_apply] at hu'
      apply HenselianRing.is_henselian (f.map (Pi.evalRingHom R i)) (hf.map _) (a₀ i)
      · have he := Polynomial.eval_map_apply (p := f) (Pi.evalRingHom R i) a₀
        simp only [Pi.evalRingHom_apply] at he
        rw [he]
        exact ha i
      · have he := Polynomial.eval_map_apply (p := f.derivative) (Pi.evalRingHom R i) a₀
        simp only [Pi.evalRingHom_apply] at he
        simpa only [derivative_map, he] using hu'
    choose a hroot hmem using hcoord
    refine ⟨a, ?_, hmem⟩
    exact funext fun i ↦ by
      have he := Polynomial.eval_map_apply (p := f) (Pi.evalRingHom R i) a
      simp only [Pi.evalRingHom_apply] at he
      simpa only [IsRoot, he, Pi.zero_apply] using hroot i

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
  have hq (j : ι) :
      q.map (Pi.evalRingHom R j) = if h : j = i then h ▸ f else X := by
    by_cases hji : j = i
    · subst j
      simp [q, e, hg]
    · simp [q, e, hji]
  have heval : q.eval (Pi.single i a₀) ∈ pi I := by
    intro j
    have he := Polynomial.eval_map_apply (p := q) (Pi.evalRingHom R j) (Pi.single i a₀)
    simp only [Pi.evalRingHom_apply] at he
    rw [← he, hq]
    split_ifs with hji
    · subst j
      simpa using ha
    · simp [hji]
  have hderiv : IsUnit (q.derivative.eval (Pi.single i a₀)) := by
    rw [Pi.isUnit_iff]
    intro j
    have he := Polynomial.eval_map_apply (p := q.derivative)
      (Pi.evalRingHom R j) (Pi.single i a₀)
    simp only [Pi.evalRingHom_apply] at he
    rw [← he, ← derivative_map, hq]
    split_ifs with hji
    · subst j
      simpa using hunit
    · simp
  -- The assembled polynomial is not necessarily monic, but its root is simple in every
  -- factor. The nonmonic Hensel lemma therefore applies to the product pair.
  obtain ⟨a, hroot, hmem⟩ := q.exists_isRoot_sub_mem heval (hderiv.map (Quotient.mk (pi I)))
  refine ⟨a i, ?_, ?_⟩
  · have hr := congrFun hroot i
    have he := Polynomial.eval_map_apply (p := q) (Pi.evalRingHom R i) a
    simp only [Pi.evalRingHom_apply] at he
    rw [← he, hq] at hr
    simpa only [IsRoot, dite_true, Pi.zero_apply] using hr
  · simpa using hmem i

/-- A product pair is henselian exactly when each of its factors is henselian.
No finiteness assumption on the index set is required. -/
theorem henselianRing_pi_iff :
    HenselianRing (∀ i, R i) (pi I) ↔ ∀ i, HenselianRing (R i) (I i) :=
  ⟨fun _ ↦ henselianRing_of_pi I, fun h ↦ by let := h; infer_instance⟩

end Ideal
