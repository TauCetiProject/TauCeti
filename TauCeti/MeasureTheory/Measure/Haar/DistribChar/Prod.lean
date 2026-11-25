/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
public import TauCeti.Algebra.Group.Action.Pointwise.Set.Units
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar.Basic

/-!
# The Haar character of units of products of rings

For a locally compact topological ring `R`, a unit `x` of `R` acts on the additive group of `R` by
left multiplication, and `μ (x • s) = distribHaarChar R x * μ s` for every regular additive Haar
measure `μ` on `R` and every set `s`. This file computes that character on products.

* A unit of `R × S` acts on a product set `s ×ˢ t` coordinatewise
  (`Units.smul_set_prod`), and a unit of `Π i, T i` acts on a box `univ.pi C`
  coordinatewise (`Units.smul_set_univ_pi`).
* Product Haar measures are products on boxes, so on a product `R × S` the character of a unit is
  the product of the characters of its two components, and on a finite product `Π i, T i` it is
  the product of the characters of the coordinates. Each formula is read off one box of compact
  factors with nonempty interior, through Mathlib's criterion
  `MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul`.

## Main results

* `MeasureTheory.distribHaarChar_prod`, `MeasureTheory.distribHaarChar_pi`: products.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism, and restricted Haar products).
* The FLT project (`ImperialCollegeLondon/FLT`, Apache 2.0) proves the corresponding formulas
  `ringHaarChar_prod'` and `ringHaarChar_pi'` in `FLT/HaarMeasure/HaarChar/Ring.lean` (by Kevin
  Buzzard).
-/

public section

open MeasureTheory Measure Set TopologicalSpace
open scoped NNReal ENNReal Pointwise

namespace MeasureTheory

section Ring

variable {R S : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [Ring S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]

/-- **The Haar character of a product.** A unit of `R × S` scales Haar measure on `R × S` by the
product of the characters of its components. -/
theorem distribHaarChar_prod [SecondCountableTopology R] [SecondCountableTopology S]
    (x : (R × S)ˣ) :
    distribHaarChar (R × S) x =
      distribHaarChar R (Units.map (MonoidHom.fst R S) x) *
        distribHaarChar S (Units.map (MonoidHom.snd R S) x) := by
  borelize R S
  let μ : Measure R := addHaar
  let ν : Measure S := addHaar
  let K : PositiveCompacts R := Classical.arbitrary _
  let L : PositiveCompacts S := Classical.arbitrary _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ.prod ν) (s := (K : Set R) ×ˢ L) ?_ ?_ ?_
  · rw [prod_prod]
    exact mul_ne_zero (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
      (measure_pos_of_nonempty_interior ν L.interior_nonempty).ne'
  · rw [prod_prod]
    exact ENNReal.mul_ne_top K.isCompact.measure_ne_top L.isCompact.measure_ne_top
  · rw [Units.smul_set_prod, prod_prod, prod_prod, ← distribHaarChar_mul, ← distribHaarChar_mul,
      ENNReal.coe_mul]
    ring

variable {ι : Type*} [Fintype ι] {T : ι → Type*} [∀ i, Ring (T i)] [∀ i, TopologicalSpace (T i)]
  [∀ i, IsTopologicalRing (T i)] [∀ i, LocallyCompactSpace (T i)]

/-- **The Haar character of a finite product.** A unit of `Π i, T i` scales Haar measure on
`Π i, T i` by the product of the characters of its coordinates. -/
theorem distribHaarChar_pi [∀ i, SecondCountableTopology (T i)] (x : (Π i, T i)ˣ) :
    distribHaarChar (Π i, T i) x =
      ∏ i, distribHaarChar (T i) (Units.map (Pi.evalMonoidHom T i) x) := by
  let _ (i : ι) : MeasurableSpace (T i) := borel (T i)
  have _ (i : ι) : BorelSpace (T i) := ⟨rfl⟩
  let μ (i : ι) : Measure (T i) := addHaar
  let K (i : ι) : PositiveCompacts (T i) := Classical.arbitrary _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := univ.pi fun i ↦ (K i : Set (T i))) ?_ ?_ ?_
  · rw [pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
      (measure_pos_of_nonempty_interior (μ i) (K i).interior_nonempty).ne'
  · rw [pi_pi]
    exact ENNReal.prod_ne_top fun i _ ↦ (K i).isCompact.measure_ne_top
  · rw [Units.smul_set_univ_pi, pi_pi, pi_pi, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ (distribHaarChar_mul (μ i) _ _).symm

end Ring

end MeasureTheory
