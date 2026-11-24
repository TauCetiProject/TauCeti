/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.MeasureTheory.Measure.Haar.RestrictedProduct.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Units

/-!
# The Haar character of units of a restricted product of rings

Let `R i` be a countable family of second-countable locally compact topological rings with open
subrings `B i`, compact at almost every index, so that the restricted product
`Πʳ i, [R i, B i]` is a locally compact topological ring. A unit `x` of the restricted product
scales additive Haar measure on it by the finitary product of the Haar characters of its
coordinates:

`distribHaarChar (Πʳ i, [R i, B i]) x = ∏ᶠ i, distribHaarChar (R i) (x i)`,

with the convention `μ (x • s) = distribHaarChar _ x * μ s` for regular additive Haar measures `μ`.

Only finitely many factors differ from `1`, because at almost every index both `x i` and its
inverse lie in `B i`, so that `x i • B i = B i`. The proof chooses compact sets `K₀ i` with nonempty
interior, equal to `B i` at the cofinitely many indices where `B i` is compact, and evaluates the
restricted Haar product `TauCeti.restrictedAddHaar` on the box with factors `K₀ i` and on its image
under multiplication by `x`, the box with factors `x i • K₀ i`
(`RestrictedProduct.units_smul_box`). Mathlib's criterion
`MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul` turns the resulting box formula
(`TauCeti.restrictedAddHaar_box_eq_finprod`) into the identity of characters. Applied to the
finite adeles of a number field, this computes the Haar character of a finite idele.

## Main results

* `RestrictedProduct.distribHaarChar_eq_finprod`: the Haar character of a unit of a restricted
  product of rings.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., §3.5, pp. 186–189 (the modulus of an automorphism, and restricted Haar products).
* The FLT project (`ImperialCollegeLondon/FLT`, Apache 2.0) proves the corresponding formula
  `ringHaarChar_restrictedProduct` in `FLT/HaarMeasure/HaarChar/Ring.lean` (by Kevin Buzzard),
  through Haar characters of continuous multiplicative equivalences of restricted products; the
  proof here goes through `TauCeti.restrictedAddHaar` instead.
-/

public section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct Set TauCeti TopologicalSpace
open scoped ENNReal NNReal Pointwise RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : ι → Type*} [∀ i, SetLike (A i) (R i)] {B : ∀ i, A i}

variable [∀ i, Ring (R i)] [∀ i, SubringClass (A i) (R i)] [Countable ι]
  [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
  [∀ i, LocallyCompactSpace (R i)] [∀ i, SecondCountableTopology (R i)]
  [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]

/-- **The Haar character of a restricted product of rings.** If `Πʳ i, [R i, B i]` is locally
compact, a unit `x` of it scales additive Haar measure by the finitary product of the Haar
characters of its coordinates. -/
theorem distribHaarChar_eq_finprod [LocallyCompactSpace (Πʳ i, [R i, B i])]
    (x : (Πʳ i, [R i, B i])ˣ) :
    distribHaarChar (Πʳ i, [R i, B i]) x =
      ∏ᶠ i, distribHaarChar (R i) (Units.map (evalMonoidHom R i) x) := by
  classical
  let _ (i : ι) : MeasurableSpace (R i) := borel (R i)
  have _ (i : ι) : BorelSpace (R i) := ⟨rfl⟩
  have hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (R i)) :=
    eventually_isCompact_of_weaklyLocallyCompactSpace_restrictedProduct
      (fun i ↦ hBopen.out i)
      (fun i ↦ (AddSubgroup.ofClass (B i)).isClosed_of_isOpen (hBopen.out i))
      fun i ↦ ⟨0, zero_mem (B i)⟩
  -- Local Haar measures giving mass `1` to a compact set `K₀ i`, equal to `B i` when compact.
  let K₀ (i : ι) : PositiveCompacts (R i) :=
    if h : IsCompact (B i : Set (R i)) then
      ⟨⟨B i, h⟩, by simp [(hBopen.out i).interior_eq]⟩
    else Classical.arbitrary _
  have hK₀ : ∀ᶠ i in cofinite, (K₀ i : Set (R i)) = B i :=
    hBcompact.mono fun i hi ↦ by simp [K₀, hi]
  let μ (i : ι) : Measure (R i) := addHaarMeasure (K₀ i)
  have hμB : ∀ᶠ i in cofinite, μ i (B i) = 1 := hK₀.mono fun i hi ↦ hi ▸ addHaarMeasure_self
  let xi (i : ι) : (R i)ˣ := Units.map (evalMonoidHom R i) x
  -- At almost every index `x i` and its inverse lie in `B i`, so `x i • B i = B i`.
  have hxB : ∀ᶠ i in cofinite, xi i • (B i : Set (R i)) = B i := by
    filter_upwards [x.val.eventually, x⁻¹.val.eventually] with i hx hxinv
    have hxinv' : (((xi i)⁻¹ : (R i)ˣ) : R i) ∈ B i := by simpa [xi] using hxinv
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul]
    refine ⟨fun h ↦ ?_, fun h ↦ mul_mem hxinv' h⟩
    have : (xi i : R i) * ((((xi i)⁻¹ : (R i)ˣ) : R i) * y) = y := by simp
    exact this ▸ mul_mem (by simpa [xi] using hx) h
  have hbox : ∀ᶠ i in cofinite, xi i • (K₀ i : Set (R i)) = B i := by
    filter_upwards [hK₀, hxB] with i hi hx
    rw [hi, hx]
  have hK₀meas (i : ι) : μ i (K₀ i) = 1 := addHaarMeasure_self
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := restrictedAddHaar B μ hμB)
    (s := box fun i ↦ (K₀ i : Set (R i))) ?_ ?_ ?_
  · simp [restrictedAddHaar_box_eq_finprod B μ hμB hK₀, hK₀meas]
  · simp [restrictedAddHaar_box_eq_finprod B μ hμB hK₀, hK₀meas]
  rw [units_smul_box, restrictedAddHaar_box_eq_finprod B μ hμB hbox,
    restrictedAddHaar_box_eq_finprod B μ hμB hK₀]
  rw [finprod_congr fun i ↦ (distribHaarChar_mul (μ i) (xi i) (K₀ i)).symm]
  simp_rw [hK₀meas, mul_one, finprod_one]
  rw [mul_one]
  exact (ENNReal.ofNNRealHom.toMonoidHom.map_finprod_of_injective ENNReal.coe_injective _).symm

end RestrictedProduct
