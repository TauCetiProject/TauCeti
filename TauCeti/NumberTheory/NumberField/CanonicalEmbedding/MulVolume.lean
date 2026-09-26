/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import Mathlib.RingTheory.Complex
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction
public import TauCeti.RingTheory.NormTrace.Pi
public import TauCeti.RingTheory.NormTrace.Prod

/-!
# The volume scaling of multiplication on the mixed space

Multiplication by a fixed point `c` of the mixed space is an `ℝ`-linear endomorphism whose
determinant is the `ℝ`-algebra norm of `c`, so it scales Lebesgue measure by the absolute value
of that norm.  The norm is computed here as one factor per real place and one `Complex.normSq`
per complex place, and its absolute value is `mixedEmbedding.norm c`.

Specialising to the image of a unit, which has mixed norm one, gives that the unit action on the
mixed space leaves the volume of every set unchanged.

## Main results

* `NumberField.mixedEmbedding.algebraNorm_apply`: the `ℝ`-algebra norm of `c`, as a product over
  the places;
* `NumberField.mixedEmbedding.abs_algebraNorm`: the absolute value of that norm is
  `mixedEmbedding.norm c`;
* `NumberField.mixedEmbedding.volume_image_mul_left`: multiplication by `c` scales volume by
  `mixedEmbedding.norm c`;
* `MeasureTheory.SMulInvariantMeasure (𝓞 K)ˣ (mixedSpace K) volume`: the unit action preserves
  volume, so Mathlib's `measure_smul` and `measure_preimage_smul` apply.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Pointwise

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The `ℝ`-algebra norm of a point of the mixed space.**  Each real coordinate contributes
its own factor and each complex coordinate contributes the norm of multiplication by a complex
number, namely `Complex.normSq`. -/
theorem algebraNorm_apply (c : mixedSpace K) :
    Algebra.norm ℝ c = (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  simp [TauCeti.Algebra.norm_prod, TauCeti.Algebra.norm_pi, Algebra.norm_complex_apply]

/-- **The absolute `ℝ`-algebra norm of `c` is the mixed norm of `c`.**  Reach for this rather
than `algebraNorm_apply` when the norm feeds a measure-scaling lemma such as
`Measure.addHaar_image_linearMap`, which asks for the absolute value. -/
theorem abs_algebraNorm (c : mixedSpace K) : |Algebra.norm ℝ c| = mixedEmbedding.norm c := by
  -- Both sides are the same product of local absolute values: a real place contributes `|c.1 w|`
  -- with `mult w = 1`, a complex place `Complex.normSq (c.2 w) = ‖c.2 w‖ ^ 2` with `mult w = 2`.
  rw [algebraNorm_apply, abs_mul, Finset.abs_prod, Finset.abs_prod, mixedEmbedding.norm_apply,
    InfinitePlace.prod_eq_prod_mul_prod]
  simp [normAtPlace_apply_of_isReal, normAtPlace_apply_of_isComplex, Complex.normSq_eq_norm_sq,
    Subtype.prop]

open scoped Classical in
/-- **Multiplication by `c` scales volume by the mixed norm of `c`.**  The set `A` is arbitrary,
so there is no measurability hypothesis to discharge.  Its specialisation to the action of a
unit, where the factor is one, is the `SMulInvariantMeasure` instance below. -/
theorem volume_image_mul_left (c : mixedSpace K) (A : Set (mixedSpace K)) :
    volume ((c * ·) '' A) = ENNReal.ofReal (mixedEmbedding.norm c) * volume A := by
  have h : (c * ·) = ⇑(Algebra.lmul ℝ (mixedSpace K) c) := funext fun _ ↦ by simp
  rw [h, Measure.addHaar_image_linearMap, ← Algebra.norm_apply, abs_algebraNorm]

open scoped Classical in
/-- **The unit action preserves volume.**  With it, `measure_smul` and `measure_preimage_smul`
are the volume equations for `u • A` and `(u • ·) ⁻¹' A`, and `measurePreserving_smul` and the
`IsFundamentalDomain` lemmas apply to the unit action.  For a general multiplier `c`, where the
factor is `mixedEmbedding.norm c`, use `volume_image_mul_left`. -/
instance : SMulInvariantMeasure (𝓞 K)ˣ (mixedSpace K) volume :=
  -- A unit has mixed norm one, so the factor `volume_image_mul_left` supplies is one.
  have h (v : (𝓞 K)ˣ) (A : Set (mixedSpace K)) : volume (v • A) = volume A := by
    simp [← Set.image_smul, volume_image_mul_left]
  -- The preimage under `u` is the image under `u⁻¹`.
  ⟨fun u s _ ↦ by rw [Set.preimage_smul, h]⟩

end NumberField.mixedEmbedding
