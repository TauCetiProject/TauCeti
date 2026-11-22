/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.UnitAction

/-!
# The volume scaling of multiplication on the mixed space

Multiplication by a fixed point `c` of the mixed space is an `ℝ`-linear endomorphism whose
determinant is the `ℝ`-algebra norm of `c` (`NumberField.mixedEmbedding.algebraNorm_apply`, in
`CanonicalEmbedding.Basic`), so it scales Lebesgue measure by the absolute value of that norm
(`NumberField.mixedEmbedding.abs_algebraNorm`).

Specialising to the image of a unit, which has mixed norm one, gives that the unit action on the
mixed space leaves the volume of every set unchanged.

## Main results

* `NumberField.mixedEmbedding.abs_det_changeOfVariables`: the absolute value of the real
  determinant of the `mixedSpace K`-linear change of variables `z ↦ ∑ i, z i • b i` of
  `ι → mixedSpace K`, for any family `b` of vectors of `ι → K`, is `|N (det b)|`;
* `NumberField.mixedEmbedding.volume_image_mul_left`: multiplication by `c` scales volume by
  `mixedEmbedding.norm c`;
* `NumberField.mixedEmbedding.integral_comp_mul_left`: the corresponding change of variables
  `∫ g (c * x) = (mixedEmbedding.norm c)⁻¹ • ∫ g` in an integral;
* `MeasureTheory.SMulInvariantMeasure (𝓞 K)ˣ (mixedSpace K) volume`: the unit action preserves
  volume, so Mathlib's `measure_smul` and `measure_preimage_smul` apply.
-/

public section

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Pointwise

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Multiplication by `c` scales volume by the mixed norm of `c`.**  The set `A` is arbitrary,
so there is no measurability hypothesis to discharge.  Its specialisation to the action of a
unit, where the factor is one, is the `SMulInvariantMeasure` instance below. -/
theorem volume_image_mul_left (c : mixedSpace K) (A : Set (mixedSpace K)) :
    volume ((c * ·) '' A) = ENNReal.ofReal (mixedEmbedding.norm c) * volume A := by
  have h : (c * ·) = ⇑(Algebra.lmul ℝ (mixedSpace K) c) := funext fun _ ↦ by simp
  rw [h, Measure.addHaar_image_linearMap, ← Algebra.norm_apply, abs_algebraNorm]

open scoped Classical in
/-- **Change of variables for multiplication on the mixed space.** If `c` has nonzero mixed norm,
the substitution `x ↦ c * x` divides an integral over the mixed space by `mixedEmbedding.norm c`.
No integrability or measurability hypothesis on `g` is needed. -/
theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : mixedSpace K → E) {c : mixedSpace K} (hc : mixedEmbedding.norm c ≠ 0) :
    ∫ x, g (c * x) = (mixedEmbedding.norm c)⁻¹ • ∫ x, g x := by
  have hu : IsUnit c := TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero.mpr hc
  let e : mixedSpace K ≃L[ℝ] mixedSpace K :=
    (hu.unit.mulLeftLinearEquiv ℝ (mixedSpace K)).toContinuousLinearEquiv
  have hdet : LinearMap.det (Algebra.lmul ℝ (mixedSpace K) c) ≠ 0 := by
    rw [← Algebra.norm_apply, ← abs_ne_zero, abs_algebraNorm]
    exact hc
  have hmap : Measure.map (c * ·) volume =
      ENNReal.ofReal (mixedEmbedding.norm c)⁻¹ • (volume : Measure (mixedSpace K)) := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
    rwa [abs_inv, ← Algebra.norm_apply, abs_algebraNorm] at h
  have h := e.toHomeomorph.measurableEmbedding.integral_map (μ := volume) g
  -- The homeomorphism underlying `e` is multiplication by `c`.
  have he : ⇑e.toHomeomorph = (c * ·) := rfl
  rw [he, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c))] at h
  exact h.symm

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

open scoped Classical in
/-- The absolute value of the real determinant of the change of variables `z ↦ ∑ i, z i • b i` of
`ι → mixedSpace K` is the absolute value of the algebra norm of `det b`. -/
theorem abs_det_changeOfVariables {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → K) :
    |LinearMap.det
      ((Matrix.toLin' (Matrix.of fun j i ↦ mixedEmbedding K (b i j))).restrictScalars ℝ)| =
      |(Algebra.norm ℚ (Matrix.of b).det : ℝ)| := by
  have hA : (Matrix.of fun j i ↦ mixedEmbedding K (b i j)) =
      ((Matrix.of b).map (mixedEmbedding K)).transpose := rfl
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hA, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, abs_algebraNorm, norm_eq_norm]
  simp

end NumberField.mixedEmbedding
