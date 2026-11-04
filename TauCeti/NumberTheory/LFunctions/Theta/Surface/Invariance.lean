/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar

/-!
# Inversion and translation of the norm-one surface measure

The product-over-places normalization of `surfaceHaar` is invariant under coordinatewise
inversion and under multiplication by any positive norm-one parameter. Thus theta integrals
can be changed from a unit fundamental domain to its inverse or a translate without changing
the measure. These are the substitutions in the inversion formula for the averaged theta
kernel and in the comparison of the Euclidean dual with the trace dual of an ideal lattice.

The measure is defined using the radial shell `1 ≤ N(y) ≤ e`. Inversion carries that shell
to `e⁻¹ ≤ N(y) ≤ 1`; both have `dt / t`-mass one. The surface/radial product formula shows
that this change of shell introduces no constant.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, especially (5.8).
-/

public section

open MeasureTheory Measure Set NumberField NumberField.mixedEmbedding

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- Translation by a norm-one parameter preserves `d*x` in the product-over-places
normalization. -/
theorem measurePreserving_surfaceMul (c : normOneSurface K) :
    MeasurePreserving (surfaceMul c) (surfaceHaar K) (surfaceHaar K) := by
  refine ⟨(surfaceMul c).continuous.measurable, ?_⟩
  ext A hA
  have hc := mem_normOneSurface.mp c.property
  have hCA : MeasurableSet (Subtype.val '' A) :=
    (measurableSet_normOneSurface K).subtype_image hA
  have hC : MeasurableSet (surfacePart ⁻¹' (Subtype.val '' A) ∩
      archNorm ⁻¹' Icc 1 (Real.exp 1)) :=
    (measurable_surfacePart hCA).inter (continuous_archNorm.measurable measurableSet_Icc)
  rw [map_apply (surfaceMul c).continuous.measurable hA,
    surfaceHaar_apply ((surfaceMul c).continuous.measurable hA)]
  have heq : surfacePart ⁻¹' (Subtype.val '' ((surfaceMul c) ⁻¹' A)) ∩
      archNorm ⁻¹' Icc 1 (Real.exp 1) =ᵐ[archHaar K]
      (c.val * ·) ⁻¹' (surfacePart ⁻¹' (Subtype.val '' A) ∩
        archNorm ⁻¹' Icc 1 (Real.exp 1)) := by
    filter_upwards [ae_archHaar_pos] with y hy
    let x : normOneSurface K := ⟨surfacePart y, surfacePart_mem_normOneSurface hy⟩
    have hx : surfacePart y = (x : realSpace K) := rfl
    simp only [mem_inter_iff, mem_preimage, surfacePart_mul hc.2, map_mul, hc.2,
      one_mul, hx, ← surfaceMul_apply c x, Subtype.coe_injective.mem_set_image]
  rw [measure_congr heq, ← map_apply (measurable_const_mul c.val) hC,
    map_archHaar_mul_left hc.1, ← surfaceHaar_apply hA]

/-- Inversion preserves `d*x`. Its change of radial shell contributes no normalization factor. -/
theorem measurePreserving_surfaceInv :
    MeasurePreserving (surfaceInv K) (surfaceHaar K) (surfaceHaar K) := by
  refine ⟨(surfaceInv K).continuous.measurable, ?_⟩
  ext A hA
  have hCA : MeasurableSet (Subtype.val '' A) :=
    (measurableSet_normOneSurface K).subtype_image hA
  have hC : MeasurableSet (surfacePart ⁻¹' (Subtype.val '' A) ∩
      archNorm ⁻¹' Icc (Real.exp 1)⁻¹ 1) :=
    (measurable_surfacePart hCA).inter (continuous_archNorm.measurable measurableSet_Icc)
  have hmass : multHaar (Icc (Real.exp 1)⁻¹ 1) = 1 := by
    rw [multHaar_Icc (inv_pos.mpr (Real.exp_pos 1))
      (inv_le_one_of_one_le₀ (Real.one_le_exp zero_le_one))]
    simp [Real.log_inv]
  rw [map_apply (surfaceInv K).continuous.measurable hA,
    surfaceHaar_apply ((surfaceInv K).continuous.measurable hA)]
  have heq : surfacePart ⁻¹' (Subtype.val '' ((surfaceInv K) ⁻¹' A)) ∩
      archNorm ⁻¹' Icc 1 (Real.exp 1) =ᵐ[archHaar K]
      Inv.inv ⁻¹' (surfacePart ⁻¹' (Subtype.val '' A) ∩
        archNorm ⁻¹' Icc (Real.exp 1)⁻¹ 1) := by
    filter_upwards [ae_archHaar_pos] with y hy
    let x : normOneSurface K := ⟨surfacePart y, surfacePart_mem_normOneSurface hy⟩
    have hx : surfacePart y = (x : realSpace K) := rfl
    simp only [mem_inter_iff, mem_preimage, surfacePart_inv (archNorm_pos hy).le, archNorm_inv, hx,
      ← surfaceInv_apply x, Subtype.coe_injective.mem_set_image]
    congr 1
    apply propext
    exact ⟨fun h ↦ ⟨(inv_le_inv₀ (Real.exp_pos 1) (archNorm_pos hy)).mpr h.2,
        (inv_le_one₀ (archNorm_pos hy)).mpr h.1⟩,
      fun h ↦ ⟨(inv_le_one₀ (archNorm_pos hy)).mp h.2,
        (inv_le_inv₀ (Real.exp_pos 1) (archNorm_pos hy)).mp h.1⟩⟩
  rw [measure_congr heq, ← map_apply measurable_inv hC, map_archHaar_inv,
    archHaar_surfacePart_preimage_inter hA measurableSet_Icc, hmass, mul_one]

end TauCeti.LFunctions
