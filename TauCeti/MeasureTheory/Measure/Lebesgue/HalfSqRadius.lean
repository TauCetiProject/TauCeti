/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Pushing Lebesgue measure forward by half the squared radius

The map `(q, p) ↦ (q² + p²) / 2` sends planar Lebesgue measure to `2π` times Lebesgue measure on
the half-line `[0, ∞)` (`TauCeti.map_volume_half_sq_add_sq`): in polar coordinates `(r, θ)` the
area element is `r dr dθ = ds dθ` for `s = r² / 2`, and the angle ranges over an interval of
length `2π`. Taking products, the map `(q, p) ↦ ((q_i² + p_i²) / 2)_i` on `ℝ^ι × ℝ^ι` sends
Lebesgue measure to `(2π)^|ι|` times Lebesgue measure on the closed positive orthant
(`TauCeti.map_volume_pi_half_sq_add_sq`).

Read on `ℂ^ι` with `z_i = q_i + i p_i`, these maps are the moment maps `|z_i|² / 2` of the reversed
rotation actions `z_i ↦ exp(-i θ_i) z_i` of the circle and of the torus, and the statements
compute their Duistermaat–Heckman measures.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal Real

/-- **Half the squared radius pushes planar Lebesgue measure to `2π` times Lebesgue measure on
`[0, ∞)`.** -/
theorem map_volume_half_sq_add_sq :
    (volume : Measure (ℝ × ℝ)).map (fun x ↦ (x.1 ^ 2 + x.2 ^ 2) / 2) =
      ENNReal.ofReal (2 * π) • volume.restrict (Ici 0) := by
  have hq : Measurable fun x : ℝ × ℝ ↦ (x.1 ^ 2 + x.2 ^ 2) / 2 := by fun_prop
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  ext A hA
  rw [Measure.map_apply hq hA, smul_apply, smul_eq_mul, Measure.restrict_apply hA,
    ← lintegral_indicator_one (hq hA), ← lintegral_comp_polarCoord_symm]
  -- In polar coordinates the integrand only depends on the radius `r`, through `r² / 2`.
  have hpolar : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      ((fun x : ℝ × ℝ ↦ (x.1 ^ 2 + x.2 ^ 2) / 2) ⁻¹' A).indicator 1 (polarCoord.symm p) =
        ENNReal.ofReal p.1 * A.indicator 1 (p.1 ^ 2 / 2) := fun p _ ↦ by
    have h : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq p.2
    rw [polarCoord_symm_apply, smul_eq_mul]
    congr 1
    by_cases hA' : p.1 ^ 2 / 2 ∈ A
    · rw [indicator_of_mem hA', indicator_of_mem (by simpa only [mem_preimage, h] using hA'),
        Pi.one_apply, Pi.one_apply]
    · rw [indicator_of_notMem hA', indicator_of_notMem (by simpa only [mem_preimage, h] using hA')]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpolar, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  -- Integrate out the angle, then substitute `s = r² / 2` in the radial integral.
  have hrad := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioi (a := (0 : ℝ)))
    (f := fun r : ℝ ↦ r ^ 2 / 2) (f' := fun r ↦ r)
    (fun r _ ↦ by simpa using ((hasDerivAt_pow 2 r).div_const 2).hasDerivWithinAt)
    (fun r hr r' hr' h ↦ by
      simp only at h
      nlinarith [mem_Ioi.1 hr, mem_Ioi.1 hr'])
    (A.indicator 1)
  have himage : (fun r : ℝ ↦ r ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
    ext s
    refine ⟨?_, fun hs ↦ ⟨√(2 * s), Real.sqrt_pos.2 (by simpa using hs), ?_⟩⟩
    · rintro ⟨r, hr, rfl⟩
      exact div_pos (pow_pos hr 2) two_pos
    · dsimp only
      rw [Real.sq_sqrt (by linarith [mem_Ioi.1 hs])]
      ring
  rw [himage, setLIntegral_congr_fun measurableSet_Ioi
    (f := fun r ↦ ENNReal.ofReal |r| * A.indicator 1 (r ^ 2 / 2))
    (g := fun r ↦ ENNReal.ofReal r * A.indicator 1 (r ^ 2 / 2))
    (fun r hr ↦ by simp only [abs_of_pos (mem_Ioi.1 hr)])] at hrad
  have hm : Measurable fun r : ℝ ↦ ENNReal.ofReal r * A.indicator 1 (r ^ 2 / 2) :=
    ENNReal.measurable_ofReal.mul ((measurable_one.indicator hA).comp (by fun_prop))
  rw [lintegral_prod (fun z : ℝ × ℝ ↦ ENNReal.ofReal z.1 * A.indicator 1 (z.1 ^ 2 / 2))
    (hm.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [lintegral_mul_const _ hm, ← hrad, lintegral_indicator_one hA, Measure.restrict_apply hA,
    mul_comm]
  ring_nf

variable {ι : Type*} [Fintype ι]

/-- **Half the squared radii push Lebesgue measure on `ℝ^ι × ℝ^ι` to `(2π)^|ι|` times Lebesgue
measure on the closed positive orthant of `ℝ^ι`.** -/
theorem map_volume_pi_half_sq_add_sq :
    (volume : Measure ((ι → ℝ) × (ι → ℝ))).map (fun x i ↦ (x.1 i ^ 2 + x.2 i ^ 2) / 2) =
      ENNReal.ofReal (2 * π) ^ Fintype.card ι • volume.restrict (univ.pi fun _ ↦ Ici 0) := by
  have hq : Measurable fun x : ℝ × ℝ ↦ (x.1 ^ 2 + x.2 ^ 2) / 2 := by fun_prop
  -- `ENNReal.ofReal c` is the coercion of the nonnegative real `c.toNNReal`.
  have hsmul : ENNReal.ofReal (2 * π) • (volume : Measure ℝ).restrict (Ici 0) =
      (2 * π).toNNReal • volume.restrict (Ici 0) := (ENNReal.smul_def _ _).symm
  have : SigmaFinite (ENNReal.ofReal (2 * π) • (volume : Measure ℝ).restrict (Ici 0)) := by
    rw [hsmul]
    infer_instance
  have : SigmaFinite ((volume : Measure (ℝ × ℝ)).map fun x ↦ (x.1 ^ 2 + x.2 ^ 2) / 2) := by
    rw [map_volume_half_sq_add_sq]
    infer_instance
  have he := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).symm
  have hfun : (fun x : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (x.1 i ^ 2 + x.2 i ^ 2) / 2) =
      (fun w i ↦ ((w i).1 ^ 2 + (w i).2 ^ 2) / 2) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).symm :=
    (rfl)
  rw [hfun, ← Measure.map_map (by fun_prop) he.measurable, he.map_eq, volume_pi,
    Measure.pi_map_pi fun _ ↦ hq.aemeasurable, map_volume_half_sq_add_sq]
  refine Measure.pi_eq fun s hs ↦ ?_
  simp only [smul_apply, smul_eq_mul, Measure.restrict_apply (hs _)]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hs), ← pi_inter_distrib, volume_pi_pi,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end TauCeti
