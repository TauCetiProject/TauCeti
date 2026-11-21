/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Dilations on the affine Sobolev field space

Pulling a field back by the dilation `z ↦ t • z` (`TauCeti.Vortex.dilateField`) acts on the
affine Sobolev field space `A_m^k` of framed plane vortex fields.

* Nonzero dilations preserve the natural-order Sobolev fields
  (`TauCeti.Vortex.dilateField_mem_sobolevFields_natCast`).
* A positive dilation fixes the reference field off a disc, since the winding phase is homogeneous
  of degree `0` and the angular form `dθ` is invariant under dilations
  (`TauCeti.Vortex.hasCompactSupport_dilateField_referenceField_sub`), so it maps `A_m^k` to
  itself (`TauCeti.Vortex.dilateField_mem_framedFieldSpace`).

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open Complex Filter Topology TemperedDistribution

namespace TauCeti.Vortex

variable {t : ℝ} {m : ℕ}

/-- Nonzero dilations preserve the natural-order Sobolev fields. -/
theorem dilateField_mem_sobolevFields_natCast (ht : t ≠ 0) {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    dilateField t y ∈ sobolevFields k := by
  have h (j : Fin 4) : (fun z ↦ y (t • z) j) ∈ realSobolevFunctions ℂ k 2 := by
    simpa using comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast (by norm_num)
      (by norm_num) (LinearEquiv.smulOfNeZero ℝ ℂ t ht).toContinuousLinearEquiv
      (mem_sobolevFields.1 hy j)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 0)
  · simpa [dilateField_apply, Pi.smul_def] using Submodule.smul_mem _ t (h 1)
  · simpa [dilateField_apply] using h 2
  · simpa [dilateField_apply] using h 3

/-- A positive dilation fixes the reference field off a disc: the winding phase is homogeneous of
degree `0` and the angular form `dθ` is invariant. So the two differ by a compactly supported
field. -/
theorem hasCompactSupport_dilateField_referenceField_sub (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (ht : 0 < t) : HasCompactSupport (dilateField t (referenceField f m) - referenceField f m) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
  have hr := f.rOut_pos
  have hst := div_nonneg (Real.sqrt_nonneg f.rOut) ht.le
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop
    (√f.rOut + √f.rOut / t + 1)] with z hz
  have hsq {s : ℝ} (hs : √f.rOut ≤ s) : f.rOut ≤ s ^ 2 :=
    (Real.sq_sqrt hr.le).symm.le.trans (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2)
  have h₁ : f.rOut ≤ ‖z‖ ^ 2 := hsq (by linarith [Real.sqrt_nonneg f.rOut])
  have h₂ : f.rOut ≤ ‖t • z‖ ^ 2 := hsq (by
    rw [norm_smul, Real.norm_of_nonneg ht.le, ← div_le_iff₀' ht]
    linarith [Real.sqrt_nonneg f.rOut])
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith [Real.sqrt_nonneg f.rOut])
  simp only [Pi.sub_apply, Pi.zero_apply, dilateField_apply, referenceField_eq_of_rOut_le f m h₁,
    referenceField_eq_of_rOut_le f m h₂, smul_div_norm_smul ht, sub_eq_zero]
  ext i
  fin_cases i <;> simp [abs_of_pos ht] <;> field_simp

/-- **Dilation of the affine field space.** A positive dilation maps `A_m^k` into itself, for
every natural order `k`. -/
theorem dilateField_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {k : ℕ} (ht : 0 < t)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    dilateField t x ∈ framedFieldSpace f m k := by
  rw [mem_framedFieldSpace] at hx ⊢
  have href := mem_sobolevFields_of_hasCompactSupport
    (y := dilateField t (referenceField f m) - referenceField f m)
    ((contDiff_dilateField (contDiff_referenceField f m) t).sub (contDiff_referenceField f m))
    (hasCompactSupport_dilateField_referenceField_sub f m ht) k
  have hsplit : dilateField t x - referenceField f m = dilateField t (x - referenceField f m) +
      (dilateField t (referenceField f m) - referenceField f m) := by
    rw [dilateField_sub]
    abel
  rw [hsplit]
  exact add_mem (dilateField_mem_sobolevFields_natCast ht.ne' hx) href

end TauCeti.Vortex
