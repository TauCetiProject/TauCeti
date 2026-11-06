/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier

/-!
# Smooth coefficient multiplication on plane-vortex Sobolev fields

The direction space of the affine vortex field space is defined using real `L²` representatives
and Mathlib's Bessel-potential regularity, coordinate by coordinate. Smooth bounded coefficients
with bounded derivatives through order `k` preserve this space at integer order `k`. The
coefficient need not have a Sobolev tail: this is the form needed for the linear terms produced
by expanding the equation and gauge action about a nondecaying reference field.

The matrix version allows mixing the connection and section coordinates and permits different
bounds for each coefficient. These results assert membership, not boundedness of a completed
operator or smoothness of the nonlinear equation map.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution
open scoped ContDiff

/-- Smooth matrix coefficients act on integer-order plane-vortex Sobolev fields whenever
each entry and its derivatives through order `k` are bounded. This includes coordinate changes
which mix connection and section variations. -/
theorem mulVec_mem_sobolevFields_natCast (k : ℕ)
    {A : Fin 4 → Fin 4 → ℂ → ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hbound : ∀ i j, ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ M)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    (fun z ↦ WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j)) ∈
      sobolevFields k := by
  refine mem_sobolevFields.mpr fun i ↦ ?_
  have hentry (j : Fin 4) : (fun z ↦ A i j z * y z j) ∈ realSobolevFunctions ℂ k 2 := by
    obtain ⟨u, hu, huS⟩ := mem_realSobolevFunctions.mp (mem_sobolevFields.mp hy j)
    obtain ⟨M, hM, hMbound⟩ := hbound i j
    obtain ⟨v, hvS, hv⟩ :=
      exists_mem_realSobolevSubmodule_ae_eq_mul_of_bounded_derivatives
        (by norm_num : (1 : ENNReal) < 2) (by norm_num : (2 : ENNReal) ≠ ⊤)
        k (hA i j) hM hMbound (mem_realSobolevSubmodule.mpr huS)
    refine mem_realSobolevFunctions_of_ae_eq (coeFn_mem_realSobolevFunctions hvS) ?_
    filter_upwards [hv, hu] with z hvz huz
    rw [hvz, huz]
  convert Submodule.sum_mem _ (t := Finset.univ) fun j _ ↦ hentry j using 1
  ext z
  simp

/-- Multiplication by a smooth real coefficient with bounded derivatives through order `k`
preserves the integer-order Sobolev direction space of plane-vortex fields. No decay of the
coefficient is required. -/
theorem smul_mem_sobolevFields_natCast (k : ℕ) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ j ≤ k, ∀ z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ M)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    (fun z ↦ ψ z • y z) ∈ sobolevFields k := by
  have hdiag : ∀ i j : Fin 4, ContDiff ℝ ∞ (fun z ↦ if i = j then ψ z else 0) := by
    intro i j
    split_ifs
    · exact hψ
    · exact contDiff_const
  have hdiag_bound : ∀ i j : Fin 4, ∃ M ≥ 0, ∀ n ≤ k, ∀ z,
      ‖iteratedFDeriv ℝ n (fun w ↦ if i = j then ψ w else 0) z‖ ≤ M := by
    intro i j
    refine ⟨M, hM, fun n hn z ↦ ?_⟩
    by_cases hij : i = j
    · simpa only [ite_eq_left hij] using hbound n hn z
    · simpa only [ite_eq_right hij, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hM
  have h := mulVec_mem_sobolevFields_natCast k hdiag hdiag_bound hy
  have hfield : (fun z ↦ WithLp.toLp 2 (fun i ↦
      ∑ j : Fin 4, (if i = j then ψ z else 0) * y z j)) = fun z ↦ ψ z • y z := by
    ext z i
    simp [PiLp.smul_apply, smul_eq_mul]
  exact hfield ▸ h

end TauCeti.Vortex
