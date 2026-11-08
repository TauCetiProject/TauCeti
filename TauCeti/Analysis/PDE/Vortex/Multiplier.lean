/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier

/-!
# Smooth coefficient multiplication on plane-vortex Sobolev fields

The direction space of the affine vortex field space is defined using real `L²` representatives
and Mathlib's Bessel-potential regularity, coordinate by coordinate. Smooth bounded coefficients
with bounded derivatives through order `k` preserve this space at integer order `k`. The
coefficient need not have a Sobolev tail: this is the form needed for the linear terms produced
by expanding the equation and gauge action about a nondecaying reference field.

The matrix version allows mixing the connection and section coordinates and permits different
bounds for each coefficient. In particular a smooth gauge with bounded derivatives through order
`k` preserves the Sobolev fields under its linear action
(`gaugeLinearAction_mem_sobolevFields_natCast`).
These results assert membership, not boundedness of a completed operator or smoothness of the
nonlinear equation map.

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
  refine mem_sobolevFields.mpr fun i ↦ mem_realSobolevFunctions.mpr ?_
  have hentry (j : Fin 4) : ∃ v : Lp ℝ 2 (volume : Measure ℂ),
      v ∈ realSobolevSubmodule ℂ k 2 ∧
        (v : ℂ → ℝ) =ᵐ[volume] fun z ↦ A i j z * y z j := by
    obtain ⟨u, hu, huS⟩ := mem_realSobolevFunctions.mp (mem_sobolevFields.mp hy j)
    obtain ⟨M, hM, hMbound⟩ := hbound i j
    obtain ⟨v, hvS, hv⟩ :=
      exists_mem_realSobolevSubmodule_ae_eq_mul_of_bounded_derivatives
        (by norm_num : (1 : ENNReal) < 2) (by norm_num : (2 : ENNReal) ≠ ⊤)
        k (hA i j) hM hMbound (mem_realSobolevSubmodule.mpr huS)
    refine ⟨v, hvS, ?_⟩
    filter_upwards [hv, hu] with z hvz huz
    rw [hvz, huz]
  choose v hvS hv using hentry
  refine ⟨∑ j, v j, ?_, mem_realSobolevSubmodule.mp
    (Submodule.sum_mem _ fun j _ ↦ hvS j)⟩
  filter_upwards [Lp.coeFn_finsetSum Finset.univ v, Filter.eventually_all.mpr hv] with z hz hvz
  simp only [hz, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ hvz j

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

/-- **Smooth gauges act on Sobolev fields.** A smooth gauge whose derivatives through order `k`
are bounded preserves the integer-order Sobolev fields under its linear action, which rotates the
section and fixes the connection. No decay of the gauge is required. -/
theorem gaugeLinearAction_mem_sobolevFields_natCast {k : ℕ} {u : ℂ → Circle}
    (hu : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)))
    (hbound : ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ (u z : ℂ)) z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    gaugeLinearAction u y ∈ sobolevFields k := by
  have hc (i : Fin 4) := mem_sobolevFields.1 hy i
  have h0 : (fun _ : ℂ ↦ (0 : ℝ)) ∈ realSobolevFunctions ℂ k 2 := zero_mem _
  -- The linear action is `P y + Re u • Q y + Im u • R y` with constant `P`, `Q`, `R`.
  have hP : (fun z ↦ !₂[y z 0, y z 1, 0, 0]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [hc 0, hc 1, h0, h0]
  have hQ : (fun z ↦ !₂[0, 0, y z 2, y z 3]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [h0, h0, hc 2, hc 3]
  have hR : (fun z ↦ !₂[0, 0, -y z 3, y z 2]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [h0, h0, neg_mem (hc 3), hc 2]
  -- A single bound for the derivatives through order `k` of `Re u` and of `Im u`.
  choose! C hC using hbound
  have hL (L : ℂ →L[ℝ] ℝ) : ∃ M ≥ 0, ∀ n ≤ k, ∀ z,
      ‖iteratedFDeriv ℝ n (fun z ↦ L (u z : ℂ)) z‖ ≤ M := by
    refine ⟨‖L‖ * ∑ n ∈ Finset.range (k + 1), |C n|, by positivity, fun n hn z ↦ ?_⟩
    refine (L.norm_iteratedFDeriv_comp_left hu.contDiffAt (by exact_mod_cast le_top)).trans ?_
    gcongr
    exact (hC n hn z).trans ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun n ↦ |C n|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))))
  obtain ⟨Mr, hMr, hre⟩ := hL Complex.reCLM
  obtain ⟨Mi, hMi, him⟩ := hL Complex.imCLM
  convert add_mem (add_mem hP
    (smul_mem_sobolevFields_natCast k (Complex.reCLM.contDiff.comp hu) hMr hre hQ))
    (smul_mem_sobolevFields_natCast k (Complex.imCLM.contDiff.comp hu) hMi him hR) using 1
  ext z i
  fin_cases i <;>
    simp only [gaugeLinearAction_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Pi.add_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, mul_zero, add_zero, zero_add, mul_neg] <;>
    ring

end TauCeti.Vortex
