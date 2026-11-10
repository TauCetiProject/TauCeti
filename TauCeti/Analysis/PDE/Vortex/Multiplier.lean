/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
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
(`gaugeLinearAction_mem_sobolevFields_natCast`). Multiplication by a coordinate of a framed field
of `A_m^n`, which combines a smooth reference coordinate with a Sobolev tail, preserves `H^n(ℂ)` for
`n > 1` (`mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`), since `H^n(ℂ)` is then an
algebra.
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
  refine mem_sobolevFields.mpr fun i ↦ ?_
  have hentry (j : Fin 4) : (fun z ↦ A i j z * y z j) ∈ realSobolevFunctions ℂ k 2 := by
    obtain ⟨M, -, hM⟩ := hbound i j
    exact mul_mem_realSobolevFunctions_of_bounded_derivatives (by norm_num) (by norm_num) k
      (hA i j) (fun n hn ↦ ⟨M, hM n hn⟩) (mem_sobolevFields.mp hy j)
  convert Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) ↦ hentry j using 1
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

/-- **Multiplication by a coordinate of a framed field.** For an integer `n > 1`, multiplying a
real `H^n` function by a coordinate of a field of `A_m^n` gives an `H^n` function. The
reference coordinate is smooth with bounded derivatives, and `H^n(ℂ)` is an algebra. -/
theorem mul_mem_realSobolevFunctions_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)}
    {m n : ℕ} (hn : 1 < n) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m n)
    (i : Fin 4) {g : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ n 2) :
    (fun z ↦ x z i * g z) ∈ realSobolevFunctions ℂ n 2 := by
  have hw : (fun z ↦ (x - referenceField f m) z i) ∈ realSobolevFunctions ℂ n 2 :=
    mem_sobolevFields.1 (mem_framedFieldSpace.1 hx) i
  have href := mul_mem_realSobolevFunctions_of_bounded_derivatives (p := 2) (by norm_num)
    (by norm_num) n (contDiff_euclidean.1 (contDiff_referenceField f m) i)
    (fun j _ ↦ exists_norm_iteratedFDeriv_referenceField_apply_le f m i j) hg
  have hprod := mul_mem_realSobolevFunctions
    (finrank_real_complex_lt_two_mul (by exact_mod_cast hn)) hw hg
  convert add_mem href hprod using 1
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, PiLp.sub_apply]
  ring

end TauCeti.Vortex
