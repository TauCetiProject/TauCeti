/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.NonDiscrete.Basic
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Transvection
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
import TauCeti.NumberTheory.Padics.Factorial

/-!
# Rational Spin points accumulate in the finite adeles

Factorial powers of a canonical rational Spin transvection lift converge to the identity in the
finite adelic Spin group. At each prime this follows from the explicit lift `1 + ι w * ι u` and
continuity in the parameter. All powers are integral on the same cofinite set of primes, so
coordinatewise convergence takes place in one principal restricted-product stage.

For a nondegenerate isotropic rational quadratic space of dimension at least three, these
powers are nonidentity: their projections are the nonidentity Eichler transvections. Thus the
rational Spin diagonal is not discrete in the finite adeles. The distinction from the full
adeles holds for Spin as well as for the orthogonal and special orthogonal groups.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen* (1952).
-/

public section

namespace TauCeti.QuadraticMap.OrthogonalCompactOpens

open _root_.QuadraticMap _root_.CliffordAlgebra TauCeti Filter Topology
open scoped TensorProduct

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) {u w : V}

/-- Factorial powers of a canonical rational Spin transvection lift converge to the identity
in the finite adelic Spin group, for every compatible compact-open reference family. -/
theorem tendsto_finiteAdelicSpinDiagonal_spinTransvection_factorial
    (hQ : Q.Nondegenerate) (hu : Q u = 0) (huw : polar Q u w = 0) :
    Tendsto (fun n : ℕ ↦ U.finiteAdelicSpinDiagonal
      (spinTransvection hQ hu huw ^ n.factorial)) atTop (𝓝 1) := by
  let g := spinTransvection hQ hu huw
  have hlocal (p : Nat.Primes) : Tendsto (fun n : ℕ ↦
      spinGroupBaseChange (A := ℚ_[p]) Q (g ^ n.factorial)) atTop (𝓝 1) := by
    -- Use the invertibility witness fixed by the scalar-extension theorem.
    let : Invertible (2 : ℚ_[p]) :=
      (Invertible.map (algebraMap ℚ ℚ_[p]) 2).copy 2 (map_ofNat _ _).symm
    let : TopologicalSpace (ℚ_[p] ⊗[ℚ] V) := moduleTopology ℚ_[p] _
    let up : ℚ_[p] ⊗[ℚ] V := 1 ⊗ₜ[ℚ] u
    let wp : ℚ_[p] ⊗[ℚ] V := 1 ⊗ₜ[ℚ] w
    have hup : (Q.baseChange ℚ_[p]) up = 0 := by
      simp [up, QuadraticForm.baseChange_tmul, hu]
    have huwp : polar (Q.baseChange ℚ_[p]) up wp = 0 := by
      simp [up, wp, QuadraticForm.polar_baseChange_tmul, huw]
    let E (t : ℚ_[p]) := spinTransvection (QuadraticForm.Nondegenerate.baseChange hQ)
      (w := t • wp) hup (by simp [polar_smul_right, huwp])
    have hE : Continuous E :=
      continuous_spinTransvection (fun _ : ℚ_[p] ↦ up) (fun t ↦ t • wp)
        (QuadraticForm.Nondegenerate.baseChange hQ) (fun _ ↦ hup)
        (fun t ↦ by simp [polar_smul_right, huwp]) continuous_const
        ((continuous_id : Continuous (fun t : ℚ_[p] ↦ t)).smul
          (continuous_const : Continuous (fun _ : ℚ_[p] ↦ wp)))
    have hEn (n : ℕ) : E (n : ℚ_[p]) =
        spinGroupBaseChange (A := ℚ_[p]) Q (g ^ n) := by
      rw [map_pow]
      dsimp only [g]
      rw [spinGroupBaseChange_spinTransvection, spinTransvection_pow]
      simp only [E, up, wp, Nat.cast_smul_eq_nsmul]
    have hzero : E 0 = 1 := by
      apply Subtype.ext
      simp [E]
    have ht := hE.continuousAt.tendsto.comp (tendsto_padic_natCast_factorial (p : ℕ))
    rw [hzero] at ht
    exact ht.congr fun n ↦ hEn n.factorial
  apply (tendsto_restrictedProduct_iff_of_eventually_mem
    (le_principal_iff.mpr (U.eventually_spin g))
    (Eventually.of_forall fun n p hp ↦ by
      rw [finiteAdelicSpinDiagonal_apply, map_pow]
      exact (U.spin p).pow_mem hp _)
    (fun p _ ↦ (U.spin p).one_mem)).mpr
  simpa only [finiteAdelicSpinDiagonal_apply, RestrictedProduct.one_apply, g] using hlocal

/-- A nontrivial rational Eichler root subgroup prevents the rational Spin diagonal from being
discrete in the finite adeles. -/
theorem not_discreteTopology_range_finiteAdelicSpinDiagonal_of_transvection
    (hQ : Q.Nondegenerate) (hu : Q u = 0) (huw : polar Q u w = 0)
    (hu₀ : u ≠ 0) (hw : w ∉ ℚ ∙ u) :
    ¬ DiscreteTopology U.finiteAdelicSpinDiagonal.range := by
  let g := spinTransvection hQ hu huw
  have hne (n : ℕ) : g ^ n.factorial ≠ 1 := by
    intro hn
    dsimp only [g] at hn
    rw [spinTransvection_pow, spinTransvection_eq_one_iff hQ hu _ hu₀] at hn
    rw [← Nat.cast_smul_eq_nsmul ℚ, (ℚ ∙ u).smul_mem_iff
      (by exact_mod_cast n.factorial_ne_zero)] at hn
    exact hw hn
  exact U.finiteAdelicSpinDiagonal.not_discreteTopology_range_of_tendsto_one
    (U.tendsto_finiteAdelicSpinDiagonal_spinTransvection_factorial hQ hu huw)
    (Eventually.of_forall fun n ↦
      (map_ne_one_iff _ U.finiteAdelicSpinDiagonal_injective).mpr (hne n))

/-- For a nondegenerate isotropic rational quadratic space of dimension at least three, the
rational Spin diagonal is not discrete in the finite adeles. -/
theorem not_discreteTopology_range_finiteAdelicSpinDiagonal
    (hQ : Q.Nondegenerate) (hdim : 3 ≤ Module.finrank ℚ V)
    (hiso : ∃ u : V, u ≠ 0 ∧ Q u = 0) :
    ¬ DiscreteTopology U.finiteAdelicSpinDiagonal.range := by
  obtain ⟨u, hu₀, hu⟩ := hiso
  obtain ⟨w, huw, hw⟩ :=
    Q.exists_polar_eq_zero_not_mem_span_of_finrank_ge_three (hQ.polarBilin_ne_zero hu₀) hdim
  exact U.not_discreteTopology_range_finiteAdelicSpinDiagonal_of_transvection hQ hu huw hu₀ hw

end

end TauCeti.QuadraticMap.OrthogonalCompactOpens
