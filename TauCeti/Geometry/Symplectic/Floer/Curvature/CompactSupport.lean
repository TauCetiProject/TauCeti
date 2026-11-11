/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy

/-!
# Uniform curvature bounds for compactly supported perturbation families

A jointly `C¹` family of Hamiltonian one-forms with a common compact domain support has a
uniform integrated curvature bound on compact parameter and target windows. The bound holds
along arbitrary maps into the target window, without a measurability assumption on those maps.
It controls localized perturbations of Floer data without multiplying a bound by the length
of a cylindrical end.

The curvature includes both domain derivatives and the Poisson bracket. Joint `C¹` regularity
controls all three terms; a bound on the Hamiltonians alone would not suffice.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  for the curvature of Hamiltonian perturbations and its role in energy estimates.
-/

public section

open Filter Function MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The curvature of a jointly `C¹` Hamiltonian family is continuous jointly in the external
parameter, domain point and target point. -/
theorem continuous_hamiltonianCurvature_family (ω : SymplecticForm V)
    {Ks Kt : P → ℝ × ℝ → V → ℝ}
    (hKs : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Kt q.1.1 q.1.2 q.2)) :
    Continuous (fun q : (P × (ℝ × ℝ)) × V ↦
      ω.hamiltonianCurvature (Ks q.1.1) (Kt q.1.1) q.1.2 q.2) := by
  have hD (K : P → ℝ × ℝ → V → ℝ)
      (hK : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ K q.1.1 q.1.2 q.2))
      (v : ℝ × ℝ) :
      Continuous (fun q : (P × (ℝ × ℝ)) × V ↦
        fderiv ℝ (fun z ↦ K q.1.1 z q.2) q.1.2 v) := by
    have hK' : ContDiff ℝ 1 (uncurry fun (q : (P × (ℝ × ℝ)) × V) z ↦
        K q.1.1 z q.2) :=
      hK.comp ((contDiff_fst.fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
    exact (Continuous.fderiv_one hK' continuous_fst.snd).clm_apply continuous_const
  have hXs := ω.continuous_uncurry_hamiltonianVectorField
    (K := fun p : P × (ℝ × ℝ) ↦ Ks p.1 p.2) hKs
  have hXt := ω.continuous_uncurry_hamiltonianVectorField
    (K := fun p : P × (ℝ × ℝ) ↦ Kt p.1 p.2) hKt
  exact (((hD Kt hKt stdComplexLineReal).sub (hD Ks hKs stdComplexLineImag)).sub
    (ω.continuous_apply_comp hXs hXt)).congr fun q ↦ by
      simp [hamiltonianCurvature_def, poissonBracket_def, uncurry]

/-- A jointly `C¹` family supported in a common compact domain set has a finite integrated
curvature bound, uniform over compact parameter and target windows and over all maps into the
target window. In particular the bound is independent of any truncation of the domain. -/
theorem exists_lintegral_enorm_hamiltonianCurvature_le_of_isCompact
    (ω : SymplecticForm V) {Ks Kt : P → ℝ × ℝ → V → ℝ}
    (hKs : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Ks q.1.1 q.1.2 q.2))
    (hKt : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ Kt q.1.1 q.1.2 q.2))
    {A : Set P} {D : Set (ℝ × ℝ)} {Q : Set V}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q)
    (hs : ∀ p ∈ A, ∀ z ∉ D, Ks p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, Kt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → V, (∀ z ∈ D, u z ∈ Q) →
      ∫⁻ z, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB⟩ := ((hA.prod hD).prod hQ).exists_bound_of_continuousOn
    (ω.continuous_hamiltonianCurvature_family hKs hKt).continuousOn
  refine ⟨max B 0 * volume.real D, mul_nonneg (le_max_right _ _) (measureReal_nonneg),
    fun p hp u hu ↦ ?_⟩
  calc
    ∫⁻ z, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ
      = ∫⁻ z in D, ‖ω.hamiltonianCurvature (Ks p) (Kt p) z (u z)‖ₑ := by
        symm
        apply setLIntegral_eq_of_support_subset
        intro z hz
        by_contra hzD
        have h0 := ω.hamiltonianCurvature_eq_zero_of_notMem hD.isClosed
          (hs p hp) (ht p hp) hzD (u z)
        simp [h0] at hz
    _ ≤ ∫⁻ _ in D, ENNReal.ofReal (max B 0) := by
        apply setLIntegral_mono' hD.measurableSet
        intro z hz
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((hB ((p, z), u z) ⟨⟨hp, hz⟩, hu z hz⟩).trans
          (le_max_left _ _))
    _ = ENNReal.ofReal (max B 0 * volume.real D) := by
        rw [setLIntegral_const, ENNReal.ofReal_mul (le_max_right _ _),
          ofReal_measureReal hD.measure_lt_top.ne]

end TauCeti.SymplecticForm
