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
    have hd (q : (P × (ℝ × ℝ)) × V) :
        fderiv ℝ (fun z ↦ K q.1.1 z q.2) q.1.2 v =
          fderiv ℝ (fun q : (P × (ℝ × ℝ)) × V ↦ K q.1.1 q.1.2 q.2) q ((0, v), 0) := by
      have h := (hK.differentiable one_ne_zero q).hasFDerivAt.comp
        (f := fun z : ℝ × ℝ ↦ ((q.1.1, z), q.2)) q.1.2
        (((hasFDerivAt_const (𝕜 := ℝ) q.1.1 q.1.2).prodMk
          (hasFDerivAt_id q.1.2)).prodMk (hasFDerivAt_const q.2 q.1.2))
      exact congrArg (fun L ↦ L v) h.fderiv
    exact ((hK.continuous_fderiv one_ne_zero).clm_apply continuous_const).congr fun q ↦ (hd q).symm
  have hXs := ω.continuous_uncurry_hamiltonianVectorField
    (K := fun p : P × (ℝ × ℝ) ↦ Ks p.1 p.2) hKs
  have hXt := ω.continuous_uncurry_hamiltonianVectorField
    (K := fun p : P × (ℝ × ℝ) ↦ Kt p.1 p.2) hKt
  exact (((hD Kt hKt stdComplexLineReal).sub (hD Ks hKs stdComplexLineImag)).sub
    (ω.continuous_apply_comp hXs hXt)).congr fun q ↦ by
      simp [hamiltonianCurvature_def, poissonBracket_def, uncurry]

/-- If both components of a Hamiltonian one-form vanish off a closed domain set, its curvature
also vanishes off that set. No differentiability assumption is needed. -/
theorem hamiltonianCurvature_eq_zero_of_notMem (ω : SymplecticForm V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {D : Set (ℝ × ℝ)} (hD : IsClosed D)
    (hs : ∀ z ∉ D, Ks z = 0) (ht : ∀ z ∉ D, Kt z = 0)
    {z : ℝ × ℝ} (hz : z ∉ D) (x : V) : ω.hamiltonianCurvature Ks Kt z x = 0 := by
  have h : ∀ᶠ w in 𝓝 z, w ∉ D := hD.isOpen_compl.mem_nhds hz
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq
    (h.mono fun w hw ↦ hs w hw) (h.mono fun w hw ↦ ht w hw)]
  simp [hamiltonianCurvature_def]

/-- Adding a perturbation supported in a closed set inside an open region where the original
one-form vanishes adds their curvatures exactly: there are no mixed Poisson-bracket terms. -/
theorem hamiltonianCurvature_add_of_eq_zero_on (ω : SymplecticForm V)
    {Ks Kt δs δt : ℝ × ℝ → V → ℝ} {D U : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hKs : ∀ z ∈ U, Ks z = 0) (hKt : ∀ z ∈ U, Kt z = 0)
    (hδs : ∀ z ∉ D, δs z = 0) (hδt : ∀ z ∉ D, δt z = 0) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (fun w y ↦ Ks w y + δs w y) (fun w y ↦ Kt w y + δt w y) z x =
      ω.hamiltonianCurvature Ks Kt z x + ω.hamiltonianCurvature δs δt z x := by
  by_cases hz : z ∈ D
  · have hs : Ks =ᶠ[𝓝 z] 0 := eventually_of_mem (hU.mem_nhds (hDU hz)) hKs
    have ht : Kt =ᶠ[𝓝 z] 0 := eventually_of_mem (hU.mem_nhds (hDU hz)) hKt
    have hsum := ω.hamiltonianCurvature_congr_of_eventuallyEq
      (Ks := fun w y ↦ Ks w y + δs w y) (Kt := fun w y ↦ Kt w y + δt w y)
      (Ks' := δs) (Kt' := δt)
      (hs.mono fun w hw ↦ by simp [hw]) (ht.mono fun w hw ↦ by simp [hw])
    rw [hsum, ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht]
    simp [hamiltonianCurvature_def]
  · have hs : δs =ᶠ[𝓝 z] 0 := eventually_of_mem (hD.isOpen_compl.mem_nhds hz) hδs
    have ht : δt =ᶠ[𝓝 z] 0 := eventually_of_mem (hD.isOpen_compl.mem_nhds hz) hδt
    have hsum := ω.hamiltonianCurvature_congr_of_eventuallyEq
      (Ks := fun w y ↦ Ks w y + δs w y) (Kt := fun w y ↦ Kt w y + δt w y)
      (Ks' := Ks) (Kt' := Kt)
      (hs.mono fun w hw ↦ by simp [hw]) (ht.mono fun w hw ↦ by simp [hw])
    rw [hsum, ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht]
    simp [hamiltonianCurvature_def]

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
