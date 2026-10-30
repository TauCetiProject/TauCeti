/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Neck

/-!
# Curvature bounds when turning off Hamiltonian perturbations

For `K = K_s ds + K_t dt`, scaling both components by a domain-independent real number `r`
does not simply scale the curvature. With the convention
`R_K = ∂s K_t - ∂t K_s - {K_s, K_t}`, the exact formula is
`R_(rK) = r R_K + (r - r²) {K_s, K_t}`, proved in
`SymplecticForm.hamiltonianCurvature_const_smul` in the energy module.
Consequently, for `0 ≤ r ≤ 1`, an integrable target-uniform bound `M` on `|R_K|` and a bound
`P` on `|{K_s, K_t}|` give the uniform curvature allowance `∫ (M + P / 4)`.
This controls the curvature term in the energy identity during a homotopy from zero to `K`.
The parameter is held fixed when taking domain derivatives; a domain-dependent cutoff has
additional derivative terms and is not covered by this formula.

The final theorem combines this allowance with cylindrical neck insertion. Its bound is
independent of both `r ∈ [0, 1]` and the neck length `L ≥ 0`. The unscaled datum must already
be cylindrical near the insertion line. These are coordinate estimates on a symplectic vector
space; no global punctured moduli space or geometric comparison is constructed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian perturbations and the curvature term in the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8.

The neck estimate uses `SymplecticForm.integral_abs_hamiltonianCurvature_neckStretch_le`.
-/

public section

open Filter Function MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ}

/-- On a measurable coordinate domain, integrable bounds on curvature and the Poisson bracket
control the integrated absolute curvature throughout the scaling homotopy. -/
theorem integral_abs_hamiltonianCurvature_const_smul_le (ω : SymplecticForm V) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) {T : Set (ℝ × ℝ)} (hT : MeasurableSet T)
    {u : ℝ × ℝ → V}
    {M P : ℝ × ℝ → ℝ}
    (hM : ∀ z ∈ T, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ M z)
    (hP : ∀ z ∈ T, ∀ x, |ω.poissonBracket (Ks z) (Kt z) x| ≤ P z)
    (hMi : IntegrableOn M T) (hPi : IntegrableOn P T) :
    ∫ z in T, |ω.hamiltonianCurvature (r • Ks) (r • Kt) z (u z)| ≤
      ∫ z in T, M z + P z / 4 := by
  have hbound (z : ℝ × ℝ) (hz : z ∈ T) :
      |ω.hamiltonianCurvature (r • Ks) (r • Kt) z (u z)| ≤ M z + P z / 4 :=
    (ω.abs_hamiltonianCurvature_const_smul_le hr Ks Kt z (u z)).trans
      (add_le_add (hM z hz (u z)) (div_le_div_of_nonneg_right (hP z hz (u z)) (by norm_num)))
  by_cases hfi : IntegrableOn (fun z ↦ |ω.hamiltonianCurvature (r • Ks) (r • Kt) z (u z)|) T
  · exact setIntegral_mono_on hfi (hMi.add (hPi.div_const 4)) hT hbound
  · rw [integral_undef hfi]
    exact setIntegral_nonneg hT fun z hz ↦ (abs_nonneg _).trans (hbound z hz)

/-- The scaling allowance persists after inserting any cylindrical neck. Thus scaling to zero
and stretching the neck have one common integrated curvature bound. -/
theorem integral_abs_hamiltonianCurvature_neckStretch_const_smul_le
    (ω : SymplecticForm V) {r c L : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hL : 0 ≤ L)
    (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t))
    (u : ℝ × ℝ → V) {M P : ℝ × ℝ → ℝ} {a b : ℝ × ℝ}
    (hac : a.1 ≤ c) (hcb : c ≤ b.1)
    (hM : ∀ z ∈ Icc a b, ∀ x, |ω.hamiltonianCurvature Ks Kt z x| ≤ M z)
    (hP : ∀ z ∈ Icc a b, ∀ x, |ω.poissonBracket (Ks z) (Kt z) x| ≤ P z)
    (hMi : IntegrableOn M (Icc a b)) (hPi : IntegrableOn P (Icc a b)) :
    ∫ z in Icc a (b.1 + L, b.2),
        |ω.hamiltonianCurvature (Floer.neckStretch c L (r • Ks))
          (Floer.neckStretch c L (r • Kt)) z (u z)| ≤
      ∫ z in Icc a b, M z + P z / 4 := by
  have hs : ∀ᶠ s in 𝓝 c, ∀ t, (r • Ks) (s, t) = 0 := by
    filter_upwards [hKs] with s hs t
    simp [hs t]
  have ht : ∀ᶠ s in 𝓝 c, ∀ t, (r • Kt) (s, t) = (r • Kt) (c, t) := by
    filter_upwards [hKt] with s ht t
    simp only [Pi.smul_apply, ht t]
  refine ω.integral_abs_hamiltonianCurvature_neckStretch_le hL hs ht u hac hcb
    (fun z hz x ↦ ?_) (hMi.add (hPi.div_const 4))
  exact (ω.abs_hamiltonianCurvature_const_smul_le hr Ks Kt z x).trans
    (add_le_add (hM z hz x) (div_le_div_of_nonneg_right (hP z hz x) (by norm_num)))

end TauCeti.SymplecticForm
