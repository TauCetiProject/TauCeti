/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Compression

/-!
# The pair-of-pants energy identity for maps defined near a truncation

The energy identity of the pair-of-pants perturbation on the truncation `S_R` of
`S = ℂ ∖ {0, 1}`, for a manifold target,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`, is
stated for maps `u` which are `C¹` on all of `S`. Every term of the identity only depends on `u`
near `S_R`. This file proves the identity, and the integrability of the curvature along `u` over
`S_R`, for maps which are `C¹` (respectively continuous) on some open neighbourhood `U` of `S_R`
only, in the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_subset`;
* `integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation`.

Such maps arise when the pair of pants is a piece of a larger domain: for instance on a plumbed
four-punctured sphere, a map is defined on the receiving pair of pants only off a further puncture
far out on one of its ends.

The neighbourhood `U` contains some truncation `S_{R + ε}` with `ε > 0`
(`TauCeti.ThricePuncturedSphere.exists_pos_truncation_add_subset`). The compression
`TauCeti.ThricePuncturedSphere.truncationCompression R ε` is a smooth map of `S` into `S_{R + ε}`
which is the identity near `S_R`. So `u` composed with the compression is `C¹` on all of `S` and
agrees with `u` near `S_R`, and the identity for it is the identity for `u`. The energy density
at a point only depends on the germ of the map there
(`SmoothTwoForm.floerEnergyDensity_congr_of_eventuallyEq`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
open scoped Topology Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ} {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} {R : ℝ}

/-- An open neighbourhood `U` of the truncation `S_R`, `R ≥ 0`, in real coordinates, receives a
`C¹` map of `S` which is the identity near `S_R`: the compression of `S` into a truncation
`S_{R + ε} ⊆ U`. -/
private theorem exists_compression (hR : 0 ≤ R) (hU : IsOpen U)
    (hTU : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ U) :
    ∃ c : ℝ × ℝ → ℝ × ℝ, ContDiffOn ℝ 1 c thricePuncturedSphereReal ∧
      MapsTo c thricePuncturedSphereReal U ∧
      ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, c =ᶠ[𝓝 z] id := by
  obtain ⟨ε, hε, hεU⟩ := exists_pos_truncation_add_subset
    (hU.preimage Complex.equivRealProdCLM.continuous) fun w hw ↦
      hTU (by rwa [mem_preimage, ContinuousLinearEquiv.symm_apply_apply])
  refine ⟨fun z ↦ Complex.equivRealProdCLM
    (truncationCompression R ε (Complex.equivRealProdCLM.symm z)), ?_, fun z hz ↦
      hεU (truncationCompression_mem_truncation hR hε hz), fun z hz ↦ ?_⟩
  · exact Complex.equivRealProdCLM.contDiff.comp_contDiffOn
      ((contDiffOn_truncationCompression (n := 1) hR hε).comp
        Complex.equivRealProdCLM.symm.contDiff.contDiffOn fun _ hz ↦ hz)
  · filter_upwards [(Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
      (truncationCompression_eventuallyEq hε hz)] with z' hz'
    rw [hz', id, ContinuousLinearEquiv.apply_symm_apply, id]

/-- **The curvature is integrable over a truncation, along a map continuous near it.** Along a map
`u` which is continuous on an open neighbourhood `U` of the truncation `S_R`, `R ≥ 0`, the
curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians on a manifold is
integrable over `S_R`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (hR : 0 ≤ R)
    (hU : IsOpen U) (hTU : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ U)
    (hu : ContinuousOn u U) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  obtain ⟨c, hc, hcU, hcid⟩ := exists_compression hR hU hTU
  refine ((integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs
    (hu.comp hc.continuousOn hcU)).mono_set fun z hz ↦ ?_).congr_fun (fun z hz ↦ ?_)
      (measurableSet_preimage_truncation R)
  · exact ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  · simp only [comp_apply, (hcid z hz).eq_of_nhds, id]

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- **The energy identity on the truncated pair of pants, for maps defined near the
truncation.** Let `K` be the pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a
finite-dimensional manifold with a nondegenerate two-form, and let `u` be `C¹` on an open
neighbourhood `U` of the truncation `S_R`, `R ≥ 1`. Then, as for maps which are `C¹` on all of `S`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`),

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0` and `1`, `-` on the output end `∞`, and the cutoff
`β = smoothTransition` of the perturbation. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_subset
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (hR : 1 ≤ R)
    (hU : IsOpen U) (hTU : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  obtain ⟨c, hc, hcU, hcid⟩ := exists_compression (by linarith) hU hTU
  have hT := measurableSet_preimage_truncation R
  -- Composed with the compression, `u` is `C¹` on `S` and agrees with `u` near `S_R`.
  have hv : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, u ∘ c =ᶠ[𝓝 z] u :=
    fun z hz ↦ (hcid z hz).fun_comp u
  have key := hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs
    (hu.comp hc.contMDiffOn hcU) hR
  have hE : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (u ∘ c) z = ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
    setIntegral_congr_fun hT fun z hz ↦ ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (hv z hz)
  have hA : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      (SmoothBundleForm.eval₂ ω ((u ∘ c) z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ c) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ c) z stdComplexLineImag) : ℝ) =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) :=
    setIntegral_congr_fun hT fun z hz ↦ by
      rw [← floerEnergyDensity_zero, ← floerEnergyDensity_zero,
        ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (hv z hz)]
  have hRK : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z ((u ∘ c) z) = ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) :=
    setIntegral_congr_fun hT fun z hz ↦ by rw [(hv z hz).eq_of_nhds]
  -- The boundary circles `±s = R` lie in `S_R`.
  have hB (q : Puncture) : ∫ t in (0 : ℝ)..1, H q t ((u ∘ c) (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) =
      ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) :=
    intervalIntegral.integral_congr fun t _ ↦ by
      have hR₀ : (0 : ℝ) < R := by linarith
      have hmem : Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)) ∈
          Complex.equivRealProdCLM.symm ⁻¹' truncation R := by
        rw [mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
        exact cylindricalEndLift_mem_truncation q hR₀ t
      rw [(hv _ hmem).eq_of_nhds]
  simpa only [hE, hA, hRK, hB] using key

end TauCeti.SmoothTwoForm
