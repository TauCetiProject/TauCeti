/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped

/-!
# The energy identity on the capped pair of pants

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants by PSS planes. The result is a sphere with three poles, which in the coordinate
`w` of `ℂ` are `0`, `1` and `∞`, and the Hamiltonian perturbation
`K = TauCeti.Floer.cappedPerturbation a L H` on it vanishes outside the compact truncation
`S_{L + 3}` of the pair of pants (`TauCeti.Floer.cappedPerturbation_eq_zero_of_notMem_truncation`).
So the Floer energy of a map `u` has no boundary term: the energy identity reads

`E(u) = ∫ u^* ω - ∫ R_K(u)`,

where `R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` is the curvature of `K` in the global coordinate
`z = s + i t` of `ℂ`. This holds over every region containing `S_{L + 3}`, in particular over the
whole plane, which is the three-pole sphere minus the pole `∞`. The map only needs to be `C¹` near
`S_{L + 3}`; for instance a map defined on the pair of pants itself is allowed.

Along the comparison family `K_R = TauCeti.Floer.cappedComparisonPerturbation H R`, `R ≥ 0`, the
truncation grows without bound, but the energy identity holds over the whole plane for every `R`.
For a symplectic vector space target, combined with the uniform curvature bound
`TauCeti.SymplecticForm.abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le`, the
energy then differs from the symplectic area by at most `2 (B₀ + B₁ + B_∞)` for `|H_q| ≤ B_q`,
uniformly over the family. This is the kind of energy bound, independent of the family parameter,
on which compactness of the moduli spaces of the comparison family rests.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation`: the
  energy identity for a manifold target with a nondegenerate two-form.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_cappedPerturbation`: the energy identity for
  a symplectic vector space target.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_cappedComparisonPerturbation`: the energy
  identity over the whole plane for every member of the comparison family.
* `TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`:
  the energy bound, uniform over the comparison family.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations, and Section 12.1, on the PSS isomorphism.
-/

public noncomputable section

open Set Function MeasureTheory Manifold
open TauCeti.ThricePuncturedSphere

namespace TauCeti.Floer

variable {M : Type*} {H : Puncture → ℝ → M → ℝ}

/-- Outside the truncation `S_{L + 3}`, in real coordinates, the capped perturbation vanishes on
every tangent vector. -/
private theorem cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation {a L : ℝ} {z : ℝ × ℝ}
    (hz : z ∉ Complex.equivRealProdCLM.symm ⁻¹' truncation (L + 3)) (v : ℂ) :
    (fun x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x v) = 0 :=
  funext fun x ↦ by simp [cappedPerturbation_eq_zero_of_notMem_truncation hz x]

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- **The energy identity on the capped pair of pants, for a manifold target.** Let `K` be the
capped perturbation with scaling factor `a` and neck length `L`, built from period-one `C¹`
Hamiltonians `H_q` on a finite-dimensional manifold with a nondegenerate two-form, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Let `u` be
`C¹` over an open neighbourhood `U` of the truncation `S_{L + 3}`. Then for every measurable set
`D ⊇ S_{L + 3}` over which the energy density and the curvature `R_K(u)` are integrable,

`∫_D E = ∫_D u^* ω - ∫_D R_K(u)`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (a L : ℝ)
    {U D : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hTU : Complex.equivRealProdCLM.symm ⁻¹' truncation (L + 3) ⊆ U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hD : MeasurableSet D)
    (hTD : Complex.equivRealProdCLM.symm ⁻¹' truncation (L + 3) ⊆ D)
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u) D)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) D) :
    ∫ z in D, ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in D, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∫ z in D, ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
  hω.integral_floerEnergyDensity_of_forall_notMem_eq_zero hU hu
    (contMDiff_uncurry_cappedPerturbation_apply hH hHs a L 1).contMDiffOn
    (contMDiff_uncurry_cappedPerturbation_apply hH hHs a L Complex.I).contMDiffOn
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation _)) hTU
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz 1)
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz Complex.I)
    hD hTD hE hR

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **The energy identity on the capped pair of pants.** Let `K` be the capped perturbation with
scaling factor `a` and neck length `L`, built from period-one `C¹` Hamiltonians `H_q` on a
symplectic vector space, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global
coordinate `z = s + i t` of `ℂ`. Let `u` be `C¹` over an open neighbourhood `U` of the truncation
`S_{L + 3}`. Then for every measurable set `D ⊇ S_{L + 3}` over which the energy density is
integrable,

`∫_D E = ∫_D u^* ω - ∫_D R_K(u)`. -/
theorem integral_floerEnergyDensity_cappedPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (a L : ℝ)
    {U D : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hTU : Complex.equivRealProdCLM.symm ⁻¹' truncation (L + 3) ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (hD : MeasurableSet D)
    (hTD : Complex.equivRealProdCLM.symm ⁻¹' truncation (L + 3) ⊆ D)
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u) D) :
    ∫ z in D, ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in D, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        ∫ z in D, ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
  ω.integral_floerEnergyDensity_of_forall_notMem_eq_zero hU hu
    (contDiff_uncurry_cappedPerturbation_apply hH hHs a L 1).contDiffOn
    (contDiff_uncurry_cappedPerturbation_apply hH hHs a L Complex.I).contDiffOn
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation _)) hTU
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz 1)
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz Complex.I)
    hD hTD hE

/-- **The energy identity along the comparison family.** For every member `K_R` of the comparison
family, built from period-one `C¹` Hamiltonians on a symplectic vector space, and every `C¹` map
`u` of finite energy, the energy over the whole plane is `∫ u^* ω - ∫ R_{K_R}(u)`. -/
theorem integral_floerEnergyDensity_cappedComparisonPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (R : ℝ)
    (hu : ContDiff ℝ 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
        Complex.I) u)) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  rw [cappedComparisonPerturbation_def] at hE ⊢
  simpa only [Measure.restrict_univ] using
    ω.integral_floerEnergyDensity_cappedPerturbation hH hHs _ _ isOpen_univ (subset_univ _)
      hu.contDiffOn MeasurableSet.univ (subset_univ _) hE.integrableOn

/-- **The energy bound is uniform over the comparison family.** For period-one `C¹` Hamiltonians
with `|H_q| ≤ B_q` on a symplectic vector space, every `R ≥ 0` and every `C¹` map `u` of finite
energy, the energy of `u` for `K_R` over the whole plane differs from its symplectic area by at
most `2 (B₀ + B₁ + B_∞)`. -/
theorem abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {R : ℝ} (hR : 0 ≤ R) (hu : ContDiff ℝ 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
        Complex.I) u)) :
    |(∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z) -
      ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)| ≤
      2 * ∑ q, B q := by
  rw [ω.integral_floerEnergyDensity_cappedComparisonPerturbation hH hHs R hu hE,
    sub_sub_cancel_left, abs_neg]
  simpa only [Measure.restrict_univ] using
    ω.abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le hH hHs hB hR u univ

end TauCeti.SymplecticForm
