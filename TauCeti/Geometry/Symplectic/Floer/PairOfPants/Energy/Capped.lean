/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped

/-!
# The energy identity on the capped three-pole sphere

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes. The result is a sphere
with three poles `0`, `1` and `∞`, carrying the Hamiltonian perturbation
`K = TauCeti.Floer.cappedPerturbation a L H`, and the one-parameter comparison family
`K_R = TauCeti.Floer.cappedComparisonPerturbation H R`. The datum vanishes near the three poles
(`TauCeti.Floer.cappedPerturbation_eq_zero_of_notMem_truncation`), so for a map `u` of the sphere,
written as a map of the plane chart `ℂ ≅ ℝ × ℝ` of the complement of `∞`, the pulled-back one-form
`K(u)` has compact support in the plane. Its exterior derivative therefore integrates to zero, and
the Floer energy of `u` for `K` is

`E(u) = ∫ u^* ω - ∫ R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation`), for a map into
a manifold with a nondegenerate two-form. Here `∫ u^* ω` is the symplectic area of the map `u`,
and `R_K` is the curvature of the perturbation. When `ω` is closed and `u` extends to the sphere,
the area is the topological energy `ω(A)` of the class `A` of the extension; the results below
assume neither.
Unlike the energy identity on the pair of pants
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action`), no end actions appear: the domain is
closed. The identity holds along the whole comparison family
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedComparisonPerturbation`); at
`R = 0` the datum vanishes and the energy density is the symplectic area density, as for the
unperturbed problem on the three-pole sphere
(`SmoothTwoForm.floerEnergyDensity_cappedComparisonPerturbation_zero`).

The identity is local: the datum vanishes outside the compact truncation `S_{L + 3}` of the pair
of pants, so it suffices that `u` be `C¹` near `S_{L + 3}`, for instance a map defined on the pair
of pants itself, and the energy over every measurable region `D ⊇ S_{L + 3}` is
`∫_D u^* ω - ∫_D R_K(u)`
(`SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_cappedPerturbation`, and
`SymplecticForm.setIntegral_floerEnergyDensity_cappedPerturbation` for a vector space target).

For a solution of the Floer equation `(du - X_K)^{0,1} = 0` with tame almost complex structures
the energy is nonnegative, so `∫ R_K(u) ≤ ∫ u^* ω`
(`SmoothTwoForm.IsNondegenerate.integral_hamiltonianCurvature_cappedPerturbation_le`): a map whose
area is below its integrated curvature is not a solution. For closed `ω` and a solution extending
to the sphere in the class `A`, the bound reads `∫ R_K(u) ≤ ω(A)`.

For a symplectic vector space target the integrated curvature of `K_R`, `R ≥ 0`, is at most
`2 (B₀ + B₁ + B_∞)` for bounds `|H_q| ≤ B_q` of the end Hamiltonians
(`SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le` for the
constant form `SymplecticForm.constSmooth`). So the energy differs from the symplectic area by at
most `2 (B₀ + B₁ + B_∞)`, uniformly over the family
(`SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`). This is
the energy bound, uniform in `R` for a fixed area, under which compactness of the comparison
family is to be proved.

## Main results

* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation`: the energy
  identity on the capped three-pole sphere.
* `SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_cappedPerturbation`,
  `SymplecticForm.setIntegral_floerEnergyDensity_cappedPerturbation`: the energy identity over
  any region containing the truncation, for maps that are `C¹` near it.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedComparisonPerturbation`: the
  energy identity along the comparison family.
* `SmoothTwoForm.IsNondegenerate.integral_hamiltonianCurvature_cappedPerturbation_le`: the area of
  a solution bounds its integrated curvature.
* `SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`: the energy
  bound uniform over the comparison family, for a vector space target.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations, and Section 12.1, on the PSS isomorphism.
-/

public section

open Set Function MeasureTheory
open scoped Manifold
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

/-- **The energy identity on the capped three-pole sphere.** Let `K` be the capped perturbation
with scaling factor `a` and neck length `L`, built from period-one `C¹` Hamiltonians `H_q`, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`.
For a `C¹` map `u` of the plane into a manifold with a nondegenerate two-form, whose energy density
and curvature term `R_K(u)` are integrable, the energy of `u` is its symplectic area minus the
integral of `R_K(u)`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (a L : ℝ)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
  hω.integral_floerEnergyDensity_of_hasCompactSupport hu
    (contMDiff_cappedPerturbation_apply hH hHs a L 1)
    (contMDiff_cappedPerturbation_apply hH hHs a L Complex.I)
    (hasCompactSupport_cappedPerturbation_apply a L u 1)
    (hasCompactSupport_cappedPerturbation_apply a L u Complex.I) hE hR

/-- **The energy identity on the capped three-pole sphere, localized near the truncation.** Let
`K` be the capped perturbation with scaling factor `a` and neck length `L`, built from period-one
`C¹` Hamiltonians `H_q` on a finite-dimensional manifold with a nondegenerate two-form, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`.
Let `u` be `C¹` over an open neighbourhood `U` of the truncation `S_{L + 3}`. Then for every
measurable set `D ⊇ S_{L + 3}` over which the energy density and the curvature `R_K(u)` are
integrable,

`∫_D E = ∫_D u^* ω - ∫_D R_K(u)`. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_cappedPerturbation [FiniteDimensional ℝ E]
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
  hω.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero hU hu
    (contMDiff_cappedPerturbation_apply hH hHs a L 1).contMDiffOn
    (contMDiff_cappedPerturbation_apply hH hHs a L Complex.I).contMDiffOn
    (isCompact_preimage_truncation _) hTU
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz 1)
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz Complex.I)
    hD hTD hE hR

/-- **The energy identity along the comparison family.** For every `R`, the energy of a map of the
plane for the datum `K_R` of the comparison family is its symplectic area minus the integral of
`R_{K_R}(u)`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cappedComparisonPerturbation
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (R : ℝ)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z) := by
  simp only [cappedComparisonPerturbation_def] at hE hR ⊢
  exact hω.integral_floerEnergyDensity_cappedPerturbation hH hHs _ _ hu hE hR

/-- **The unperturbed end of the comparison family.** For `R = 0` the datum vanishes, and the
energy density of any map of the plane is its symplectic area density. -/
theorem floerEnergyDensity_cappedComparisonPerturbation_zero (ω : SmoothTwoForm I M)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H 0 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H 0 (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
  simp

/-- **The area of a solution bounds its integrated curvature.** If `u` solves the Floer equation
`(du - X_K)^{0,1} = 0` for the capped perturbation, with almost complex structures `J z` tamed by
the two-form, then the integral of `R_K(u)` is at most the symplectic area of `u`. -/
theorem IsNondegenerate.integral_hamiltonianCurvature_cappedPerturbation_le
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (a L : ℝ)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) ≤
      ∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
  have h := hω.integral_floerEnergyDensity_cappedPerturbation hH hHs a L hu hE hR
  have hE₀ := integral_nonneg (μ := volume) (f := ω.floerEnergyDensity
    (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
    fun z ↦ floerEnergyDensity_nonneg hω (hJ z) (hfloer z)
  linarith

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **The energy identity on the capped three-pole sphere, localized near the truncation, for a
vector space target.** Let `K` be the capped perturbation with scaling factor `a` and neck length
`L`, built from period-one `C¹` Hamiltonians `H_q` on a symplectic vector space. Let `u` be `C¹`
over an open neighbourhood `U` of the truncation `S_{L + 3}`. Then for every measurable set
`D ⊇ S_{L + 3}` over which the energy density is integrable,

`∫_D E = ∫_D u^* ω - ∫_D R_K(u)`. -/
theorem setIntegral_floerEnergyDensity_cappedPerturbation (ω : SymplecticForm V)
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
  ω.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero hU hu
    (contDiff_cappedPerturbation_apply hH hHs a L 1).contDiffOn
    (contDiff_cappedPerturbation_apply hH hHs a L Complex.I).contDiffOn
    (isCompact_preimage_truncation _) hTU
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz 1)
    (fun _ hz ↦ cappedPerturbation_apply_eq_zero_of_notMem_preimage_truncation hz Complex.I)
    hD hTD hE

/-- **The energy identity along the comparison family, for a vector space target.** For every
member `K_R` of the comparison family, built from period-one `C¹` Hamiltonians on a symplectic
vector space, and every `C¹` map `u` of finite energy, the energy over the whole plane is
`∫ u^* ω - ∫ R_{K_R}(u)`. The curvature term is integrable automatically. -/
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
    ω.setIntegral_floerEnergyDensity_cappedPerturbation hH hHs _ _ isOpen_univ (subset_univ _)
      hu.contDiffOn MeasurableSet.univ (subset_univ _) hE.integrableOn

/-- **The energy bound is uniform over the comparison family.** For a symplectic vector space
target, period-one `C¹` Hamiltonians with `|H_q| ≤ B_q`, a `C¹` map `u` of the plane and `R ≥ 0`,
if the energy density of `u` for the datum `K_R` is integrable, then the energy of `u` differs
from its symplectic area by at most `2 (B₀ + B₁ + B_∞)`. -/
theorem abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {R : ℝ} (hR₀ : 0 ≤ R) (hu : ContDiff ℝ 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      u)) :
    |(∫ z, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)| ≤
        2 * ∑ q, B q := by
  have hHs' (q : Puncture) : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) := by
    have h := (hHs q).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hbound :=
    ω.constSmooth.abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le hH hHs' hB
      hR₀ u univ
  simp only [Measure.restrict_univ, hamiltonianCurvature_constSmooth] at hbound
  rw [ω.integral_floerEnergyDensity_cappedComparisonPerturbation hH hHs R hu hE,
    sub_sub_cancel_left, abs_neg]
  exact hbound

end TauCeti.SymplecticForm
