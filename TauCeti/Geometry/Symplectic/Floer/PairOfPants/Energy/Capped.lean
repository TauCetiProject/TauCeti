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

For a solution of the Floer equation `(du - X_K)^{0,1} = 0` with tame almost complex structures
the energy is nonnegative, so `∫ R_K(u) ≤ ∫ u^* ω`
(`SmoothTwoForm.IsNondegenerate.integral_hamiltonianCurvature_cappedPerturbation_le`): a map whose
area is below its integrated curvature is not a solution. For closed `ω` and a solution extending
to the sphere in the class `A`, the bound reads `∫ R_K(u) ≤ ω(A)`.

For a symplectic vector space target the integrated curvature of `K_R`, `R ≥ 0`, is at most
`2 (B₀ + B₁ + B_∞)` for bounds `|H_q| ≤ B_q` of the end Hamiltonians
(`SymplecticForm.abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le`). So the
energy differs from the symplectic area by at most `2 (B₀ + B₁ + B_∞)`, uniformly over the family
(`SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`). This is
the energy bound, uniform in `R` for a fixed area, under which compactness of the comparison
family is to be proved.

## Main results

* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cappedPerturbation`: the energy
  identity on the capped three-pole sphere.
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

/-- **The energy bound is uniform over the comparison family.** For a symplectic vector space
target, period-one `C¹` Hamiltonians with `|H_q| ≤ B_q`, a `C¹` map `u` of the plane and `R ≥ 0`,
if the energy density and the curvature term of `u` for the datum `K_R` are integrable, then the
energy of `u` differs from its symplectic area by at most `2 (B₀ + B₁ + B_∞)`. -/
theorem abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {R : ℝ} (hR₀ : 0 ≤ R) (hu : ContDiff ℝ 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) :
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
  have h := ω.isNondegenerate_constSmooth.integral_floerEnergyDensity_cappedComparisonPerturbation
    hH hHs' R hu.contMDiff
    (hE.congr (Filter.Eventually.of_forall fun z ↦ (floerEnergyDensity_constSmooth ω _ _ u z).symm))
    (hR.congr (Filter.Eventually.of_forall fun z ↦
      (hamiltonianCurvature_constSmooth ω _ _ z (u z)).symm))
  -- The area density of the constant form is `ω(∂ₛu, ∂ₜu)`.
  have harea : ∫ z, (SmoothBundleForm.eval₂ ω.constSmooth (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineImag) : ℝ) =
        ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z ↦ by
      refine (eval₂_constSmooth_mfderiv_eq ω u z stdComplexLineReal stdComplexLineImag).trans ?_
      simp only [mvfderiv_eq_fderiv]
      -- `fromTangentSpace z` is the identity of `ℝ × ℝ`, read as its own tangent space; the
      -- coordinate vectors are typed in the model, so the composite is not rewritten by `simp`.
      rfl)
  have hbound := ω.abs_setIntegral_hamiltonianCurvature_cappedComparisonPerturbation_le hH hHs hB
    hR₀ u univ
  rw [setIntegral_univ] at hbound
  simp only [floerEnergyDensity_constSmooth, hamiltonianCurvature_constSmooth] at h
  rw [h, harea, sub_sub_cancel_left, abs_neg]
  exact hbound

end TauCeti.SymplecticForm
