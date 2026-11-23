/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.MovingEnds
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Topology.Separation.Basic
import TauCeti.Topology.Instances.Real.Periodic

/-!
# Normalizing the Hamiltonians of a sphere with moving input ends

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H(t, x)` and `H(t, x) + k(t)` generate the same flow, have the same one-periodic orbits and give
the same Floer equation. This file shows how the energy identity of a sphere with moving input
ends,

`∫ E = ∫ u^*ω + (∑ i, ∫₀¹ H_i(t, x_i(t)) dt - ∫₀¹ Hout(t, xout(t)) dt) - ∫ R_K(u)`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation`),
absorbs a change of normalization of the input Hamiltonians `H i` and of the output Hamiltonian
`Hout`, for a manifold target with a two-form `ω`, such as a closed symplectic manifold. The
spheres with moving input ends carry the family of four-punctured spheres that compares the two
compositions of the pair-of-pants product, so this is the normalization bookkeeping of that
family's energy identity.

The datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout` is additive in the Hamiltonians,
so normalizing `H i` by `k i` and `Hout` by `kout` adds to it the datum `κ` of the
target-independent Hamiltonians `k i` and `kout`, which has no Hamiltonian vector field
(`TauCeti.Floer.puncturedSpherePerturbation_add_const`). Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density are
  unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_puncturedSpherePerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_puncturedSpherePerturbation_add_const`);
* off the centers of the input ends, the curvature changes by the curvature of `κ`, which does not
  depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_puncturedSpherePerturbation_add_const`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_puncturedSpherePerturbation_const_target`);
* for nonzero scales and pairwise disjoint end discs inside the disc of radius `2 exp(2π)`, the
  hypotheses of the moving-ends energy identity, and period-one `C¹` functions `k i` and `kout`,
  the curvature of `κ` integrates over the sphere minus its punctures to
  `∑ i, ∫₀¹ k i - ∫₀¹ kout`
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_const`).

So, under the same hypotheses on the input ends, for period-one `C¹` Hamiltonians `H i`, `Hout`
and normalizations `k i`, `kout`, along every map whose curvature for `H` and `Hout` is
integrable, the integrated curvature changes by `∑ i, ∫₀¹ k i - ∫₀¹ kout`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_add_const`),
which is exactly the change of the Hamiltonian terms at the asymptotic loops. The two changes
cancel in the energy identity, as they must, since the energy itself is unchanged.

The curvature of `κ` is the exterior derivative `∂_s κ_t - ∂_t κ_s` of a one-form on the domain,
the same for every target. Its integral is computed once, on `ℂ` with its standard symplectic
form, by the energy identity along the constant map `0`, whose energy and area vanish.

This file adapts the normalization bookkeeping of the pair of pants,
`TauCeti/Geometry/Symplectic/Floer/PairOfPants/Normalization/Basic.lean`, with the same structure
and proof method, to the `ι`-indexed datum `TauCeti.Floer.puncturedSpherePerturbation`; the pair
of pants is its case of two input ends
(`TauCeti.Floer.puncturedSpherePerturbation_eq_pairOfPantsPerturbation`), and the integrated
curvature statements of that file are derived from the ones here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold Topology

namespace TauCeti

namespace Floer

variable {M ι : Type*} [Fintype ι]

/-- The components of the datum of target-independent Hamiltonians, as functions of the domain
point alone: their values at any target point `y`. -/
private theorem puncturedSpherePerturbation_const_target_fun (c a : ι → ℂ) (k : ι → ℝ → ℝ)
    (kout : ℝ → ℝ) (y : M) (v : ℂ) :
    (fun z (x : M) ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
        (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
        (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [puncturedSpherePerturbation_const_target c a k kout _ x y]

/-- The components of the normalized datum are the components of the original one plus those of
the datum of the normalizing functions, evaluated at any target point `y`. -/
private theorem puncturedSpherePerturbation_add_const_fun (c a : ι → ℂ) (H : ι → ℝ → M → ℝ)
    (Hout : ℝ → M → ℝ) (k : ι → ℝ → ℝ) (kout : ℝ → ℝ) (y : M) (v : ℂ) :
    (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
        (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x v +
        puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t) (fun t (_ : M) ↦ kout t)
          (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [puncturedSpherePerturbation_add_const, add_apply,
    puncturedSpherePerturbation_const_target c a k kout _ x y]

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}
  {k : ι → ℝ → ℝ} {kout : ℝ → ℝ}

/-- **Normalizing the Hamiltonians does not change the Floer equation.** The perturbed derivative
`du - X_K` of any map into `M` is the same for the Hamiltonians `H i`, `Hout` and for
`H i + k i`, `Hout + kout`. -/
@[simp]
theorem perturbedMFDeriv_puncturedSpherePerturbation_add_const (ω : SmoothTwoForm I M)
    (c a : ι → ℂ) (H : ι → ℝ → M → ℝ) (Hout : ℝ → M → ℝ) (k : ι → ℝ → ℝ) (kout : ℝ → ℝ)
    (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u := by
  rw [puncturedSpherePerturbation_add_const_fun c a H Hout k kout (u 0),
    puncturedSpherePerturbation_add_const_fun c a H Hout k kout (u 0), perturbedMFDeriv_add_const]

/-- **Normalizing the Hamiltonians does not change the energy density.** -/
@[simp]
theorem floerEnergyDensity_puncturedSpherePerturbation_add_const (ω : SmoothTwoForm I M)
    (c a : ι → ℂ) (H : ι → ℝ → M → ℝ) (Hout : ℝ → M → ℝ) (k : ι → ℝ → ℝ) (kout : ℝ → ℝ)
    (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u := by
  rw [puncturedSpherePerturbation_add_const_fun c a H Hout k kout (u 0),
    puncturedSpherePerturbation_add_const_fun c a H Hout k kout (u 0), floerEnergyDensity_add_const]

/-- The curvature of the datum of target-independent Hamiltonians does not depend on the target
point. -/
theorem hamiltonianCurvature_puncturedSpherePerturbation_const_target (ω : SmoothTwoForm I M)
    (c a : ι → ℂ) (k : ι → ℝ → ℝ) (kout : ℝ → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [puncturedSpherePerturbation_const_target_fun c a k kout x,
    puncturedSpherePerturbation_const_target_fun c a k kout x, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

/-- **The curvature of the normalized datum.** Off the centers of the input ends, the curvature of
the datum of the Hamiltonians `H i + k i` and `Hout + kout` is the curvature for `H i` and `Hout`
plus the curvature of the datum of the target-independent Hamiltonians `k i` and `kout`. -/
theorem hamiltonianCurvature_puncturedSpherePerturbation_add_const
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hk : ∀ i, Periodic (k i) 1)
    (hks : ∀ i, ContDiff ℝ 1 (k i)) (hkout : Periodic kout 1) (hkouts : ContDiff ℝ 1 kout)
    (ha : ∀ i, a i ≠ 0) {z : ℝ × ℝ} (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) z x +
        ω.hamiltonianCurvature
          (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
            (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
            (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hdk (v : ℂ) := differentiableAt_puncturedSpherePerturbation_domain (I := I)
    (H := fun i t (_ : M) ↦ k i t) (Hout := fun t _ ↦ kout t)
    (fun i ↦ (hk i).comp (Function.const M)) (fun i ↦ (hks i).contMDiff.comp contMDiff_fst)
    (hkout.comp (Function.const M)) (hkouts.contMDiff.comp contMDiff_fst) ha hz x v
  rw [puncturedSpherePerturbation_add_const_fun c a H Hout k kout x,
    puncturedSpherePerturbation_add_const_fun c a H Hout k kout x,
    hamiltonianCurvature_add_const ω
      (differentiableAt_puncturedSpherePerturbation_domain hH hHs hHout hHouts ha hz x 1)
      (differentiableAt_puncturedSpherePerturbation_domain hH hHs hHout hHouts ha hz x Complex.I)
      (hdk 1) (hdk Complex.I),
    puncturedSpherePerturbation_const_target_fun c a k kout x,
    puncturedSpherePerturbation_const_target_fun c a k kout x]

/-- The curvature of a datum of target-independent Hamiltonians is the exterior derivative of a
one-form on the domain, whatever the target, so it is the curvature computed on `ℂ` with its
standard symplectic form, at `0`. -/
private theorem hamiltonianCurvature_puncturedSpherePerturbation_const_eq_complex
    (ω : SmoothTwoForm I M) (c a : ι → ℂ) (k : ι → ℝ → ℝ) (kout : ℝ → ℝ) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      stdComplexSymplecticForm.constSmooth.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : ℂ) ↦ k i t)
          (fun t (_ : ℂ) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : ℂ) ↦ k i t)
          (fun t (_ : ℂ) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := by
  rw [puncturedSpherePerturbation_const_target_fun c a k kout x,
    puncturedSpherePerturbation_const_target_fun c a k kout x, hamiltonianCurvature_const,
    puncturedSpherePerturbation_const_target_fun c a k kout (0 : ℂ),
    puncturedSpherePerturbation_const_target_fun c a k kout (0 : ℂ), hamiltonianCurvature_const]
  -- Both sides are the same exterior derivative of a one-form on the domain.
  simp only [puncturedSpherePerturbation_def, add_apply, sum_apply, inputEndPerturbation_apply,
    positivePlanePerturbation_def, negativePlanePerturbation_def]

/-- **The integrated curvature of a normalization.** For period-one `C¹` functions `k i` and
`kout` of time, nonzero scales, and discs `‖w - c i‖ < ‖a i‖ / 2` pairwise disjoint and in the
disc `‖w‖ ≤ 2 exp (2π)`, the curvature of the datum of the target-independent Hamiltonians `k i`
and `kout` on `M` integrates over the sphere minus its punctures to `∑ i, ∫₀¹ k i - ∫₀¹ kout`,
along any map `u`, whatever the configuration of the input ends. -/
theorem setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_const (ω : SmoothTwoForm I M)
    (hk : ∀ i, Periodic (k i) 1) (hks : ∀ i, ContDiff ℝ 1 (k i)) (hkout : Periodic kout 1)
    (hkouts : ContDiff ℝ 1 kout) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (u : ℝ × ℝ → M) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : M) ↦ k i t)
          (fun t (_ : M) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∑ i, ∫ t in (0 : ℝ)..1, k i t) - ∫ t in (0 : ℝ)..1, kout t := by
  rw [integral_congr_ae (Eventually.of_forall fun z ↦
    hamiltonianCurvature_puncturedSpherePerturbation_const_eq_complex ω c a k kout z (u z))]
  choose B hB using fun i ↦ (hk i).exists_forall_norm_le one_ne_zero (hks i).continuous
  obtain ⟨Bout, hBout⟩ := hkout.exists_forall_norm_le one_ne_zero hkouts.continuous
  -- Along the constant map `0`, the energy density and the area density vanish.
  have hE : stdComplexSymplecticForm.constSmooth.floerEnergyDensity
      (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : ℂ) ↦ k i t)
        (fun t (_ : ℂ) ↦ kout t) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ puncturedSpherePerturbation c a (fun i t (_ : ℂ) ↦ k i t)
        (fun t (_ : ℂ) ↦ kout t) (Complex.equivRealProdCLM.symm z) x Complex.I)
      (fun _ ↦ (0 : ℂ)) = 0 := by
    funext z
    rw [SymplecticForm.floerEnergyDensity_constSmooth,
      puncturedSpherePerturbation_const_target_fun c a k kout 0,
      puncturedSpherePerturbation_const_target_fun c a k kout 0,
      SymplecticForm.floerEnergyDensity_def, SymplecticForm.perturbedFDeriv_const]
    simp
  have hA : (fun z : ℝ × ℝ ↦ (SmoothBundleForm.eval₂ stdComplexSymplecticForm.constSmooth
      ((fun _ ↦ (0 : ℂ)) z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun _ ↦ (0 : ℂ)) z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun _ ↦ (0 : ℂ)) z stdComplexLineImag) : ℝ)) = 0 := by
    funext z
    rw [SymplecticForm.eval₂_constSmooth_mfderiv_stdComplexLine _ (fun _ ↦ (0 : ℂ)) z]
    simp
  -- The energy identity for the constant map `0` leaves only the curvature and the end terms.
  have hid := IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation
    (SymplecticForm.isNondegenerate_constSmooth stdComplexSymplecticForm)
    (H := fun i t (_ : ℂ) ↦ k i t) (Hout := fun t _ ↦ kout t)
    (fun i ↦ (hk i).comp (Function.const _)) (fun i ↦ (hks i).contMDiff.comp contMDiff_fst)
    (hkout.comp (Function.const _)) (hkouts.contMDiff.comp contMDiff_fst)
    ha hsep hout (B := B) (fun i t _ ↦ hB i t) (fun t _ ↦ hBout t) (u := fun _ ↦ (0 : ℂ))
    contMDiffOn_const (x := fun _ _ ↦ 0) (xout := fun _ ↦ 0) (fun _ _ ↦ tendsto_const_nhds)
    (fun _ ↦ tendsto_const_nhds) (by rw [hE]; exact integrableOn_zero)
    (by rw [hA]; exact integrableOn_zero)
  rw [hE, hA] at hid
  simp only [integral_zero', zero_add] at hid
  linarith

/-- **Normalizing the Hamiltonians shifts the integrated curvature.** Along a map whose curvature
for `H i` and `Hout` is integrable over the sphere minus its punctures, the integrated curvature of
the datum of the Hamiltonians `H i + k i` and `Hout + kout` is the integrated curvature for `H i`
and `Hout` plus `∑ i, ∫₀¹ k i - ∫₀¹ kout`. This is also the change of the Hamiltonian terms
`∑ i, ∫₀¹ H_i(t, x_i(t)) dt - ∫₀¹ Hout(t, xout(t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation`, so the two
changes cancel and the energy identity for the normalized Hamiltonians is the one for `H i` and
`Hout`. -/
theorem setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_add_const
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (hk : ∀ i, Periodic (k i) 1)
    (hks : ∀ i, ContDiff ℝ 1 (k i)) (hkout : Periodic kout 1) (hkouts : ContDiff ℝ 1 kout)
    (ha : ∀ i, a i ≠ 0) (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a (fun i t y ↦ H i t y + k i t)
          (fun t y ↦ Hout t y + kout t) (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ω.hamiltonianCurvature
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) z (u z)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, k i t) - ∫ t in (0 : ℝ)..1, kout t) := by
  choose B hB using fun i ↦ (hk i).exists_forall_norm_le one_ne_zero (hks i).continuous
  obtain ⟨Bout, hBout⟩ := hkout.exists_forall_norm_le one_ne_zero hkouts.continuous
  have hS : IsOpen {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i} :=
    isOpen_forall_ne Complex.equivRealProdCLM.symm.continuous
  -- The curvature of the normalization does not depend on the target point, so it is integrable
  -- along `u` because it is along a constant map.
  have hκ := (ω.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation
    (H := fun i t _ ↦ k i t) (Hout := fun t _ ↦ kout t)
    (fun i ↦ (hk i).comp (Function.const _)) (fun i ↦ (hks i).contMDiff.comp contMDiff_fst)
    (hkout.comp (Function.const _)) (hkouts.contMDiff.comp contMDiff_fst)
    ha hsep hout (B := B) (fun i t _ ↦ hB i t) (fun t _ ↦ hBout t) (u := fun _ ↦ u 0)
    continuousOn_const).congr_fun
    (fun z _ ↦ ω.hamiltonianCurvature_puncturedSpherePerturbation_const_target c a k kout z (u 0)
      (u z)) hS.measurableSet
  rw [← ω.setIntegral_hamiltonianCurvature_puncturedSpherePerturbation_const hk hks hkout hkouts
    ha hsep hout u, ← integral_add hu hκ]
  exact setIntegral_congr_fun hS.measurableSet fun z hz ↦
    ω.hamiltonianCurvature_puncturedSpherePerturbation_add_const hH hHs hHout hHouts hk hks hkout
      hkouts ha hz (u z)

end SmoothTwoForm

end TauCeti
