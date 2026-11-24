/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# Normalizing the Hamiltonian of a PSS plane

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H(t, x)` and `H(t, x) + c(t)` generate the same flow, have the same one-periodic orbits and give
the same Floer equation, while the action of a capped loop changes by the time average `∫₀¹ c`
(`TauCeti.cappedLoopAction_add_const`). This file shows how the energy identity of a PSS plane
with end sign `ε = ±1`,

`E(u) = ε A_H(x, u) - ∫_ℂ R_K(u)`

(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`), absorbs
such a change of normalization, for a manifold target `M` with a two-form `ω`, such as a closed
symplectic manifold, and for a symplectic vector space target.

The perturbation of a PSS plane (`TauCeti.Floer.PSSPlane.perturbation`) is additive in the
Hamiltonian, so normalizing by `c` adds to it the perturbation `k` of the target-independent
Hamiltonian `c`, which has no Hamiltonian vector field
(`TauCeti.Floer.PSSPlane.perturbation_add_const`). Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density
  are unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_pssPlanePerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_pssPlanePerturbation_add_const`);
* the curvature changes by the curvature of `k`, which does not depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_pssPlanePerturbation_add_const`);
* the integral of the curvature of `k` over the plane is exactly `ε ∫₀¹ c`
  (`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_pssPlanePerturbation_const`).

So along every map whose curvature for `H` is integrable over the plane, the integrated curvature
changes by `ε ∫₀¹ c`
(`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_pssPlanePerturbation_add_const`), which is
exactly the change `ε ∫₀¹ c` of the term `ε A_H(x, u)`. The two changes cancel in the energy
identity, as they must, since the energy itself is unchanged.

The curvature of `k` is the exterior derivative `∂_s k_t - ∂_t k_s` of a one-form on the domain,
the same for every target. Its integral is computed once, for a symplectic vector space, from the
energy identity on the disc `‖w‖ ≤ exp (4π)` along a constant map
(`TauCeti.SymplecticForm.integral_hamiltonianCurvature_pssPlanePerturbation_const`). The
vector-space curvature statements are the specializations of the manifold ones to the constant
form `TauCeti.SymplecticForm.constSmooth`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory Real
open scoped Manifold

namespace TauCeti

namespace Floer.PSSPlane

variable {M : Type*}

/-- The components of the perturbation of a target-independent Hamiltonian, as functions of the
domain point alone: their values at any target point `y`. -/
private theorem perturbation_const_target_fun (p : PSSPlane) (c : ℝ → ℝ) (y : M) (v : ℂ) :
    (fun z (x : M) ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [perturbation_const_target p c _ x y]

/-- The components of the normalized perturbation are the components of the original one plus
those of the perturbation of the normalizing function, evaluated at any target point `y`. -/
private theorem perturbation_add_const_fun (p : PSSPlane) (H : ℝ → M → ℝ) (c : ℝ → ℝ) (y : M)
    (v : ℂ) :
    (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x v +
        p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [perturbation_add_const, add_apply, perturbation_const_target p c _ x y]

end Floer.PSSPlane

/-! ### Symplectic vector spaces: the Floer equation and the curvature of a normalization -/

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : PSSPlane}
  {c : ℝ → ℝ}

variable [FiniteDimensional ℝ V]

/-- **Normalizing the Hamiltonian does not change the Floer equation on a PSS plane.** The
perturbed derivative `du - X_K` of any map is the same for the Hamiltonians `H` and `H + c`. -/
@[simp]
theorem perturbedFDeriv_pssPlanePerturbation_add_const (ω : SymplecticForm V) (H : ℝ → V → ℝ)
    (c : ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) u =
      ω.perturbedFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [perturbation_add_const_fun p H c 0, perturbation_add_const_fun p H c 0,
    perturbedFDeriv_add_const]

/-- **Normalizing the Hamiltonian does not change the energy density on a PSS plane.** -/
@[simp]
theorem floerEnergyDensity_pssPlanePerturbation_add_const (ω : SymplecticForm V) (H : ℝ → V → ℝ)
    (c : ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) u =
      ω.floerEnergyDensity (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [perturbation_add_const_fun p H c 0, perturbation_add_const_fun p H c 0,
    floerEnergyDensity_add_const]

/-- The curvature of the perturbation of a target-independent Hamiltonian on a PSS plane does not
depend on the target point. -/
theorem hamiltonianCurvature_pssPlanePerturbation_const_target (ω : SymplecticForm V)
    (c : ℝ → ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z y := by
  rw [perturbation_const_target_fun p c x, perturbation_const_target_fun p c x,
    hamiltonianCurvature_const, hamiltonianCurvature_const]

/-- **The integrated curvature of a normalization on a PSS plane.** For a period-one `C¹` function
`c` of time, the curvature of the perturbation of the target-independent Hamiltonian `c` on a PSS
plane with end sign `ε` integrates over the plane to `ε ∫₀¹ c`, along any map `u`. -/
theorem integral_hamiltonianCurvature_pssPlanePerturbation_const (ω : SymplecticForm V)
    (hc : Periodic c 1) (hcs : ContDiff ℝ 1 c) (u : ℝ × ℝ → V) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) =
      p.endSign * ∫ t in (0 : ℝ)..1, c t := by
  have hc' : Periodic (fun t (_ : V) ↦ c t) 1 := fun t ↦ funext fun _ ↦ hc t
  have hcs' : ContDiff ℝ 1 (uncurry fun t (_ : V) ↦ c t) := hcs.comp contDiff_fst
  -- Along the constant map `0`, the energy density and the area density vanish.
  have hE : ω.floerEnergyDensity
      (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x
        Complex.I) (fun _ ↦ (0 : V)) = 0 := by
    funext z
    rw [perturbation_const_target_fun p c 0, perturbation_const_target_fun p c 0,
      floerEnergyDensity_def, perturbedFDeriv_const]
    simp
  have hA : (fun z : ℝ × ℝ ↦ ω (fderiv ℝ (fun _ ↦ (0 : V)) z stdComplexLineReal)
      (fderiv ℝ (fun _ ↦ (0 : V)) z stdComplexLineImag)) = 0 := by
    funext z
    simp
  -- The energy identity on the disc `‖w‖ ≤ exp (4π)` for the constant map `0` leaves only the
  -- curvature and the end term.
  have h := ω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall (p := p) hc' hcs'
    (u := fun _ ↦ (0 : V)) contDiff_const one_le_two
  rw [hE, hA, ω.setIntegral_hamiltonianCurvature_pssPlanePerturbation_closedBall hc' hcs' _
    le_rfl, smoothTransition.one_of_one_le (by norm_num)] at h
  simp only [Pi.zero_apply, integral_zero, integral_zero', zero_add, mul_one] at h
  -- The curvature does not depend on the target point, so it is the same along `u` and `0`.
  rw [integral_congr_ae (ae_of_all _ fun z ↦
    ω.hamiltonianCurvature_pssPlanePerturbation_const_target c z (u z) 0)]
  linarith

end SymplecticForm

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer Floer.PSSPlane

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {p : PSSPlane} {H : ℝ → M → ℝ} {c : ℝ → ℝ}

/-- **Normalizing the Hamiltonian does not change the Floer equation on a PSS plane, for a
manifold target.** The perturbed derivative `du - X_K` of any map into `M` is the same for the
Hamiltonians `H` and `H + c`. -/
@[simp]
theorem perturbedMFDeriv_pssPlanePerturbation_add_const (ω : SmoothTwoForm I M) (H : ℝ → M → ℝ)
    (c : ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) u =
      ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [perturbation_add_const_fun p H c (u 0), perturbation_add_const_fun p H c (u 0),
    perturbedMFDeriv_add_const]

/-- **Normalizing the Hamiltonian does not change the energy density on a PSS plane, for a
manifold target.** -/
@[simp]
theorem floerEnergyDensity_pssPlanePerturbation_add_const (ω : SmoothTwoForm I M)
    (H : ℝ → M → ℝ) (c : ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) u =
      ω.floerEnergyDensity (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [perturbation_add_const_fun p H c (u 0), perturbation_add_const_fun p H c (u 0),
    floerEnergyDensity_add_const]

/-- The curvature of the perturbation of a target-independent Hamiltonian on a PSS plane does not
depend on the target point, for a manifold target. -/
theorem hamiltonianCurvature_pssPlanePerturbation_const_target (ω : SmoothTwoForm I M)
    (c : ℝ → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z y := by
  rw [perturbation_const_target_fun p c x, perturbation_const_target_fun p c x,
    hamiltonianCurvature_const, hamiltonianCurvature_const]

/-- **The curvature of the normalized perturbation of a PSS plane, for a manifold target.** At
every point of the plane, the curvature of the perturbation of the Hamiltonian `H + c` is the
curvature for `H` plus the curvature of the perturbation of the target-independent Hamiltonian
`c`. -/
theorem hamiltonianCurvature_pssPlanePerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hc : Periodic c 1) (hcs : ContDiff ℝ 1 c) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z x =
      ω.hamiltonianCurvature (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z x +
        ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x
            Complex.I) z x := by
  have hc' : Periodic (fun t (_ : M) ↦ c t) 1 := fun t ↦ funext fun _ ↦ hc t
  have hcs' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ c t) :=
    hcs.contMDiff.comp contMDiff_fst
  rw [perturbation_add_const_fun p H c x, perturbation_add_const_fun p H c x,
    hamiltonianCurvature_add_const ω (differentiableAt_perturbation_domain hH hHs z x 1)
      (differentiableAt_perturbation_domain hH hHs z x Complex.I)
      (differentiableAt_perturbation_domain hc' hcs' z x 1)
      (differentiableAt_perturbation_domain hc' hcs' z x Complex.I),
    perturbation_const_target_fun p c x, perturbation_const_target_fun p c x]

/-- **The integrated curvature of a normalization on a PSS plane, for a manifold target.** For a
period-one `C¹` function `c` of time, the curvature of the perturbation of the target-independent
Hamiltonian `c` on `M` on a PSS plane with end sign `ε` integrates over the plane to `ε ∫₀¹ c`,
along any map `u`. -/
theorem integral_hamiltonianCurvature_pssPlanePerturbation_const (ω : SmoothTwoForm I M)
    (hc : Periodic c 1) (hcs : ContDiff ℝ 1 c) (u : ℝ × ℝ → M) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) =
      p.endSign * ∫ t in (0 : ℝ)..1, c t := by
  -- The curvature of a target-independent datum is the exterior derivative of a one-form on the
  -- domain, whatever the target; on `ℂ` with its standard symplectic form it was computed above.
  have h (z : ℝ × ℝ) : ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation (fun t (_ : M) ↦ c t) (Complex.equivRealProdCLM.symm z) x
        Complex.I) z (u z) =
      stdComplexSymplecticForm.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t (_ : ℂ) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t (_ : ℂ) ↦ c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z 0 := by
    rw [perturbation_const_target_fun p c (u z), perturbation_const_target_fun p c (u z),
      hamiltonianCurvature_const, perturbation_const_target_fun p c (0 : ℂ),
      perturbation_const_target_fun p c (0 : ℂ), SymplecticForm.hamiltonianCurvature_const]
    -- Both sides are the same exterior derivative of a one-form on the domain.
    simp only [perturbation_def]
  rw [integral_congr_ae (ae_of_all _ h)]
  exact stdComplexSymplecticForm.integral_hamiltonianCurvature_pssPlanePerturbation_const hc hcs
    fun _ ↦ 0

/-- **Normalizing the Hamiltonian shifts the integrated curvature of a PSS plane, for a manifold
target.** Along a map whose curvature for `H` is integrable over the plane, the integrated
curvature of the perturbation of the Hamiltonian `H + c` on a PSS plane with end sign `ε` is the
integrated curvature for `H` plus `ε ∫₀¹ c`. Since the capped action of every loop changes by
`∫₀¹ c` (`TauCeti.cappedLoopAction_add_const`), this is also the change of the term `ε A_H(x, u)`
of the energy identity
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, so the two
changes cancel and the energy identity for `H + c` is the one for `H`. -/
theorem integral_hamiltonianCurvature_pssPlanePerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hc : Periodic c 1) (hcs : ContDiff ℝ 1 c) {u : ℝ × ℝ → M}
    (hu : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) =
      (∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) +
        p.endSign * ∫ t in (0 : ℝ)..1, c t := by
  -- The curvature of the normalization does not depend on the target point, so it is integrable
  -- along `u` because it is along a constant map.
  have hk := (ω.integrable_hamiltonianCurvature_pssPlanePerturbation (p := p)
    (fun t ↦ funext fun _ ↦ hc t) (hcs.contMDiff.comp contMDiff_fst) (u := fun _ ↦ u 0)
    continuous_const).congr (ae_of_all _ fun z ↦
      ω.hamiltonianCurvature_pssPlanePerturbation_const_target c z (u 0) (u z))
  rw [← ω.integral_hamiltonianCurvature_pssPlanePerturbation_const hc hcs u, ← integral_add hu hk]
  exact integral_congr_ae (ae_of_all _ fun z ↦
    ω.hamiltonianCurvature_pssPlanePerturbation_add_const hH hHs hc hcs z (u z))

end SmoothTwoForm

/-! ### Symplectic vector spaces: the curvature of the normalized perturbation -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : PSSPlane} {H : ℝ → V → ℝ} {c : ℝ → ℝ}

/-- **The curvature of the normalized perturbation of a PSS plane.** At every point of the plane,
the curvature of the perturbation of the Hamiltonian `H + c` is the curvature for `H` plus the
curvature of the perturbation of the target-independent Hamiltonian `c`. This is the vector-space
case of `SmoothTwoForm.hamiltonianCurvature_pssPlanePerturbation_add_const`. -/
theorem hamiltonianCurvature_pssPlanePerturbation_add_const (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hc : Periodic c 1)
    (hcs : ContDiff ℝ 1 c) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z x =
      ω.hamiltonianCurvature (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z x +
        ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation (fun t (_ : V) ↦ c t) (Complex.equivRealProdCLM.symm z) x
            Complex.I) z x := by
  have h := ω.constSmooth.hamiltonianCurvature_pssPlanePerturbation_add_const (p := p) hH
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff) hc hcs z x
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **Normalizing the Hamiltonian shifts the integrated curvature of a PSS plane.** Along a map
whose curvature for `H` is integrable over the plane, the integrated curvature of the perturbation
of the Hamiltonian `H + c` on a PSS plane with end sign `ε` is the integrated curvature for `H`
plus `ε ∫₀¹ c`. This is the vector-space case of
`SmoothTwoForm.integral_hamiltonianCurvature_pssPlanePerturbation_add_const`. -/
theorem integral_hamiltonianCurvature_pssPlanePerturbation_add_const (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) (hc : Periodic c 1)
    (hcs : ContDiff ℝ 1 c) {u : ℝ × ℝ → V}
    (hu : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) :
    ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation (fun t y ↦ H t y + c t) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) =
      (∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) +
        p.endSign * ∫ t in (0 : ℝ)..1, c t := by
  have h := ω.constSmooth.integral_hamiltonianCurvature_pssPlanePerturbation_add_const (p := p) hH
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff) hc hcs
    (by simpa only [hamiltonianCurvature_constSmooth] using hu)
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

end SymplecticForm

end TauCeti
