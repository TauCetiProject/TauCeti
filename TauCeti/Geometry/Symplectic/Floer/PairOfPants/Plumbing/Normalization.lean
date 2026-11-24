/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Asymptotic
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Topology.Instances.Real.Periodic

/-!
# Normalizing the Hamiltonians of the plumbed four-punctured sphere

Plumbing the output end of a pair of pants with Hamiltonians `Ha` into the input end `q ≠ ∞` of a
pair of pants with Hamiltonians `Hb`, `Hb q = Ha ∞`, along a neck of length `L > 4`, gives the
four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}` with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`), the domains of the family relating the two compositions
`(a ⋆ b) ⋆ c` and `a ⋆ (b ⋆ c)` of the pair-of-pants product. Its energy identity
(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`) is

`∫ E(u) = ∫ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, x'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, x_r(t)) dt
  - ∫ R_K(u)`.

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time. This
file shows how the identity absorbs a change of normalization `Ha r + ca r`, `Hb r + cb r` of the
Hamiltonians of both pairs of pants by functions `ca r`, `cb r` of time, with `cb q = ca ∞` so
that the normalized Hamiltonians still match on the neck, for a manifold target `M` with a
two-form `ω`, such as a closed symplectic manifold, and for a symplectic vector space target.

The plumbed perturbation is additive in the Hamiltonians, so normalizing adds the plumbed
perturbation `k` of the target-independent Hamiltonians `ca r`, `cb r`
(`TauCeti.Floer.plumbedPerturbation_add_const`), which has no Hamiltonian vector field.
Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density
  are unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_plumbedPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_plumbedPerturbation_add_const`);
* on `Σ_L` the curvature changes by the curvature of `k`, which does not depend on the target
  point (`TauCeti.SmoothTwoForm.hamiltonianCurvature_plumbedPerturbation_add_const`);
* the integral of the curvature of `k` over `Σ_L` is exactly
  `∑_{r ≠ ∞} ∫₀¹ ca_r + ∑_{r ≠ q} ±∫₀¹ cb_r`, the sum over the four outer ends with the sign `+`
  on the three inputs and `-` on the output, whatever the neck length
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_plumbedPerturbation_const`). The
  normalization `cb q = ca ∞` of the neck does not enter.

So along every map whose curvature for `Ha`, `Hb` is integrable on `Σ_L`, the integrated curvature
changes by `∑_{r ≠ ∞} ∫₀¹ ca_r + ∑_{r ≠ q} ±∫₀¹ cb_r`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_plumbedPerturbation_add_const`). This is
exactly the change of the Hamiltonian terms at the asymptotic orbits of the four outer ends, so
the two changes cancel in the energy identity, as they must, since the energy itself is
unchanged.

The curvature of `k` is the exterior derivative `∂_s k_t - ∂_t k_s` of a one-form on the domain,
the same for every target. Its integral is computed once, for a symplectic vector space, by the
energy identity on the whole plumbed four-punctured sphere along a constant map
(`TauCeti.SymplecticForm.setIntegral_hamiltonianCurvature_plumbedPerturbation_const`). The
vector-space curvature statements are the specializations of the manifold ones to the constant
form `TauCeti.SymplecticForm.constSmooth`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimates for compositions of pair-of-pants products.
-/

public section

open Set Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti

namespace Floer

variable {M : Type*}

/-- The components of the plumbed perturbation of target-independent Hamiltonians, as functions
of the domain point alone: their values at any target point `y`. -/
private theorem plumbedPerturbation_const_target_fun (ca cb : Puncture → ℝ → ℝ) (q : Puncture)
    (L : ℝ) (y : M) (v : ℂ) :
    (fun z (x : M) ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [plumbedPerturbation_const_target ca cb q L _ x y]

/-- The components of the normalized plumbed perturbation are the components of the original one
plus those of the plumbed perturbation of the normalizing functions, evaluated at any target
point `y`. -/
private theorem plumbedPerturbation_add_const_fun (Ha Hb : Puncture → ℝ → M → ℝ)
    (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ) (y : M) (v : ℂ) :
    (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t) (fun r t y ↦ Hb r t y + cb r t)
        q L (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v +
        plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [plumbedPerturbation_add_const, add_apply,
    plumbedPerturbation_const_target ca cb q L _ x y]

end Floer

/-! ### Symplectic vector spaces: the Floer equation and the curvature of a normalization -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {q : Puncture} {L : ℝ} {ca cb : Puncture → ℝ → ℝ}

/-- **Normalizing the Hamiltonians does not change the Floer equation on the plumbed
four-punctured sphere.** The perturbed derivative `du - X_K` of any map is the same for the
Hamiltonians `Ha r`, `Hb r` and `Ha r + ca r`, `Hb r + cb r`. -/
@[simp]
theorem perturbedFDeriv_plumbedPerturbation_add_const (ω : SymplecticForm V)
    (Ha Hb : Puncture → ℝ → V → ℝ) (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ)
    (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [plumbedPerturbation_add_const_fun Ha Hb ca cb q L 0,
    plumbedPerturbation_add_const_fun Ha Hb ca cb q L 0, perturbedFDeriv_add_const]

/-- **Normalizing the Hamiltonians does not change the energy density on the plumbed
four-punctured sphere.** -/
@[simp]
theorem floerEnergyDensity_plumbedPerturbation_add_const (ω : SymplecticForm V)
    (Ha Hb : Puncture → ℝ → V → ℝ) (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ)
    (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [plumbedPerturbation_add_const_fun Ha Hb ca cb q L 0,
    plumbedPerturbation_add_const_fun Ha Hb ca cb q L 0, floerEnergyDensity_add_const]

/-- The curvature of the plumbed perturbation of target-independent Hamiltonians does not depend
on the target point. -/
theorem hamiltonianCurvature_plumbedPerturbation_const_target (ω : SymplecticForm V)
    (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [plumbedPerturbation_const_target_fun ca cb q L 0,
    plumbedPerturbation_const_target_fun ca cb q L 0, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

/-- **The integrated curvature of a normalization of the plumbed four-punctured sphere.** For
period-one `C¹` functions `ca r`, `cb r` of time with `cb q = ca ∞`, the curvature of the plumbed
perturbation of the target-independent Hamiltonians `ca r`, `cb r` integrates over the
four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}` to `∑_{r ≠ ∞} ∫₀¹ ca_r + ∑_{r ≠ q} ±∫₀¹ cb_r`, with
the sign `+` on the input ends and `-` on the output end, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_plumbedPerturbation_const (ω : SymplecticForm V)
    (hq : q ≠ inf) (hca : ∀ r, Periodic (ca r) 1) (hcb : ∀ r, Periodic (cb r) 1)
    (hcas : ∀ r, ContDiff ℝ 1 (ca r)) (hcbs : ∀ r, ContDiff ℝ 1 (cb r)) (hc : cb q = ca inf)
    (hL : 4 < L) (u : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, ca r t) +
        ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, cb r t := by
  choose Ba hBa using fun r ↦ (hca r).exists_forall_norm_le one_ne_zero (hcas r).continuous
  choose Bb hBb using fun r ↦ (hcb r).exists_forall_norm_le one_ne_zero (hcbs r).continuous
  -- Along the constant map `0`, the energy density and the area density vanish.
  have hE : ω.constSmooth.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x Complex.I) (fun _ ↦ (0 : V)) = 0 := by
    funext z
    rw [floerEnergyDensity_constSmooth, plumbedPerturbation_const_target_fun ca cb q L 0,
      plumbedPerturbation_const_target_fun ca cb q L 0, floerEnergyDensity_def,
      perturbedFDeriv_const]
    simp
  have hA : (fun z : ℝ × ℝ ↦ (SmoothBundleForm.eval₂ ω.constSmooth ((fun _ ↦ (0 : V)) z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) (fun _ ↦ (0 : V)) z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) (fun _ ↦ (0 : V)) z stdComplexLineImag) : ℝ)) = 0 := by
    funext z
    exact (eval₂_constSmooth_mfderiv_stdComplexLine ω (fun _ ↦ 0) z).trans (by simp)
  -- The energy identity for the constant map `0` leaves only the curvature and the end terms.
  have h := (isNondegenerate_constSmooth ω).integral_floerEnergyDensity_plumbedPerturbation hq
    (fun r t ↦ funext fun _ ↦ hca r t) (fun r t ↦ funext fun _ ↦ hcb r t)
    (fun r ↦ (hcas r).contMDiff.comp contMDiff_fst)
    (fun r ↦ (hcbs r).contMDiff.comp contMDiff_fst) (by simp only [hc]) hL
    (fun r t _ ↦ Real.norm_eq_abs _ ▸ hBa r t) (fun r t _ ↦ Real.norm_eq_abs _ ▸ hBb r t)
    (u := fun _ ↦ (0 : V)) contMDiffOn_const (xa := fun _ _ ↦ 0) (xb := fun _ _ ↦ 0)
    (fun _ _ _ ↦ tendsto_const_nhds) (fun _ _ _ ↦ tendsto_const_nhds)
    (by rw [hE]; exact integrableOn_zero) (by rw [hA]; exact integrableOn_zero)
  rw [hE, hA] at h
  simp only [integral_zero', zero_add, hamiltonianCurvature_constSmooth] at h
  -- The curvature does not depend on the target point, so it is the same along `u` and `0`.
  have hu : (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) =
      fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 :=
    funext fun z ↦ ω.hamiltonianCurvature_plumbedPerturbation_const_target ca cb q L z (u z) 0
  rw [hu]
  linarith

end SymplecticForm

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {Ha Hb : Puncture → ℝ → M → ℝ} {ca cb : Puncture → ℝ → ℝ} {q : Puncture} {L : ℝ}

/-- **Normalizing the Hamiltonians does not change the Floer equation on the plumbed
four-punctured sphere, for a manifold target.** The perturbed derivative `du - X_K` of any map
into `M` is the same for the Hamiltonians `Ha r`, `Hb r` and `Ha r + ca r`, `Hb r + cb r`. -/
@[simp]
theorem perturbedMFDeriv_plumbedPerturbation_add_const (ω : SmoothTwoForm I M)
    (Ha Hb : Puncture → ℝ → M → ℝ) (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ)
    (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [plumbedPerturbation_add_const_fun Ha Hb ca cb q L (u 0),
    plumbedPerturbation_add_const_fun Ha Hb ca cb q L (u 0), perturbedMFDeriv_add_const]

/-- **Normalizing the Hamiltonians does not change the energy density on the plumbed
four-punctured sphere, for a manifold target.** -/
@[simp]
theorem floerEnergyDensity_plumbedPerturbation_add_const (ω : SmoothTwoForm I M)
    (Ha Hb : Puncture → ℝ → M → ℝ) (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ)
    (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [plumbedPerturbation_add_const_fun Ha Hb ca cb q L (u 0),
    plumbedPerturbation_add_const_fun Ha Hb ca cb q L (u 0), floerEnergyDensity_add_const]

/-- The curvature of the plumbed perturbation of target-independent Hamiltonians does not depend
on the target point, for a manifold target. -/
theorem hamiltonianCurvature_plumbedPerturbation_const_target (ω : SmoothTwoForm I M)
    (ca cb : Puncture → ℝ → ℝ) (q : Puncture) (L : ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [plumbedPerturbation_const_target_fun ca cb q L x,
    plumbedPerturbation_const_target_fun ca cb q L x, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

/-- **The curvature of the normalized plumbed perturbation, for a manifold target.** At every
point of the four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}`, the curvature of the plumbed
perturbation of the Hamiltonians `Ha r + ca r`, `Hb r + cb r` is the curvature for `Ha r`, `Hb r`
plus the curvature of the plumbed perturbation of the target-independent Hamiltonians `ca r`,
`cb r`. -/
theorem hamiltonianCurvature_plumbedPerturbation_add_const (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hca : ∀ r, Periodic (ca r) 1) (hcb : ∀ r, Periodic (cb r) 1)
    (hcas : ∀ r, ContDiff ℝ 1 (ca r)) (hcbs : ∀ r, ContDiff ℝ 1 (cb r)) (hc : cb q = ca inf)
    (hL : 4 < L) {z : ℝ × ℝ}
    (hz : (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t)
            q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t)
            q L (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  -- The target-independent Hamiltonians are again periodic, `C¹` and matching on the neck.
  have hca' : ∀ r, Periodic (fun t (_ : M) ↦ ca r t) 1 := fun r t ↦ funext fun _ ↦ hca r t
  have hcb' : ∀ r, Periodic (fun t (_ : M) ↦ cb r t) 1 := fun r t ↦ funext fun _ ↦ hcb r t
  have hcas' : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ ca r t) :=
    fun r ↦ (hcas r).contMDiff.comp contMDiff_fst
  have hcbs' : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ cb r t) :=
    fun r ↦ (hcbs r).contMDiff.comp contMDiff_fst
  have hc' : (fun t (_ : M) ↦ cb q t) = fun t _ ↦ ca inf t := by simp only [hc]
  rw [plumbedPerturbation_add_const_fun Ha Hb ca cb q L x,
    plumbedPerturbation_add_const_fun Ha Hb ca cb q L x,
    hamiltonianCurvature_add_const ω
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hz x 1)
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hz x Complex.I)
      (differentiableAt_plumbedPerturbation_domain hq hca' hcb' hcas' hcbs' hc' hL hz x 1)
      (differentiableAt_plumbedPerturbation_domain hq hca' hcb' hcas' hcbs' hc' hL hz x
        Complex.I),
    plumbedPerturbation_const_target_fun ca cb q L x,
    plumbedPerturbation_const_target_fun ca cb q L x]

/-- **The integrated curvature of a normalization of the plumbed four-punctured sphere, for a
manifold target.** For period-one `C¹` functions `ca r`, `cb r` of time with `cb q = ca ∞`, the
curvature of the plumbed perturbation of the target-independent Hamiltonians `ca r`, `cb r` on `M`
integrates over the four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}` to
`∑_{r ≠ ∞} ∫₀¹ ca_r + ∑_{r ≠ q} ±∫₀¹ cb_r`, with the sign `+` on the input ends and `-` on the
output end, along any map `u`. -/
theorem setIntegral_hamiltonianCurvature_plumbedPerturbation_const (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hca : ∀ r, Periodic (ca r) 1) (hcb : ∀ r, Periodic (cb r) 1)
    (hcas : ∀ r, ContDiff ℝ 1 (ca r)) (hcbs : ∀ r, ContDiff ℝ 1 (cb r)) (hc : cb q = ca inf)
    (hL : 4 < L) (u : ℝ × ℝ → M) :
    ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, ca r t) +
        ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, cb r t := by
  -- The curvature of a target-independent datum is the exterior derivative of a one-form on the
  -- domain, whatever the target; on `ℂ` with its standard symplectic form it was computed above.
  have h (z : ℝ × ℝ) : ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      stdComplexSymplecticForm.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t (_ : ℂ) ↦ ca r t) (fun r t (_ : ℂ) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t (_ : ℂ) ↦ ca r t) (fun r t (_ : ℂ) ↦ cb r t) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := by
    rw [plumbedPerturbation_const_target_fun ca cb q L (u z),
      plumbedPerturbation_const_target_fun ca cb q L (u z), hamiltonianCurvature_const,
      plumbedPerturbation_const_target_fun ca cb q L (0 : ℂ),
      plumbedPerturbation_const_target_fun ca cb q L (0 : ℂ),
      SymplecticForm.hamiltonianCurvature_const]
    -- Both sides are the same exterior derivative of a one-form on the domain.
    simp only [plumbedPerturbation_def, pairOfPantsPerturbation_def]
  rw [integral_congr_ae (Eventually.of_forall h)]
  exact stdComplexSymplecticForm.setIntegral_hamiltonianCurvature_plumbedPerturbation_const hq hca
    hcb hcas hcbs hc hL fun _ ↦ 0

/-- **Normalizing the Hamiltonians shifts the integrated curvature of the plumbed four-punctured
sphere, for a manifold target.** Along a map whose curvature for `Ha r`, `Hb r` is integrable on
the four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}`, the integrated curvature of the plumbed
perturbation of the Hamiltonians `Ha r + ca r`, `Hb r + cb r`, with `cb q = ca ∞`, is the
integrated curvature for `Ha r`, `Hb r` plus `∑_{r ≠ ∞} ∫₀¹ ca_r + ∑_{r ≠ q} ±∫₀¹ cb_r`, with the
sign `+` on the input ends and `-` on the output end. This is also the change of the Hamiltonian
terms of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation` at the asymptotic
loops of the four outer ends, so the two changes cancel and the energy identity for the normalized
Hamiltonians is the one for `Ha r`, `Hb r`. -/
theorem setIntegral_hamiltonianCurvature_plumbedPerturbation_add_const (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hca : ∀ r, Periodic (ca r) 1) (hcb : ∀ r, Periodic (cb r) 1)
    (hcas : ∀ r, ContDiff ℝ 1 (ca r)) (hcbs : ∀ r, ContDiff ℝ 1 (cb r)) (hc : cb q = ca inf)
    (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, ca r t) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, cb r t) := by
  have hm := (isOpen_plumbedSphere q L).measurableSet
  -- The curvature of the normalization does not depend on the target point, so it is integrable
  -- along `u` because it is along a constant map.
  have hk : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (fun r t (_ : M) ↦ ca r t) (fun r t (_ : M) ↦ cb r t) q L
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    exact (ω.integrableOn_hamiltonianCurvature_plumbedPerturbation hq
      (fun r t ↦ funext fun _ ↦ hca r t) (fun r t ↦ funext fun _ ↦ hcb r t)
      (fun r ↦ (hcas r).contMDiff.comp contMDiff_fst)
      (fun r ↦ (hcbs r).contMDiff.comp contMDiff_fst) (by simp only [hc]) hL
      (u := fun _ ↦ u 0) continuousOn_const).congr_fun
      (fun z _ ↦ ω.hamiltonianCurvature_plumbedPerturbation_const_target ca cb q L z (u 0) (u z))
      hm
  rw [← ω.setIntegral_hamiltonianCurvature_plumbedPerturbation_const hq hca hcb hcas hcbs hc hL u,
    ← integral_add hu hk]
  exact setIntegral_congr_fun hm fun z hz ↦
    ω.hamiltonianCurvature_plumbedPerturbation_add_const hq hHa hHb hHas hHbs hab hca hcb hcas
      hcbs hc hL hz (u z)

end SmoothTwoForm

/-! ### Symplectic vector spaces: the curvature of the normalized perturbation -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {ca cb : Puncture → ℝ → ℝ} {q : Puncture} {L : ℝ}

/-- **The curvature of the normalized plumbed perturbation.** At every point of the four-punctured
sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}`, the curvature of the plumbed perturbation of the Hamiltonians
`Ha r + ca r`, `Hb r + cb r` is the curvature for `Ha r`, `Hb r` plus the curvature of the plumbed
perturbation of the target-independent Hamiltonians `ca r`, `cb r`. This is the vector-space case
of `SmoothTwoForm.hamiltonianCurvature_plumbedPerturbation_add_const`. -/
theorem hamiltonianCurvature_plumbedPerturbation_add_const (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hca : ∀ r, Periodic (ca r) 1) (hcb : ∀ r, Periodic (cb r) 1)
    (hcas : ∀ r, ContDiff ℝ 1 (ca r)) (hcbs : ∀ r, ContDiff ℝ 1 (cb r)) (hc : cb q = ca inf)
    (hL : 4 < L) {z : ℝ × ℝ}
    (hz : (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t)
            q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (fun r t (_ : V) ↦ ca r t) (fun r t (_ : V) ↦ cb r t)
            q L (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_plumbedPerturbation_add_const hq hHa hHb
      (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
      (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hca hcb hcas hcbs
      hc hL hz x

/-- **Normalizing the Hamiltonians shifts the integrated curvature of the plumbed four-punctured
sphere.** Along a map whose curvature for `Ha r`, `Hb r` is integrable on the four-punctured
sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}`, the integrated curvature of the plumbed perturbation of the
Hamiltonians `Ha r + ca r`, `Hb r + cb r`, with `cb q = ca ∞`, is the integrated curvature for
`Ha r`, `Hb r` plus `∑_{r ≠ ∞} ∫₀¹ ca_r + ∑_{r ≠ q} ±∫₀¹ cb_r`, with the sign `+` on the input ends
and `-` on the output end. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_plumbedPerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_plumbedPerturbation_add_const (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hca : ∀ r, Periodic (ca r) 1) (hcb : ∀ r, Periodic (cb r) 1)
    (hcas : ∀ r, ContDiff ℝ 1 (ca r)) (hcbs : ∀ r, ContDiff ℝ 1 (cb r)) (hc : cb q = ca inf)
    (hL : 4 < L) {u : ℝ × ℝ → V}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (fun r t y ↦ Ha r t y + ca r t)
          (fun r t y ↦ Hb r t y + cb r t) q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, ca r t) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, cb r t) := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.setIntegral_hamiltonianCurvature_plumbedPerturbation_add_const hq hHa hHb
      (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
      (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hca hcb hcas hcbs
      hc hL (by simpa only [hamiltonianCurvature_constSmooth] using hu)

end SymplecticForm

end TauCeti
