/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Normalization.Basic

/-!
# Normalizing the end Hamiltonians of the input-exchange family

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H_q(t, x)` and `H_q(t, x) + d_q(t)` have the same flow, the same one-periodic orbits and the same
Floer equation. This file shows how the energy identity of the input-exchange family
`K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, the family of perturbation data on
the pair of pants `S = ℂ ∖ {0, 1}` with which graded commutativity of the pair-of-pants product is
proved,

`E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_{K_c}(u)`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation`), absorbs
such a change of normalization on its three ends, for a manifold target `M` with a two-form `ω`,
such as a closed symplectic manifold, and for a symplectic vector space target.

Each member of the family is additive in the end Hamiltonians, so normalizing by `d` adds to it
the member, with the same parameter `c`, of the family of the target-independent Hamiltonians
`d_q`, which has no Hamiltonian vector field (`TauCeti.Floer.exchangePerturbation_add_const`).
Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density are
  unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_exchangePerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_exchangePerturbation_add_const`);
* on `S` the curvature changes by the curvature of the target-independent datum, which does not
  depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_exchangePerturbation_add_const`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_exchangePerturbation_const_target`);
* the curvature of the target-independent datum integrates over `S` to `∑ q, ±∫₀¹ d_q`, with the
  sign `+` on the input ends `0`, `1` and `-` on the output end `∞`, for every `c ∈ [0, 1]`
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_exchangePerturbation_const`).

So along every map `u` which is continuous on `S`, the integrated curvature changes by exactly
`∑ q, ±∫₀¹ d_q`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_exchangePerturbation_add_const`), which
is the change of the Hamiltonian terms at the asymptotic orbits: the two changes cancel in the
energy identity, as they must, since the energy itself is unchanged. The constant is the same as
for the pair of pants, whatever the position `c` of the output end.

The member `c` of the family is the pullback of the pair-of-pants datum along the diffeomorphism
`Φ_c` of `S` (`TauCeti.Floer.perturbationPullback_exchangeMap_exchangePerturbation`), and the
integrated curvature is invariant under `Φ_c`
(`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_image_exchangeMap`). The integrated
statements are therefore those of the pair of pants
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const` and
`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`),
applied to the map `u ∘ Φ_c`. The integrability that the latter needs holds along every map which
is continuous on `S`
(`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`), so no
integrability hypothesis remains. The vector-space statements are the specializations of the
manifold ones to the constant form `TauCeti.SymplecticForm.constSmooth`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti

namespace Floer

variable {M : Type*}

/-- Replacing the output Hamiltonian of target-independent Hamiltonians by `0` keeps them
target-independent. -/
private theorem update_const_target (d : Puncture → ℝ → ℝ) :
    update (fun q t (_ : M) ↦ d q t) inf 0 = fun q t (_ : M) ↦ update d inf 0 q t := by
  ext q t y
  rcases eq_or_ne q inf with rfl | hq
  · simp
  · simp [update_of_ne hq]

/-- **Normalizing the end Hamiltonians of the input-exchange family.** Adding functions `d_q` of
time to the end Hamiltonians adds the member, with the same parameter, of the input-exchange
family of the target-independent Hamiltonians `d_q`. -/
theorem exchangePerturbation_add_const (H : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ)
    (c : ℝ) (w : ℂ) (x : M) :
    exchangePerturbation (fun q t y ↦ H q t y + d q t) c w x =
      exchangePerturbation H c w x + exchangePerturbation (fun q t (_ : M) ↦ d q t) c w x := by
  have hup : update (fun q t y ↦ H q t y + d q t) inf 0 =
      update H inf 0 + update (fun q t (_ : M) ↦ d q t) inf 0 := by
    ext q t y
    rcases eq_or_ne q inf with rfl | hq
    · simp
    · simp [update_of_ne hq]
  simp only [exchangePerturbation_def, hup, pairOfPantsPerturbation_add, Pi.add_apply,
    negativePlanePerturbation_def, mul_add, add_smul]
  abel

/-- The member of the input-exchange family of target-independent Hamiltonians does not depend on
the target point. -/
theorem exchangePerturbation_const_target (d : Puncture → ℝ → ℝ) (c : ℝ) (w : ℂ) (x y : M) :
    exchangePerturbation (fun q t (_ : M) ↦ d q t) c w x =
      exchangePerturbation (fun q t (_ : M) ↦ d q t) c w y := by
  rw [exchangePerturbation_def, exchangePerturbation_def, update_const_target,
    pairOfPantsPerturbation_const_target _ _ x y]
  simp only [negativePlanePerturbation_def]

/-- The components of the member of the family of target-independent Hamiltonians, as functions
of the domain point alone: their values at any target point `y`. -/
private theorem exchangePerturbation_const_target_fun (d : Puncture → ℝ → ℝ) (c : ℝ) (y : M)
    (v : ℂ) :
    (fun z (x : M) ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
        (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [exchangePerturbation_const_target d c _ x y]

/-- The components of the normalized member are the components of the original one plus those
of the member of the family of the normalizing functions, evaluated at any target point `y`. -/
private theorem exchangePerturbation_add_const_fun (H : Puncture → ℝ → M → ℝ)
    (d : Puncture → ℝ → ℝ) (c : ℝ) (y : M) (v : ℂ) :
    (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x v +
        exchangePerturbation (fun q t (_ : M) ↦ d q t) c (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [exchangePerturbation_add_const, add_apply,
    exchangePerturbation_const_target d c _ x y]

end Floer

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ} {d : Puncture → ℝ → ℝ} {c : ℝ}

omit [IsManifold I ⊤ M] in
/-- Period-one `C¹` normalizations `d_q` give, for every parameter, a member of the family of
target-independent Hamiltonians on `M` which is `C¹` at every point of `S`. -/
private theorem contMDiffAt_exchangePerturbation_const_apply (hd : ∀ q, Periodic (d q) 1)
    (hds : ∀ q, ContDiff ℝ 1 (d q)) (c : ℝ) :
    ∀ z ∈ thricePuncturedSphereReal, ∀ x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c p.1 p.2)
      (Complex.equivRealProdCLM.symm z, x) :=
  contMDiffAt_exchangePerturbation_apply (H := fun q t (_ : M) ↦ d q t)
    (fun q t ↦ funext fun _ ↦ hd q t) (fun q ↦ (hds q).contMDiff.comp contMDiff_fst) c

/-- **Normalizing the end Hamiltonians does not change the Floer equation of the input-exchange
family.** For every member of the family, the perturbed derivative `du - X_K` of any map into `M`
is the same for the end Hamiltonians `H_q` and `H_q + d_q`. -/
@[simp]
theorem perturbedMFDeriv_exchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ) (c : ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [exchangePerturbation_add_const_fun H d c (u 0),
    exchangePerturbation_add_const_fun H d c (u 0),
    perturbedMFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density of the input-exchange
family.** -/
@[simp]
theorem floerEnergyDensity_exchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (d : Puncture → ℝ → ℝ) (c : ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [exchangePerturbation_add_const_fun H d c (u 0),
    exchangePerturbation_add_const_fun H d c (u 0),
    floerEnergyDensity_add_const]

/-- The curvature of the member of the input-exchange family of target-independent Hamiltonians
does not depend on the target point. -/
theorem hamiltonianCurvature_exchangePerturbation_const_target (ω : SmoothTwoForm I M)
    (d : Puncture → ℝ → ℝ) (c : ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [exchangePerturbation_const_target_fun d c x, exchangePerturbation_const_target_fun d c x,
    hamiltonianCurvature_const, hamiltonianCurvature_const]

/-- **The curvature of the normalized input-exchange family.** At every point of the pair of
pants, the curvature of the member `c` of the family of the end Hamiltonians `H_q + d_q` is the
curvature for `H_q` plus the curvature of the member `c` of the family of the target-independent
Hamiltonians `d_q`. -/
theorem hamiltonianCurvature_exchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (c : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hK := contMDiffAt_exchangePerturbation_apply hH hHs c z hz x
  have hk := contMDiffAt_exchangePerturbation_const_apply (I := I) hd hds c z hz x
  rw [exchangePerturbation_add_const_fun H d c x, exchangePerturbation_add_const_fun H d c x,
    hamiltonianCurvature_add_const ω (differentiableAt_domain_of_contMDiffAt hK one_ne_zero 1)
      (differentiableAt_domain_of_contMDiffAt hK one_ne_zero Complex.I)
      (differentiableAt_domain_of_contMDiffAt hk one_ne_zero 1)
      (differentiableAt_domain_of_contMDiffAt hk one_ne_zero Complex.I),
    exchangePerturbation_const_target_fun d c x, exchangePerturbation_const_target_fun d c x]

/-- **The integrated curvature of a normalization along the input-exchange family.** For
period-one `C¹` functions `d_q` of time and `0 ≤ c ≤ 1`, the curvature of the member `c` of the
input-exchange family of the target-independent Hamiltonians `d_q` on `M` integrates over the pair
of pants to `∑ q, ±∫₀¹ d_q`, with the sign `+` on the input ends and `-` on the output end, along
any map `u`. -/
theorem setIntegral_hamiltonianCurvature_exchangePerturbation_const (ω : SmoothTwoForm I M)
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t (_ : M) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  -- Transport along `Φ_c` to the pair-of-pants datum of the `d_q` and the map `u ∘ Φ_c`.
  rw [← image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁,
    ω.integral_hamiltonianCurvature_image_exchangeMap
      (contMDiffAt_exchangePerturbation_const_apply hd hds c)
      (perturbationPullback_exchangeMap_exchangePerturbation hc₀ hc₁) hc₀ hc₁ u
      isOpen_thricePuncturedSphereReal.measurableSet subset_rfl]
  exact ω.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const hd hds _

/-- **Normalizing the end Hamiltonians shifts the integrated curvature of the input-exchange
family.** Along a map `u` which is continuous on the pair of pants, for `0 ≤ c ≤ 1` the integrated
curvature of the member `c` of the family of the end Hamiltonians `H_q + d_q` is the integrated
curvature for `H_q` plus `∑ q, ±∫₀¹ d_q`, with the sign `+` on the input ends and `-` on the output
end. This is also the change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy
identity `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_exchangePerturbation`, so the
two changes cancel and the energy identity for `H_q + d_q` is the one for `H_q`. -/
theorem setIntegral_hamiltonianCurvature_exchangePerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  have hHd : ∀ q, Periodic (fun t y ↦ H q t y + d q t) 1 := fun q t ↦ funext fun y ↦ by
    simp only [hH q t, hd q t]
  have hHds : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (uncurry fun t y ↦ H q t y + d q t) := fun q ↦
    (hHs q).add ((hds q).contMDiff.comp contMDiff_fst)
  -- `u ∘ Φ_c` is continuous on `S`, since `Φ_c` is continuous and maps `S` to itself.
  have hv : ContinuousOn (u ∘ exchangeMap c) thricePuncturedSphereReal :=
    hu.comp (contDiff_exchangeMap c).continuous.continuousOn fun w hw ↦
      (exchangeMap_mem_thricePuncturedSphereReal_iff hc₀ hc₁ w).2 hw
  -- Transport both integrals along `Φ_c` and apply the pair-of-pants statement to `u ∘ Φ_c`.
  have hS := isOpen_thricePuncturedSphereReal.measurableSet
  rw [← image_exchangeMap_thricePuncturedSphereReal hc₀ hc₁,
    ω.integral_hamiltonianCurvature_image_exchangeMap
      (contMDiffAt_exchangePerturbation_apply hHd hHds c)
      (perturbationPullback_exchangeMap_exchangePerturbation hc₀ hc₁) hc₀ hc₁ u hS subset_rfl,
    ω.integral_hamiltonianCurvature_image_exchangeMap
      (contMDiffAt_exchangePerturbation_apply hH hHs c)
      (perturbationPullback_exchangeMap_exchangePerturbation hc₀ hc₁) hc₀ hc₁ u hS subset_rfl]
  exact ω.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const hH hHs hd hds
    (ω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation hH hHs hv)

end SmoothTwoForm

/-! ### Symplectic vector spaces -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {d : Puncture → ℝ → ℝ} {c : ℝ}

/-- **Normalizing the end Hamiltonians does not change the Floer equation of the input-exchange
family.** For every member of the family, the perturbed derivative `du - X_K` of any map is the
same for the end Hamiltonians `H_q` and `H_q + d_q`. -/
@[simp]
theorem perturbedFDeriv_exchangePerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (d : Puncture → ℝ → ℝ) (c : ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [exchangePerturbation_add_const_fun H d c 0, exchangePerturbation_add_const_fun H d c 0,
    perturbedFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density of the input-exchange
family.** -/
@[simp]
theorem floerEnergyDensity_exchangePerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (d : Puncture → ℝ → ℝ) (c : ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [exchangePerturbation_add_const_fun H d c 0, exchangePerturbation_add_const_fun H d c 0,
    floerEnergyDensity_add_const]

/-- **The curvature of the normalized input-exchange family.** At every point of the pair of
pants, the curvature of the member `c` of the family of the end Hamiltonians `H_q + d_q` is the
curvature for `H_q` plus the curvature of the member `c` of the family of the target-independent
Hamiltonians `d_q`. This is the vector-space case of
`SmoothTwoForm.hamiltonianCurvature_exchangePerturbation_add_const`. -/
theorem hamiltonianCurvature_exchangePerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (c : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation (fun q t (_ : V) ↦ d q t) c
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation (fun q t (_ : V) ↦ d q t) c
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_exchangePerturbation_add_const hH
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hd hds c hz x

/-- **The integrated curvature of a normalization along the input-exchange family.** For
period-one `C¹` functions `d_q` of time and `0 ≤ c ≤ 1`, the curvature of the member `c` of the
input-exchange family of the target-independent Hamiltonians `d_q` integrates over the pair of
pants to `∑ q, ±∫₀¹ d_q`, along any map `u`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_exchangePerturbation_const`. -/
theorem setIntegral_hamiltonianCurvature_exchangePerturbation_const (ω : SymplecticForm V)
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (u : ℝ × ℝ → V) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t (_ : V) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t (_ : V) ↦ d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.setIntegral_hamiltonianCurvature_exchangePerturbation_const hd hds hc₀ hc₁ u

/-- **Normalizing the end Hamiltonians shifts the integrated curvature of the input-exchange
family.** Along a map `u` which is continuous on the pair of pants, for `0 ≤ c ≤ 1` the integrated
curvature of the member `c` of the family of the end Hamiltonians `H_q + d_q` is the integrated
curvature for `H_q` plus `∑ q, ±∫₀¹ d_q`. This is also the change of the Hamiltonian terms of the
energy identity, so the energy identity for `H_q + d_q` is the one for `H_q`. This is the
vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_exchangePerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_exchangePerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hd : ∀ q, Periodic (d q) 1) (hds : ∀ q, ContDiff ℝ 1 (d q)) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V} (hu : ContinuousOn u thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation (fun q t y ↦ H q t y + d q t) c
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.setIntegral_hamiltonianCurvature_exchangePerturbation_add_const hH
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hd hds hc₀ hc₁ hu

end SymplecticForm

end TauCeti
