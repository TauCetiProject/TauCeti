/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Normalizing the end Hamiltonians of the pair of pants

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time:
`H_q(t, x)` and `H_q(t, x) + c_q(t)` generate the same flow, have the same one-periodic orbits,
and give the same Floer equation. Their actions differ by the time average of `c_q`
(`TauCeti.SymplecticForm.hamiltonianAction_add_const`). This file shows how the energy identity
of the pair of pants

`E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`

absorbs such a change of normalization on its three ends, for a target manifold `M` with a
two-form `ω` (namespace `SmoothTwoForm`). The statements for a symplectic vector space target
(namespace `SymplecticForm`) are their specializations to the constant form
`SymplecticForm.constSmooth`, and have the same names, except that the perturbed derivative is
`perturbedFDeriv` instead of `perturbedMFDeriv`.

The pair-of-pants perturbation (`TauCeti.Floer.pairOfPantsPerturbation`) is additive in the end
Hamiltonians, so normalizing by `c` adds to it the perturbation `k` of the target-independent
Hamiltonians `c_q`, which has no Hamiltonian vector field
(`TauCeti.Floer.pairOfPantsPerturbation_add_const`). Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density
  are unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_pairOfPantsPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_pairOfPantsPerturbation_add_const`);
* the curvature changes by the curvature of `k`, which does not depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_const_target`);
* the integral of the curvature of `k` over the pair of pants is exactly the sum
  `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`
  (`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const`). This
  is the equality case of the one-sided curvature bound
  `SmoothTwoForm.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation`
  of `PairOfPants/Curvature.lean`, applied to `c_q` and `-c_q`.

So along every map whose curvature for `H_q` is integrable on `S`, the integrated curvature
changes by `∑ q, ±∫₀¹ c_q`
(`TauCeti.SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`),
which is exactly the change `∑ q, ±∫₀¹ c_q` of the Hamiltonian terms at the asymptotic orbits.
The two changes cancel in the energy identity, as they must, since the energy itself is unchanged.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

open scoped Manifold

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ}

/-! ### Changes of normalization

Changing the end Hamiltonians by functions of time, `H_q ↦ H_q + c_q(t)`, adds to the perturbation
the target-independent datum `K^c` of the functions `c_q`. It changes neither the Hamiltonian
vector fields, nor the Floer equation, nor the energy density, and it adds to the curvature the
curvature of `K^c`, whose integral over `S` is `∫₀¹ c_0 + ∫₀¹ c_1 - ∫₀¹ c_∞`. This is exactly the
change `∑ q, ±∫₀¹ c_q` of the Hamiltonian terms at the asymptotic orbits in the energy identity, so
the energy identity is invariant under the change of normalization. -/

omit [TopologicalSpace M] in
/-- Period-one functions of time `c_q` are period-one target-independent Hamiltonians. -/
private theorem periodic_const_target {c : Puncture → ℝ → ℝ} (hc : ∀ q, Periodic (c q) 1)
    (q : Puncture) : Periodic (fun t (_ : M) ↦ c q t) 1 :=
  fun t ↦ funext fun _ ↦ hc q t

omit [IsManifold I ⊤ M] in
/-- `C¹` functions of time `c_q` are `C¹` target-independent Hamiltonians. -/
private theorem contMDiff_uncurry_const_target {c : Puncture → ℝ → ℝ}
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ c q t) :=
  (hcs q).contMDiff.comp contMDiff_fst

/-- **A change of normalization does not change the perturbed derivative.** The perturbed
derivative `du - X_K` of the pair-of-pants perturbation of the Hamiltonians `H_q + c_q(t)` is that
of the Hamiltonians `H_q`, so the two data have the same Floer equation. -/
@[simp]
theorem perturbedMFDeriv_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
  rw [pairOfPantsPerturbation_add_const_fun H c _ (u z),
    pairOfPantsPerturbation_add_const_fun H c _ (u z), perturbedMFDeriv_add_const]

/-- **A change of normalization does not change the energy density.** The Floer energy density of
the pair-of-pants perturbation of the Hamiltonians `H_q + c_q(t)` is that of the Hamiltonians
`H_q`. -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (H : Puncture → ℝ → M → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def,
    ω.perturbedMFDeriv_pairOfPantsPerturbation_add_const H c u z]

/-- The curvature of the perturbation of functions of time `c_q` does not depend on the target
point. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_const_target (ω : SmoothTwoForm I M)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [pairOfPantsPerturbation_const_target_fun c _ x,
    pairOfPantsPerturbation_const_target_fun c _ x, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

/-- **A change of normalization adds a target-independent curvature.** At points of `S`, the
curvature of the pair-of-pants perturbation of the Hamiltonians `H_q + c_q(t)` is that of the
Hamiltonians `H_q` plus that of the functions of time `c_q`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {c : Puncture → ℝ → ℝ} (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q))
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hc' := periodic_const_target (M := M) hc
  have hcM := contMDiff_uncurry_const_target (I := I) (M := M) hcs
  rw [pairOfPantsPerturbation_add_const_fun H c _ x, pairOfPantsPerturbation_add_const_fun H c _ x,
    pairOfPantsPerturbation_const_target_fun c _ x, pairOfPantsPerturbation_const_target_fun c _ x,
    ω.hamiltonianCurvature_add_const
      (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz x 1)
      (differentiableAt_pairOfPantsPerturbation_domain hH hHs hz x Complex.I)
      (differentiableAt_pairOfPantsPerturbation_domain hc' hcM hz x 1)
      (differentiableAt_pairOfPantsPerturbation_domain hc' hcM hz x Complex.I),
    ω.hamiltonianCurvature_const]

/-- The curvature of the perturbation of the functions of time `-c_q` is the opposite of that of
the functions of time `c_q`. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_neg_const (ω : SmoothTwoForm I M)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ -c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ -c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      -ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  rw [pairOfPantsPerturbation_const_target_fun (fun q t ↦ -c q t) _ x,
    pairOfPantsPerturbation_const_target_fun (fun q t ↦ -c q t) _ x,
    pairOfPantsPerturbation_const_target_fun c _ x, pairOfPantsPerturbation_const_target_fun c _ x,
    ω.hamiltonianCurvature_const,
    ω.hamiltonianCurvature_const]
  simp only [pairOfPantsPerturbation_neg (fun q t (_ : M) ↦ c q t), neg_apply, fderiv_fun_neg]
  ring

/-- **The integrated curvature of the perturbation of functions of time.** Along every map `u`,
the curvature of the pair-of-pants perturbation of period-one `C¹` functions of time `c_q`, which
does not depend on the target point, integrates over `S` to `∫₀¹ c_0 + ∫₀¹ c_1 - ∫₀¹ c_∞`. It is
the equality case of the one-sided curvature bound. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SmoothTwoForm I M)
    {c : Puncture → ℝ → ℝ} (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q))
    (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  -- The curvature does not depend on the target point, so `u` may be replaced by a constant map.
  have hu : (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) = fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : M) ↦ c q t)
        (Complex.equivRealProdCLM.symm z) x Complex.I) z (u 0) :=
    funext fun z ↦ ω.hamiltonianCurvature_pairOfPantsPerturbation_const_target c z (u z) (u 0)
  rw [hu]
  have hle := ω.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation
    (periodic_const_target hc) (contMDiff_uncurry_const_target hcs)
    (fun q ↦ (hcs q).continuous.intervalIntegrable 0 1) (fun _ _ _ ↦ le_rfl)
    (continuousOn_const (c := u 0))
  have hge := ω.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation
    (h := fun q t ↦ -c q t)
    (periodic_const_target (c := fun q t ↦ -c q t) fun q t ↦ by simp only [hc q t])
    (contMDiff_uncurry_const_target (c := fun q t ↦ -c q t) fun q ↦ (hcs q).neg)
    (fun q ↦ (hcs q).continuous.neg.intervalIntegrable 0 1) (fun _ _ _ ↦ le_rfl)
    (continuousOn_const (c := u 0))
  simp only [hamiltonianCurvature_pairOfPantsPerturbation_neg_const, integral_neg,
    intervalIntegral.integral_neg, mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at hge
  exact le_antisymm hge hle

/-- **The integrated curvature under a change of normalization.** Along every map `u` whose
curvature for `H_q` is integrable on `S`, changing the period-one `C¹` end Hamiltonians `H_q` by
period-one `C¹` functions of time `c_q` changes the integrated curvature of the pair-of-pants
perturbation by `∫₀¹ c_0 + ∫₀¹ c_1 - ∫₀¹ c_∞`:

`∫_S R_{K^{H + c}}(u) = ∫_S R_{K^H}(u) + ∫₀¹ c_0 + ∫₀¹ c_1 - ∫₀¹ c_∞`.

This is the change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` at the asymptotic orbits,
so the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation` for `H + c` is
the identity for `H`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {c : Puncture → ℝ → ℝ} (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q))
    {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  -- The curvature of the functions of time does not depend on the target point, so it is
  -- integrable along `u` because it is along a constant map.
  have hk := (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω
    (periodic_const_target hc) (contMDiff_uncurry_const_target hcs) (u := fun _ ↦ u 0)
    continuousOn_const).congr_fun
    (fun z _ ↦ ω.hamiltonianCurvature_pairOfPantsPerturbation_const_target c z (u 0) (u z))
    isOpen_thricePuncturedSphereReal.measurableSet
  rw [← ω.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const hc hcs u,
    ← integral_add hu hk]
  exact setIntegral_congr_fun isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
    ω.hamiltonianCurvature_pairOfPantsPerturbation_add_const hH hHs hc hcs hz (u z)

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {c : Puncture → ℝ → ℝ}

/-- **Normalizing the end Hamiltonians does not change the Floer equation.** The perturbed
derivative `du - X_K` of any map is the same for the end Hamiltonians `H_q` and
`H_q + c_q`. -/
@[simp]
theorem perturbedFDeriv_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  rw [pairOfPantsPerturbation_add_const_fun H c _ 0, pairOfPantsPerturbation_add_const_fun H c _ 0,
    perturbedFDeriv_add_const]

/-- **Normalizing the end Hamiltonians does not change the energy density.** This is the
vector-space case of `SmoothTwoForm.floerEnergyDensity_pairOfPantsPerturbation_add_const`. -/
@[simp]
theorem floerEnergyDensity_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (H : Puncture → ℝ → V → ℝ) (c : Puncture → ℝ → ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u := by
  funext z
  rw [← floerEnergyDensity_constSmooth, ← floerEnergyDensity_constSmooth,
    SmoothTwoForm.floerEnergyDensity_pairOfPantsPerturbation_add_const]

/-- The curvature of the perturbation of target-independent Hamiltonians does not depend on the
target point. This is the vector-space case of
`SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_const_target`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_const_target (ω : SymplecticForm V)
    (c : Puncture → ℝ → ℝ) (z : ℝ × ℝ) (x y : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [← hamiltonianCurvature_constSmooth, ← hamiltonianCurvature_constSmooth,
    SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_const_target]

/-- **The curvature of the normalized perturbation.** At every point of the pair of pants, the
curvature of the perturbation of the end Hamiltonians `H_q + c_q` is the curvature for `H_q` plus
the curvature of the perturbation of the target-independent Hamiltonians `c_q`. This is the
vector-space case of `SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_add_const`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
            (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_pairOfPantsPerturbation_add_const hH
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs hz x

/-- **The integrated curvature of a normalization.** For period-one `C¹` functions `c_q` of time,
the curvature of the pair-of-pants perturbation of the target-independent Hamiltonians `c_q`
integrates over the pair of pants to `∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-`
on the output end, along any map `u`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const (ω : SymplecticForm V)
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) (u : ℝ × ℝ → V) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t (_ : V) ↦ c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  have h := ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_const hc hcs u
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **Normalizing the end Hamiltonians shifts the integrated curvature.** Along a map whose
curvature for `H_q` is integrable on the pair of pants, the integrated curvature of the
perturbation of the end Hamiltonians `H_q + c_q` is the integrated curvature for `H_q` plus
`∑ q, ±∫₀¹ c_q`, with the sign `+` on the input ends and `-` on the output end. This is also the
change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation`, so the two changes cancel
and the energy identity for `H_q + c_q` is the one for `H_q`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hcs : ∀ q, ContDiff ℝ 1 (c q)) {u : ℝ × ℝ → V}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (fun q t y ↦ H q t y + c q t)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, c q t := by
  have h := ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_add_const hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hcs
    (by simp only [hamiltonianCurvature_constSmooth]; exact hu)
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

end SymplecticForm

end TauCeti
