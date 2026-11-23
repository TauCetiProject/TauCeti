/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.CappedAction
public import TauCeti.Geometry.Symplectic.Floer.Plane.Orbit.Manifold
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# The energy of a PSS plane in a manifold at its asymptotic orbit

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one `C¹` Hamiltonian `H` on a finite-dimensional manifold `M` with a nondegenerate two-form
`ω`, such as a closed symplectic manifold, and let `ε = ±1` be the sign of the end of `p`. For a map
`u` of the plane and `R ∈ ℝ` write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`ε s = R` of the end, where `φ(z) = exp (2π ε z)` is the end lift, and `D_R` for the disc
`‖w‖ ≤ exp (2πR)` that this circle bounds. On each disc, for `R ≥ 2`, the energy of `u` is

`∫_{D_R} E = ∫_{D_R} u^*ω + ε ∫₀¹ H(t, ℓ_R(t)) dt - ∫_ℂ R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`), and
the right-hand side is `ε` times the capped action `A_H(ℓ_R, u ∘ endDisc R)` of the loop, capped by
the disc of the plane that it bounds, minus the integrated curvature
(`integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction` in
`TauCeti.SmoothTwoForm.IsNondegenerate`).
This file passes to the limit `R → ∞`.

* **The capped end actions converge.** If the energy density of `u` is integrable over the plane,
  the capped actions `A_H(ℓ_R, u ∘ endDisc R)` converge as `R → ∞`, to `ε (∫ E + ∫ R_K(u))`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.tendsto_cappedLoopAction_pssPlanePerturbation`). No
  equation is needed: the discs `D_R` exhaust the plane.
* **The energy at the asymptotic loop.** If moreover the area density `u^*ω` is integrable over the
  plane, and the loops `ℓ_{R_i}` converge pointwise to a loop `x` along some `R_i → ∞` with
  `|H(t, ℓ_{R_i}(t))| ≤ B` for `t ∈ [0, 1]`, then
  `∫ E = ∫ u^*ω + ε ∫₀¹ H(t, x(t)) dt - ∫ R_K(u)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation`), and
  the capped end actions converge to the capped action `ε ∫ u^*ω + ∫₀¹ H(t, x(t)) dt` of `x`, capped
  by the whole plane
  (`IsNondegenerate.tendsto_cappedLoopAction_pssPlanePerturbation_of_tendsto` in
  `TauCeti.SmoothTwoForm`). For a solution of the Floer equation with almost complex structures
  tamed by `ω` and `|H| ≤ B` everywhere, the energy is nonnegative, so `ε` times this capped action
  is bounded below:
  `-B ≤ ∫ u^*ω + ε ∫₀¹ H(t, x(t)) dt`
  (`neg_le_integral_add_endSign_mul_intervalIntegral_pssPlanePerturbation` in
  `TauCeti.SmoothTwoForm.IsNondegenerate`). On the negative plane, which caps an output orbit, this
  says that the capped action of the output is at most `B`.
* **For finite-energy planes.** A finite-energy solution of the Floer equation with image in a
  compact set breaks off a one-periodic orbit `x` at its end, along some sequence of radii
  (`exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact` in
  `TauCeti.SmoothTwoForm.IsNondegenerate`). Hence its energy is given by the identity above at the
  orbit `x`, and its capped end actions converge to the capped action of `x`
  (`exists_mem_periodicSolutions_integral_floerEnergyDensity_pssPlanePerturbation_eq` in
  `TauCeti.SmoothTwoForm.IsNondegenerate`).

So the energy of a finite-energy PSS plane is its topological energy at its asymptotic orbit, with
the plane itself as the cap of that orbit, corrected by the curvature of the perturbation. The
convergence of the capped actions, a hypothesis of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, is derived
here from the integrability of the energy density. On a symplectic vector space the same identity
is `exists_periodic_hasDerivAt_lintegral_floerEnergyDensity_pssPlanePerturbation_eq` in
`TauCeti.SymplecticForm`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  energy of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity of perturbed pseudoholomorphic curves.
-/

public section

open Set Real Function MeasureTheory Filter
open scoped Topology Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer Floer.PSSPlane

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {p : PSSPlane} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- The discs `D_R = {‖w‖ ≤ exp (2πR)}` of the plane exhaust it as `R → ∞`. -/
private theorem aecover_closedBall_exp {ι : Type*} {l : Filter ι} {R : ι → ℝ}
    (hR : Tendsto R l atTop) :
    AECover volume l fun i ↦
      Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R i)) :=
  aecover_preimage_closedBall Complex.equivRealProdCLM.symm.continuous
    (Real.tendsto_exp_atTop.comp (hR.const_mul_atTop Real.two_pi_pos))

/-- **The capped end actions of a PSS plane in a manifold converge.** Let `K` be the perturbation
of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional manifold with a
nondegenerate two-form `ω`, and let `u` be a `C¹` map whose Floer energy density is integrable over
the plane. Then the capped actions `A_H(ℓ_R, u ∘ endDisc R)` of the loops
`ℓ_R(t) = u(φ(ε R + i t))`, each capped by the disc of the plane that it bounds, converge as
`R → ∞` to `ε (∫ E + ∫ R_K(u))`. Here `ε` is the sign of the end of the plane and
`φ(z) = exp (2π ε z)` is the end lift. -/
theorem tendsto_cappedLoopAction_pssPlanePerturbation (hω : ω.IsNondegenerate)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)) :
    Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
      (𝓝 (p.endSign * ((∫ z, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) +
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z
          (u z)))) := by
  -- On `D_R`, `R ≥ 2`, the energy is `ε` times the capped action minus the curvature, so the
  -- capped action is `ε` times the energy over `D_R` plus the curvature, and `ε² = 1`.
  refine ((((aecover_closedBall_exp tendsto_id).integral_tendsto_of_countably_generated
    hE).add_const _).const_mul p.endSign).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with R hR
  rw [id,
    hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs hu hR, sub_add_cancel, ← mul_assoc, endSign_mul_endSign, one_mul]

/-- **The energy identity of a PSS plane in a manifold at its asymptotic loop.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, and let `u` be a `C¹` map whose Floer energy density
and symplectic area density are integrable over the plane. If along a countably generated filter
`R i → ∞` and the loops `ℓ_{R i}(t) = u(φ(ε R i + i t))` converge pointwise to a loop `x`, with
`|H(t, ℓ_{R i}(t))| ≤ B` for `t ∈ [0, 1]` eventually, then

`∫ E = ∫ u^*ω + ε ∫₀¹ H(t, x(t)) dt - ∫ R_K(u)`

over the plane. Here `ε` is the sign of the end of the plane and `φ(z) = exp (2π ε z)` is the end
lift. The loops need only converge along sequences, as they do at the end of a finite-energy PSS
plane before nondegeneracy is used. -/
theorem integral_floerEnergyDensity_pssPlanePerturbation {ι : Type*} (hω : ω.IsNondegenerate)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {R : ι → ℝ} (hR : Tendsto R l atTop) {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun i ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R i) + ↑t * Complex.I)))) l (𝓝 (x t))) {B : ℝ}
    (hB : ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, |H t (u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R i) + ↑t * Complex.I))))| ≤ B)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        p.endSign * (∫ t in 0..1, H t (x t)) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hcover := aecover_closedBall_exp hR
  -- Along the converging loops, the Hamiltonian terms converge by dominated convergence.
  have hloop : Tendsto (fun i ↦ ∫ t in 0..1, H t (u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R i) + ↑t * Complex.I))))) l
      (𝓝 (∫ t in 0..1, H t (x t))) :=
    tendsto_intervalIntegral_comp_of_tendsto_of_norm_le (Φ := uncurry H) hHs.continuous
      (Eventually.of_forall fun i ↦ (hu.continuous.comp (Complex.equivRealProdCLM.continuous.comp
        ((p.contDiff_cylindricalEndLift (n := 0)).continuous.comp (by fun_prop)))).continuousOn)
      (hB.mono fun i hi t ht ↦ (Real.norm_eq_abs _).trans_le
        (hi t (Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)))) fun t _ ↦ hx t
  -- Both sides are limits of the two sides of the identity on the discs `D_{R i}`, `R i ≥ 2`.
  refine tendsto_nhds_unique (hcover.integral_tendsto_of_countably_generated hE) ?_
  refine (((hcover.integral_tendsto_of_countably_generated hA).add
    (hloop.const_mul p.endSign)).sub_const _).congr' ?_
  filter_upwards [hR.eventually_ge_atTop 2] with i hi
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall hH hHs hu (by linarith),
    smoothTransition.one_of_one_le (by linarith), mul_one,
    ω.setIntegral_hamiltonianCurvature_pssPlanePerturbation_closedBall hH hHs u hi]

/-- **The capped end actions of a PSS plane converge to the capped action of its asymptotic
loop.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation`, the capped actions
`A_H(ℓ_R, u ∘ endDisc R)` of the loops `ℓ_R(t) = u(φ(ε R + i t))`, each capped by the disc of the
plane that it bounds, converge as `R → ∞` to

`ε ∫ u^*ω + ∫₀¹ H(t, x(t)) dt`,

the capped action of the asymptotic loop `x` capped by the whole plane, oriented as the end of the
plane. -/
theorem tendsto_cappedLoopAction_pssPlanePerturbation_of_tendsto {ι : Type*}
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {R : ι → ℝ} (hR : Tendsto R l atTop) {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun i ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R i) + ↑t * Complex.I)))) l (𝓝 (x t))) {B : ℝ}
    (hB : ∀ᶠ i in l, ∀ t ∈ Icc (0 : ℝ) 1, |H t (u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R i) + ↑t * Complex.I))))| ≤ B)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) :
    Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
      (𝓝 (p.endSign * (∫ z, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∫ t in 0..1, H t (x t))) := by
  convert hω.tendsto_cappedLoopAction_pssPlanePerturbation hH hHs hu hE using 2
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation hH hHs hu hR hx hB hE hA, sub_add_cancel,
    mul_add, ← mul_assoc, endSign_mul_endSign, one_mul]

/-- **The capped action bound at the asymptotic loop of a PSS plane.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation`, with `|H| ≤ B`
everywhere, if `u` solves the Floer equation `(du - X_K)^{0,1} = 0` on the plane for almost complex
structures `J(z)` tamed by `ω`, then its energy is nonnegative and its integrated curvature is at
most `B`, so

`-B ≤ ∫ u^*ω + ε ∫₀¹ H(t, x(t)) dt`.

This is `ε` times the capped action of `x` capped by the plane: on the negative plane the capped
action of its output loop is at most `B`, and on the positive plane that of its input loop is at
least `-B`. -/
theorem neg_le_integral_add_endSign_mul_intervalIntegral_pssPlanePerturbation {ι : Type*}
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {R : ι → ℝ} (hR : Tendsto R l atTop)
    {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun i ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R i) + ↑t * Complex.I)))) l (𝓝 (x t)))
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) :
    -B ≤ (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
      p.endSign * ∫ t in 0..1, H t (x t) := by
  -- `-B ≤ ε a` for the limit `a` of the capped end actions, and `ε² = 1`.
  have := hω.neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation hH hHs hB hu hJ
    hfloer (hω.tendsto_cappedLoopAction_pssPlanePerturbation_of_tendsto hH hHs hu hR hx
      (Eventually.of_forall fun _ _ _ ↦ hB _ _) hE hA)
  rwa [mul_add, ← mul_assoc, endSign_mul_endSign, one_mul] at this

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {e : M → F}

/-- **The energy of a finite-energy PSS plane in a manifold at its asymptotic orbit.** Let `𝔎` be
the perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`. Let `u` be a `C¹` map with image in a compact set `K`,
solving the Floer equation `(du - X_𝔎)^{0,1} = 0` on the plane for almost
complex structures `J(z)`, whose Floer energy density and symplectic area density are integrable
over the plane. Let `e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on
`K` and with injective differential at the points of `K`, and suppose that the structures are
uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J(z) v)` with `c > 0`. Then there is a
one-periodic orbit `x` of the Hamiltonian vector field in `K` at which

`∫ E = ∫ u^*ω + ε ∫₀¹ H(t, x(t)) dt - ∫ R_𝔎(u)`,

and the capped actions `A_H(ℓ_R, u ∘ endDisc R)` of the loops `ℓ_R(t) = u(φ(ε R + i t))`, each
capped by the disc of the plane that it bounds, converge as `R → ∞` to the capped action
`ε ∫ u^*ω + ∫₀¹ H(t, x(t)) dt` of `x` capped by the plane. Here `ε` is the sign of the end of the
plane and `φ(z) = exp (2π ε z)` is the end lift. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pssPlanePerturbation_eq
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ q ∈ K, Injective (mvfderiv I e q)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (huK : ∀ z, u z ∈ K) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ}
    (hc : 0 < c) (hJc : ∀ z v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∫ z, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          p.endSign * (∫ t in 0..1, H t (x t)) -
          ∫ z, ω.hamiltonianCurvature
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z
            (u z) ∧
      Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
        (𝓝 (p.endSign * (∫ z, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∫ t in 0..1, H t (x t))) := by
  -- The end of `u` breaks off an orbit `x` along some radii `R n → ∞`.
  obtain ⟨x, hx, hxK, R, hR, -, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation_of_isCompact p hH hHs he
      hK he_inj hde (r := 0) hu.contMDiffOn (fun z _ ↦ huK z) J hc (fun z _ ↦ hJc z)
      (fun z _ ↦ hfloer z) ((setLIntegral_le_lintegral _ _).trans_lt hE.lintegral_lt_top).ne
  -- `H` is bounded on `[0, 1] × K`, which contains the graphs of the end loops.
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hHs.continuous.continuousOn
  have hBu (z) : ∀ t ∈ Icc (0 : ℝ) 1, |H t (u z)| ≤ B := fun t ht ↦
    (Real.norm_eq_abs _).symm.trans_le (hB (t, u z) ⟨ht, huK z⟩)
  exact ⟨x, hx, hxK, hω.integral_floerEnergyDensity_pssPlanePerturbation hH hHs hu hR hpt
      (.of_forall fun _ t ↦ hBu _ t) hE hA,
    hω.tendsto_cappedLoopAction_pssPlanePerturbation_of_tendsto hH hHs hu hR hpt
      (.of_forall fun _ t ↦ hBu _ t) hE hA⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
