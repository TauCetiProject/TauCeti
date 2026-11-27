/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Normalized
public import TauCeti.Analysis.PDE.Vortex.Gauge.Cohomology
public import TauCeti.Analysis.PDE.Vortex.Kernel.Tangent
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.RingTheory.Polynomial.SymmetricPower

/-!
# The velocity of the family of plane vortices over the divisor space

For `c ∈ ℂᵐ`, `m ≥ 1`, the normalized vortex `y_c` (`TauCeti.Vortex.normalizedVortex`) is the
framed degree-`m` plane vortex whose zero divisor has the symmetric coordinates `c`, put in the
gauge whose section has the fixed winding phase at infinity. It depends smoothly on `c`, jointly in
the point (`TauCeti.Vortex.contDiff_normalizedVortex_uncurry`) and in every Sobolev space
(`TauCeti.Vortex.SobolevFieldSpace.contDiff_subRef_normalizedVortex`). This file computes its
velocity `∂_v y_c = w ↦ ∂_v (c ↦ y_c (w))` in a direction `v ∈ ℂᵐ`, in terms of the kernel of the
gauge-fixed operator `L_{y_c} = d₀* ⊕ d₁` and its divisor coordinates
`E : ker L_{y_c} ≃ ℂᵐ` (`TauCeti.Vortex.normalizedVortexKernelEquiv`, the divisor coordinates
`TauCeti.Vortex.gaugeFixedKernelEquivCoeff` at `y_c`), which identify the kernel
with the tangent space of `Sym^m ℂ` through the divisor variation
(`TauCeti.Vortex.IsDivisorVariation`):

`∂_v y_c = E⁻¹ v + d₀ u`

for a phase `u` in `H^(k+2)`
(`TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_add_gaugeDirection`).
So the abstract identification of `ker L_{y_c}` with the tangent space of the divisor space is the
derivative of the family of vortices, up to an infinitesimal gauge transformation, collisions of
zeros included. In particular the velocity is an infinitesimal gauge transformation only when
`v = 0` (`TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_gaugeDirection_iff`): the normalized
family is transverse to the gauge orbits.

The proof assembles three facts about the velocity.

* **It solves the linearized equation.** For any jointly `C²` family of plane fields `F_q` that
  solve the vortex equation near a parameter `p`, the velocity `∂_v F_p` satisfies
  `d₁ ∂_v F_p = 0` at `F_p` (`TauCeti.Vortex.linearizedEquation_fderiv_eq_zero`): differentiate the
  equation in the parameter, swapping the parameter and spatial derivatives
  (`TauCeti.fderiv_fderiv_slice_apply_comm`).
* **It lies in every Sobolev space.** The coordinates of `y_c - x_m` form a smooth family in
  `H^s(ℂ)⁴`, whose continuous representatives
  (`TauCeti.Vortex.SobolevFieldSpace.toZeroAtInfty_subRef_apply`) therefore have parameter
  derivatives in `H^s(ℂ)` (`BesselPotentialSpace.fderiv_apply_mem_realSobolevFunctions`), so the
  velocity lies in
  `H^s(ℂ)⁴` for every `s` (`TauCeti.Vortex.fderiv_normalizedVortex_mem_sobolevFields`). With the
  first point, it is a cocycle of the deformation complex at `y_c`, so it differs from an element
  of `ker L_{y_c}` by a coboundary `d₀ u`
  (`TauCeti.Vortex.exists_sub_gaugeDirection_mem_gaugeFixedKernel`).
* **Its divisor variation is `v`.** The section of `y_c` is `H_c P_c`, with `P_c` the monic
  polynomial with lower coefficients `c` and `H_c` jointly smooth and nowhere zero. Its velocity is
  `∂_v H_c P_c + H_c R_v`, where `R_v = ∂_v P_c` is the polynomial with coefficients `v`
  (`TauCeti.Polynomial.fderiv_eval_monicOfCoeff_apply`), so its divisor variation is `R_v`
  (`TauCeti.Vortex.isDivisorVariation_fderiv_of_sectionValue_eq_mul`,
  `TauCeti.Vortex.isDivisorVariation_fderiv_normalizedVortex`). Coboundaries have divisor
  variation zero (`TauCeti.Vortex.isDivisorVariation_gaugeDirection`), and `E` is characterized by
  the divisor variation (`TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_eq_iff`).

## Main definitions

* `TauCeti.Vortex.normalizedVortexKernelEquiv`: the divisor coordinates
  `E : ker L_{y_c} ≃ ℂᵐ` of the kernel of the gauge-fixed operator at `y_c`.

## Main results

* `TauCeti.Vortex.isDivisorVariation_fderiv_normalizedVortex`: the velocity of `y_c` in the
  direction `v` has divisor variation the polynomial with coefficients `v`.
* `TauCeti.Vortex.fderiv_normalizedVortex_mem_sobolevFields`: the velocity of `y_c` lies in
  `H^s(ℂ)⁴` for every `s`.
* `TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_add_gaugeDirection`: `∂_v y_c = E⁻¹ v + d₀ u`.
* `TauCeti.Vortex.exists_fderiv_normalizedVortex_eq_gaugeDirection_iff`: `∂_v y_c` is an
  infinitesimal gauge transformation exactly when `v = 0`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

open Complex Filter Topology Polynomial MeasureTheory Module TemperedDistribution
open scoped ContDiff BesselPotentialSpace

namespace TauCeti.Vortex

/-! ### The divisor variation of the velocity -/

section DivisorVariation

variable {m : ℕ}

open TauCeti.Polynomial in
/-- The section of the normalized vortex `y_c` is `g_c exp (u_c) P_c`. -/
private theorem sectionValue_normalizedVortex (c : Fin m → ℂ) (w : ℂ) :
    sectionValue (normalizedVortex c) w =
      ((polynomialGauge c w : ℂ) * (Real.exp (backgroundAmplitude (monicOfCoeff c).eval w +
        reducedSolution (monicOfCoeff c) w) : ℂ)) * (monicOfCoeff c).eval w := by
  rw [normalizedVortex_def, sectionValue_gaugeTransform, sectionValue_polynomialVortex, mul_assoc]

/-- The normalized vortices are differentiable in the divisor coordinates at every point. -/
private theorem differentiableAt_normalizedVortex_apply (c : Fin m → ℂ) (w : ℂ) :
    DifferentiableAt ℝ (fun c' ↦ normalizedVortex c' w) c :=
  (contDiff_normalizedVortex_uncurry.differentiable (by simp) (c, w)).comp
    (f := fun c' ↦ (c', w)) c (differentiableAt_id.prodMk (differentiableAt_const w))

open TauCeti.Polynomial in
/-- **The velocity of the normalized vortices moves the divisor by its coordinates.** The
velocity `∂_v y_c` of the normalized vortices in the direction `v ∈ ℂᵐ` has divisor variation the
polynomial with coefficients `v`, the velocity of the monic polynomial `P_c` with lower
coefficients `c`. -/
theorem isDivisorVariation_fderiv_normalizedVortex (c v : Fin m → ℂ) :
    IsDivisorVariation (normalizedVortex c) (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v)
      ((Sym.coeffEquiv ℂ m).symm c : Multiset ℂ) ((degreeLTEquiv ℂ m).symm v) := by
  have hP : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ (monicOfCoeff p.1).eval p.2 :=
    (contDiff_eval_monicOfCoeff contDiff_fst contDiff_snd).restrict_scalars ℝ
  refine isDivisorVariation_fderiv_of_sectionValue_eq_mul
    (H := fun c' w ↦ (polynomialGauge c' w : ℂ) * (Real.exp (backgroundAmplitude
      (monicOfCoeff c').eval w + reducedSolution (monicOfCoeff c') w) : ℂ))
    (differentiableAt_normalizedVortex_apply c)
    ?_ (fun w ↦ mul_ne_zero (Circle.coe_ne_zero _) (by exact_mod_cast (Real.exp_pos _).ne'))
    sectionValue_normalizedVortex
    (fun w ↦ ((hasFDerivAt_eval_monicOfCoeff c w).restrictScalars ℝ).differentiableAt)
    (fun w ↦ ?_) ?_
  · exact (contDiff_polynomialGauge.mul (ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
      ((contDiff_parametric_backgroundAmplitude (f := fun c' ↦ (monicOfCoeff c').eval) hP).add
        contDiff_reducedSolution_monicOfCoeff)))).of_le (by simp)
  · rw [((hasFDerivAt_eval_monicOfCoeff c w).restrictScalars ℝ).fderiv,
      ContinuousLinearMap.coe_restrictScalars', ← (hasFDerivAt_eval_monicOfCoeff c w).fderiv,
      fderiv_eval_monicOfCoeff_apply]
  · rw [← Sym.toMonic_coeffEquiv_symm, Sym.coe_toMonic, ofMultiset_apply]

end DivisorVariation

/-! ### The velocity in the kernel of the gauge-fixed operator -/

section NormalizedVortex

open BesselPotentialSpace TauCeti.Polynomial

variable {m : ℕ}

/-- **The velocity of the normalized vortices lies in every Sobolev space.** The derivative
`w ↦ ∂_v y_c (w)` of the normalized vortices `y_c` in the divisor coordinates `c`, in the direction
`v`, lies in `H^s(ℂ)⁴` for every `s`. -/
theorem fderiv_normalizedVortex_mem_sobolevFields (hm : 0 < m) (c v : Fin m → ℂ) (s : ℝ) :
    (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v) ∈ sobolevFields s := by
  refine sobolevFields_mono (le_max_left s 2) (mem_sobolevFields.2 fun j ↦ ?_)
  have hs : finrank ℝ ℂ < 2 * max s 2 := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith [le_max_right s 2]
  have hU : ContDiff ℝ ∞ fun c' ↦
      (SobolevFieldSpace.normalizedVortex hm default (max s 2) c').subRef j :=
    contDiff_pi.1 (SobolevFieldSpace.contDiff_subRef_normalizedVortex hm default
      (by positivity)) j
  have h := fderiv_apply_mem_realSobolevFunctions hs (hU.differentiable (by simp) c)
    (g := fun c' w ↦ normalizedVortex c' w j - referenceField default m w j)
    (fun c' w ↦ by
      rw [SobolevFieldSpace.toZeroAtInfty_subRef_apply hs, SobolevFieldSpace.coe_normalizedVortex])
    v
  convert h using 2 with w
  rw [fderiv_sub_const, (differentiableAt_normalizedVortex_apply c w).fderiv_piLp_apply]

/-- The velocity of the normalized vortices is smooth in the point. -/
private theorem contDiff_fderiv_normalizedVortex (c v : Fin m → ℂ) :
    ContDiff ℝ ∞ fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v := by
  have h : ContDiff ℝ ∞ (Function.uncurry fun (w : ℂ) (c' : Fin m → ℂ) ↦ normalizedVortex c' w) :=
    contDiff_normalizedVortex_uncurry.comp (contDiff_snd.prodMk contDiff_fst)
  exact (h.fderiv contDiff_const le_rfl).clm_apply contDiff_const

/-- **The divisor coordinates of the kernel at a normalized vortex.** For `m ≥ 1`, the real-linear
isomorphism `E : ker L_{y_c} ≃ ℂᵐ` sending an element of the kernel of the gauge-fixed operator at
the normalized vortex `y_c` to the coefficients of its divisor variation: the divisor coordinates
`TauCeti.Vortex.gaugeFixedKernelEquivCoeff` at `y_c`. -/
def normalizedVortexKernelEquiv (hm : 0 < m) (c : Fin m → ℂ) :
    gaugeFixedKernel (normalizedVortex c) ≃ₗ[ℝ] (Fin m → ℂ) :=
  gaugeFixedKernelEquivCoeff (contDiff_normalizedVortex c)
    (fun w ↦ by simp [equation_normalizedVortex hm c w]) (tendsto_normSq_normalizedVortex hm c)
    (isZeroMultiplicity_sectionValue_normalizedVortex c)

/-- **The velocity of the normalized vortices is the kernel field of its divisor coordinates, up
to gauge.** Let `y_c` be the normalized vortex with divisor coefficients `c ∈ ℂᵐ`, `m ≥ 1`, and let
`E : ker L_{y_c} ≃ ℂᵐ` be the divisor coordinates of the kernel of its gauge-fixed operator
(`TauCeti.Vortex.normalizedVortexKernelEquiv`). For every direction `v ∈ ℂᵐ` and every `k ≥ 3`, the
velocity `∂_v y_c` of the family is the kernel field `E⁻¹ v` plus an infinitesimal gauge
transformation `d₀ u` with `u ∈ H^(k+2)` of class `C³`. -/
theorem exists_fderiv_normalizedVortex_eq_add_gaugeDirection (hm : 0 < m) {k : ℕ} (hk : 3 ≤ k)
    (c v : Fin m → ℂ) :
    ∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧
      (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v) =
        ((normalizedVortexKernelEquiv hm c).symm v : ℂ → EuclideanSpace ℝ (Fin 4)) +
          gaugeDirection (normalizedVortex c) u := by
  set δ := fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v
  have hsol := equation_normalizedVortex hm c
  -- The velocity is a cocycle of the deformation complex.
  have hcoc : δ ∈ deformationCocycles (normalizedVortex c) k := mem_deformationCocycles.2
    ⟨fderiv_normalizedVortex_mem_sobolevFields hm c v _,
      (contDiff_fderiv_normalizedVortex c v).of_le (by simp), fun w ↦
        linearizedEquation_fderiv_eq_zero
          (contDiff_normalizedVortex_uncurry.contDiffAt.of_le (by simp))
          (.of_forall fun c' ↦ equation_normalizedVortex hm c' w) v⟩
  obtain ⟨u, hu, hu3, hK⟩ := exists_sub_gaugeDirection_mem_gaugeFixedKernel hk
    (normalizedVortex_mem_framedFieldSpace hm default c _) (contDiff_normalizedVortex c).continuous
    hsol hcoc
  refine ⟨u, hu, hu3, ?_⟩
  -- Its harmonic representative has divisor variation `v`.
  have hdiv : IsDivisorVariation (normalizedVortex c) (δ - gaugeDirection (normalizedVortex c) u)
      ((Sym.coeffEquiv ℂ m).symm c : Multiset ℂ) ((degreeLTEquiv ℂ m).symm v) := by
    have h := (isDivisorVariation_fderiv_normalizedVortex c v).add
      ((isDivisorVariation_gaugeDirection _ hu3.continuous _).smul (-1))
    simpa [sub_eq_add_neg] using h
  have hE : (normalizedVortexKernelEquiv hm c).symm v = ⟨_, (Submodule.mem_inf.1 hK).left⟩ := by
    rw [LinearEquiv.symm_apply_eq, normalizedVortexKernelEquiv, gaugeFixedKernelEquivCoeff_apply,
      (gaugeFixedKernelEquivDegreeLT_eq_iff _ _ _ _).2 hdiv, LinearEquiv.apply_symm_apply]
  rw [hE]
  simp

/-- **The normalized family is transverse to the gauge orbits.** For `m ≥ 1` and `k ≥ 3`, the
velocity `∂_v y_c` of the normalized vortices is an infinitesimal gauge transformation `d₀ u`, with
`u ∈ H^(k+2)` of class `C³`, only for `v = 0`. -/
theorem exists_fderiv_normalizedVortex_eq_gaugeDirection_iff (hm : 0 < m) {k : ℕ} (hk : 3 ≤ k)
    (c v : Fin m → ℂ) :
    (∃ u ∈ realSobolevFunctions ℂ (k + 2) 2, ContDiff ℝ 3 u ∧
      (fun w ↦ fderiv ℝ (fun c' ↦ normalizedVortex c' w) c v) =
        gaugeDirection (normalizedVortex c) u) ↔ v = 0 := by
  refine ⟨fun ⟨u', hu', hu'3, hδ'⟩ ↦ ?_, fun hv ↦ ⟨0, zero_mem _, contDiff_const, ?_⟩⟩
  · obtain ⟨u, hu, hu3, hδ⟩ := exists_fderiv_normalizedVortex_eq_add_gaugeDirection hm hk c v
    set E := normalizedVortexKernelEquiv hm c
    -- `E⁻¹ v = d₀ (u' - u)` is a coboundary in the kernel of `L_{y_c}`, hence zero.
    have hB : (E.symm v : ℂ → EuclideanSpace ℝ (Fin 4)) ∈
        deformationCoboundaries (normalizedVortex c) k := by
      refine mem_deformationCoboundaries.2 ⟨u' - u, sub_mem hu' hu, hu'3.sub hu3, funext fun w ↦ ?_⟩
      rw [gaugeDirection_sub _ (hu'3.differentiable (by simp) w) (hu3.differentiable (by simp) w),
        ← congrFun hδ' w, congrFun hδ w]
      simp
    have h0 := eq_zero_of_mem_gaugeFixedKernel_of_mem_deformationCoboundaries (E.symm v).property hB
    simpa using congrArg E (Subtype.ext h0 : E.symm v = 0)
  · subst hv
    rw [gaugeDirection_zero]
    ext w : 1
    simp

end NormalizedVortex

end TauCeti.Vortex
