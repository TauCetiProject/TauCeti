/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# The energy identity on the pair of pants

Let `K` be a `C¹` Hamiltonian perturbation datum on the pair of pants `S = ℂ ∖ {0, 1}` which is
`H_q(t) dt` beyond some height `T₀` on each of its three ends, for continuous period-one
Hamiltonians `H_q`, and let `u` be a `C²` map from `S` to a symplectic vector space `(V, ω)`.
Assume that on each end `q` the actions `A_{H_q}` of the loops `t ↦ u(φ_q(s, t))`
(`TauCeti.SymplecticForm.hamiltonianAction`) converge to a limit `A_q` as the signed longitudinal
coordinate `±s` tends to infinity. This file proves the energy identity of the pair-of-pants
product,

`E(u) = A₀ + A₁ - A_∞ - ∫_S R_K(u)`,

where `E(u)` is the integral of the Floer energy density and `R_K` is the curvature of `K`. It
holds when the energy density and the curvature term are integrable, and also when the energy
density is merely nonnegative, as it is for a solution of the Floer equation, and the curvature
term is integrable; then the energy is finite. The two positive ends at `0` and `1` are the inputs
and the negative end at `∞` is the output. The actions cap each loop by the cone over it, which
fixes the area convention. Two caps of a loop differ by a sphere, and every sphere in `V` has area
zero because the symplectic form of a vector space is exact, `ω = dλ`. So the actions do not
depend on the caps, and the spherical correction `ω(A)` of a product coefficient vanishes.

Below the height `T₀`, `K` is only required to be `C¹`; beyond `T₀` it must equal `H_q(t) dt`.
The identity therefore covers the pair-of-pants perturbation
`TauCeti.Floer.pairOfPantsPerturbation`, the family obtained from it by inserting continuation
necks on the ends, and its sums with compactly supported variations of the Hamiltonian term in the
core of `S`, such as the variations used to achieve transversality.

The same argument applies to a map `u` which is `C¹` on `S`, with values in a finite-dimensional
manifold `M` with a nondegenerate two-form `ω`, such as a closed symplectic manifold, for `K` which
is `C¹` on `S × M`. As `ω` need not be exact, the area `∫ u^*ω` stays a separate term: if on each
end `q` the integrals `∫₀¹ H_q(t, u(φ_q(s, t))) dt` tend to `h_q` as `±s → ∞`, then
`E(u) = ∫ u^*ω + h₀ + h₁ - h_∞ - ∫_S R_K(u)`, for integrable area density and curvature term.

## Main results

* `SymplecticForm.integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm`:
  the energy identity for an integrable energy density, in terms of the limits of the end-loop
  actions.
* `SymplecticForm.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`,
  `SymplecticForm.integrable_floerEnergyDensity_of_eq_smul_endAngularForm`: the energy identity
  for a nonnegative energy density, which is then integrable.
* `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_eq_sum_hamiltonianAction`:
  the energy identity for the pair-of-pants perturbation.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`: the
  energy identity for a manifold target and an integrable energy density, in terms of the area
  and the limits of the end-loop integrals of the Hamiltonians.
* `SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`,
  `SmoothTwoForm.IsNondegenerate.integrable_floerEnergyDensity_of_eq_smul_endAngularForm`: the
  energy identity for a manifold target and a nonnegative energy density, which is then
  integrable.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations on punctured surfaces.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends and their energy.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/- Proof outline. The proof does not need Stokes' theorem on the non-rectangular core of `S`.
Pointwise, the energy density plus the curvature is the exterior derivative of the one-form
`α = K(u) + λ(u)`, where `λₓ(v) = ½ ω(x, v)` is the primitive of `ω`
(`TauCeti.SymplecticForm.floerEnergyDensity_add_hamiltonianCurvature_eq`). Multiply by the smooth
cutoff `χ_T = ∏_q (1 - β(±s_q - T))`, which is compactly supported in `S` and equal to `1`
away from the parts `±s_q > T` of the ends. Integration by parts on the plane gives
`∫ χ_T (e + R_K(u)) = -∫ dχ_T ∧ α` for the energy density `e`. The two-form `dχ_T ∧ α` is
supported in the collars `T ≤ ±s_q ≤ T + 1`, where `K = H_q dt` once `T ≥ T₀`. Transported to
the coordinates of the ends, the collar integrals are the averages `±∫ β'(±s - T) A_{H_q}(s) ds`
of the loop actions. Letting `T → ∞`, dominated convergence and the convergence of the actions
give the identity. For a nonnegative energy density, monotone convergence replaces dominated
convergence on the energy side, since `χ_T` increases with `T`. For a manifold target the
one-form is `α = K(u)` alone, the area density `ω(∂_s u, ∂_t u)` is kept as a separate term, and
the collar integrals are the averages `±∫ β'(±s - T) h_q(s) ds` of the end-loop integrals
`h_q(s) = ∫₀¹ H_q(t, u(φ_q(s, t))) dt`. -/

section Cutoff

/-- The signed longitudinal coordinate `±s_q` of the end `q`, at a point of `ℝ × ℝ ≃ ℂ`. -/
private noncomputable def endHeight (q : Puncture) (z : ℝ × ℝ) : ℝ :=
  q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re

/-- The cutoff truncating the pair of pants at height `T` on each end: the product over the three
ends of `1 - β(±s_q - T)`, and `0` at the punctures `0` and `1`. -/
private noncomputable def truncation (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  if Complex.equivRealProdCLM.symm z = 0 ∨ Complex.equivRealProdCLM.symm z = 1 then 0
  else ∏ q, (1 - smoothTransition (endHeight q z - T))

private theorem contDiffAt_endHeight (q : Puncture) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (endHeight q) z := by
  unfold endHeight
  exact contDiffAt_const.mul ((q.contDiffAt_re_endCoord hz).comp z
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt)

/-- The cutoff at height `T` vanishes off the compact truncation `S_{T+1}`. -/
private theorem truncation_eq_zero_of_notMem {T : ℝ} {z : ℝ × ℝ}
    (hz : z ∉ Complex.equivRealProdCLM.symm ⁻¹' ThricePuncturedSphere.truncation (T + 1)) :
    truncation T z = 0 := by
  rw [truncation]
  split_ifs with h
  · rfl
  · obtain ⟨q, hq⟩ : ∃ q, T + 1 < endHeight q z := by
      by_contra! h'
      exact hz (mem_truncation.2 ⟨(not_or.1 h).1, (not_or.1 h).2, h'⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ q) ?_
    rw [smoothTransition.one_of_one_le (by linarith), sub_self]

/-- The cutoff vanishes near the punctures `0` and `1`. -/
private theorem truncation_eventuallyEq_zero (T : ℝ) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z = 0 ∨ Complex.equivRealProdCLM.symm z = 1) :
    truncation T =ᶠ[𝓝 z] 0 := by
  have hz' : z ∉ Complex.equivRealProdCLM.symm ⁻¹' ThricePuncturedSphere.truncation (T + 1) :=
    ThricePuncturedSphere.notMem_truncation_of_eq_zero_or_eq_one hz _
  filter_upwards [(isCompact_preimage_truncation (T + 1)).isClosed.isOpen_compl.mem_nhds hz']
    with z' hz' using truncation_eq_zero_of_notMem hz'

private theorem hasCompactSupport_truncation (T : ℝ) : HasCompactSupport (truncation T) :=
  HasCompactSupport.intro (isCompact_preimage_truncation (T + 1))
    fun _ hz ↦ truncation_eq_zero_of_notMem hz

/-- On the thrice-punctured sphere the cutoff is given by its product formula nearby. -/
private theorem truncation_eventuallyEq_prod (T : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    truncation T =ᶠ[𝓝 z] fun z' ↦ ∏ q, (1 - smoothTransition (endHeight q z' - T)) := by
  filter_upwards [isOpen_thricePuncturedSphereReal.mem_nhds hz] with z' hz'
  rw [truncation, ite_eq_right (not_or.2 (mem_thricePuncturedSphereReal_iff.1 hz'))]

private theorem contDiff_truncation (T : ℝ) : ContDiff ℝ 1 (truncation T) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : Complex.equivRealProdCLM.symm z = 0 ∨ Complex.equivRealProdCLM.symm z = 1
  · exact contDiffAt_const.congr_of_eventuallyEq (truncation_eventuallyEq_zero T hz)
  · have hz' := not_or.1 hz
    refine ContDiffAt.congr_of_eventuallyEq ?_
      (truncation_eventuallyEq_prod T (mem_thricePuncturedSphereReal_iff.2 hz'))
    exact contDiffAt_prod fun q _ ↦ contDiffAt_const.sub
      (smoothTransition.contDiffAt.comp z
        ((contDiffAt_endHeight q (ne_endCenter hz' q)).sub contDiffAt_const))

/-- The support of the cutoff stays away from the punctures. -/
private theorem mem_tsupport_truncation {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ tsupport (truncation T)) :
    z ∈ thricePuncturedSphereReal := by
  by_contra h
  rw [mem_thricePuncturedSphereReal_iff, not_and_or, not_not, not_not] at h
  exact (notMem_tsupport_iff_eventuallyEq.2 (truncation_eventuallyEq_zero T h)) hz

private theorem truncation_mem_Icc (T : ℝ) (z : ℝ × ℝ) : truncation T z ∈ Icc 0 1 := by
  rw [truncation]
  split_ifs
  · simp
  · exact ⟨Finset.prod_nonneg fun q _ ↦ sub_nonneg.2 (smoothTransition.le_one _),
      Finset.prod_le_one₀ (fun q _ ↦ sub_nonneg.2 (smoothTransition.le_one _))
        fun q _ ↦ sub_le_self _ (smoothTransition.nonneg _)⟩

/-- At a point of the thrice-punctured sphere where every end height is below `T`, the cutoff
is `1` nearby. -/
private theorem truncation_eventuallyEq_one {T : ℝ} {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hT : ∀ q, endHeight q z < T) : truncation T =ᶠ[𝓝 z] fun _ ↦ 1 := by
  have hev : ∀ᶠ z' in 𝓝 z, ∀ q, endHeight q z' < T := eventually_all.2 fun q ↦
    (contDiffAt_endHeight q (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)
      (n := 0)).continuousAt.eventually (gt_mem_nhds (hT q))
  filter_upwards [truncation_eventuallyEq_prod T hz, hev] with z' h₁ h₂
  rw [h₁]
  exact Finset.prod_eq_one fun q _ ↦ by
    rw [smoothTransition.zero_of_nonpos (by linarith [h₂ q]), sub_zero]

/-- As the height tends to infinity, the cutoff tends to `1` on the thrice-punctured sphere. -/
private theorem tendsto_truncation {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) :
    Tendsto (fun T ↦ truncation T z) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_all.2 fun q ↦ eventually_ge_atTop (endHeight q z)] with T hT
  rw [truncation, ite_eq_right (not_or.2 (mem_thricePuncturedSphereReal_iff.1 hz))]
  exact (Finset.prod_eq_one fun q _ ↦ by
    rw [smoothTransition.zero_of_nonpos (by linarith [hT q]), sub_zero]).symm

/-- The end height at the image of a cylinder point is its signed longitudinal coordinate. -/
private theorem endHeight_endChart (q : Puncture) (ζ : ℝ × ℝ) :
    endHeight q (endChart q ζ) = q.endSign * ζ.1 := by
  rw [endHeight, re_endCoord_endChart]

/-- Along the end `q`, where `±s > 0`, the cutoff at height `T ≥ 0` is `1 - β(±s - T)`. -/
private theorem truncation_endChart {T : ℝ} (hT : 0 ≤ T) {q : Puncture} {ζ : ℝ × ℝ}
    (hζ : 0 < q.endSign * ζ.1) :
    truncation T (endChart q ζ) = 1 - smoothTransition (q.endSign * ζ.1 - T) := by
  have hw := equivRealProdCLM_symm_endChart q ζ
  have hζ' : 0 < q.endSign * (Complex.equivRealProdCLM.symm ζ).re := by simpa using hζ
  have hS := q.cylindricalEndLift_ne_zero_and_ne_one hζ'
  have hr (r : Puncture) (hr : r ≠ q) : endHeight r (endChart q ζ) ≤ 0 :=
    endSign_mul_re_endCoord_nonpos hr.symm (by rwa [re_endCoord_endChart])
  rw [truncation, ite_eq_right (by rw [hw]; exact not_or.2 hS), Finset.prod_eq_single q,
    endHeight_endChart]
  · intro r _ hrq
    rw [smoothTransition.zero_of_nonpos (by linarith [hr r hrq]), sub_zero]
  · simp

end Cutoff

section Parts

variable {K : ℂ → V → ℂ →L[ℝ] ℝ} {u : ℝ × ℝ → V}

/-- The `ds` component `K_s(u) + ½ ω(u, ∂_s u)` of the one-form `α = K(u) + λ(u)` on the pair of
pants, in the global coordinate. -/
private noncomputable def primitiveS (ω : SymplecticForm V) (K : ℂ → V → ℂ →L[ℝ] ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  K (Complex.equivRealProdCLM.symm z) (u z) 1 +
    1 / 2 * ω (u z) (fderiv ℝ u z stdComplexLineReal)

/-- The `dt` component `K_t(u) + ½ ω(u, ∂_t u)` of the one-form `α = K(u) + λ(u)` on the pair of
pants, in the global coordinate. -/
private noncomputable def primitiveT (ω : SymplecticForm V) (K : ℂ → V → ℂ →L[ℝ] ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  K (Complex.equivRealProdCLM.symm z) (u z) Complex.I +
    1 / 2 * ω (u z) (fderiv ℝ u z stdComplexLineImag)

omit [FiniteDimensional ℝ V] in
/-- The perturbation evaluated along a `C¹` map is `C¹` on the thrice-punctured sphere. -/
private theorem contDiffAt_perturbation_comp
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hu : ContDiffAt ℝ 1 u z) (v : ℂ) :
    ContDiffAt ℝ 1 (fun z ↦ K (Complex.equivRealProdCLM.symm z) (u z) v) z :=
  (hK _ hz (u z) v).comp (f := fun z ↦ (z, u z)) z (contDiffAt_id.prodMk hu)

private theorem contDiffOn_primitiveS (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) :
    ContDiffOn ℝ 1 (primitiveS ω K u) thricePuncturedSphereReal := fun z hz ↦ by
  have hu' := hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)
  exact ((contDiffAt_perturbation_comp hK hz (hu'.of_le one_le_two) 1).add
    (contDiffAt_const.mul (ω.toBilinForm.toContinuousBilinearMap.contDiffAt_bilinear_fderiv_apply
      hu' _))).contDiffWithinAt

private theorem contDiffOn_primitiveT (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) :
    ContDiffOn ℝ 1 (primitiveT ω K u) thricePuncturedSphereReal := fun z hz ↦ by
  have hu' := hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)
  exact ((contDiffAt_perturbation_comp hK hz (hu'.of_le one_le_two) _).add
    (contDiffAt_const.mul (ω.toBilinForm.toContinuousBilinearMap.contDiffAt_bilinear_fderiv_apply
      hu' _))).contDiffWithinAt

/-- On the thrice-punctured sphere, the energy density plus the curvature of the perturbation `K`
is the exterior derivative of `α = K(u) + λ(u)`. -/
private theorem floerEnergyDensity_add_hamiltonianCurvature_eq_primitive (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z
        (u z) =
      fderiv ℝ (primitiveT ω K u) z stdComplexLineReal -
        fderiv ℝ (primitiveS ω K u) z stdComplexLineImag :=
  -- `primitiveS` and `primitiveT` are by definition the components of `α` in the general identity.
  ω.floerEnergyDensity_add_hamiltonianCurvature_eq
    (hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz))
    ((hK _ hz _ _).differentiableAt one_ne_zero)
    ((hK _ hz _ _).differentiableAt one_ne_zero)

/-- A function continuous on the thrice-punctured sphere becomes integrable after multiplication
by the cutoff. -/
private theorem integrable_truncation_mul (T : ℝ) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F thricePuncturedSphereReal) : Integrable fun z ↦ truncation T z * F z :=
  (contDiff_truncation T).continuous.integrable_mul_of_continuousOn
    (hasCompactSupport_truncation T)
    (fun _ hz ↦ mem_tsupport_truncation hz) hF

/-- A function continuous on the thrice-punctured sphere becomes integrable after multiplication
by a derivative of the cutoff. -/
private theorem integrable_fderiv_truncation_mul (T : ℝ) (v : ℝ × ℝ) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F thricePuncturedSphereReal) :
    Integrable fun z ↦ fderiv ℝ (truncation T) z v * F z :=
  (((contDiff_truncation T).continuous_fderiv one_ne_zero).clm_apply
    continuous_const).integrable_mul_of_continuousOn
    ((hasCompactSupport_truncation T).fderiv_apply (𝕜 := ℝ) v)
    (fun _ hz ↦ mem_tsupport_truncation (tsupport_fderiv_apply_subset ℝ v hz)) hF

/-- **Integration by parts against the cutoff.** For a function `F` which is `C¹` on the
thrice-punctured sphere, the derivative of `F` in a direction `v`, weighted by the cutoff at
height `T`, integrates to minus the integral of `F` against the derivative of the cutoff. -/
private theorem integral_truncation_mul_fderiv (T : ℝ) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F thricePuncturedSphereReal) (v : ℝ × ℝ) :
    ∫ z, truncation T z * fderiv ℝ F z v = -∫ z, fderiv ℝ (truncation T) z v * F z := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hχS : tsupport (truncation T) ⊆ thricePuncturedSphereReal := fun z hz ↦
    mem_tsupport_truncation hz
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_fderiv_truncation_mul T v hF.continuousOn)
    (integrable_truncation_mul T ((hF.continuousOn_fderiv_of_isOpen
      isOpen_thricePuncturedSphereReal le_rfl).clm_apply continuousOn_const))
    (integrable_truncation_mul T hF.continuousOn)
    (fun z _ ↦ (contDiff_truncation T).differentiable one_ne_zero z)
    (fun z hz ↦ (hF.differentiableOn one_ne_zero z (hχS hz)).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hχS hz)))

/-- The two-form `dχ ∧ α` for the cutoff `χ` at height `T` and the one-form `α = K(u) + λ(u)`,
evaluated on `(∂_s, ∂_t)`. -/
private noncomputable def boundaryForm (ω : SymplecticForm V) (K : ℂ → V → ℂ →L[ℝ] ℝ)
    (u : ℝ × ℝ → V) (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (truncation T) z stdComplexLineReal * primitiveT ω K u z -
    fderiv ℝ (truncation T) z stdComplexLineImag * primitiveS ω K u z

private theorem integrable_boundaryForm (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (T : ℝ) :
    Integrable (boundaryForm ω K u T) :=
  (integrable_fderiv_truncation_mul T _ (contDiffOn_primitiveT ω hK hu).continuousOn).sub
    (integrable_fderiv_truncation_mul T _ (contDiffOn_primitiveS ω hK hu).continuousOn)

/-- **Integration by parts against the cutoff.** The energy density plus the curvature, weighted by
the cutoff at height `T`, integrates to minus the integral of `dχ ∧ α`, for the one-form
`α = K(u) + λ(u)`. -/
private theorem integral_truncation_mul_eq (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (T : ℝ) :
    ∫ z, truncation T z * (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z
        (u z)) =
      -∫ z, boundaryForm ω K u T z := by
  have hS := contDiffOn_primitiveS ω hK hu
  have hT := contDiffOn_primitiveT ω hK hu
  have hχS : tsupport (truncation T) ⊆ thricePuncturedSphereReal := fun z hz ↦
    mem_tsupport_truncation hz
  have hfd {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F thricePuncturedSphereReal) (v : ℝ × ℝ) :
      ContinuousOn (fun z ↦ fderiv ℝ F z v) thricePuncturedSphereReal :=
    (hF.continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl).clm_apply
      continuousOn_const
  calc _ = ∫ z, (truncation T z * fderiv ℝ (primitiveT ω K u) z stdComplexLineReal -
        truncation T z * fderiv ℝ (primitiveS ω K u) z stdComplexLineImag) := by
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        dsimp only
        by_cases hz : z ∈ thricePuncturedSphereReal
        · rw [floerEnergyDensity_add_hamiltonianCurvature_eq_primitive ω hK hu hz, mul_sub]
        · have h0 : truncation T z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hz (hχS h)
          simp [h0]
    _ = _ := by
        rw [integral_sub (integrable_truncation_mul T (hfd hT _))
          (integrable_truncation_mul T (hfd hS _)), integral_truncation_mul_fderiv T hT,
          integral_truncation_mul_fderiv T hS]
        simp only [boundaryForm]
        rw [integral_sub (integrable_fderiv_truncation_mul T _ hT.continuousOn)
          (integrable_fderiv_truncation_mul T _ hS.continuousOn)]
        ring

end Parts

section Ends

variable {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V} {T₀ : ℝ}

/-- Along the end `q`, where `±s > 0`, the derivative of the cutoff at height `T ≥ 0`, composed with
the Jacobian of the end chart, is `-β'(±s - T) (±1)` times the longitudinal coordinate. -/
private theorem fderiv_truncation_endChart_apply {T : ℝ} (hT : 0 ≤ T) {q : Puncture} {ζ : ℝ × ℝ}
    (hζ : 0 < q.endSign * ζ.1) (v : ℝ × ℝ) :
    fderiv ℝ (truncation T) (endChart q ζ) (fderiv ℝ (endChart q) ζ v) =
      -(deriv smoothTransition (q.endSign * ζ.1 - T) * q.endSign) * v.1 := by
  have hφ : DifferentiableAt ℝ (endChart q) ζ := (hasFDerivAt_endChart q ζ).differentiableAt
  -- In end coordinates the cutoff is `1 - β(±s - T)`, a function of `s` alone.
  set g : ℝ → ℝ := fun s ↦ 1 - smoothTransition (q.endSign * s - T)
  have hg : HasDerivAt g (-(deriv smoothTransition (q.endSign * ζ.1 - T) * q.endSign)) ζ.1 := by
    have h := (((hasDerivAt_id ζ.1).const_mul q.endSign).sub_const T).smoothTransition
    simpa using h.const_sub 1
  have hloc : truncation T ∘ endChart q =ᶠ[𝓝 ζ] g ∘ Prod.fst := by
    have hopen : IsOpen {ζ' : ℝ × ℝ | 0 < q.endSign * ζ'.1} :=
      isOpen_lt continuous_const (continuous_const.mul continuous_fst)
    filter_upwards [hopen.mem_nhds hζ] with ζ' hζ'
    exact truncation_endChart hT hζ'
  have hcomp := fderiv_comp ζ ((contDiff_truncation T).differentiable one_ne_zero _) hφ
  have h₁ := congrArg (· v) hcomp
  rw [hloc.fderiv_eq, ((hg.hasFDerivAt.comp ζ (hasFDerivAt_fst)).fderiv)] at h₁
  simpa [mul_comm] using h₁.symm

/-- **A wedge with the derivative of the cutoff in end coordinates.** On the end `q`, where
`±s > 0`, the two-form `dχ ∧ (a ds + b dt)` for the cutoff `χ` at height `T ≥ 0` and constants
`a`, `b`, transported to the coordinates of the end with its Jacobian, is `-±β'(±s - T)` times the
value of `a ds + b dt` on the image `dφ_q(∂_t)` of the angular direction. -/
private theorem abs_det_mul_fderiv_truncation_wedge_endChart {T : ℝ} (hT : 0 ≤ T) {q : Puncture}
    {ζ : ℝ × ℝ} (hζ : 0 < q.endSign * ζ.1) (a b : ℝ) :
    |(fderiv ℝ (endChart q) ζ).det| *
        (fderiv ℝ (truncation T) (endChart q ζ) stdComplexLineReal * b -
          fderiv ℝ (truncation T) (endChart q ζ) stdComplexLineImag * a) =
      -(q.endSign * deriv smoothTransition (q.endSign * ζ.1 - T) *
        ((fderiv ℝ (endChart q) ζ stdComplexLineImag).1 * a +
          (fderiv ℝ (endChart q) ζ stdComplexLineImag).2 * b)) := by
  set L := fderiv ℝ (endChart q) ζ
  set κ := fderiv ℝ (truncation T) (endChart q ζ)
  have hκ (v : ℝ × ℝ) :
      κ (L v) = -(deriv smoothTransition (q.endSign * ζ.1 - T) * q.endSign) * v.1 :=
    fderiv_truncation_endChart_apply hT hζ v
  -- The Jacobian times `dχ ∧ α` is the wedge of the pullbacks of `dχ` and `α` along `dφ`.
  have hwedge : L.det * (κ stdComplexLineReal * b - κ stdComplexLineImag * a) =
      κ (L stdComplexLineReal) * ((L stdComplexLineImag).1 * a + (L stdComplexLineImag).2 * b) -
        κ (L stdComplexLineImag) *
          ((L stdComplexLineReal).1 * a + (L stdComplexLineReal).2 * b) := by
    have h := LinearMap.det_mul_wedge_finTwoProd (L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) (κ : ℝ × ℝ →ₗ[ℝ] ℝ)
      (a • LinearMap.fst ℝ ℝ ℝ + b • LinearMap.snd ℝ ℝ ℝ)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, smul_eq_mul, ContinuousLinearMap.coe_coe] at h
    rw [ContinuousLinearMap.det, stdComplexLineReal_eq, stdComplexLineImag_eq]
    linear_combination h
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q ζ), hwedge, hκ, hκ]
  simp only [stdComplexLineReal_fst, stdComplexLineImag_fst, mul_zero, zero_mul, sub_zero,
    mul_one]
  ring

omit [FiniteDimensional ℝ V] in
/-- **The boundary term in end coordinates.** On the end `q`, for `T ≥ 0` with `K = H_q dt`
beyond height `T₀ ≤ T`, the two-form `dχ ∧ α`, transported to the coordinates of the end with its
Jacobian, is `-±β'(±s - T) (H_q(t, u_q) + ½ ω(u_q, ∂_t u_q))` for `u_q = u ∘ φ_q`. -/
private theorem abs_det_mul_wedge_endChart (ω : SymplecticForm V)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {T : ℝ}
    (hT : 0 ≤ T) (hT₀ : T₀ ≤ T) {q : Puncture} {ζ : ℝ × ℝ} (hζ : 0 < q.endSign * ζ.1) :
    |(fderiv ℝ (endChart q) ζ).det| *
        (fderiv ℝ (truncation T) (endChart q ζ) stdComplexLineReal *
            primitiveT ω K u (endChart q ζ) -
          fderiv ℝ (truncation T) (endChart q ζ) stdComplexLineImag *
            primitiveS ω K u (endChart q ζ)) =
      -(q.endSign * deriv smoothTransition (q.endSign * ζ.1 - T) *
        (H q ζ.2 (u (endChart q ζ)) +
          1 / 2 * ω (u (endChart q ζ)) (fderiv ℝ (u ∘ endChart q) ζ stdComplexLineImag))) := by
  set L := fderiv ℝ (endChart q) ζ
  set x := u (endChart q ζ)
  have hw := endChart_mem_thricePuncturedSphereReal hζ
  have hφ : DifferentiableAt ℝ (endChart q) ζ := (hasFDerivAt_endChart q ζ).differentiableAt
  have hu₁ : DifferentiableAt ℝ u (endChart q ζ) :=
    (hu.differentiableOn (by norm_num) _ hw).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds hw)
  -- The pulled-back one-form `α ∘ dφ` on `∂_t` is `K` in end coordinates plus `½ ω(u_q, ∂_t u_q)`.
  have hdu (e : ℝ × ℝ) : fderiv ℝ u (endChart q ζ) e =
      e.1 • fderiv ℝ u (endChart q ζ) stdComplexLineReal +
        e.2 • fderiv ℝ u (endChart q ζ) stdComplexLineImag := by
    simpa using (fderiv ℝ u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine e
  have hα : (L stdComplexLineImag).1 * primitiveS ω K u (endChart q ζ) +
      (L stdComplexLineImag).2 * primitiveT ω K u (endChart q ζ) =
        perturbationPullback (endChart q)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ x +
          1 / 2 * ω x (fderiv ℝ (u ∘ endChart q) ζ stdComplexLineImag) := by
    rw [fderiv_comp ζ hu₁ hφ, ContinuousLinearMap.comp_apply, hdu, perturbationPullback_apply]
    simp only [primitiveS, primitiveT, map_add, map_smul, smul_eq_mul]
    ring
  rw [abs_det_mul_fderiv_truncation_wedge_endChart hT hζ, hα]
  -- Where `β'(±s - T) ≠ 0`, the end coordinate satisfies `±s ≥ T ≥ T₀`, so `K = H_q dt` there.
  by_cases hs : T₀ ≤ q.endSign * ζ.1
  · rw [perturbationPullback_endChart_stdComplexLineImag_of_le hKH hH hs]
  · rw [smoothTransition.deriv_of_neg (by linarith)]
    ring

/-- On the end `q`, the integral over one period of `H_q(t, u_q) + ½ ω(u_q, ∂_t u_q)` is the
action of the loop `t ↦ u_q(s, t)`, for `u_q = u ∘ φ_q`. -/
private theorem integral_Ico_eq_hamiltonianAction (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {q : Puncture} {s : ℝ}
    (hs : 0 < q.endSign * s) :
    ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), (H q t (u (endChart q (s, t))) +
        1 / 2 * ω (u (endChart q (s, t))) (fderiv ℝ (u ∘ endChart q) (s, t) stdComplexLineImag)) =
      ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t))) := by
  set x : ℝ → V := fun t ↦ u (endChart q (s, t)) with hx
  have huq (t : ℝ) : ContDiffAt ℝ 2 (u ∘ endChart q) (s, t) :=
    (hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds
      (endChart_mem_thricePuncturedSphereReal (z := (s, t)) hs))).comp (s, t)
      (contDiff_endChart q 2).contDiffAt
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ ↦ (s, t)) stdComplexLineImag t := by
    simpa [stdComplexLineImag_eq] using HasDerivAt.prodMk (hasDerivAt_const t s) (hasDerivAt_id t)
  have hderiv (t : ℝ) : deriv x t = fderiv ℝ (u ∘ endChart q) (s, t) stdComplexLineImag :=
    (((huq t).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  have hper : Periodic x 1 := fun t ↦ by simp only [x, endChart_add_one]
  -- The integrand is continuous and periodic, so its integral over any period is the same.
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦
    ((huq t).continuousAt).comp (continuous_const.prodMk continuous_id).continuousAt
  have hdxc : Continuous (deriv x) := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    simp only [funext hderiv]
    exact (((huq t).fderiv_right (m := 1) (by norm_num)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).clm_apply continuousAt_const
  have hHc : Continuous fun t ↦ H q t (x t) :=
    (hHc q).comp (continuous_id.prodMk hxc)
  have hωc : Continuous fun t ↦ ω (x t) (deriv x t) := ω.continuous_apply_comp hxc hdxc
  have hG : Periodic (fun t ↦ H q t (x t) + 1 / 2 * ω (x t) (deriv x t)) 1 := fun t ↦ by
    simp only [hper t, hper.deriv t, hH q t]
  calc _ = ∫ t in (-1 / 2 : ℝ)..(-1 / 2 + 1), (H q t (x t) + 1 / 2 * ω (x t) (deriv x t)) := by
        rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
          show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
        simp only [hderiv]
        simp only [hx]
    _ = ∫ t in (0 : ℝ)..(0 + 1), (H q t (x t) + 1 / 2 * ω (x t) (deriv x t)) :=
        hG.intervalIntegral_add_eq _ _
    _ = _ := by
        rw [zero_add, intervalIntegral.integral_add (hHc.intervalIntegrable _ _)
          ((hωc.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
          hamiltonianAction_def, loopArea_def]
        ring

private theorem hasFDerivWithinAt_endChart (q : Puncture) (ζ : ℝ × ℝ) (s : Set (ℝ × ℝ)) :
    HasFDerivWithinAt (endChart q) (fderiv ℝ (endChart q) ζ) s ζ :=
  (hasFDerivAt_endChart q ζ).differentiableAt.hasFDerivAt.hasFDerivWithinAt

/-- **The boundary term on one end.** For `T ≥ 2` with `K = H_q dt` beyond height `T₀ ≤ T`, the
integral of `dχ ∧ α` over the end `q` is `-±∫ β'(±s - T) A_q(s) ds`, where `A_q(s)` is the action
of the loop `t ↦ u(φ_q(s, t))`; the weighted actions are integrable. -/
private theorem integral_image_endChart_boundaryForm (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {T : ℝ} (hT : 2 ≤ T) (hT₀ : T₀ ≤ T)
    (q : Puncture) :
    ∫ z in endChart q '' endStrip q, boundaryForm ω K u T z =
        -(q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
          ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t)))) ∧
      Integrable fun s ↦ deriv smoothTransition (q.endSign * s - T) *
        ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t))) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set F : ℝ × ℝ → ℝ := fun ζ ↦ -(q.endSign * deriv smoothTransition (q.endSign * ζ.1 - T) *
    (H q ζ.2 (u (endChart q ζ)) +
      1 / 2 * ω (u (endChart q ζ)) (fderiv ℝ (u ∘ endChart q) ζ stdComplexLineImag)))
  set A : ℝ → ℝ := fun s ↦ deriv smoothTransition (q.endSign * s - T) *
    ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t)))
  have hS₁ : MeasurableSet {s : ℝ | 1 / 2 < q.endSign * s} :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  -- In end coordinates the integrand is `F`.
  have hcongr : EqOn (fun ζ ↦ |(fderiv ℝ (endChart q) ζ).det| • boundaryForm ω K u T (endChart q ζ))
      F (endStrip q) := fun ζ hζ ↦ by
    dsimp only
    rw [smul_eq_mul, boundaryForm]
    exact abs_det_mul_wedge_endChart ω hKH hH hu (by linarith) hT₀
      (endSign_mul_pos_of_mem_endStrip hζ)
  have hint : IntegrableOn F (endStrip q) :=
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_endStrip q)
      (fun ζ _ ↦ hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q) _).1
      (integrable_boundaryForm ω hK hu T).integrableOn).congr_fun hcongr
      (measurableSet_endStrip q)
  -- Integrating out the angular coordinate gives the actions of the loops.
  have hinner (s : ℝ) (hs : s ∈ {s : ℝ | 1 / 2 < q.endSign * s}) :
      ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), F (s, t) = -(q.endSign * A s) := by
    have hs' : 0 < q.endSign * s := by
      have : 1 / 2 < q.endSign * s := hs
      linarith
    simp only [F, A]
    rw [integral_neg, integral_const_mul, integral_Ico_eq_hamiltonianAction ω hH hHc hu hs']
    ring
  have hzero (s : ℝ) (hs : s ∉ {s : ℝ | 1 / 2 < q.endSign * s}) : A s = 0 := by
    have : q.endSign * s ≤ 1 / 2 := not_lt.1 hs
    simp only [A, smoothTransition.deriv_of_neg (by linarith : q.endSign * s - T < 0), zero_mul]
  rw [endStrip_def, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at hint
  have hint' : IntegrableOn (fun s ↦ ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), F (s, t))
      {s : ℝ | 1 / 2 < q.endSign * s} := hint.integral_prod_left
  have hA : IntegrableOn A {s : ℝ | 1 / 2 < q.endSign * s} := by
    refine IntegrableOn.congr_fun (hint'.const_mul (-q.endSign)) (fun s hs ↦ ?_) hS₁
    rw [hinner s hs]
    linear_combination (A s) * q.endSign_mul_self
  refine ⟨?_, hA.integrable_of_forall_notMem_eq_zero hzero⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_endStrip q)
    (fun ζ _ ↦ hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q),
    setIntegral_congr_fun (measurableSet_endStrip q) hcongr, endStrip_def,
    Measure.volume_eq_prod, setIntegral_prod _ (by rwa [IntegrableOn, ← Measure.prod_restrict]),
    setIntegral_congr_fun hS₁ hinner, integral_neg, integral_const_mul,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- Away from the three end strips the cutoff at height `T ≥ 2` is locally constant, so its
derivative vanishes there. -/
private theorem fderiv_truncation_eq_zero {T : ℝ} (hT : 2 ≤ T) {z : ℝ × ℝ}
    (hz : z ∉ ⋃ q, endChart q '' endStrip q) : fderiv ℝ (truncation T) z = 0 := by
  by_cases hzS : z ∈ thricePuncturedSphereReal
  · have hT' (q : Puncture) : endHeight q z < T := by
      by_contra h
      rw [not_lt, endHeight] at h
      exact hz (mem_iUnion.2 ⟨q, mem_image_endChart hzS (by linarith)⟩)
    rw [(truncation_eventuallyEq_one hzS hT').fderiv_eq, fderiv_const_apply]
  · simp only [mem_thricePuncturedSphereReal_iff, not_and_or, not_not] at hzS
    rw [(truncation_eventuallyEq_zero T hzS).fderiv_eq]
    simp

omit [FiniteDimensional ℝ V] in
/-- Away from the three end strips the boundary term vanishes. -/
private theorem boundaryForm_eq_zero (ω : SymplecticForm V) {T : ℝ} (hT : 2 ≤ T) {z : ℝ × ℝ}
    (hz : z ∉ ⋃ q, endChart q '' endStrip q) : boundaryForm ω K u T z = 0 := by
  simp [boundaryForm, fderiv_truncation_eq_zero hT hz]

/-- **The truncated energy identity.** For `T ≥ 2` with `K = H_q dt` beyond height `T₀ ≤ T`, the
energy density plus the curvature, weighted by the cutoff at height `T`, integrates to the signed
sum over the three ends of the actions `A_q(s)` of the loops `t ↦ u(φ_q(s, t))`, averaged against
`β'(±s - T)`. -/
private theorem integral_truncation_mul_eq_sum (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {T : ℝ} (hT : 2 ≤ T) (hT₀ : T₀ ≤ T) :
    ∫ z, truncation T z * (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) =
      ∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
        ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t))) := by
  rw [integral_truncation_mul_eq ω hK hu T,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ boundaryForm_eq_zero ω hT hz,
    integral_iUnion_fintype (fun q ↦ measurable_image_of_fderivWithin (measurableSet_endStrip q)
      (fun ζ _ ↦ hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q))
      pairwise_disjoint_image_endChart
      fun q ↦ (integrable_boundaryForm ω hK hu T).integrableOn]
  simp only [fun q ↦ (integral_image_endChart_boundaryForm ω hK hKH hH hHc hu hT hT₀ q).1,
    Finset.sum_neg_distrib, neg_neg]

end Ends


section Limit

variable {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V} {T₀ : ℝ}

/-- The cutoff increases with the height. -/
private theorem truncation_le_truncation {T T' : ℝ} (h : T ≤ T') (z : ℝ × ℝ) :
    truncation T z ≤ truncation T' z := by
  rw [truncation, truncation]
  split_ifs
  · exact le_rfl
  · exact Finset.prod_le_prod₀ (fun q _ ↦ sub_nonneg.2 (smoothTransition.le_one _))
      fun q _ ↦ sub_le_sub_left (smoothTransition.monotone (by linarith)) 1

/-- As the height tends to infinity, the integrals of an integrable function against the cutoffs
tend to its integral, by dominated convergence. -/
private theorem tendsto_integral_truncation_mul {f : ℝ × ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun T ↦ ∫ z, truncation T z * f z) atTop (𝓝 (∫ z, f z)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖f z‖)
    (Eventually.of_forall fun T ↦
      (contDiff_truncation T).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun T ↦ ae_of_all _ fun z ↦ ?_) hf.norm ?_
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Real.norm_of_nonneg (truncation_mem_Icc T z).1]
      exact (truncation_mem_Icc T z).2)
  · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
    simpa using (tendsto_truncation hz).mul_const (f z)

/-- The energy density of a `C²` map is continuous on `S` for data which is `C¹` there. -/
private theorem continuousOn_floerEnergyDensity_thricePuncturedSphereReal (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) :
    ContinuousOn (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) thricePuncturedSphereReal :=
  ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal (hu.of_le one_le_two)
    (fun p hp ↦ (hK p.1 hp.1 p.2 1).contDiffWithinAt)
    (fun p hp ↦ (hK p.1 hp.1 p.2 Complex.I).contDiffWithinAt)

/-- As the height tends to infinity, the actions on the ends averaged against `β'(±s - T)` tend to
the limiting actions. -/
private theorem tendsto_sum_integral_deriv_smoothTransition_mul (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (A q))) :
    Tendsto (fun T ↦ ∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
      ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t)))) atTop
      (𝓝 (∑ q, q.endSign * A q)) :=
  tendsto_finsetSum _ fun q _ ↦ by
    have h := smoothTransition.tendsto_integral_deriv_mul_sub_mul
      q.endSign_ne_zero (by simpa only [Puncture.inv_endSign] using hA q)
      (eventually_ge_atTop (max 2 T₀) |>.mono fun T hT ↦
        (integral_image_endChart_boundaryForm ω hK hKH hH hHc hu (le_of_max_le_left hT)
          (le_of_max_le_right hT) q).2)
    rw [abs_endSign, inv_one, one_mul] at h
    exact h.const_mul _

/-- **The energy identity for perturbations that are cylindrical on the ends.** Let `K` be a
perturbation datum on `S = ℂ ∖ {0, 1}` which is `C¹` jointly in the domain and target points, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t`, and
which is `H_q(t) dt` beyond the height `T₀` on each end `q`, for continuous period-one
Hamiltonians `H_q`. Let `u` be a `C²` map from `S` to a symplectic vector space whose Floer energy
density and curvature term `R_K(u)` are integrable. Suppose that on each end `q` the actions of the
loops `t ↦ u(φ_q(s, t))` tend to `A_q` as `±s → ∞`. Then the energy of `u` is
`E = A₀ + A₁ - A_∞ - ∫ R_K(u)`.

On the compact part of `S` below the height `T₀` the datum is only required to be `C¹`: this
covers the pair-of-pants perturbation, its family with continuation necks, and its sums with
compactly supported variations. -/
theorem integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm
    (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (A q))) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∑ q, q.endSign * A q - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  set f : ℝ × ℝ → ℝ := fun z ↦ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
    ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  have hf : Integrable f := hE.add hR
  -- As `T → ∞`, the truncated energies tend to the full integral by dominated convergence.
  have hlhs := tendsto_integral_truncation_mul hf
  have heq : ∫ z, f z = ∑ q, q.endSign * A q :=
    tendsto_nhds_unique (hlhs.congr' (eventually_ge_atTop (max 2 T₀) |>.mono fun T hT ↦
      integral_truncation_mul_eq_sum ω hK hKH hH hHc hu (le_of_max_le_left hT)
        (le_of_max_le_right hT)))
      (tendsto_sum_integral_deriv_smoothTransition_mul ω hK hKH hH hHc hu hA)
  rw [← heq, integral_add hE hR]
  ring

/-- **The energy identity on the pair of pants.** Let `K` be the pair-of-pants perturbation of
period-one `C¹` Hamiltonians `H_q` on the ends of `S = ℂ ∖ {0, 1}`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t`, and let `u` be a
`C²` map from `S` to a symplectic vector space whose Floer energy density and curvature term
`R_K(u)` are integrable. Suppose that on each end `q` the actions of the loops
`t ↦ u(φ_q(s, t))` tend to `A_q` as `±s → ∞`. Then the energy of `u` is
`E = A₀ + A₁ - A_∞ - ∫ R_K(u)`: the actions at the two positive (input) ends minus the action at
the negative (output) end, minus the integrated curvature. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_eq_sum_hamiltonianAction
    (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (A q))) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∑ q, q.endSign * A q - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z
        (u z) :=
  integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm ω
    (fun _ hz x v ↦ contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH
    (fun q ↦ (hHs q).continuous) hu hE hR hA

/-- **The energy identity for a nonnegative energy density.** Under the hypotheses of
`integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm`, suppose that
the Floer energy density of `u` is nonnegative on `S`, as it is for a solution of the Floer
equation with tame almost complex structures. Then no integrability of the energy density is
needed: the energy of `u`, as a Lebesgue integral, is `E = A₀ + A₁ - A_∞ - ∫ R_K(u)`, and in
particular it is finite. -/
theorem lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (A q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (∑ q, q.endSign * A q - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  set r : ℝ × ℝ → ℝ := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  have hKs (v : ℂ) : ContDiffOn ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) :=
    fun p hp ↦ (hK p.1 hp.1 p.2 v).contDiffWithinAt
  have he' : ContinuousOn e thricePuncturedSphereReal :=
    continuousOn_floerEnergyDensity_thricePuncturedSphereReal ω hK hu
  have hr' : ContinuousOn r thricePuncturedSphereReal :=
    ω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal hu.continuousOn
      (hKs 1) (hKs Complex.I)
  -- The heights `n + max 2 T₀` exhaust `S`.
  set T : ℕ → ℝ := fun n ↦ n + max 2 T₀
  have hT : Tendsto T atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hT₂ (n : ℕ) : 2 ≤ T n := by
    simp only [T]; linarith [n.cast_nonneg (α := ℝ), le_max_left 2 T₀]
  have hT₀ (n : ℕ) : T₀ ≤ T n := by
    simp only [T]; linarith [n.cast_nonneg (α := ℝ), le_max_right 2 T₀]
  have hχe (n : ℕ) : Integrable fun z ↦ truncation (T n) z * e z := integrable_truncation_mul _ he'
  have hχr (n : ℕ) : Integrable fun z ↦ truncation (T n) z * r z := integrable_truncation_mul _ hr'
  have hχe₀ (n : ℕ) (z : ℝ × ℝ) : 0 ≤ truncation (T n) z * e z := by
    by_cases hz : z ∈ thricePuncturedSphereReal
    · exact mul_nonneg (truncation_mem_Icc _ z).1 (he z hz)
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz (mem_tsupport_truncation h), zero_mul]
  -- On each truncation the weighted energy is the averaged actions minus the weighted curvature.
  have hid (n : ℕ) : ∫ z, truncation (T n) z * e z =
      (∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T n) *
        ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t)))) -
        ∫ z, truncation (T n) z * r z := by
    rw [← integral_truncation_mul_eq_sum ω hK hKH hH hHc hu (hT₂ n) (hT₀ n), eq_sub_iff_add_eq,
      ← integral_add (hχe n) (hχr n)]
    simp only [e, r, mul_add]
  -- The weighted curvature integrals converge by dominated convergence.
  have hrlim : Tendsto (fun n ↦ ∫ z, truncation (T n) z * r z) atTop (𝓝 (∫ z, r z)) :=
    (tendsto_integral_truncation_mul hR).comp hT
  -- The weighted energies increase to the energy by monotone convergence.
  have helim : Tendsto (fun n ↦ ∫⁻ z, ENNReal.ofReal (truncation (T n) z * e z)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (e z))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ (hχe n).aestronglyMeasurable.aemeasurable.ennreal_ofReal) ?_ ?_
    · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz m n hmn
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (truncation_le_truncation (by simp only [T]; gcongr) z) (he z hz))
    · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
      have h := (ENNReal.continuous_ofReal.tendsto _).comp
        (((tendsto_truncation hz).comp hT).mul_const (e z))
      rwa [one_mul] at h
  refine tendsto_nhds_unique helim ?_
  simp only [fun n ↦ (ofReal_integral_eq_lintegral_ofReal (hχe n)
    (ae_of_all _ (hχe₀ n))).symm, hid]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (((tendsto_sum_integral_deriv_smoothTransition_mul ω hK hKH hH hHc hu hA).comp hT).sub hrlim)

/-- **A nonnegative energy density is integrable.** Under the hypotheses of
`lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`, the Floer energy density of `u` is
integrable, so `integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm`
applies to it. -/
theorem integrable_floerEnergyDensity_of_eq_smul_endAngularForm (ω : SymplecticForm V)
    (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHc : ∀ q, Continuous (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {A : Puncture → ℝ}
    (hA : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (A q))) :
    Integrable (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) := by
  refine ⟨?_, ?_⟩
  · -- The energy density is continuous on `S`, whose complement is null.
    rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal]
    exact (continuousOn_floerEnergyDensity_thricePuncturedSphereReal ω hK hu).aestronglyMeasurable
      isOpen_thricePuncturedSphereReal.measurableSet
  · rw [HasFiniteIntegral, lintegral_congr_ae (g := fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)) (by
        filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
        exact Real.eNorm_eq_ofReal (he z hz)),
      lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm ω hK hKH hH hHc hu he hR hA]
    exact ENNReal.ofReal_lt_top

end Limit

end SymplecticForm

/-! ### The energy identity for a manifold target -/

namespace SmoothTwoForm

open Floer
open scoped _root_.Manifold

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {u : ℝ × ℝ → M} {T₀ : ℝ}

section Parts

omit [IsManifold I ⊤ M] in
/-- The components of a datum which is `C¹` on `S × M`, read in real coordinates, are `C¹`
jointly in the domain point of `S` and the target point. -/
private theorem contMDiffOn_perturbation
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x)) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) 1
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
      contMDiffAt_snd
  exact (((hK ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (z, x) hφ).clm_apply
    contMDiffAt_const).contMDiffWithinAt

omit [IsManifold I ⊤ M] in
/-- A datum which is `C¹` on `S × M`, evaluated along a map which is `C¹` on `S`, is `C¹` on
`S`. -/
private theorem contDiffOn_perturbation_comp
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (v : ℂ) :
    ContDiffOn ℝ 1 (fun z ↦ K (Complex.equivRealProdCLM.symm z) (u z) v)
      thricePuncturedSphereReal :=
  contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_perturbation hK v).comp
    (contMDiffOn_id.prodMk hu) fun _ hz ↦ ⟨hz, mem_univ _⟩)

/-- On `S`, the energy density plus the curvature is the symplectic area density plus the
exterior derivative `∂_s(K_t(u)) - ∂_t(K_s(u))` of the one-form `K(u)`. -/
private theorem IsNondegenerate.floerEnergyDensity_add_hamiltonianCurvature_eq
    [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) Complex.I) z
            stdComplexLineReal -
          fderiv ℝ (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) 1) z stdComplexLineImag) := by
  have hzS : (z, u z) ∈ thricePuncturedSphereReal ×ˢ (univ : Set M) := ⟨hz, mem_univ _⟩
  have hKz (v : ℂ) := ((contMDiffOn_perturbation hK v).contMDiffAt
    ((isOpen_thricePuncturedSphereReal.prod isOpen_univ).mem_nhds hzS)).mdifferentiableAt
      one_ne_zero
  rw [hω.floerEnergyDensity_eq ((hu.contMDiffAt
    (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt one_ne_zero) (hKz 1)
    (hKz Complex.I)]
  ring

/-- The two-form `dχ ∧ K(u)` for the cutoff `χ` at height `T` and the one-form `K(u)`, evaluated
on `(∂_s, ∂_t)`. -/
private noncomputable def boundaryForm (K : ℂ → M → ℂ →L[ℝ] ℝ) (u : ℝ × ℝ → M) (T : ℝ)
    (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (SymplecticForm.truncation T) z stdComplexLineReal *
      K (Complex.equivRealProdCLM.symm z) (u z) Complex.I -
    fderiv ℝ (SymplecticForm.truncation T) z stdComplexLineImag *
      K (Complex.equivRealProdCLM.symm z) (u z) 1

omit [IsManifold I ⊤ M] in
private theorem integrable_boundaryForm
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (T : ℝ) :
    Integrable (boundaryForm K u T) :=
  (SymplecticForm.integrable_fderiv_truncation_mul T _
    (contDiffOn_perturbation_comp hK hu Complex.I).continuousOn).sub
    (SymplecticForm.integrable_fderiv_truncation_mul T _
      (contDiffOn_perturbation_comp hK hu 1).continuousOn)

omit [IsManifold I ⊤ M] in
/-- The exterior derivative of `K(u)`, weighted by the cutoff at height `T`, integrates to minus
the integral of `dχ ∧ K(u)`. -/
private theorem integral_truncation_mul_exteriorDeriv_eq
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (T : ℝ) :
    ∫ z, (SymplecticForm.truncation T z * fderiv ℝ
      (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) Complex.I) z stdComplexLineReal -
        SymplecticForm.truncation T z * fderiv ℝ
          (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) 1) z stdComplexLineImag) =
      -∫ z, boundaryForm K u T z := by
  have hS := contDiffOn_perturbation_comp hK hu 1
  have hT := contDiffOn_perturbation_comp hK hu Complex.I
  have hχd {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F thricePuncturedSphereReal) (v : ℝ × ℝ) :=
    SymplecticForm.integrable_truncation_mul T ((hF.continuousOn_fderiv_of_isOpen
      isOpen_thricePuncturedSphereReal le_rfl).clm_apply (continuousOn_const (c := v)))
  rw [integral_sub (hχd hT _) (hχd hS _), SymplecticForm.integral_truncation_mul_fderiv T hT,
    SymplecticForm.integral_truncation_mul_fderiv T hS]
  unfold boundaryForm
  rw [integral_sub (SymplecticForm.integrable_fderiv_truncation_mul T _ hT.continuousOn)
    (SymplecticForm.integrable_fderiv_truncation_mul T _ hS.continuousOn)]
  ring

/-- **Integration by parts against the cutoff, for a manifold target.** The energy density,
weighted by the cutoff at height `T`, is integrable, and its integral is the weighted symplectic
area, minus the integral of `dχ ∧ K(u)`, minus the weighted curvature. -/
private theorem IsNondegenerate.integral_truncation_mul_floerEnergyDensity_eq
    [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) (T : ℝ) :
    Integrable (fun z ↦ SymplecticForm.truncation T z * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ∧
      ∫ z, SymplecticForm.truncation T z * ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z, SymplecticForm.truncation T z *
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
          (∫ z, boundaryForm K u T z) -
          ∫ z, SymplecticForm.truncation T z * ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hχd {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F thricePuncturedSphereReal) (v : ℝ × ℝ) :
      Integrable fun z ↦ SymplecticForm.truncation T z * fderiv ℝ F z v :=
    SymplecticForm.integrable_truncation_mul T ((hF.continuousOn_fderiv_of_isOpen
      isOpen_thricePuncturedSphereReal le_rfl).clm_apply continuousOn_const)
  have hparts := integral_truncation_mul_exteriorDeriv_eq hK hu T
  set χ := SymplecticForm.truncation T
  set a : ℝ × ℝ → ℝ := fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)
  set r : ℝ × ℝ → ℝ := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  set dT : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ
    (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) Complex.I) z stdComplexLineReal
  set dS : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ
    (fun w ↦ K (Complex.equivRealProdCLM.symm w) (u w) 1) z stdComplexLineImag
  -- The area density of a map which is `C¹` on `S` is continuous on `S`.
  have ha := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv
    isOpen_thricePuncturedSphereReal hu stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at ha
  have hχa : Integrable fun z ↦ χ z * a z := SymplecticForm.integrable_truncation_mul T ha
  have hχd' : Integrable fun z ↦ χ z * dT z - χ z * dS z :=
    (hχd (contDiffOn_perturbation_comp hK hu Complex.I) _).sub
      (hχd (contDiffOn_perturbation_comp hK hu 1) _)
  have hχad : Integrable fun z ↦ χ z * a z + (χ z * dT z - χ z * dS z) := hχa.add hχd'
  have hχr : Integrable fun z ↦ χ z * r z :=
    hR.bdd_mul (c := 1) (SymplecticForm.contDiff_truncation T).continuous.aestronglyMeasurable
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_of_nonneg (SymplecticForm.truncation_mem_Icc T z).1]
        exact (SymplecticForm.truncation_mem_Icc T z).2)
  -- Pointwise, the weighted energy density is the weighted area, plus the weighted exterior
  -- derivative of `K(u)`, minus the weighted curvature; off `S` the cutoff vanishes.
  have hpt : (fun z ↦ χ z * ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      fun z ↦ χ z * a z + (χ z * dT z - χ z * dS z) - χ z * r z := by
    funext z
    by_cases hz : z ∈ thricePuncturedSphereReal
    · linear_combination χ z * hω.floerEnergyDensity_add_hamiltonianCurvature_eq hK hu hz
    · have h0 : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
        hz (SymplecticForm.mem_tsupport_truncation h)
      simp [h0]
  rw [hpt]
  refine ⟨hχad.sub hχr, ?_⟩
  rw [integral_sub hχad hχr, integral_add hχa hχd', hparts]
  ring

end Parts

section Ends

omit [TopologicalSpace M] in
/-- **The boundary term in end coordinates, for a manifold target.** On the end `q`, for `T ≥ 0`
with `K = H_q dt` beyond height `T₀ ≤ T`, the two-form `dχ ∧ K(u)`, transported to the
coordinates of the end with its Jacobian, is `-±β'(±s - T) H_q(t, u(φ_q(s, t)))`. -/
private theorem abs_det_mul_boundaryForm_endChart
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) {T : ℝ} (hT : 0 ≤ T) (hT₀ : T₀ ≤ T) {q : Puncture}
    {ζ : ℝ × ℝ} (hζ : 0 < q.endSign * ζ.1) :
    |(fderiv ℝ (endChart q) ζ).det| * boundaryForm K u T (endChart q ζ) =
      -(q.endSign * deriv smoothTransition (q.endSign * ζ.1 - T) * H q ζ.2 (u (endChart q ζ))) := by
  rw [boundaryForm, SymplecticForm.abs_det_mul_fderiv_truncation_wedge_endChart hT hζ]
  -- The value of `K(u)` on `dφ_q(∂_t)` is the pullback of `K` along the end chart on `∂_t`.
  have hα := perturbationPullback_apply (endChart q)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) stdComplexLineImag ζ
    (u (endChart q ζ))
  rw [← hα]
  -- Where `β'(±s - T) ≠ 0`, the end coordinate satisfies `±s ≥ T ≥ T₀`, so `K = H_q dt` there.
  by_cases hs : T₀ ≤ q.endSign * ζ.1
  · rw [perturbationPullback_endChart_stdComplexLineImag_of_le hKH hH hs]
  · rw [smoothTransition.deriv_of_neg (by linarith)]
    ring

omit [TopologicalSpace M] in
/-- On the end `q`, the integral of `H_q(t, u(φ_q(s, t)))` over `[-1/2, 1/2)` is its integral over
the period `[0, 1]`. -/
private theorem integral_Ico_eq_intervalIntegral (hH : ∀ q, Periodic (H q) 1) (q : Puncture)
    (s : ℝ) :
    ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), H q t (u (endChart q (s, t))) =
      ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t))) := by
  have hper : Periodic (fun t ↦ H q t (u (endChart q (s, t)))) 1 := fun t ↦ by
    simp only [endChart_add_one, hH q t]
  have h := hper.intervalIntegral_add_eq (-1 / 2) 0
  rw [zero_add, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    intervalIntegral.integral_of_le (by norm_num)] at h
  rw [integral_Ico_eq_integral_Ioc, h]

omit [IsManifold I ⊤ M] in
/-- **The boundary term on one end, for a manifold target.** For `T ≥ 2` with `K = H_q dt` beyond
height `T₀ ≤ T`, the integral of `dχ ∧ K(u)` over the end `q` is `-±∫ β'(±s - T) h_q(s) ds`,
where `h_q(s) = ∫₀¹ H_q(t, u(φ_q(s, t))) dt`; the weighted integrals `h_q` are integrable. -/
private theorem integral_image_endChart_boundaryForm
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {T : ℝ} (hT : 2 ≤ T)
    (hT₀ : T₀ ≤ T) (q : Puncture) :
    ∫ z in endChart q '' endStrip q, boundaryForm K u T z =
        -(q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
          ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t)))) ∧
      Integrable fun s ↦ deriv smoothTransition (q.endSign * s - T) *
        ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t))) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set F : ℝ × ℝ → ℝ := fun ζ ↦ -(q.endSign * deriv smoothTransition (q.endSign * ζ.1 - T) *
    H q ζ.2 (u (endChart q ζ)))
  set A : ℝ → ℝ := fun s ↦ deriv smoothTransition (q.endSign * s - T) *
    ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t)))
  have hS₁ : MeasurableSet {s : ℝ | 1 / 2 < q.endSign * s} :=
    measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  -- In end coordinates the integrand is `F`.
  have hcongr : EqOn (fun ζ ↦ |(fderiv ℝ (endChart q) ζ).det| • boundaryForm K u T (endChart q ζ))
      F (endStrip q) := fun ζ hζ ↦ by
    dsimp only
    rw [smul_eq_mul]
    exact abs_det_mul_boundaryForm_endChart hKH hH (by linarith) hT₀
      (endSign_mul_pos_of_mem_endStrip hζ)
  have hint : IntegrableOn F (endStrip q) :=
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_endStrip q)
      (fun ζ _ ↦ SymplecticForm.hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q) _).1
      (integrable_boundaryForm hK hu T).integrableOn).congr_fun hcongr
      (measurableSet_endStrip q)
  -- Integrating out the angular coordinate gives the integrals of the end Hamiltonian.
  have hinner (s : ℝ) (_ : s ∈ {s : ℝ | 1 / 2 < q.endSign * s}) :
      ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), F (s, t) = -(q.endSign * A s) := by
    simp only [F, A]
    rw [integral_neg, integral_const_mul, integral_Ico_eq_intervalIntegral hH q s]
    ring
  have hzero (s : ℝ) (hs : s ∉ {s : ℝ | 1 / 2 < q.endSign * s}) : A s = 0 := by
    have : q.endSign * s ≤ 1 / 2 := not_lt.1 hs
    simp only [A, smoothTransition.deriv_of_neg (by linarith : q.endSign * s - T < 0), zero_mul]
  rw [endStrip_def, Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict] at hint
  have hint' : IntegrableOn (fun s ↦ ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), F (s, t))
      {s : ℝ | 1 / 2 < q.endSign * s} := hint.integral_prod_left
  have hA : IntegrableOn A {s : ℝ | 1 / 2 < q.endSign * s} := by
    refine IntegrableOn.congr_fun (hint'.const_mul (-q.endSign)) (fun s hs ↦ ?_) hS₁
    rw [hinner s hs]
    linear_combination (A s) * q.endSign_mul_self
  refine ⟨?_, hA.integrable_of_forall_notMem_eq_zero hzero⟩
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_endStrip q)
    (fun ζ _ ↦ SymplecticForm.hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q),
    setIntegral_congr_fun (measurableSet_endStrip q) hcongr, endStrip_def,
    Measure.volume_eq_prod, setIntegral_prod _ (by rwa [IntegrableOn, ← Measure.prod_restrict]),
    setIntegral_congr_fun hS₁ hinner, integral_neg, integral_const_mul,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- **The truncated energy identity, for a manifold target.** For `T ≥ 2` with `K = H_q dt`
beyond height `T₀ ≤ T`, the energy density weighted by the cutoff at height `T` integrates to the
weighted symplectic area, plus the signed sum over the three ends of the integrals
`h_q(s) = ∫₀¹ H_q(t, u(φ_q(s, t))) dt` averaged against `β'(±s - T)`, minus the weighted
curvature. -/
private theorem IsNondegenerate.integral_truncation_mul_floerEnergyDensity_eq_sum
    [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {T : ℝ} (hT : 2 ≤ T) (hT₀ : T₀ ≤ T) :
    ∫ z, SymplecticForm.truncation T z * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z, SymplecticForm.truncation T z *
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
          ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t)))) -
        ∫ z, SymplecticForm.truncation T z * ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hzero (z : ℝ × ℝ) (hz : z ∉ ⋃ q, endChart q '' endStrip q) : boundaryForm K u T z = 0 := by
    simp [boundaryForm, SymplecticForm.fderiv_truncation_eq_zero hT hz]
  rw [(hω.integral_truncation_mul_floerEnergyDensity_eq hK hu hR T).2,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_iUnion_fintype (fun q ↦ measurable_image_of_fderivWithin (measurableSet_endStrip q)
      (fun ζ _ ↦ SymplecticForm.hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q))
      pairwise_disjoint_image_endChart
      fun q ↦ (integrable_boundaryForm hK hu T).integrableOn]
  simp only [fun q ↦ (integral_image_endChart_boundaryForm hK hKH hH hu hT hT₀ q).1,
    Finset.sum_neg_distrib]
  ring

end Ends

section Limit

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

omit [IsManifold I ⊤ M] [FiniteDimensional ℝ E] in
/-- As the height tends to infinity, the integrals of the end Hamiltonians averaged against
`β'(±s - T)` tend to their limits along the ends. -/
private theorem tendsto_sum_integral_deriv_smoothTransition_mul
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {h : Puncture → ℝ}
    (hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (h q))) :
    Tendsto (fun T ↦ ∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
      ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t)))) atTop (𝓝 (∑ q, q.endSign * h q)) :=
  tendsto_finsetSum _ fun q _ ↦ by
    have hlim := smoothTransition.tendsto_integral_deriv_mul_sub_mul
      q.endSign_ne_zero (by simpa only [Puncture.inv_endSign] using hh q)
      (eventually_ge_atTop (max 2 T₀) |>.mono fun T hT ↦
        (integral_image_endChart_boundaryForm hK hKH hH hu (le_of_max_le_left hT)
          (le_of_max_le_right hT) q).2)
    rw [abs_endSign, inv_one, one_mul] at hlim
    exact hlim.const_mul _

/-- **The energy identity for perturbations that are cylindrical on the ends, for a manifold
target.** Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a
closed symplectic manifold. Let `K` be a perturbation datum on `S = ℂ ∖ {0, 1}` which is `C¹` on
`S × M`, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate
`z = s + i t`, and which is `H_q(t) dt` beyond the height `T₀` on each end `q`, for period-one
Hamiltonians `H_q`. Let `u` be a map which is `C¹` on `S`, whose Floer energy density, symplectic
area density and curvature term `R_K(u)` are integrable. If on each end `q` the integrals
`∫₀¹ H_q(t, u(φ_q(s, t))) dt` tend to `h_q` as `±s → ∞`, then
`∫ E = ∫ u^*ω + h₀ + h₁ - h_∞ - ∫ R_K(u)`. Below the height `T₀` the datum is only required to be
`C¹`, as for the pair of pants with continuation necks or with compactly supported variations. -/
theorem IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hE : Integrable (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u))
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {h : Puncture → ℝ}
    (hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (h q))) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  -- Both sides are the limits as `T → ∞` of the two sides of the truncated identity, the
  -- weighted integrals converging by dominated convergence.
  refine tendsto_nhds_unique (SymplecticForm.tendsto_integral_truncation_mul hE) ?_
  refine ((((SymplecticForm.tendsto_integral_truncation_mul hA).add
    (tendsto_sum_integral_deriv_smoothTransition_mul hK hKH hH hu hh)).sub
      (SymplecticForm.tendsto_integral_truncation_mul hR))).congr' ?_
  filter_upwards [eventually_ge_atTop (max 2 T₀)] with T hT
  exact (hω.integral_truncation_mul_floerEnergyDensity_eq_sum hK hKH hH hu hR
    (le_of_max_le_left hT) (le_of_max_le_right hT)).symm

/-- **The energy identity for a nonnegative energy density, for a manifold target.** Under the
hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`, suppose
that the Floer energy density of `u` is nonnegative on `S`, as it is for a solution of the Floer
equation with tamed almost complex structures. Then no integrability of the energy density is
needed: the energy of `u`, as a Lebesgue integral, is
`E = ∫ u^*ω + h₀ + h₁ - h_∞ - ∫ R_K(u)`, and in particular it is finite. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {h : Puncture → ℝ}
    (hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (h q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal ((∫ z, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u
  -- The heights `n + max 2 T₀` exhaust `S`.
  set T : ℕ → ℝ := fun n ↦ n + max 2 T₀
  have hT : Tendsto T atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hT₂ (n : ℕ) : 2 ≤ T n := by
    simp only [T]; linarith [n.cast_nonneg (α := ℝ), le_max_left 2 T₀]
  have hT₀ (n : ℕ) : T₀ ≤ T n := by
    simp only [T]; linarith [n.cast_nonneg (α := ℝ), le_max_right 2 T₀]
  have hχe (n : ℕ) : Integrable fun z ↦ SymplecticForm.truncation (T n) z * e z :=
    (hω.integral_truncation_mul_floerEnergyDensity_eq hK hu hR (T n)).1
  -- On each truncation the weighted energy is given by the truncated identity.
  have hid (n : ℕ) : ∫ z, SymplecticForm.truncation (T n) z * e z =
      (∫ z, SymplecticForm.truncation (T n) z *
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T n) *
          ∫ t in (0 : ℝ)..1, H q t (u (endChart q (s, t)))) -
        ∫ z, SymplecticForm.truncation (T n) z * ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) :=
    hω.integral_truncation_mul_floerEnergyDensity_eq_sum hK hKH hH hu hR (hT₂ n) (hT₀ n)
  have hχe₀ (n : ℕ) (z : ℝ × ℝ) : 0 ≤ SymplecticForm.truncation (T n) z * e z := by
    by_cases hz : z ∈ thricePuncturedSphereReal
    · exact mul_nonneg (SymplecticForm.truncation_mem_Icc _ z).1 (he z hz)
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦
        hz (SymplecticForm.mem_tsupport_truncation h), zero_mul]
  -- The weighted energies increase to the energy by monotone convergence.
  have helim : Tendsto (fun n ↦ ∫⁻ z, ENNReal.ofReal (SymplecticForm.truncation (T n) z * e z))
      atTop (𝓝 (∫⁻ z, ENNReal.ofReal (e z))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ (hχe n).aestronglyMeasurable.aemeasurable.ennreal_ofReal) ?_ ?_
    · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz m n hmn
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (SymplecticForm.truncation_le_truncation (by simp only [T]; gcongr) z) (he z hz))
    · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
      have hlim := (ENNReal.continuous_ofReal.tendsto _).comp
        (((SymplecticForm.tendsto_truncation hz).comp hT).mul_const (e z))
      rwa [one_mul] at hlim
  refine tendsto_nhds_unique helim ?_
  simp only [fun n ↦ (ofReal_integral_eq_lintegral_ofReal (hχe n) (ae_of_all _ (hχe₀ n))).symm,
    hid]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((((SymplecticForm.tendsto_integral_truncation_mul hA).comp hT).add
      ((tendsto_sum_integral_deriv_smoothTransition_mul hK hKH hH hu hh).comp hT)).sub
      ((SymplecticForm.tendsto_integral_truncation_mul hR).comp hT))

/-- **A nonnegative energy density is integrable, for a manifold target.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`, the
Floer energy density of `u` is integrable, so
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm` applies to
it. -/
theorem IsNondegenerate.integrable_floerEnergyDensity_of_eq_smul_endAngularForm
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
    {h : Puncture → ℝ}
    (hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (h q))) :
    Integrable (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) := by
  -- The energy density is a limit of the integrable weighted densities, hence measurable.
  have hm : AEStronglyMeasurable (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u) volume := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun n : ℕ ↦ fun z ↦
      SymplecticForm.truncation n z * ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)
      (fun n ↦ (hω.integral_truncation_mul_floerEnergyDensity_eq hK hu hR n).1.1) ?_
    filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
    simpa using ((SymplecticForm.tendsto_truncation hz).comp
      tendsto_natCast_atTop_atTop).mul_const _
  refine ⟨hm, ?_⟩
  rw [HasFiniteIntegral, lintegral_congr_ae (g := fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z)) (by
        filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
        exact Real.eNorm_eq_ofReal (he z hz)),
    hω.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm hK hKH hH hu he hA hR hh]
  exact ENNReal.ofReal_lt_top

end Limit

end SmoothTwoForm

end TauCeti
