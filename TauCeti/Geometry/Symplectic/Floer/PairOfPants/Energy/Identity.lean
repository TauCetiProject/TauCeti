/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# The energy identity on the pair of pants

Let `K` be the Hamiltonian perturbation of the pair of pants `S = ℂ ∖ {0, 1}` built from
period-one Hamiltonians `H_q` on its three ends (`TauCeti.Floer.pairOfPantsPerturbation`), equal
to `H_q(t) dt` far out on each end, and let `u` be a `C²` map from `S` to a symplectic vector space
`(V, ω)`. Assume that the Floer energy density of `u` and the curvature term `R_K(u)` are
integrable over `S`, and that on each end `q` the actions `A_{H_q}` of the loops
`t ↦ u(φ_q(s, t))` (`TauCeti.SymplecticForm.hamiltonianAction`) converge to a limit `A_q` as the
signed longitudinal coordinate `±s` tends to infinity. This file proves the energy identity of the
pair-of-pants product,

`E(u) = A₀ + A₁ - A_∞ - ∫_S R_K(u)`,

where `E(u)` is the integral of the Floer energy density and `R_K` is the curvature of `K`.
The two positive ends at `0` and `1` are the inputs and the negative end at `∞` is the
output. The actions cap each loop by the cone over it, which fixes the area convention. Two caps
of a loop differ by a sphere, and every sphere in `V` has area zero because the symplectic form of
a vector space is exact, `ω = dλ`. So the actions do not depend on the caps, and the spherical
correction `ω(A)` of a product coefficient vanishes.

## Main results

* `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_eq_sum_hamiltonianAction`:
  the energy identity on the pair of pants, in terms of the limits of the end-loop actions.

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
supported in the collars `T ≤ ±s_q ≤ T + 1`, where `K = H_q dt`. Transported to the coordinates
of the ends, the collar integrals are the averages `±∫ β'(±s - T) A_{H_q}(s) ds` of the loop
actions. Letting `T → ∞`, dominated convergence and the convergence of the actions give the
identity. -/

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

private theorem isCompact_preimage_truncation (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' ThricePuncturedSphere.truncation R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)

/-- The cutoff vanishes near the punctures `0` and `1`. -/
private theorem truncation_eventuallyEq_zero (T : ℝ) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z = 0 ∨ Complex.equivRealProdCLM.symm z = 1) :
    truncation T =ᶠ[𝓝 z] 0 := by
  have hz' : z ∉ Complex.equivRealProdCLM.symm ⁻¹' ThricePuncturedSphere.truncation (T + 1) :=
    fun h ↦ by
      obtain ⟨h₀, h₁, -⟩ := mem_truncation.1 h
      exact hz.elim h₀ h₁
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

variable {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- The `ds` component `K_s(u) + ½ ω(u, ∂_s u)` of the one-form `α = K(u) + λ(u)` on the pair of
pants, in the global coordinate. -/
private noncomputable def primitiveS (ω : SymplecticForm V) (H : Puncture → ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) (u z) 1 +
    1 / 2 * ω (u z) (fderiv ℝ u z stdComplexLineReal)

/-- The `dt` component `K_t(u) + ½ ω(u, ∂_t u)` of the one-form `α = K(u) + λ(u)` on the pair of
pants, in the global coordinate. -/
private noncomputable def primitiveT (ω : SymplecticForm V) (H : Puncture → ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) (u z) Complex.I +
    1 / 2 * ω (u z) (fderiv ℝ u z stdComplexLineImag)

omit [FiniteDimensional ℝ V] in
/-- The perturbation evaluated along a `C¹` map is `C¹` on the thrice-punctured sphere. -/
private theorem contDiffAt_pairOfPantsPerturbation_comp (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hu : ContDiffAt ℝ 1 u z) (v : ℂ) :
    ContDiffAt ℝ 1 (fun z ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) (u z) v)
      z :=
  (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) v).comp
    (f := fun z ↦ (z, u z)) z (contDiffAt_id.prodMk hu)

private theorem contDiffOn_primitiveS (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) :
    ContDiffOn ℝ 1 (primitiveS ω H u) thricePuncturedSphereReal := fun z hz ↦ by
  have hu' := hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)
  exact ((contDiffAt_pairOfPantsPerturbation_comp hH hHs hz (hu'.of_le one_le_two) 1).add
    (contDiffAt_const.mul (ω.toBilinForm.toContinuousBilinearMap.contDiffAt_bilinear_fderiv_apply
      hu' _))).contDiffWithinAt

private theorem contDiffOn_primitiveT (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) :
    ContDiffOn ℝ 1 (primitiveT ω H u) thricePuncturedSphereReal := fun z hz ↦ by
  have hu' := hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)
  exact ((contDiffAt_pairOfPantsPerturbation_comp hH hHs hz (hu'.of_le one_le_two) _).add
    (contDiffAt_const.mul (ω.toBilinForm.toContinuousBilinearMap.contDiffAt_bilinear_fderiv_apply
      hu' _))).contDiffWithinAt

/-- On the thrice-punctured sphere, the energy density plus the curvature of the pair-of-pants
perturbation is the exterior derivative of `α = K(u) + λ(u)`. -/
private theorem floerEnergyDensity_add_hamiltonianCurvature_eq_primitive (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z
        (u z) =
      fderiv ℝ (primitiveT ω H u) z stdComplexLineReal -
        fderiv ℝ (primitiveS ω H u) z stdComplexLineImag :=
  -- `primitiveS` and `primitiveT` are by definition the components of `α` in the general identity.
  ω.floerEnergyDensity_add_hamiltonianCurvature_eq
    (hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz))
    ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz _ _).differentiableAt one_ne_zero)
    ((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz _ _).differentiableAt one_ne_zero)

/-- A function continuous on the thrice-punctured sphere becomes integrable after multiplication
by the cutoff. -/
private theorem integrable_truncation_mul (T : ℝ) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F thricePuncturedSphereReal) : Integrable fun z ↦ truncation T z * F z :=
  (contDiff_truncation T).continuous.integrable_mul_of_continuousOn
    (hasCompactSupport_truncation T) isOpen_thricePuncturedSphereReal
    (fun _ hz ↦ mem_tsupport_truncation hz) hF

/-- A function continuous on the thrice-punctured sphere becomes integrable after multiplication
by a derivative of the cutoff. -/
private theorem integrable_fderiv_truncation_mul (T : ℝ) (v : ℝ × ℝ) {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F thricePuncturedSphereReal) :
    Integrable fun z ↦ fderiv ℝ (truncation T) z v * F z :=
  (((contDiff_truncation T).continuous_fderiv one_ne_zero).clm_apply
    continuous_const).integrable_mul_of_continuousOn
    ((hasCompactSupport_truncation T).fderiv_apply (𝕜 := ℝ) v) isOpen_thricePuncturedSphereReal
    (fun _ hz ↦ mem_tsupport_truncation (tsupport_fderiv_apply_subset ℝ v hz)) hF

/-- The two-form `dχ ∧ α` for the cutoff `χ` at height `T` and the one-form `α = K(u) + λ(u)`,
evaluated on `(∂_s, ∂_t)`. -/
private noncomputable def boundaryForm (ω : SymplecticForm V) (H : Puncture → ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  fderiv ℝ (truncation T) z stdComplexLineReal * primitiveT ω H u z -
    fderiv ℝ (truncation T) z stdComplexLineImag * primitiveS ω H u z

private theorem integrable_boundaryForm (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (T : ℝ) :
    Integrable (boundaryForm ω H u T) :=
  (integrable_fderiv_truncation_mul T _ (contDiffOn_primitiveT ω hH hHs hu).continuousOn).sub
    (integrable_fderiv_truncation_mul T _ (contDiffOn_primitiveS ω hH hHs hu).continuousOn)

/-- **Integration by parts against the cutoff.** The energy density plus the curvature, weighted by
the cutoff at height `T`, integrates to minus the integral of `dχ ∧ α`, for the one-form
`α = K(u) + λ(u)`. -/
private theorem integral_truncation_mul_eq (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (T : ℝ) :
    ∫ z, truncation T z * (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z
        (u z)) =
      -∫ z, boundaryForm ω H u T z := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hS := contDiffOn_primitiveS ω hH hHs hu
  have hT := contDiffOn_primitiveT ω hH hHs hu
  have hχS : tsupport (truncation T) ⊆ thricePuncturedSphereReal := fun z hz ↦
    mem_tsupport_truncation hz
  have hfd {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F thricePuncturedSphereReal) (v : ℝ × ℝ) :
      ContinuousOn (fun z ↦ fderiv ℝ F z v) thricePuncturedSphereReal :=
    (hF.continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl).clm_apply
      continuousOn_const
  -- Integration by parts in the direction `v`, for a component `F` of `α`.
  have hparts {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F thricePuncturedSphereReal) (v : ℝ × ℝ) :
      ∫ z, truncation T z * fderiv ℝ F z v = -∫ z, fderiv ℝ (truncation T) z v * F z :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_fderiv_truncation_mul T v hF.continuousOn)
      (integrable_truncation_mul T (hfd hF v)) (integrable_truncation_mul T hF.continuousOn)
      (fun z _ ↦ (contDiff_truncation T).differentiable one_ne_zero z)
      (fun z hz ↦ (hF.differentiableOn one_ne_zero z (hχS hz)).differentiableAt
        (isOpen_thricePuncturedSphereReal.mem_nhds (hχS hz)))
  calc _ = ∫ z, (truncation T z * fderiv ℝ (primitiveT ω H u) z stdComplexLineReal -
        truncation T z * fderiv ℝ (primitiveS ω H u) z stdComplexLineImag) := by
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        dsimp only
        by_cases hz : z ∈ thricePuncturedSphereReal
        · rw [floerEnergyDensity_add_hamiltonianCurvature_eq_primitive ω hH hHs hu hz, mul_sub]
        · have h0 : truncation T z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hz (hχS h)
          simp [h0]
    _ = _ := by
        rw [integral_sub (integrable_truncation_mul T (hfd hT _))
          (integrable_truncation_mul T (hfd hS _)), hparts hT, hparts hS]
        simp only [boundaryForm]
        rw [integral_sub (integrable_fderiv_truncation_mul T _ hT.continuousOn)
          (integrable_fderiv_truncation_mul T _ hS.continuousOn)]
        ring

end Parts

section Ends

variable {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

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

omit [FiniteDimensional ℝ V] in
/-- **The boundary term in end coordinates.** On the end `q`, for `T ≥ 2`, the two-form
`dχ ∧ α`, transported to the coordinates of the end with its Jacobian, is
`-±β'(±s - T) (H_q(t, u_q) + ½ ω(u_q, ∂_t u_q))` for `u_q = u ∘ φ_q`. -/
private theorem abs_det_mul_wedge_endChart (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {T : ℝ} (hT : 2 ≤ T) {q : Puncture}
    {ζ : ℝ × ℝ} (hζ : 0 < q.endSign * ζ.1) :
    |(fderiv ℝ (endChart q) ζ).det| *
        (fderiv ℝ (truncation T) (endChart q ζ) stdComplexLineReal *
            primitiveT ω H u (endChart q ζ) -
          fderiv ℝ (truncation T) (endChart q ζ) stdComplexLineImag *
            primitiveS ω H u (endChart q ζ)) =
      -(q.endSign * deriv smoothTransition (q.endSign * ζ.1 - T) *
        (H q ζ.2 (u (endChart q ζ)) +
          1 / 2 * ω (u (endChart q ζ)) (fderiv ℝ (u ∘ endChart q) ζ stdComplexLineImag))) := by
  set L := fderiv ℝ (endChart q) ζ
  set κ := fderiv ℝ (truncation T) (endChart q ζ)
  set x := u (endChart q ζ)
  have hw := endChart_mem_thricePuncturedSphereReal hζ
  have hφ : DifferentiableAt ℝ (endChart q) ζ := (hasFDerivAt_endChart q ζ).differentiableAt
  have hu₁ : DifferentiableAt ℝ u (endChart q ζ) :=
    (hu.differentiableOn (by norm_num) _ hw).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds hw)
  have hκ (v : ℝ × ℝ) :
      κ (L v) = -(deriv smoothTransition (q.endSign * ζ.1 - T) * q.endSign) * v.1 :=
    fderiv_truncation_endChart_apply (by linarith) hζ v
  -- The pulled-back one-form `α ∘ dφ` on `∂_t` is `K` in end coordinates plus `½ ω(u_q, ∂_t u_q)`.
  have hdu (e : ℝ × ℝ) : fderiv ℝ u (endChart q ζ) e =
      e.1 • fderiv ℝ u (endChart q ζ) stdComplexLineReal +
        e.2 • fderiv ℝ u (endChart q ζ) stdComplexLineImag := by
    simpa using (fderiv ℝ u (endChart q ζ) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine e
  have hK := congrFun (congrFun (perturbationPullback_endChart (H := H) q stdComplexLineImag) ζ) x
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  rw [hI, perturbationPullback_apply] at hK
  have hα : (L stdComplexLineImag).1 * primitiveS ω H u (endChart q ζ) +
      (L stdComplexLineImag).2 * primitiveT ω H u (endChart q ζ) =
        pairOfPantsEndComponent H q Complex.I ζ x +
          1 / 2 * ω x (fderiv ℝ (u ∘ endChart q) ζ stdComplexLineImag) := by
    rw [fderiv_comp ζ hu₁ hφ, ContinuousLinearMap.comp_apply, hdu, ← hK]
    simp only [primitiveS, primitiveT, map_add, map_smul, smul_eq_mul]
    ring
  -- The Jacobian times `dχ ∧ α` is the wedge of the pullbacks of `dχ` and `α` along `dφ`.
  set a := primitiveS ω H u (endChart q ζ)
  set b := primitiveT ω H u (endChart q ζ)
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
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q ζ), hwedge, hκ, hκ, hα]
  simp only [stdComplexLineReal_fst, stdComplexLineImag_fst, mul_zero, zero_mul, sub_zero,
    mul_one]
  -- Where `β'(±s - T) ≠ 0`, the end coordinate satisfies `±s ≥ T ≥ 2`, so `K = H_q dt` there.
  by_cases hs : 2 ≤ q.endSign * ζ.1
  · rw [pairOfPantsEndComponent_I_of_pos (hH q) hζ,
      smoothTransition.one_of_one_le (by linarith), one_mul]
    ring
  · rw [smoothTransition.deriv_of_neg (by linarith)]
    ring

/-- On the end `q`, the integral over one period of `H_q(t, u_q) + ½ ω(u_q, ∂_t u_q)` is the
action of the loop `t ↦ u_q(s, t)`, for `u_q = u ∘ φ_q`. -/
private theorem integral_Ico_eq_hamiltonianAction (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
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
  have hper : Periodic x 1 := fun t ↦ by
    have h := q.periodic_cylindricalEndLift s t
    simp only [x, endChart_apply, Complex.equivRealProdCLM_symm_apply]
    push_cast at h ⊢
    rw [h]
  have hper' : Periodic (deriv x) 1 := fun t ↦ by
    rw [← deriv_comp_add_const]
    exact congrArg (deriv · t) (funext hper)
  -- The integrand is continuous and periodic, so its integral over any period is the same.
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦
    ((huq t).continuousAt).comp (continuous_const.prodMk continuous_id).continuousAt
  have hdxc : Continuous (deriv x) := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    simp only [funext hderiv]
    exact (((huq t).fderiv_right (m := 1) (by norm_num)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).clm_apply continuousAt_const
  have hHc : Continuous fun t ↦ H q t (x t) :=
    (hHs q).continuous.comp (continuous_id.prodMk hxc)
  have hωc : Continuous fun t ↦ ω (x t) (deriv x t) := ω.continuous_apply_comp hxc hdxc
  have hG : Periodic (fun t ↦ H q t (x t) + 1 / 2 * ω (x t) (deriv x t)) 1 := fun t ↦ by
    simp only [hper t, hper' t, hH q t]
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

/-- **The boundary term on one end.** For `T ≥ 2`, the integral of `dχ ∧ α` over the end `q` is
`-±∫ β'(±s - T) A_q(s) ds`, where `A_q(s)` is the action of the loop `t ↦ u(φ_q(s, t))`; the
weighted actions are integrable. -/
private theorem integral_image_endChart_boundaryForm (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {T : ℝ} (hT : 2 ≤ T) (q : Puncture) :
    ∫ z in endChart q '' endStrip q, boundaryForm ω H u T z =
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
  have hcongr : EqOn (fun ζ ↦ |(fderiv ℝ (endChart q) ζ).det| • boundaryForm ω H u T (endChart q ζ))
      F (endStrip q) := fun ζ hζ ↦ by
    dsimp only
    rw [smul_eq_mul, boundaryForm]
    exact abs_det_mul_wedge_endChart ω hH hu hT (endSign_mul_pos_of_mem_endStrip hζ)
  have hint : IntegrableOn F (endStrip q) :=
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_endStrip q)
      (fun ζ _ ↦ hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q) _).1
      (integrable_boundaryForm ω hH hHs hu T).integrableOn).congr_fun hcongr
      (measurableSet_endStrip q)
  -- Integrating out the angular coordinate gives the actions of the loops.
  have hinner (s : ℝ) (hs : s ∈ {s : ℝ | 1 / 2 < q.endSign * s}) :
      ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), F (s, t) = -(q.endSign * A s) := by
    have hs' : 0 < q.endSign * s := by
      have : 1 / 2 < q.endSign * s := hs
      linarith
    simp only [F, A]
    rw [integral_neg, integral_const_mul, integral_Ico_eq_hamiltonianAction ω hH hHs hu hs']
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

omit [FiniteDimensional ℝ V] in
/-- Away from the three end strips the cutoff at height `T ≥ 2` is locally constant, so the
boundary term vanishes there. -/
private theorem boundaryForm_eq_zero (ω : SymplecticForm V) {T : ℝ} (hT : 2 ≤ T) {z : ℝ × ℝ}
    (hz : z ∉ ⋃ q, endChart q '' endStrip q) : boundaryForm ω H u T z = 0 := by
  have hfd : fderiv ℝ (truncation T) z = 0 := by
    by_cases hzS : z ∈ thricePuncturedSphereReal
    · have hT' (q : Puncture) : endHeight q z < T := by
        by_contra h
        rw [not_lt, endHeight] at h
        exact hz (mem_iUnion.2 ⟨q, mem_image_endChart hzS (by linarith)⟩)
      rw [(truncation_eventuallyEq_one hzS hT').fderiv_eq, fderiv_const_apply]
    · simp only [mem_thricePuncturedSphereReal_iff, not_and_or, not_not] at hzS
      rw [(truncation_eventuallyEq_zero T hzS).fderiv_eq]
      simp
  simp [boundaryForm, hfd]

/-- **The truncated energy identity.** For `T ≥ 2`, the energy density plus the curvature,
weighted by the cutoff at height `T`, integrates to the signed sum over the three ends of the
actions `A_q(s)` of the loops `t ↦ u(φ_q(s, t))`, averaged against `β'(±s - T)`. -/
private theorem integral_truncation_mul_eq_sum (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {T : ℝ} (hT : 2 ≤ T) :
    ∫ z, truncation T z * (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z
        (u z)) =
      ∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
        ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t))) := by
  rw [integral_truncation_mul_eq ω hH hHs hu T,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ boundaryForm_eq_zero ω hT hz,
    integral_iUnion_fintype (fun q ↦ measurable_image_of_fderivWithin (measurableSet_endStrip q)
      (fun ζ _ ↦ hasFDerivWithinAt_endChart q ζ _) (injOn_endChart q))
      pairwise_disjoint_image_endChart
      fun q ↦ (integrable_boundaryForm ω hH hHs hu T).integrableOn]
  simp only [fun q ↦ (integral_image_endChart_boundaryForm ω hH hHs hu hT q).1,
    Finset.sum_neg_distrib, neg_neg]

end Ends

section Limit

variable {H : Puncture → ℝ → V → ℝ} {u : ℝ × ℝ → V}

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
        (u z) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set f : ℝ × ℝ → ℝ := fun z ↦ ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z +
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  have hf : Integrable f := hE.add hR
  -- The punctures form a null set.
  have hae : ∀ᵐ z : ℝ × ℝ, z ∈ thricePuncturedSphereReal := by
    refine measure_mono_null (t := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1})
      (fun z hz ↦ ?_) ?_
    · have hz' := mem_thricePuncturedSphereReal_iff.not.1 hz
      rcases not_and_or.1 hz' with h | h
      · exact Or.inl (by rw [← not_not.1 h, ContinuousLinearEquiv.apply_symm_apply])
      · exact Or.inr (by
          rw [Set.mem_singleton_iff, ← not_not.1 h, ContinuousLinearEquiv.apply_symm_apply])
    · rw [Measure.volume_eq_prod]
      exact (Set.toFinite _).measure_zero _
  -- As `T → ∞`, the truncated energies tend to the full integral by dominated convergence.
  have hlhs : Tendsto (fun T ↦ ∫ z, truncation T z * f z) atTop (𝓝 (∫ z, f z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖f z‖)
      (Eventually.of_forall fun T ↦
        (contDiff_truncation T).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (Eventually.of_forall fun T ↦ ae_of_all _ fun z ↦ ?_) hf.norm ?_
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [Real.norm_of_nonneg (truncation_mem_Icc T z).1]
        exact (truncation_mem_Icc T z).2)
    · filter_upwards [hae] with z hz
      simpa using (tendsto_truncation hz).mul_const (f z)
  -- The averaged actions on the ends tend to the limiting actions.
  have hrhs : Tendsto (fun T ↦ ∑ q, q.endSign * ∫ s, deriv smoothTransition (q.endSign * s - T) *
      ω.hamiltonianAction (H q) (fun t ↦ u (endChart q (s, t)))) atTop
      (𝓝 (∑ q, q.endSign * A q)) :=
    tendsto_finsetSum _ fun q _ ↦ by
      have h := smoothTransition.tendsto_integral_deriv_mul_sub_mul
        q.endSign_ne_zero (by simpa only [Puncture.inv_endSign] using hA q)
        (eventually_ge_atTop 2 |>.mono fun T hT ↦
          (integral_image_endChart_boundaryForm ω hH hHs hu hT q).2)
      rw [abs_endSign, inv_one, one_mul] at h
      exact h.const_mul _
  have heq : ∫ z, f z = ∑ q, q.endSign * A q :=
    tendsto_nhds_unique (hlhs.congr' (eventually_ge_atTop 2 |>.mono fun T hT ↦
      integral_truncation_mul_eq_sum ω hH hHs hu hT)) hrhs
  rw [← heq, integral_add hE hR]
  ring

end Limit

end SymplecticForm

end TauCeti
