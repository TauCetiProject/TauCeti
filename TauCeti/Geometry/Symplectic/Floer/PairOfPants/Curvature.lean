/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Curvature
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The integrated curvature of the pair-of-pants perturbation

The energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants turns a bound
`∫_S sup_X |R_K| ≤ C` on the curvature of the perturbation datum `K` into the lower bound on the
valuation of product coefficients and the upper bound on the energy of the curves they count.
This file computes such a constant `C` for the perturbation
`TauCeti.Floer.pairOfPantsPerturbation` built from period-one Hamiltonians `H_q` on the three ends
of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`. The curvature bound holds for Hamiltonians on any
manifold `M` with a two-form `ω`, such as a closed symplectic manifold.

In the coordinates `(s, t)` of the end `q` the perturbation is `β(±s) H_q(t) dt` with the cutoff
`β(±s) = smoothTransition (±s - 1)`
(`TauCeti.Floer.pairOfPantsPerturbation_cylindricalEndLift_of_pos`), so its curvature there is the
continuation curvature `±β'(±s - 1) H_q(t)`
(`SmoothTwoForm.hamiltonianCurvature_pairOfPantsEndComponent`), and the perturbation vanishes
off the parts `±s > 1` of the ends. Since the curvature is a two-form
(`SmoothTwoForm.hamiltonianCurvature_perturbationPullback`), its absolute integral over
`S` is the sum over the three ends of the integrals of `β'(±s - 1) |H_q(t)|` over half-cylinders,
and the cutoff has total increase `∫ β' = 1`. Hence, if `|H_q| ≤ B_q`, then

`∫_S |R_K(z, u(z))| dz ≤ B₀ + B₁ + B_∞`

for every map `u : S → M`, measurable or not
(`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`). The bound uses
only that `K_s ds + K_t dt` is a multiple of `H_q(t) dt` on each end, so the Poisson bracket term
of the curvature vanishes there, whatever the target; for a vector space target it specializes to
`SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`. The curvature
is computed in the global coordinate `z = s + i t` of `S ⊆ ℂ`, in which the `ds` and `dt`
components of `K` are its values on the tangent vectors `1` and `i`.

The curvature vanishes beyond the collars `1 ≤ ±s ≤ 2` of the ends
(`SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`), so along a map
continuous on `S` into a vector space it is integrable over `S`. For a manifold target and a map `u`
which is `C¹` on `S`, the pointwise energy identity `E = u^*ω + d(K(u)) - R_K(u)` holds on `S`,
where `d(K(u))` is continuous. If the energy density and the area density of `u` are integrable
over `S`, the curvature is therefore measurable on `S`, and with the bound above it is integrable
over `S`. These bounds feed the energy identity on the truncated and on the whole pair of pants,
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Truncation`.

The two-sided constant `B₀ + B₁ + B_∞` does not behave well under a change of normalization
`H_q ↦ H_q + c_q(t)`, which leaves the Floer equation unchanged and shifts the actions of the ends
by `∫₀¹ c_q`. A one-sided constant transforms correctly. Let `h_q` be functions of time,
integrable over one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output end.
In the coordinates of the end `q` the curvature, multiplied by the Jacobian of the end chart, is
`±β'(±s - 1) H_q(t)`, and `β' ≥ 0` has integral one. Since the curvature is supported in the
disjoint images of the strips of the ends, the change of variables formula gives

`∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞ ≤ ∫_S R_K(u)`.

For the best choices `h_q = inf H_q(t, ·)` on the inputs and `h_∞ = sup H_∞(t, ·)`, when they are
integrable, this is the estimate of Schwarz.

## Main results

* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`: the
  integrated curvature of the pair-of-pants perturbation along any map into a manifold is at most
  the sum of bounds for the three end Hamiltonians.
* `SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le`: hence the
  integral of the curvature over any set has absolute value at most the same sum.
* `SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`: the curvature
  vanishes where the perturbation is cylindrical, beyond the collars `1 ≤ ±s ≤ 2` of the ends.
* `TauCeti.Floer.continuousOn_fderiv_pairOfPantsPerturbation`: along a map `C¹` on `S`, the
  derivatives of the components of the perturbation are continuous on `S`.
* `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_pairOfPantsPerturbation_eq`: the pointwise
  energy identity on `S`, for a manifold target.
* `SmoothTwoForm.IsNondegenerate.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the
  curvature along a map `C¹` on `S`, with integrable energy and area densities, is integrable over
  `S`.
* `SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`,
  `SymplecticForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le`,
  `SymplecticForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`: the same
  statements for a symplectic vector space target.
* `SymplecticForm.integrableOn_truncation_pairOfPantsPerturbation`: along a map `C¹` on `S`, the
  energy, area and curvature densities are integrable over every truncation.
* `SymplecticForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the curvature along a
  map continuous on `S` is integrable over `S`.
* `SymplecticForm.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation`:
  the one-sided curvature bound.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the one-sided action estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ}

/-- Along a map `u` which is `C¹` on `S`, the derivative in the domain point of a component
`z ↦ K(z)(v)(u(z))` of the pair-of-pants perturbation of period-one `C¹` Hamiltonians on a manifold
is continuous on `S`. -/
theorem continuousOn_fderiv_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (v : ℂ) :
    ContinuousOn (fderiv ℝ (fun w ↦
      pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v))
      thricePuncturedSphereReal := by
  have hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := fun p hp ↦
    (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hp.1 p.2 v).contMDiffWithinAt
  exact (contMDiffOn_iff_contDiffOn.mp (hK.comp (contMDiffOn_id.prodMk hu)
    fun _ hz ↦ ⟨hz, mem_univ _⟩)).continuousOn_fderiv_of_isOpen
      isOpen_thricePuncturedSphereReal le_rfl

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ}

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`, for `C¹` Hamiltonians on a manifold. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ pairOfPantsPerturbation H w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_pairOfPantsPerturbation hH hHs
      ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp (f := fun w : ℂ ↦ (w, x)) _
      (contMDiffAt_id.prodMk contMDiffAt_const)
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- The components of the perturbation are differentiable in the target point, at points
of `S`, for `C¹` Hamiltonians on a manifold. -/
private theorem mdifferentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  (((contMDiffAt_pairOfPantsPerturbation hH hHs
    ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x).comp
      (f := fun y : M ↦ (Complex.equivRealProdCLM.symm z, y)) x
      (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply contMDiffAt_const).mdifferentiableAt
    one_ne_zero

variable [IsManifold I ⊤ M]

/-- **The curvature in the coordinates of an end.** On the end `q`, where `±s > 0`, the curvature
of the pulled-back perturbation `β(±s) H_q(t) dt` is `±β'(±s - 1) H_q(t)`. -/
private theorem hamiltonianCurvature_perturbationPullback_endChart (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {q : Puncture}
    {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) (x : M) :
    ω.hamiltonianCurvature
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (endChart q)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) z x =
      q.endSign * deriv smoothTransition (q.endSign * z.1 - 1) * H q z.2 x := by
  have hHt : DifferentiableAt ℝ (fun t ↦ H q t x) z.2 :=
    (((hHs q).contMDiffAt.comp (f := fun t : ℝ ↦ (t, x)) z.2
      (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).differentiableAt one_ne_zero
  rw [perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hz hHt]

/-- **The curvature on an end.** The curvature is a two-form, so on the end `q` it is
`±β'(±s - 1) H_q(t)` divided by the Jacobian of the end chart. -/
private theorem det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {q : Puncture}
    {ζ : ℝ × ℝ} (hζ : 0 < q.endSign * ζ.1) (x : M) :
    (fderiv ℝ (endChart q) ζ).det * ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (endChart q ζ) x =
      q.endSign * deriv smoothTransition (q.endSign * ζ.1 - 1) * H q ζ.2 x := by
  have hS := endChart_mem_thricePuncturedSphereReal hζ
  have k := ω.hamiltonianCurvature_perturbationPullback (φ := endChart q) (w := ζ)
    (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (x := x) ((contDiff_endChart q 2).contDiffAt)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS _ 1)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS _ Complex.I)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ 1)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ Complex.I)
  rw [hamiltonianCurvature_perturbationPullback_endChart ω hH hHs hζ] at k
  exact k.symm

/-- The curvature of the perturbation over the image of the strip of the end `q` is at most a
bound `B_q` for the Hamiltonian of that end: the cutoff `β(±s - 1)` has total increase one. -/
private theorem setLIntegral_image_endChart_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) (q : Puncture) :
    ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B q) := by
  have hβ : ∫⁻ s, ‖deriv (fun σ ↦ smoothTransition (σ - 1)) (q.endSign * s)‖ₑ = 1 := by
    simp_rw [deriv_comp_sub_const, Real.enorm_eq_ofReal smoothTransition.monotone.deriv_nonneg]
    rw [smoothTransition.lintegral_ofReal_deriv_mul_sub _ q.endSign_ne_zero, abs_endSign, inv_one,
      ENNReal.ofReal_one]
  -- The datum is differentiable jointly, hence separately, in the domain and target points.
  have hK {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) :=
    (contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs ⟨w, hw⟩ x).mdifferentiableAt
      one_ne_zero
  have hdom {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) (v : ℂ) :
      DifferentiableAt ℝ (fun w' ↦ pairOfPantsPerturbation H w' x v) w :=
    ((hK hw x).comp (f := fun w' : ℂ ↦ (w', x)) w
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt.clm_apply
        (differentiableAt_const v)
  have htgt {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) (v : ℂ) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ pairOfPantsPerturbation H w y v) x :=
    ((hK hw x).comp (f := fun y : M ↦ (w, y)) x
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)).clm_apply mdifferentiableAt_const
  have hHt (x : M) : Differentiable ℝ fun t ↦ H q t x :=
    (((hHs q).comp (f := fun t : ℝ ↦ (t, x)) (contMDiff_id.prodMk contMDiff_const)).contDiff
      ).differentiable one_ne_zero
  refine (ω.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le
    (P := fun σ ↦ smoothTransition (σ - 1)) (fun w hw x v ↦ hdom hw x v)
    (fun w hw x v ↦ htgt hw x v)
    (fun z hz x v ↦ pairOfPantsPerturbation_cylindricalEndLift_of_pos (hH q) hz x v)
    (fun σ ↦ (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.comp σ
      (differentiableAt_id.sub_const 1)) hHt (hB q) u).trans_eq ?_
  rw [hβ, one_mul]

/-- **The integrated curvature of the pair-of-pants perturbation, for a manifold target.** Let `K`
be the pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a manifold `M` with a
two-form `ω`, attached to the three ends of `S = ℂ ∖ {0, 1}`, with `|H_q| ≤ B_q`, and write its
components in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)`. Then for every map `u` into `M`, the integral of `|R_K(z, u(z))|` over the
plane is at most `B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) :=
  (ω.lintegral_enorm_hamiltonianCurvature_le_sum_endStrip
    (fun _ hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y) u).trans
    (Finset.sum_le_sum fun q _ ↦ setLIntegral_image_endChart_le ω hH hHs hB u q)

/-- The integral of the curvature of the pair-of-pants perturbation along any map into a manifold,
over any set, has absolute value at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q _ => hB₀ q),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_sum_of_nonneg fun q _ => hB₀ q]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u))

/-- **The curvature vanishes on the cylindrical parts of the ends, for a manifold target.** At a
point of `S` where the signed longitudinal coordinate of some end is greater than `2`, the
perturbation is `H_q(t) dt` in the coordinates of that end, and its curvature vanishes. Together
with the vanishing of the perturbation on the core, this confines the curvature to the collars
`1 ≤ ±s ≤ 2` of the three ends, a compact part of `S`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (x : M) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  obtain ⟨w, hw, rfl⟩ := mem_image_endChart hz (q := q) (by linarith)
  have hw₂ : 2 < q.endSign * w.1 := by rwa [re_endCoord_endChart] at hq
  -- In the coordinates of the end the curvature is `±β'(±s - 1) H_q(t)`, and `β' = 0` there.
  have key := det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart ω hH hHs
    (by linarith : 0 < q.endSign * w.1) x
  have hβ : deriv smoothTransition (q.endSign * w.1 - 1) = 0 :=
    smoothTransition.deriv_of_one_lt (by linarith)
  rw [hβ, mul_zero, zero_mul] at key
  exact (mul_eq_zero.1 key).resolve_left (det_fderiv_endChart_pos q w).ne'

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {u : ℝ × ℝ → M}

/-- **The pointwise energy identity on the pair of pants, for a manifold target.** For the
pair-of-pants perturbation `K` of period-one `C¹` Hamiltonians and a map `u` which is `C¹` on `S`,
the energy identity `E = u^*ω + d(K(u)) - R_K(u)` holds at every point of `S`. -/
theorem IsNondegenerate.floerEnergyDensity_pairOfPantsPerturbation_eq (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w)
            Complex.I) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) 1)
            z stdComplexLineImag) -
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) :=
  hω.floerEnergyDensity_eq
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz)).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) 1).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz (u z) Complex.I).mdifferentiableAt
      one_ne_zero)

/-- **The curvature is integrable over the pair of pants, for a manifold target.** Let `u` be `C¹`
on `S`, with Floer energy density and symplectic area density integrable over `S`, for the
pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians. Then the curvature `R_K(u)` is
integrable over `S`: it is the area density plus the continuous exterior derivative `d(K(u))`
minus the energy density, hence measurable, and its absolute integral is at most `B₀ + B₁ + B_∞`.
-/
theorem IsNondegenerate.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      thricePuncturedSphereReal := by
  have hSm := isOpen_thricePuncturedSphereReal.measurableSet
  refine ⟨?_, ?_⟩
  · have hd := ((continuousOn_fderiv_pairOfPantsPerturbation hH hHs hu Complex.I).clm_apply
      (continuousOn_const (c := stdComplexLineReal))).sub
      ((continuousOn_fderiv_pairOfPantsPerturbation hH hHs hu 1).clm_apply
        (continuousOn_const (c := stdComplexLineImag)))
    refine ((hA.aestronglyMeasurable.add (hd.aestronglyMeasurable hSm)).sub
      hE.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    simp only [Pi.add_apply, Pi.sub_apply,
      hω.floerEnergyDensity_pairOfPantsPerturbation_eq hH hHs hu hz]
    ring
  · have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
    refine ((setLIntegral_le_lintegral _ _).trans
      (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u)).trans_lt ?_
    exact ENNReal.sum_lt_top.2 fun q _ ↦ ENNReal.ofReal_lt_top

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- `C¹` Hamiltonians on a vector space are `C¹` maps of manifolds. -/
private theorem contMDiff_uncurry_of_contDiff
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
  contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff

/-- The components of the perturbation in real coordinates are differentiable in the domain
point, at points of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z :=
  SmoothTwoForm.differentiableAt_pairOfPantsPerturbation_domain hH
    (contMDiff_uncurry_of_contDiff hHs) hz x v

variable [FiniteDimensional ℝ V]

/-- **The curvature on an end.** The curvature is a two-form, so on the end `q` it is
`±β'(±s - 1) H_q(t)` divided by the Jacobian of the end chart. -/
private theorem det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {q : Puncture} {ζ : ℝ × ℝ} (hζ : 0 < q.endSign * ζ.1) (x : V) :
    (fderiv ℝ (endChart q) ζ).det * ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (endChart q ζ) x =
      q.endSign * deriv smoothTransition (q.endSign * ζ.1 - 1) * H q ζ.2 x := by
  simpa using
    ω.constSmooth.det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart hH
      (contMDiff_uncurry_of_contDiff hHs) hζ x

/-- **The integrated curvature of the pair-of-pants perturbation.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
`|H_q| ≤ B_q`, and write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map `u` into the target, the integral
of `|R_K(z, u(z))|` over the plane is at most `B₀ + B₁ + B_∞`. This is the vector-space case of
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le hH
    (contMDiff_uncurry_of_contDiff hHs) hB u

/-- The integral of the curvature of the pair-of-pants perturbation along any map, over any set,
has absolute value at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → V) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, B q := by
  simpa using ω.constSmooth.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le hH
    (contMDiff_uncurry_of_contDiff hHs) hB u s

/-! ### Vanishing and integrability of the curvature -/

/-- The points of `S`, in real coordinates, form an open set. -/
private theorem isOpen_puncturedSphere :
    IsOpen {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} :=
  isOpen_thricePuncturedSphereReal

/-- **The curvature vanishes on the cylindrical parts of the ends.** At a point of `S` where the
signed longitudinal coordinate of some end is greater than `2`, the perturbation is `H_q(t) dt` in
the coordinates of that end, and its curvature vanishes. Together with
`hamiltonianCurvature_pairOfPantsPerturbation_eq_zero` on the core, this confines the curvature to
the collars `1 ≤ ±s ≤ 2` of the three ends, a compact part of `S`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1)
    {q : Puncture} (hq : 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (x : V) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  simpa using ω.constSmooth.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH
    (contMDiff_uncurry_of_contDiff hHs) hz hq x

omit [FiniteDimensional ℝ V] in
/-- The components of the perturbation in real coordinates are `C¹` jointly in the domain point
of `S` and the target point. -/
private theorem contDiffOn_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contDiffWithinAt

/-- The Floer energy density, the symplectic area density and the curvature of the pair-of-pants
perturbation, along a map that is `C¹` on `S`, are integrable over every truncation. -/
theorem integrableOn_truncation_pairOfPantsPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal) (R : ℝ) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
  have hTS : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal :=
    fun z hz =>
      mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  have hKs := contDiffOn_pairOfPantsPerturbation hH hHs 1
  have hKt := contDiffOn_pairOfPantsPerturbation hH hHs Complex.I
  have hdu := hu.continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl
  refine ⟨?_, ?_, ?_⟩
  · exact ((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu hKs hKt).mono
      hTS).integrableOn_compact hT
  · exact ((ω.continuousOn_apply_comp (hdu.clm_apply continuousOn_const)
      (hdu.clm_apply continuousOn_const)).mono hTS).integrableOn_compact hT
  · exact ((ω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal
      hu.continuousOn hKs hKt).mono hTS).integrableOn_compact hT

/-- **The curvature is integrable over the pair of pants.** Along a map `u` which is continuous
on `S`, the curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians is
integrable over `S`: it is continuous on `S` and vanishes off the compact truncation `S_2`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1} := by
  have hc := ω.continuousOn_hamiltonianCurvature_comp isOpen_puncturedSphere hu
    (contDiffOn_pairOfPantsPerturbation hH hHs 1)
    (contDiffOn_pairOfPantsPerturbation hH hHs Complex.I)
  have hT : Complex.equivRealProdCLM.symm ⁻¹' truncation 2 ⊆
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1} :=
    fun z hz ↦ ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  refine ((hc.mono hT).integrableOn_compact
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation 2))).of_forall_sdiff_eq_zero
    isOpen_puncturedSphere.measurableSet fun z hz ↦ ?_
  -- Off `S_2` some end has signed longitudinal coordinate greater than `2`.
  obtain ⟨q, hq⟩ : ∃ q : Puncture,
      2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
    by_contra! h
    exact hz.2 (mem_truncation.2 ⟨hz.1.1, hz.1.2, h⟩)
  exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs hz.1 hq _

/-! ### One-sided curvature bounds -/

/-- The derivative of the cutoff of the end `q` has integral one over the part `±s > 1/2` of the
end, which contains its support. -/
private theorem setIntegral_deriv_smoothTransition_endSign (q : Puncture) :
    ∫ s in {s : ℝ | 1 / 2 < q.endSign * s}, deriv smoothTransition (q.endSign * s - 1) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦
      smoothTransition.deriv_of_neg (by linarith [not_lt.1 (notMem_ofPred_iff.1 hs)]),
    smoothTransition.integral_deriv_mul_sub, abs_endSign, inv_one]

/-- **The one-sided curvature bound on one end.** If `h` is a function of time, integrable over
one period, with `±h(t) ≤ ±H_q(t, x)` for the sign of the end `q`, then along every map `u`
continuous on `S` the curvature of the pair-of-pants perturbation over the image of the strip of
the end `q` integrates to at least `±∫₀¹ h`. In the coordinates of the end the curvature,
multiplied by the Jacobian of the end chart, is `±β'(±s - 1) H_q(t)`, and `β' ≥ 0` has
integral one. -/
private theorem endSign_mul_integral_le_setIntegral_image_endChart (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {q : Puncture}
    {h : ℝ → ℝ} (hh : IntervalIntegrable h volume 0 1)
    (hhH : ∀ t x, q.endSign * h t ≤ q.endSign * H q t x) {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) :
    q.endSign * ∫ t in (0 : ℝ)..1, h t ≤
      ∫ z in endChart q '' endStrip q, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hmeas := measurableSet_endStrip q
  have hφ (ζ : ℝ × ℝ) (_ : ζ ∈ endStrip q) :=
    (hasFDerivAt_endChart q ζ).differentiableAt.hasFDerivAt.hasFDerivWithinAt (s := endStrip q)
  -- The strip covers the angular period `[-1/2, 1/2)`, so compare with the extension `g` of `h`
  -- from `(0, 1]` to a period-one function, which has the same integral over a period.
  set g : ℝ → ℝ := fun t ↦ h (toIocMod one_pos 0 t) with hg_def
  have hg : Periodic g 1 := fun t ↦ by simp only [g, toIocMod_add_right]
  have hgh : ∀ t ∈ uIoc (0 : ℝ) 1, h t = g t := fun t ht ↦ by
    rw [uIoc_of_le zero_le_one] at ht
    simp only [hg_def]
    rw [(toIocMod_eq_self one_pos (a := 0) (b := t)).2 (by rwa [zero_add])]
  have hgi : IntegrableOn g (Ico (-1 / 2) (1 / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num)).1
      (hg.intervalIntegrable one_ne_zero (t := 0)
        ((zero_add (1 : ℝ)).symm ▸ hh.congr_ae ((ae_restrict_mem measurableSet_uIoc).mono hgh))
        _ _)
  have hgH (t : ℝ) (x : V) : q.endSign * g t ≤ q.endSign * H q t x := by
    have := hhH (toIocMod one_pos 0 t) x
    rwa [← self_sub_toIocDiv_zsmul, (hH q).sub_zsmul_eq] at this
  have hgint : ∫ t in (0 : ℝ)..1, h t = ∫ t in Ico (-1 / 2 : ℝ) (1 / 2), g t := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ hgh), integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
    have := hg.intervalIntegral_add_eq 0 (-1 / 2)
    rwa [zero_add, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at this
  have hβ : Integrable fun s : ℝ ↦ deriv smoothTransition (q.endSign * s - 1) :=
    (smoothTransition.integrable_deriv.comp_sub_right 1).comp_mul_left' q.endSign_ne_zero
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hmeas hφ (injOn_endChart q)]
  calc q.endSign * ∫ t in (0 : ℝ)..1, h t
      = ∫ ζ in endStrip q,
          deriv smoothTransition (q.endSign * ζ.1 - 1) * (q.endSign * g ζ.2) := by
        rw [Measure.volume_eq_prod, endStrip_def,
          setIntegral_prod_mul (fun s ↦ deriv smoothTransition (q.endSign * s - 1))
            (fun t ↦ q.endSign * g t), integral_const_mul,
          setIntegral_deriv_smoothTransition_endSign, one_mul, hgint]
    _ ≤ _ := by
        refine setIntegral_mono_on ?_ ?_ hmeas fun ζ hζ ↦ ?_
        · rw [IntegrableOn, Measure.volume_eq_prod, endStrip_def, ← Measure.prod_restrict]
          exact hβ.restrict.mul_prod (hgi.const_mul _)
        · refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas hφ
            (injOn_endChart q) _).1
            ((integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu).mono_set ?_)
          rintro _ ⟨ζ, hζ, rfl⟩
          exact mem_thricePuncturedSphereReal_iff.1
            (endChart_mem_thricePuncturedSphereReal (endSign_mul_pos_of_mem_endStrip hζ))
        · -- In the coordinates of the end the curvature is `±β'(±s - 1) H_q(t)`.
          rw [abs_of_pos (det_fderiv_endChart_pos q ζ), smul_eq_mul,
            det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart ω hH hHs
              (endSign_mul_pos_of_mem_endStrip hζ)]
          exact (mul_le_mul_of_nonneg_left (hgH ζ.2 (u (endChart q ζ)))
            smoothTransition.monotone.deriv_nonneg).trans_eq (by ring)

/-- **The one-sided curvature bound on the pair of pants.** Let `h_q` be functions of time,
integrable over one period, with `h_q ≤ H_q` on the input ends and `H_∞ ≤ h_∞` on the output
end, that is `±h_q(t) ≤ ±H_q(t, x)`. Along every map `u` continuous on `S`, the integrated
curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` satisfies

`∫₀¹ h_0 + ∫₀¹ h_1 - ∫₀¹ h_∞ ≤ ∫_S R_K(u)`.

Unlike the two-sided bound `|∫_S R_K(u)| ≤ B_0 + B_1 + B_∞`, it needs no bound on `|H_q|`, and
the constant transforms correctly under a change of normalization `H_q ↦ H_q + c_q(t)`, which
shifts the actions of the ends by `∫₀¹ c_q`. -/
theorem sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {h : Puncture → ℝ → ℝ} (hh : ∀ q, IntervalIntegrable (h q) volume 0 1)
    (hhH : ∀ q t x, q.endSign * h q t ≤ q.endSign * H q t x) {u : ℝ × ℝ → V}
    (hu : ContinuousOn u {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1}) :
    ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, h q t ≤
      ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hR := integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu
  have hsub (q : Puncture) : endChart q '' endStrip q ⊆
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1} := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact mem_thricePuncturedSphereReal_iff.1
      (endChart_mem_thricePuncturedSphereReal (endSign_mul_pos_of_mem_endStrip hζ))
  have hmeas (q : Puncture) : MeasurableSet (endChart q '' endStrip q) :=
    measurable_image_of_fderivWithin (measurableSet_endStrip q)
      (fun ζ _ ↦ (hasFDerivAt_endChart q ζ).hasFDerivWithinAt) (injOn_endChart q)
  -- The curvature is supported in the images of the strips of the ends.
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_puncturedSphere.measurableSet
      (iUnion_subset hsub) fun z hz ↦ ?_,
    integral_iUnion_fintype hmeas pairwise_disjoint_image_endChart fun q ↦ hR.mono_set (hsub q)]
  · exact Finset.sum_le_sum fun q _ ↦
      endSign_mul_integral_le_setIntegral_image_endChart ω hH hHs (hh q) (hhH q) hu
  · have hS : z ∈ thricePuncturedSphereReal := mem_thricePuncturedSphereReal_iff.2 hz.1
    have hlt (q : Puncture) :
        q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
      by_contra! hq
      exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endChart hS (by linarith)⟩)
    simpa only [hamiltonianCurvature_constSmooth] using
      ω.constSmooth.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt
        (K := pairOfPantsPerturbation H)
        (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y) hS hlt (u z)

end SymplecticForm

end TauCeti
