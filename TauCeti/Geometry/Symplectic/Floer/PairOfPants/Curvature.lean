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
# The integrated curvature and the energy identity of the pair-of-pants perturbation

The energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants turns a bound
`∫_S sup_X |R_K| ≤ C` on the curvature of the perturbation datum `K` into the lower bound on the
valuation of product coefficients and the upper bound on the energy of the curves they count.
This file computes such a constant `C` for the perturbation
`TauCeti.Floer.pairOfPantsPerturbation` built from period-one Hamiltonians `H_q` on the three ends
of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`. The curvature bound and the energy identity on
the truncations of `S` hold for Hamiltonians on any manifold `M` with a two-form `ω`, such as a
closed symplectic manifold; the energy identity needs `ω` nondegenerate, but not closed.

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

The same decomposition of `S` into its core, where `K` vanishes, and the three ends integrates
the energy identity over the truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), where every `±s ≤ R`. On each end the rectangle
identity `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` applies in cylinder
coordinates, after the changes of variables `SmoothTwoForm.integral_floerEnergyDensity_image` and
`SmoothTwoForm.integral_hamiltonianCurvature_image`; the boundary terms along the
angular sides cancel by periodicity, and those on the circles `±s = 1` vanish with the cutoff. For
a map `u` into `M` which is `C¹` on `S` and `R ≥ 1` this gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The three integrands are
integrable over `S_R`: the area density is continuous on `S`, and on each end the energy density
and the curvature are two-forms whose coefficients in cylinder coordinates are continuous. With the
curvature bound, the energy over `S_R` therefore differs from the area plus the Hamiltonian
boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`. Letting `R → ∞` gives the energy
identity on the whole pair of pants
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic`).

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
* `SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`,
  `SymplecticForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le`,
  `SymplecticForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`: the same
  statements for a symplectic vector space target.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`:
  the energy identity on the truncated pair of pants, for a manifold target.
* `IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`:
  the resulting energy bound, uniform in the truncation.
* `SmoothTwoForm.IsNondegenerate.integrableOn_truncation_pairOfPantsPerturbation`: the integrands
  of the identity are integrable over every truncation.
* `SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the curvature along a
  map continuous on `S` is integrable over `S`.
* `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`,
  `SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`,
  `SymplecticForm.integrableOn_truncation_pairOfPantsPerturbation`,
  `SymplecticForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the same statements
  for a symplectic vector space target.
* `SymplecticForm.sum_mul_integral_le_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation`:
  the one-sided curvature bound.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends and their energy.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the one-sided action estimate for the pair-of-pants product.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

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

/-- A `C¹` Hamiltonian is differentiable in time at each point of the target. -/
private theorem differentiable_hamiltonian_time
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (q : Puncture) (x : M) :
    Differentiable ℝ fun t ↦ H q t x :=
  (((hHs q).comp (f := fun t : ℝ ↦ (t, x)) (contMDiff_id.prodMk contMDiff_const)).contDiff
    ).differentiable one_ne_zero

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
  rw [perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hz
      (differentiable_hamiltonian_time hHs q x _)]

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
  refine (ω.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le
    (P := fun σ ↦ smoothTransition (σ - 1)) (fun w hw x v ↦ hdom hw x v)
    (fun w hw x v ↦ htgt hw x v)
    (fun z hz x v ↦ pairOfPantsPerturbation_cylindricalEndLift_of_pos (hH q) hz x v)
    (fun σ ↦ (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.comp σ
      (differentiableAt_id.sub_const 1)) (differentiable_hamiltonian_time hHs q) (hB q)
    u).trans_eq ?_
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

/-! ### The energy identity on the truncated pair of pants -/

section EnergyIdentity

/-- The part `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates: the
collar and the cylindrical part of the end inside the truncation `S_R`, over one period. -/
private noncomputable def endPiece (q : Puncture) (R : ℝ) : Set (ℝ × ℝ) :=
  {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico (-1 / 2) (1 / 2)

/-- The end pieces lie in the truncation. -/
private theorem image_endPiece_subset (q : Puncture) {R : ℝ} (hR : 1 ≤ R) :
    endChart q '' endPiece q R ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (1 ≤ q.endSign * z.1 ∧ q.endSign * z.1 ≤ R) ∧ z.2 ∈ Ico (-1 / 2 : ℝ) (1 / 2) := hz
  have hz₀ : 0 < q.endSign * z.1 := by linarith [hz'.1.1]
  have hS := mem_thricePuncturedSphereReal_iff.1 (endChart_mem_thricePuncturedSphereReal hz₀)
  refine mem_truncation.2 ⟨hS.1, hS.2, fun r => ?_⟩
  by_cases hr : q = r
  · subst hr
    rw [re_endCoord_endChart]
    exact hz'.1.2
  · have h := endSign_mul_re_endCoord_nonpos hr (w := Complex.equivRealProdCLM.symm (endChart q z))
      (by rwa [re_endCoord_endChart])
    linarith

/-- A point of the truncation on the part `±s ≥ 1` of the end `q` lies in its end piece. -/
private theorem mem_image_endPiece {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R) {q : Puncture}
    (hq : 1 ≤ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    z ∈ endChart q '' endPiece q R := by
  obtain ⟨hz₀, hz₁, hzR⟩ := mem_truncation.1 hz
  refine ⟨Complex.equivRealProdCLM (q.endCoord (Complex.equivRealProdCLM.symm z)),
    (⟨⟨by simpa using hq, by simpa using hzR q⟩, by simpa using q.im_endCoord_mem_Ico _⟩ :
      _ ∧ _), ?_⟩
  rw [endChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    q.cylindricalEndLift_endCoord (ne_endCenter ⟨hz₀, hz₁⟩ q),
    ContinuousLinearEquiv.apply_symm_apply]

/-- The end pieces of distinct ends are disjoint. -/
private theorem disjoint_image_endPiece {R : ℝ} {q r : Puncture} (hqr : q ≠ r) :
    Disjoint (endChart q '' endPiece q R) (endChart r '' endPiece r R) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have ha' : 1 ≤ q.endSign * a.1 := ha.1.1
  have hb' : 1 ≤ r.endSign * b.1 := hb.1.1
  have h := congrArg Complex.equivRealProdCLM.symm hab
  rw [equivRealProdCLM_symm_endChart, equivRealProdCLM_symm_endChart] at h
  exact cylindricalEndLift_ne_cylindricalEndLift hqr (z := Complex.equivRealProdCLM.symm a)
    (z' := Complex.equivRealProdCLM.symm b) (by simp; linarith) (by simp; linarith) h.symm

/-- The end pieces are measurable. -/
private theorem measurableSet_endPiece (q : Puncture) (R : ℝ) : MeasurableSet (endPiece q R) :=
  (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
    (measurableSet_le (measurable_const.mul measurable_id) measurable_const) |>.prod
    measurableSet_Ico

/-- The end chart is injective on an end piece. -/
private theorem injOn_endChart_endPiece (q : Puncture) (R : ℝ) :
    InjOn (endChart q) (endPiece q R) :=
  (injOn_endChart q).mono fun z hz => by
    have h : 1 ≤ q.endSign * z.1 := hz.1.1
    exact mem_endStrip_iff.2 ⟨by linarith, hz.2⟩

/-- The image of an end piece in `S` is measurable. -/
private theorem measurableSet_image_endPiece (q : Puncture) (R : ℝ) :
    MeasurableSet (endChart q '' endPiece q R) :=
  measurable_image_of_fderivWithin (measurableSet_endPiece q R)
    (fun w _ => (hasFDerivAt_endChart q w).hasFDerivWithinAt) (injOn_endChart_endPiece q R)

/-- An end piece lies in a compact subset of the part `±s > 0` of the end. -/
private theorem exists_isCompact_endPiece_subset (q : Puncture) (R : ℝ) :
    ∃ K, IsCompact K ∧ endPiece q R ⊆ K ∧ K ⊆ {z : ℝ × ℝ | 0 < q.endSign * z.1} := by
  refine ⟨((fun s ↦ q.endSign * s) ⁻¹' Icc 1 R) ×ˢ Icc (-1 / 2) (1 / 2),
    ((Homeomorph.mulLeft₀ q.endSign q.endSign_ne_zero).isCompact_preimage.2 isCompact_Icc).prod
      isCompact_Icc, fun z hz => ⟨hz.1, Ico_subset_Icc_self hz.2⟩, fun z hz => ?_⟩
  have h : 1 ≤ q.endSign * z.1 := hz.1.1
  exact (by linarith : 0 < q.endSign * z.1)

/-- A function `f` on `S` is integrable over the image of an end piece if, multiplied by the
Jacobian of the end chart, it becomes a function continuous on the part `±s > 0` of the end. -/
private theorem integrableOn_image_endPiece {q : Puncture} {R : ℝ} {f g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g {z : ℝ × ℝ | 0 < q.endSign * z.1})
    (hfg : ∀ ζ ∈ endPiece q R, (fderiv ℝ (endChart q) ζ).det * f (endChart q ζ) = g ζ) :
    IntegrableOn f (endChart q '' endPiece q R) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  obtain ⟨K, hK, hPK, hKU⟩ := exists_isCompact_endPiece_subset q R
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_endPiece q R)
    (fun ζ _ => (hasFDerivAt_endChart q ζ).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (injOn_endChart_endPiece q R)]
  refine (((hg.mono hKU).integrableOn_compact hK).mono_set hPK).congr_fun (fun ζ hζ => ?_)
    (measurableSet_endPiece q R)
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q ζ), smul_eq_mul, hfg ζ hζ]

omit [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M] in
/-- **The boundary circle of an end piece.** By periodicity, the integral of the end Hamiltonian
over the circle `±s = R` may be taken over `[0, 1]` instead of `[-1/2, 1/2]`. -/
private theorem intervalIntegral_endChart_boundary_eq (hH : ∀ q, Periodic (H q) 1)
    {u : ℝ × ℝ → M} {R : ℝ} (q : Puncture) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t))) =
      ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
  have hper : Periodic (fun t : ℝ => H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) 1 := fun t => by
    simp only [q.periodic_cylindricalEndLift (q.endSign * R) t, hH q t]
  have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
  norm_num at h
  simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
  convert h using 1 <;> norm_num

omit [IsManifold I ⊤ M] in
/-- In the coordinates of the end `q`, on its part `±s > 0`, the `ds` component of the
perturbation vanishes and the `dt` component `β(±s - 1) H_q(t)` is `C¹` jointly in the domain and
target points. -/
private theorem contMDiffOn_pairOfPantsEndComponent (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (q : Puncture) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry (pairOfPantsEndComponent H q 1))
        ({z : ℝ × ℝ | 0 < q.endSign * z.1} ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
        (uncurry (pairOfPantsEndComponent H q Complex.I))
        ({z : ℝ × ℝ | 0 < q.endSign * z.1} ×ˢ univ) := by
  have hβ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      fun p : (ℝ × ℝ) × M => smoothTransition (q.endSign * p.1.1 - 1) :=
    (smoothTransition.contDiff.comp (by fun_prop : ContDiff ℝ 1
      fun z : ℝ × ℝ => q.endSign * z.1 - 1)).contMDiff.comp contMDiff_fst
  have hHq : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 fun p : (ℝ × ℝ) × M => H q p.1.2 p.2 :=
    (hHs q).comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  exact ⟨contMDiffOn_const.congr fun p hp => pairOfPantsEndComponent_one_of_pos (hH q) hp.1 p.2,
    (hβ.smul hHq).contMDiffOn.congr fun p hp => pairOfPantsEndComponent_I_of_pos (hH q) hp.1 p.2⟩

/-- In the coordinates of the end `q`, along a map `u` continuous on `S`, the curvature
`±β'(±s - 1) H_q(t)` of the pulled-back perturbation is continuous on the part `±s > 0` of the
end. -/
private theorem continuousOn_hamiltonianCurvature_pairOfPantsEndComponent (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) (q : Puncture) :
    ContinuousOn (fun z ↦ ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) z (u (endChart q z)))
      {z : ℝ × ℝ | 0 < q.endSign * z.1} := by
  have hu' : ContinuousOn (u ∘ endChart q) {z : ℝ × ℝ | 0 < q.endSign * z.1} :=
    hu.comp (contDiff_endChart q 0).continuous.continuousOn
      fun _ hz => endChart_mem_thricePuncturedSphereReal hz
  have hβ' : Continuous fun z : ℝ × ℝ ↦ deriv smoothTransition (q.endSign * z.1 - 1) :=
    ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp (by fun_prop)
  refine ((continuousOn_const (c := q.endSign).mul hβ'.continuousOn).mul
    ((hHs q).continuous.comp_continuousOn (continuousOn_snd.prodMk hu'))).congr fun z hz => ?_
  exact ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hz
    (differentiable_hamiltonian_time hHs q _ _)

/-- The points of the truncation `S_R` off its three end pieces lie in the core, where every
`±s < 1`. -/
private theorem forall_lt_one_of_mem_core {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R \
      ⋃ q, endChart q '' endPiece q R) :
    ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
  intro q
  by_contra! h
  exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)

/-- The core of a truncation is measurable. -/
private theorem measurableSet_core (R : ℝ) :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' truncation R \
      ⋃ q, endChart q '' endPiece q R) :=
  (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_truncation R)).isClosed.measurableSet.diff
    (MeasurableSet.iUnion fun q => measurableSet_image_endPiece q R)

/-- On the core of a truncation the perturbation vanishes, so the Floer energy density is the
symplectic area density. -/
private theorem floerEnergyDensity_pairOfPantsPerturbation_of_mem_core (ω : SmoothTwoForm I M)
    {u : ℝ × ℝ → M} {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R \
      ⋃ q, endChart q '' endPiece q R) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
  have hK : pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ => 0 :=
    funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦
      (forall_lt_one_of_mem_core hz q).le)
  simp [floerEnergyDensity_def, hK, hamiltonianVectorField_const]

/-- On the core of a truncation the curvature of the perturbation vanishes. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_of_mem_core (ω : SmoothTwoForm I M)
    {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R \
      ⋃ q, endChart q '' endPiece q R) (x : M) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 :=
  ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt (K := pairOfPantsPerturbation H)
    (fun _ hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y)
    (mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz.1).1, (mem_truncation.1 hz.1).2.1⟩)
    (forall_lt_one_of_mem_core hz) x

/-- A function is integrable over the truncation `S_R`, `R ≥ 1`, if it is integrable over its core
and over its three end pieces. -/
private theorem integrableOn_truncation_of_endPiece {R : ℝ} (hR : 1 ≤ R) {f : ℝ × ℝ → ℝ}
    (hC : IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' truncation R \
      ⋃ q, endChart q '' endPiece q R))
    (hA : ∀ q, IntegrableOn f (endChart q '' endPiece q R)) :
    IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  rw [← sdiff_union_of_subset (iUnion_subset fun q => image_endPiece_subset q hR)]
  exact hC.union (integrableOn_finite_iUnion.2 hA)

/-- **The curvature is integrable over the pair of pants, for a manifold target.** Along a map `u`
into a manifold which is continuous on `S`, the curvature of the pair-of-pants perturbation of
period-one `C¹` Hamiltonians is integrable over `S`. It vanishes on the core of `S` and off the
compact truncation `S_2`, and on each end it is a two-form whose coefficient in cylinder
coordinates, `±β'(±s - 1) H_q(t)`, is continuous. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      thricePuncturedSphereReal := by
  have hpos {q : Puncture} {ζ : ℝ × ℝ} (hζ : ζ ∈ endPiece q 2) : 0 < q.endSign * ζ.1 := by
    have h : 1 ≤ q.endSign * ζ.1 := hζ.1.1
    linarith
  -- On the core of `S_2` the curvature vanishes; on the end pieces it is continuous in cylinder
  -- coordinates.
  have hT := integrableOn_truncation_of_endPiece one_le_two
    (integrableOn_zero.congr_fun (fun z hz =>
      (hamiltonianCurvature_pairOfPantsPerturbation_of_mem_core ω hz (u z)).symm)
      (measurableSet_core 2))
    fun q => integrableOn_image_endPiece
      (continuousOn_hamiltonianCurvature_pairOfPantsEndComponent ω hH hHs hu q) fun ζ hζ => by
        rw [det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart ω hH hHs (hpos hζ)]
        exact (ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) (hpos hζ)
          (differentiable_hamiltonian_time hHs q _ _)).symm
  refine hT.of_forall_sdiff_eq_zero isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦ ?_
  -- Off `S_2` some end has signed longitudinal coordinate greater than `2`.
  have hzS := mem_thricePuncturedSphereReal_iff.1 hz.1
  obtain ⟨q, hq⟩ : ∃ q : Puncture,
      2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
    by_contra! h
    exact hz.2 (mem_truncation.2 ⟨hzS.1, hzS.2, h⟩)
  exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs hzS hq _

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- In the coordinates of the end `q`, along a map `u` which is `C¹` on `S`, the Floer energy
density of the pulled-back perturbation is continuous on the part `±s > 0` of the end. -/
private theorem IsNondegenerate.continuousOn_floerEnergyDensity_pairOfPantsEndComponent
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (q : Puncture) :
    ContinuousOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q))
      {z : ℝ × ℝ | 0 < q.endSign * z.1} := by
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) {z : ℝ × ℝ | 0 < q.endSign * z.1} :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn
      fun _ hz => endChart_mem_thricePuncturedSphereReal hz
  obtain ⟨hKs, hKt⟩ := contMDiffOn_pairOfPantsEndComponent hH hHs q
  exact hω.continuousOn_floerEnergyDensity (isOpen_lt continuous_const
    (continuous_const.mul continuous_fst)) hu' hKs hKt
    (continuousOn_hamiltonianCurvature_pairOfPantsEndComponent ω hH hHs hu.continuousOn q)

/-- The cylinder-coordinate half of the energy identity over a rectangle of an end: over the strip
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 0` of the end, the pulled-back Floer energy is the
symplectic area, plus the Hamiltonian boundary terms, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_endChart_rect
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 0 < q.endSign * a₁)
    (hb : 0 < q.endSign * b₁) :
    ∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
        ω.floerEnergyDensity (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I)
          (u ∘ endChart q) w =
      (∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          (SmoothBundleForm.eval₂ ω (u (endChart q w))
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
            (pairOfPantsEndComponent H q Complex.I) w (u (endChart q w)) := by
  set U : Set (ℝ × ℝ) := {z | 0 < q.endSign * z.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  -- The rectangle lies in the part `±s > 0` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : 0 < q.endSign * z.1 := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => hU₁ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) =ᵐ[volume]
      Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`: apply the energy identity on
  -- the rectangle.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn
      fun _ hz => endChart_mem_thricePuncturedSphereReal hz
  obtain ⟨hKs, hKt⟩ := contMDiffOn_pairOfPantsEndComponent hH hHs q
  have hrect := hω.integral_floerEnergyDensity hUo hu' hKs hKt
    (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU
    (((hω.continuousOn_floerEnergyDensity_pairOfPantsEndComponent hH hHs hu q).mono
      hIccU).integrableOn_compact isCompact_Icc)
    (((continuousOn_hamiltonianCurvature_pairOfPantsEndComponent ω hH hHs hu.continuousOn
      q).mono hIccU).integrableOn_compact isCompact_Icc)
  simp only [Function.comp_apply] at hrect
  rw [hrect]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c) (u (endChart q (s, c))) =
      0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (hU₁ (z := (s, c)) hs) _
  have ht {c : ℝ} (hc : c ∈ Icc a₁ b₁) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) (u (endChart q (c, t))) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ =>
      pairOfPantsEndComponent_I_of_pos (hH q) (hU₁ (z := (c, t)) hc) _
  rw [hs₀, hs₀, ht (c := a₁) ⟨le_rfl, hab⟩, ht (c := b₁) ⟨hab, le_rfl⟩]
  ring

/-- **The energy identity on an end piece.** Over the end piece `1 ≤ ±s ≤ R` of the end `q`, the
Floer energy is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the
boundary circle `±s = R`, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_endPiece
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R)
    (q : Puncture) :
    ∫ z in endChart q '' endPiece q R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' endPiece q R, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) *
          (q.endSign * ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t)))) -
        ∫ z in endChart q '' endPiece q R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hpos {w : ℝ × ℝ} (hw : w ∈ endPiece q R) : 0 < q.endSign * w.1 := by
    have h : 1 ≤ q.endSign * w.1 := hw.1.1
    linarith
  have hS {w : ℝ × ℝ} (hw : w ∈ endPiece q R) :=
    endChart_mem_thricePuncturedSphereReal (hpos hw)
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ endPiece q R) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))).mdifferentiableAt
      one_ne_zero
  have hmeas := measurableSet_endPiece q R
  have hinj := injOn_endChart_endPiece q R
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ => hφ w) (fun w _ => det_fderiv_endChart_nonneg q w)
    (fun w hw => hud hw) (fun _ _ => mdifferentiableAt_const)
    (fun _ _ => mdifferentiableAt_const)
  have h₀ (v : ℝ × ℝ) : perturbationPullback (endChart q) (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ => hφ w)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud hw)
      (fun w hw => mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) _ 1)
      (fun w hw => mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) _ _),
    ω.integral_hamiltonianCurvature_image hmeas hinj
      (fun w _ => (contDiff_endChart q 2).contDiffAt)
      (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS hw) _ 1)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS hw) _ _)
      (fun w hw => mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) _ 1)
      (fun w hw => mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) _ _),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · have hpiece : endPiece q R = Icc 1 R ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp [endPiece, h]
    rw [hpiece, hω.integral_floerEnergyDensity_endChart_rect hH hHs hu hR
      (by rw [h]; norm_num) (by rw [h]; linarith)]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul,
      Function.comp_apply]
  · have hpiece : endPiece q R = Icc (-R) (-1) ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp only [endPiece, h, mem_prod, mem_ofPred_eq, mem_Icc]
      constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
    rw [hpiece, hω.integral_floerEnergyDensity_endChart_rect hH hHs hu (by linarith)
      (by rw [h]; linarith) (by rw [h]; norm_num)]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul,
      Function.comp_apply]
    ring

/-- The Floer energy density, the symplectic area density and the curvature of the pair-of-pants
perturbation, along a map into a manifold that is `C¹` on `S`, are integrable over every
truncation. -/
theorem IsNondegenerate.integrableOn_truncation_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) (R : ℝ) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  -- It suffices to treat the larger truncation `S_R'`, `R' = max R 1`, which is the union of its
  -- core, where every `±s < 1`, and the three end pieces.
  set R' := max R 1
  have hTT : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆
      Complex.equivRealProdCLM.symm ⁻¹' truncation R' :=
    preimage_mono (truncation_mono (le_max_left R 1))
  have hTS {R : ℝ} : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆
      thricePuncturedSphereReal := fun z hz => mem_thricePuncturedSphereReal_iff.2
    ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  have hpos {q : Puncture} {ζ : ℝ × ℝ} (hζ : ζ ∈ endPiece q R') : 0 < q.endSign * ζ.1 := by
    have h : 1 ≤ q.endSign * ζ.1 := hζ.1.1
    linarith
  -- The area density is continuous on `S`.
  have harea := ((ω.continuousOn_eval₂_mfderiv isOpen_thricePuncturedSphereReal hu).mono
    hTS).integrableOn_compact (μ := volume)
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R'))
  refine ⟨(integrableOn_truncation_of_endPiece (le_max_right R 1)
    ((harea.mono_set sdiff_subset).congr_fun
      (fun z hz => (floerEnergyDensity_pairOfPantsPerturbation_of_mem_core ω hz).symm)
      (measurableSet_core R')) fun q => ?_).mono_set hTT, harea.mono_set hTT,
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn).mono_set
      hTS⟩
  -- On an end piece the energy density is a two-form, continuous in cylinder coordinates.
  refine integrableOn_image_endPiece
    (hω.continuousOn_floerEnergyDensity_pairOfPantsEndComponent hH hHs hu q) fun ζ hζ => ?_
  have hS := endChart_mem_thricePuncturedSphereReal (hpos hζ)
  rw [← ω.floerEnergyDensity_perturbationPullback (hasFDerivAt_endChart q ζ).differentiableAt
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt
      one_ne_zero)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ 1)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ _),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]

/-- **The energy identity on the truncated pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a manifold `M` with a
nondegenerate two-form `ω`, attached to the three ends of `S = ℂ ∖ {0, 1}`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let
`u` be a map into `M` which is `C¹` on `S`. For `R ≥ 1`, over the truncation `S_R` of `S` the
Floer energy of `u` is its symplectic area, plus `β(R - 1)` times the signed sum over the three
ends of the integrals of `H_q(t)` along the boundary circles `±s = R`, minus the integrated
curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. Closedness of `ω` is not used. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set A : Puncture → Set (ℝ × ℝ) := fun q => endChart q '' endPiece q R
  set C := T \ ⋃ q, A q
  obtain ⟨hE, harea, hcurv⟩ := hω.integrableOn_truncation_pairOfPantsPerturbation hH hHs hu R
  -- The truncation is the disjoint union of its core `C`, where every `±s < 1`, and the three
  -- end pieces.
  have hAm (q : Puncture) : MeasurableSet (A q) := measurableSet_image_endPiece q R
  have hAT (q : Puncture) : A q ⊆ T := image_endPiece_subset q hR
  have hAd : Pairwise (Disjoint on A) := fun q r hqr => disjoint_image_endPiece hqr
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ q, ∫ z in A q, f z := by
    have hTC : T = C ∪ ⋃ q, A q := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun q => hf.mono_set (hAT q)]
  -- On the core the perturbation vanishes, so the energy is the area and the curvature vanishes.
  have hCm : MeasurableSet C := measurableSet_core R
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) :=
    setIntegral_congr_fun hCm fun z hz =>
      floerEnergyDensity_pairOfPantsPerturbation_of_mem_core ω hz
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz =>
      hamiltonianCurvature_pairOfPantsPerturbation_of_mem_core ω hz (u z)
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE, hCR,
    Finset.sum_congr rfl fun q _ =>
      hω.integral_floerEnergyDensity_image_endPiece hH hHs hu hR q,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [intervalIntegral_endChart_boundary_eq hH]
  ring

/-- **The energy bound on the truncated pair of pants, for a manifold target.** If the end
Hamiltonians are bounded, `|H_q| ≤ B_q`, then for every `R ≥ 1` the Floer energy over the
truncation `S_R` differs from the symplectic area plus the Hamiltonian boundary terms by at most
`B₀ + B₁ + B_∞`, uniformly in `R`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hu hR, hsub,
    abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

end EnergyIdentity

end SmoothTwoForm

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}

/-- `C¹` Hamiltonians on a vector space are `C¹` maps of manifolds. -/
private theorem contMDiff_uncurry_of_contDiff
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H q)) :=
  contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff

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

/-! ### The energy identity on the truncated pair of pants -/

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
  obtain ⟨hE, hA, hR⟩ :=
    (isNondegenerate_constSmooth ω).integrableOn_truncation_pairOfPantsPerturbation hH
      (contMDiff_uncurry_of_contDiff hHs) (contMDiffOn_iff_contDiffOn.mpr hu) R
  have hE' : ω.constSmooth.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u :=
    funext (floerEnergyDensity_constSmooth ω _ _ u)
  exact ⟨hE' ▸ hE, by simpa only [eval₂_constSmooth_mfderiv_stdComplexLine] using hA,
    by simpa only [hamiltonianCurvature_constSmooth] using hR⟩

/-- **The energy identity on the truncated pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`,
and let `u` be a map which is `C¹` on `S`. For `R ≥ 1`, over the truncation `S_R` of `S` the Floer
energy of `u` is its symplectic area, plus `β(R - 1)` times the signed sum over the three ends of
the integrals of `H_q(t)` along the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. This is the constant-form case of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`.
-/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  simpa only [floerEnergyDensity_constSmooth, hamiltonianCurvature_constSmooth,
    eval₂_constSmooth_mfderiv_stdComplexLine] using
    (isNondegenerate_constSmooth ω).integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
      hH (contMDiff_uncurry_of_contDiff hHs) (contMDiffOn_iff_contDiffOn.mpr hu) hR

/-- **The energy bound on the truncated pair of pants.** If the end Hamiltonians are bounded,
`|H_q| ≤ B_q`, then for every `R ≥ 1` the Floer energy over the truncation `S_R` differs from the
symplectic area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`.
-/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [integral_floerEnergyDensity_pairOfPantsPerturbation_truncation ω hH hHs hu hR, hsub,
    abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The curvature is integrable over the pair of pants.** Along a map `u` which is continuous
on `S`, the curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians is
integrable over `S`. This is the constant-form case of
`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`. -/
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
  simpa only [hamiltonianCurvature_constSmooth, thricePuncturedSphereReal] using
    ω.constSmooth.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation hH
      (contMDiff_uncurry_of_contDiff hHs) hu

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
