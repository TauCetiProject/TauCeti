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
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The integrated curvature and the energy identity of the pair-of-pants perturbation

The energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` for pairs of pants turns a bound
`∫_S sup_X |R_K| ≤ C` on the curvature of the perturbation datum `K` into the lower bound on the
valuation of product coefficients and the upper bound on the energy of the curves they count.
This file computes such a constant `C` for the perturbation
`TauCeti.Floer.pairOfPantsPerturbation` built from period-one Hamiltonians `H_q` on the three ends
of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`. The curvature bound holds for Hamiltonians on any
manifold `M` with a two-form `ω`, and the energy identity below for a finite-dimensional manifold
with a nondegenerate two-form, such as a closed symplectic manifold. Both specialize to a symplectic
vector space target `V` through the constant form `SymplecticForm.constSmooth`.

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

In the coordinates of an end, multiplied by the Jacobian of the end chart, the curvature along a
map `u` continuous on `S` is the continuous function `±β'(±s - 1) H_q(t, u)`, and it vanishes off
the images of the collars `1 ≤ ±s ≤ 2`. So the curvature is integrable over `S`
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`), and, along a map
which is only continuous on the truncation `S_R`, over `S_R`
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation`).

The same decomposition of `S` into its core, where `K` vanishes, and the three ends integrates
the energy identity over the truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), where every `±s ≤ R`. On each end the rectangle
identity `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` applies in cylinder
coordinates; the boundary terms along the angular sides cancel by periodicity, and those on the
circles `±s = 1` vanish with the cutoff. For `R ≥ 1` and a map `u` which is `C¹` on an open set
containing `S_R`, for instance on `S`, this gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. Here the area density
`ω(∂_s u, ∂_t u)` is continuous near `S_R`, so integrable over the compact set `S_R`, and so is the
energy density, since it differs from the area density by the curvature and the exterior
derivative `d(K(u))`, which is continuous near `S_R`. Since nothing is assumed of `u` away from
`S_R`, the identity applies to the pieces of a map defined on a larger surface into which the
pair of pants is glued, such as the plumbed four-punctured sphere. With the curvature bound, the
energy over `S_R` therefore differs from the area plus the Hamiltonian boundary terms by at most
`B₀ + B₁ + B_∞`, uniformly in `R`. Letting `R → ∞`
gives the energy identity on the whole pair of pants, in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic`.

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
* `SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`,
  `SymplecticForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the curvature along a
  map continuous on `S` is integrable over `S`.
* `SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_image_endChart`,
  `SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation`: the
  curvature along a map continuous on the image of a part `a ≤ ±s ≤ b` of an end, `a > 0`, or on
  the truncation `S_R`, is integrable over it.
* `IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart`,
  `IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart_endPiece` in
  `SmoothTwoForm`: the energy identity over the image of a rectangle of an end, and over the end
  piece `1 ≤ ±s ≤ R`, for a map which is only `C¹` near that image.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`:
  the energy identity on the truncated pair of pants, for a manifold target; the vector-space case
  is `SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`.
* `SymplecticForm.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`: the
  resulting energy bound, uniform in the truncation; the manifold version is
  `IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le` in
  the namespace `SmoothTwoForm`.
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

namespace Floer

/-! ### The boundary circles of the end pieces -/

/-- **The boundary circle of an end piece.** By periodicity, the integral of the end Hamiltonian
over the circle `±s = R` may be taken over `[0, 1]` instead of `[-1/2, 1/2]`. -/
private theorem intervalIntegral_endChart_boundary_eq {M : Type*} {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1) {u : ℝ × ℝ → M} {R : ℝ} (q : Puncture) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t))) =
      ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
  have hper : Periodic (fun t : ℝ => H q t (u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) 1 := fun t => by
    simp only [q.periodic_cylindricalEndLift (q.endSign * R) t, hH q t]
  simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
  exact hper.intervalIntegral_neg_div_two_eq

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ}

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
    simp_rw [deriv_comp_sub_const, Real.eNorm_eq_ofReal smoothTransition.monotone.deriv_nonneg]
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
    ← Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_sum_of_nonneg fun q _ => hB₀ q]
  exact (eNorm_integral_le_lintegral_eNorm _).trans ((setLIntegral_le_lintegral _ _).trans
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
  obtain ⟨w, _, rfl⟩ := mem_image_endChart hz (q := q) (by linarith)
  have hw₂ : 2 < q.endSign * w.1 := by rwa [re_endCoord_endChart] at hq
  -- In the coordinates of the end the curvature is `±β'(±s - 1) H_q(t)`, and `β' = 0` there.
  have key := det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart ω hH hHs
    (by linarith : 0 < q.endSign * w.1) x
  have hβ : deriv smoothTransition (q.endSign * w.1 - 1) = 0 :=
    smoothTransition.deriv_of_one_lt (by linarith)
  rw [hβ, mul_zero, zero_mul] at key
  exact (mul_eq_zero.1 key).resolve_left (det_fderiv_endChart_pos q w).ne'


/-! ### The energy identity on the truncated pair of pants -/

omit [IsManifold I ⊤ M] in
/-- Along a map continuous on a set `U`, the curvature of the pair-of-pants perturbation in the
coordinates of the end `q`, multiplied by the Jacobian of the end chart, is
`±β'(±s - 1) H_q(t, u)`, a continuous function on the preimage of `U` under the end chart. -/
private theorem continuousOn_endSign_mul_deriv_smoothTransition_mul
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    {U : Set (ℝ × ℝ)} (hu : ContinuousOn u U) (q : Puncture) :
    ContinuousOn (fun w : ℝ × ℝ ↦
        q.endSign * deriv smoothTransition (q.endSign * w.1 - 1) * H q w.2 (u (endChart q w)))
      (endChart q ⁻¹' U) := by
  have hβ : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hu' : ContinuousOn (fun w ↦ u (endChart q w)) (endChart q ⁻¹' U) :=
    hu.comp (contDiff_endChart q 0).continuous.continuousOn (mapsTo_preimage _ _)
  have hHu : ContinuousOn (fun w : ℝ × ℝ ↦ H q w.2 (u (endChart q w))) (endChart q ⁻¹' U) :=
    (hHs q).continuous.comp_continuousOn (continuousOn_snd.prodMk hu')
  exact (continuous_const.mul (hβ.comp (by fun_prop))).continuousOn.mul hHu

/-- **The curvature is integrable over the pair of pants, for a manifold target.** Along a map `u`
which is continuous on `S`, the curvature of the pair-of-pants perturbation of period-one `C¹`
Hamiltonians on a manifold is integrable over `S`. It vanishes off the images of the collars
`1 ≤ ±s ≤ 2` of the three ends, and in the coordinates of an end, multiplied by the Jacobian of
the end chart, it is the continuous function `±β'(±s - 1) H_q(t, u)`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) thricePuncturedSphereReal := by
  refine ω.integrableOn_hamiltonianCurvature_of_forall_integrableOn_endStrip
    (fun _ hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y)
    (fun w x ↦ (contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs w x).mdifferentiableAt
      one_ne_zero) fun q ↦ ?_
  -- In the coordinates of the end the pulled-back curvature along `u` is `±β'(±s - 1) H_q(t, u)`,
  -- which is continuous on the compact closure of the collar `1 ≤ ±s ≤ 2` and vanishes off it.
  have hpos {w : ℝ × ℝ}
      (hw : w ∈ {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ 2} ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) :
      0 < q.endSign * w.1 := by
    linarith [hw.1.1]
  refine ((((continuousOn_endSign_mul_deriv_smoothTransition_mul hHs hu q).mono
    fun w hw ↦ endChart_mem_thricePuncturedSphereReal (hpos hw)).integrableOn_compact
    ((isCompact_setOf_endSign_mul_mem_Icc q 1 2).prod isCompact_Icc)).of_forall_sdiff_eq_zero
      (measurableSet_endStrip q)
    fun w ⟨hw, hwC⟩ ↦ ?_).congr_fun (fun w hw ↦ ?_) (measurableSet_endStrip q)
  · have hσ : q.endSign * w.1 - 1 < 0 ∨ 1 < q.endSign * w.1 - 1 := by
      by_contra! h
      exact hwC ⟨⟨by linarith [h.1], by linarith [h.2]⟩,
        Ico_subset_Icc_self (mem_endStrip_iff.1 hw).2⟩
    rcases hσ with hσ | hσ
    · simp [smoothTransition.deriv_of_neg hσ]
    · simp [smoothTransition.deriv_of_one_lt hσ]
  · rw [hamiltonianCurvature_perturbationPullback_endChart ω hH hHs
      (endSign_mul_pos_of_mem_endStrip hw)]

/-- **The curvature is integrable over a part of an end, for a manifold target.** Along a map `u`
which is continuous on a set `V` containing the image of the part `a ≤ ±s ≤ b` of the end `q`,
for `0 < a`, the curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians on a
manifold is integrable over the image of `a ≤ ±s ≤ b`, `t ∈ [-1/2, 1/2)`. In the coordinates of
the end, multiplied by the Jacobian of the end chart, it is the function `±β'(±s - 1) H_q(t, u)`,
which is continuous on the compact closure of that part of the end. Nothing is assumed about `u`
off `V`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_image_endChart
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    {V : Set (ℝ × ℝ)} (hu : ContinuousOn u V) {q : Puncture} {a b : ℝ} (ha : 0 < a)
    (hV : ∀ z : ℝ × ℝ, a ≤ q.endSign * z.1 → q.endSign * z.1 ≤ b → endChart q z ∈ V) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (endChart q '' ({s | a ≤ q.endSign * s ∧ q.endSign * s ≤ b} ×ˢ Ico (-1 / 2) (1 / 2))) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set P : Set ℝ := {s | a ≤ q.endSign * s ∧ q.endSign * s ≤ b}
  have hP : IsCompact P := isCompact_setOf_endSign_mul_mem_Icc q a b
  have hPm : MeasurableSet (P ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) :=
    hP.isClosed.measurableSet.prod measurableSet_Ico
  have hPc : IsCompact (P ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) := hP.prod isCompact_Icc
  have hpos {w : ℝ × ℝ} (hw : w.1 ∈ P) : 0 < q.endSign * w.1 := by
    linarith [hw.1]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hPm
    (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    ((injOn_endChart_univ_prod_Ico q (-1 / 2)).mono
      (prod_mono (subset_univ _) (by norm_num)))]
  have hVP : P ×ˢ Icc (-1 / 2 : ℝ) (1 / 2) ⊆ endChart q ⁻¹' V := fun w hw ↦ hV w hw.1.1 hw.1.2
  refine ((((continuousOn_endSign_mul_deriv_smoothTransition_mul hHs hu q).mono
    hVP).integrableOn_compact hPc).mono_set
    (prod_mono subset_rfl Ico_subset_Icc_self)).congr_fun (fun w hw ↦ ?_) hPm
  rw [abs_of_pos (det_fderiv_endChart_pos q w), smul_eq_mul,
    det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart ω hH hHs (hpos hw.1)]

/-- **The curvature is integrable over a truncation of the pair of pants, for a manifold target.**
Along a map `u` which is continuous on the truncation `S_R`, the curvature of the pair-of-pants
perturbation of period-one `C¹` Hamiltonians on a manifold is integrable over `S_R`. It vanishes
on the core of `S_R`, where every `±s < 1`, and in the coordinates of an end, multiplied by the
Jacobian of the end chart, it is the function `±β'(±s - 1) H_q(t, u)`, continuous on the compact
closure of the part `1 ≤ ±s ≤ R` of the end. Nothing is assumed about `u` off `S_R`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M} {R : ℝ}
    (hu : ContinuousOn u (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  set A : Puncture → Set (ℝ × ℝ) := fun q => endChart q '' endPiece q R
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- On each end piece, the curvature is integrable in the coordinates of the end.
  have hA (q : Puncture) : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) (A q) := by
    simp only [A, endPiece_def]
    exact integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_image_endChart ω hH hHs hu
      one_pos fun z h₁ h₂ ↦ endChart_mem_preimage_truncation (by linarith) h₂
  -- Off the end pieces every `±s < 1`, the perturbation vanishes nearby, and so does the curvature.
  refine (integrableOn_finite_iUnion.2 hA).of_forall_sdiff_eq_zero
    (isCompact_preimage_truncation R).isClosed.measurableSet fun z hz ↦ ?_
  refine ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt (K := pairOfPantsPerturbation H)
    (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y)
    (preimage_truncation_subset_thricePuncturedSphereReal R hz.1) (fun q ↦ ?_) (u z)
  by_contra! h
  exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endChart_endPiece hz.1 h⟩)

section Energy

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- The cylinder-coordinate half of the energy identity over a rectangle of an end, for a
manifold target: over the strip `[a₁, b₁] × [-1/2, 1/2)`, contained in an open set `U` on which
the end sign times the first coordinate is positive and which the end chart maps into a set where
`u` is `C¹`, the pulled-back Floer energy is the symplectic area, plus the Hamiltonian boundary
terms, minus the integrated curvature. The pulled-back energy density is integrable over the
rectangle automatically. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_endChart_rect
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    {V : Set (ℝ × ℝ)} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hU₁ : ∀ {z : ℝ × ℝ}, z.1 ∈ Icc a₁ b₁ → z ∈ U)
    (hpos : ∀ {z : ℝ × ℝ}, z ∈ U → 0 < q.endSign * z.1)
    (hUV : ∀ {z : ℝ × ℝ}, z ∈ U → endChart q z ∈ V) :
    ∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
        ω.floerEnergyDensity (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I)
          (u ∘ endChart q) w =
      (∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          (SmoothBundleForm.eval₂ ω ((u ∘ endChart q) w)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ w in Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
            (pairOfPantsEndComponent H q Complex.I) w ((u ∘ endChart q) w) := by
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) =ᵐ[volume]
      Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => hU₁ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`, and its curvature is the
  -- continuous function `±β'(±s - 1) H_q(t)`.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn fun _ hw => hUV hw
  have hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q 1)) (U ×ˢ univ) :=
    (contMDiffOn_const (c := (0 : ℝ))).congr fun p hp =>
      pairOfPantsEndComponent_one_of_pos (hpos hp.1) p.2
  have hβH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 fun p : (ℝ × ℝ) × M =>
      smoothTransition (q.endSign * p.1.1 - 1) * H q p.1.2 p.2 :=
    ((smoothTransition.contDiff.comp (f := fun z : ℝ × ℝ => q.endSign * z.1 - 1)
      (by fun_prop)).contMDiff.comp contMDiff_fst).smul
      ((hHs q).comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
  have hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q Complex.I)) (U ×ˢ univ) :=
    hβH.contMDiffOn.congr fun p hp => pairOfPantsEndComponent_I_of_pos (hH q) (hpos hp.1) p.2
  have hR : IntegrableOn (fun w ↦ ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) w ((u ∘ endChart q) w))
      (Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ((continuousOn_endSign_mul_deriv_smoothTransition_mul hHs
      hu.continuousOn q).mono fun w hw ↦ hUV (hIccU hw)).congr fun w hw ↦ ?_
    exact ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) (hpos (hIccU hw))
      ((((hHs q).comp (contMDiff_id.prodMk contMDiff_const)).contDiff.differentiable
        one_ne_zero) w.2)
  rw [hω.integral_floerEnergyDensity hUo hu' hKs hKt (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU
    (hω.integrableOn_floerEnergyDensity hUo hu' hKs hKt isCompact_Icc hIccU hR) hR]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c)
      ((u ∘ endChart q) (s, c)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hpos (hU₁ (z := (s, c)) hs)) _
  have ht {c : ℝ} (hc : c ∈ Icc a₁ b₁) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) ((u ∘ endChart q) (c, t)) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ =>
      pairOfPantsEndComponent_I_of_pos (hH q) (hpos (hU₁ (z := (c, t)) hc)) _
  rw [hs₀, hs₀, ht (c := a₁) ⟨le_rfl, hab⟩, ht (c := b₁) ⟨hab, le_rfl⟩]
  ring

/-- **The energy identity over a rectangle of an end, for a manifold target.** Over the image in
`S` of a rectangle `[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 0` of the end `q`, the Floer energy
of the pair-of-pants perturbation is the symplectic area, plus the integral of the Hamiltonian term
`β(±s - 1) H_q(t)` over the boundary circle `s = b₁` minus that over `s = a₁`, minus the integrated
curvature. The map `u` need only be `C¹` on an open set `V` containing the image of the whole strip
`[a₁, b₁] × ℝ`; the energy density is then integrable over the rectangle automatically. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 0 < q.endSign * a₁)
    (hb : 0 < q.endSign * b₁) (hV : ∀ z : ℝ × ℝ, z.1 ∈ Icc a₁ b₁ → endChart q z ∈ V) :
    ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  set U : Set (ℝ × ℝ) := {z | 0 < q.endSign * z.1} ∩ endChart q ⁻¹' V
  have hUo : IsOpen U := (isOpen_lt continuous_const (continuous_const.mul continuous_fst)).inter
    (hVo.preimage (contDiff_endChart q 0).continuous)
  -- The rectangle lies in the part `±s > 0` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : z ∈ U := by
    have h₀ : 0 < q.endSign * z.1 := by
      obtain ⟨h₁, h₂⟩ := hz
      rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
    exact ⟨h₀, hV z hz⟩
  have hsU {z : ℝ × ℝ} (hz : z ∈ s) : z ∈ U := hU₁ hz.1
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := hz.1
  have hS {z : ℝ × ℝ} (hz : z ∈ U) := endChart_mem_thricePuncturedSphereReal (hpos hz)
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart_univ_prod_Ico q (-1 / 2)).mono (prod_mono (subset_univ _) (by norm_num))
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (hVo.mem_nhds hw.2)).mdifferentiableAt one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ U) (v : ℂ) :=
    mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) (u (endChart q w)) v
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals.
  rw [ω.integral_eval₂_mfderiv_stdComplexLine_image hmeas hinj (fun w _ => hφ w)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud (hsU hw)),
    ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ => hφ w)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud (hsU hw))
      (fun w hw => htgt (hsU hw) 1) (fun w hw => htgt (hsU hw) _),
    ω.integral_hamiltonianCurvature_image hmeas hinj
      (fun w _ => (contDiff_endChart q 2).contDiffAt)
      (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS (hsU hw)) _ 1)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS (hsU hw)) _ _)
      (fun w hw => htgt (hsU hw) 1) (fun w hw => htgt (hsU hw) _),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  exact hω.integral_floerEnergyDensity_endChart_rect hH hHs hu hab hUo hU₁ hpos (fun hw ↦ hw.2)

/-- **The energy identity on an end piece, for a manifold target.** Over the image in `S` of the
end piece `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2)`, of the end `q`, the Floer energy of the pair-of-pants
perturbation is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the
boundary circle `±s = R`, minus the integrated curvature; the boundary term on the circle `±s = 1`
vanishes with the cutoff. The map `u` need only be `C¹` on an open set `V` containing the image of
the part `1 ≤ ±s ≤ R` of the end. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart_endPiece
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    {R : ℝ} {V : Set (ℝ × ℝ)} (hVo : IsOpen V) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    (hR : 1 ≤ R) (q : Puncture)
    (hV : ∀ z : ℝ × ℝ, 1 ≤ q.endSign * z.1 → q.endSign * z.1 ≤ R → endChart q z ∈ V) :
    ∫ z in endChart q '' endPiece q R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' endPiece q R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (q.endSign * ∫ t in (0 : ℝ)..1, H q t
          (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in endChart q '' endPiece q R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rw [← intervalIntegral_endChart_boundary_eq hH q]
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · rw [endPiece_of_endSign_eq_one h,
      hω.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart hH hHs hVo hu
      hR (by rw [h]; norm_num) (by rw [h]; linarith)
      (fun z hz ↦ hV z (by rw [h]; linarith [hz.1]) (by rw [h]; linarith [hz.2]))]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · rw [endPiece_of_endSign_eq_neg_one h,
      hω.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart hH hHs hVo hu
      (by linarith) (by rw [h]; linarith) (by rw [h]; norm_num)
      (fun z hz ↦ hV z (by rw [h]; linarith [hz.2]) (by rw [h]; linarith [hz.1]))]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]
    ring

/-- **The energy identity on the truncated pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a finite-dimensional manifold
with a nondegenerate two-form, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the
global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C¹` on an open set `V`
containing the truncation `S_R` of `S`, for instance on `S` itself. For `R ≥ 1`, the Floer energy
over `S_R` is the symplectic area, plus `β(R - 1)` times
the signed sum over the three ends of the integrals of `H_q(t)` along the boundary circles
`±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. The energy, area and curvature densities are integrable over `S_R` automatically.
Nothing is assumed about `u` off `V`, so `u` may be singular beyond `S_R`, as happens for a map
on a pair of pants glued into a larger surface. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    {R : ℝ} {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
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
  have hT : IsCompact T := isCompact_preimage_truncation R
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  have harea := ω.integrableOn_eval₂_mfderiv hVo hu hT hTV stdComplexLineReal stdComplexLineImag
  have hcurv := integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation ω hH hHs
    (hu.continuousOn.mono hTV)
  have hKp := contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    (contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs)
  have hE := hω.integrableOn_floerEnergyDensity (hVo.inter isOpen_thricePuncturedSphereReal)
    (hu.mono inter_subset_left) ((hKp 1).mono (prod_mono inter_subset_right subset_rfl))
    ((hKp Complex.I).mono (prod_mono inter_subset_right subset_rfl)) hT (subset_inter hTV hTS)
    hcurv
  -- The truncation is the disjoint union of its core `C`, where every `±s < 1`, and the three
  -- end pieces.
  have hAm (q : Puncture) : MeasurableSet (A q) := measurableSet_image_endChart_endPiece q R
  have hAT (q : Puncture) : A q ⊆ T := image_endChart_endPiece_subset_preimage_truncation q R
  have hAd : Pairwise (Disjoint on A) := fun q r hqr => disjoint_image_endChart_endPiece hqr
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ q, ∫ z in A q, f z := by
    have hTC : T = C ∪ ⋃ q, A q := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun q => hf.mono_set (hAT q)]
  -- On the core the perturbation vanishes nearby, so the energy is the area and the curvature
  -- vanishes.
  have hcore {z : ℝ × ℝ} (hz : z ∈ C) :
      ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
    intro q
    by_contra! h
    exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endChart_endPiece hz.1 h⟩)
  have hCm : MeasurableSet C := hT.isClosed.measurableSet.diff (MeasurableSet.iUnion hAm)
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
    refine setIntegral_congr_fun hCm fun z hz => ?_
    have hK : pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ => 0 :=
      funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦ (hcore hz q).le)
    simp [floerEnergyDensity_def, hK, hamiltonianVectorField_const]
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz =>
      ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt (K := pairOfPantsPerturbation H)
        (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y) (hTS hz.1) (hcore hz)
        (u z)
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE, hCR,
    Finset.sum_congr rfl fun q _ =>
      hω.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart_endPiece hH hHs hVo hu
        hR q fun z h₁ h₂ ↦ hTV (endChart_mem_preimage_truncation (by linarith) h₂),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- **The energy bound on the truncated pair of pants, for a manifold target.** If the end
Hamiltonians are bounded, `|H_q| ≤ B_q`, then for every `R ≥ 1` and every map `u` which is `C¹`
on an open set containing the truncation `S_R`, the Floer energy over `S_R` differs from the
symplectic area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in
`R`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    {R : ℝ} {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hVo hTV hu hR,
    hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

end Energy

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
  Floer.differentiableAt_pairOfPantsPerturbation_domain hH
    (contMDiff_uncurry_of_contDiff hHs) hz x v

/-- The components of the perturbation are differentiable in the target point, at points
of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
      x :=
  mdifferentiableAt_iff_differentiableAt.1
    (Floer.mdifferentiableAt_pairOfPantsPerturbation_target hH
      (contMDiff_uncurry_of_contDiff hHs) hz x v)

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
  have hT := isCompact_preimage_truncation R
  have hTS := preimage_truncation_subset_thricePuncturedSphereReal R
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

/-- **The energy identity on the truncated pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`,
and let `u` be a map which is `C¹` on `S`. For `R ≥ 1`, over the truncation `S_R` of `S` the Floer
energy of `u` is its symplectic area, plus `β(R - 1)` times the signed sum over the three ends of
the integrals of `H_q(t)` along the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. This is the vector-space case of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`. -/
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
    hH (contMDiff_uncurry_of_contDiff hHs) isOpen_thricePuncturedSphereReal
    (preimage_truncation_subset_thricePuncturedSphereReal R) (contMDiffOn_iff_contDiffOn.mpr hu) hR


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
integrable over `S`. This is the vector-space case of
`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`. -/
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
  have h := ω.constSmooth.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation hH
    (contMDiff_uncurry_of_contDiff hHs) hu
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h


/-! ### One-sided curvature bounds -/

/-- The points of `S`, in real coordinates, form an open set. -/
private theorem isOpen_puncturedSphere :
    IsOpen {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1} :=
  isOpen_thricePuncturedSphereReal

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
    exact hg.intervalIntegral_neg_div_two_eq.symm
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
