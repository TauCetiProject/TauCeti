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
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`).

The same decomposition of `S` into its core, where `K` vanishes, and the three ends integrates
the energy identity over the truncation `S_R` of `S`
(`TauCeti.ThricePuncturedSphere.truncation`), where every `±s ≤ R`. On each end the rectangle
identity `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` applies in cylinder
coordinates; the boundary terms along the angular sides cancel by periodicity, and those on the
circles `±s = 1` vanish with the cutoff. For a map `u` which is `C¹` on `S` and `R ≥ 1` this
gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. Here the area density
`ω(∂_s u, ∂_t u)` is continuous on `S`, so integrable over the compact set `S_R`, and so is the
energy density, since it differs from the area density by the curvature and the exterior
derivative `d(K(u))`, which is continuous on `S`. With the curvature bound, the energy over `S_R`
therefore differs from the area plus the Hamiltonian boundary terms by at most `B₀ + B₁ + B_∞`,
uniformly in `R`. Letting `R → ∞`
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

/-! ### The pieces of a truncation of the pair of pants -/

/-- The part `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates: the
collar and the cylindrical part of the end inside the truncation `S_R`, over one period. -/
private noncomputable def endPiece (q : Puncture) (R : ℝ) : Set (ℝ × ℝ) :=
  {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico (-1 / 2) (1 / 2)

/-- An end piece is measurable. -/
private theorem measurableSet_endPiece (q : Puncture) (R : ℝ) : MeasurableSet (endPiece q R) :=
  (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
    (measurableSet_le (measurable_const.mul measurable_id) measurable_const) |>.prod
    measurableSet_Ico

/-- An end piece lies in the strip of its end, where the end chart is injective. -/
private theorem endPiece_subset_endStrip (q : Puncture) (R : ℝ) : endPiece q R ⊆ endStrip q :=
  fun z hz => mem_endStrip_iff.2 ⟨by linarith [hz.1.1], hz.2⟩

/-- The closure of an end piece, `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2]`, is compact. -/
private theorem isCompact_closedEndPiece (q : Puncture) (R : ℝ) :
    IsCompact ({s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) :=
  ((Homeomorph.mulLeft₀ q.endSign q.endSign_ne_zero).isCompact_preimage.2
    (isCompact_Icc (a := 1) (b := R))).prod isCompact_Icc

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

/-- The image of an end piece in `S` is measurable. -/
private theorem measurableSet_image_endPiece (q : Puncture) (R : ℝ) :
    MeasurableSet (endChart q '' endPiece q R) :=
  measurable_image_of_fderivWithin (measurableSet_endPiece q R)
    (fun w _ => (hasFDerivAt_endChart q w).hasFDerivWithinAt)
    ((injOn_endChart q).mono (endPiece_subset_endStrip q R))

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
  have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
  norm_num at h
  simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
  convert h using 1 <;> norm_num

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


/-! ### The energy identity on the truncated pair of pants -/

omit [IsManifold I ⊤ M] in
/-- The components of the perturbation in real coordinates are `C¹` jointly in the domain point
of `S` and the target point, for `C¹` Hamiltonians on a manifold. -/
private theorem contMDiffOn_pairOfPantsPerturbation (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hK := contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs
    ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) 1
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
      contMDiffAt_snd
  exact ((hK.comp (z, x) hφ).clm_apply contMDiffAt_const).contMDiffWithinAt

omit [IsManifold I ⊤ M] in
/-- Along a map continuous on `S`, the curvature of the pair-of-pants perturbation in the
coordinates of the end `q`, multiplied by the Jacobian of the end chart, is
`±β'(±s - 1) H_q(t, u)`, a continuous function on the part `±s > 0` of the end. -/
private theorem continuousOn_endSign_mul_deriv_smoothTransition_mul
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) (q : Puncture) :
    ContinuousOn (fun w : ℝ × ℝ ↦
        q.endSign * deriv smoothTransition (q.endSign * w.1 - 1) * H q w.2 (u (endChart q w)))
      {w | 0 < q.endSign * w.1} := by
  have hβ : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hu' : ContinuousOn (fun w ↦ u (endChart q w)) {w : ℝ × ℝ | 0 < q.endSign * w.1} :=
    hu.comp (contDiff_endChart q 0).continuous.continuousOn
      fun _ hw ↦ endChart_mem_thricePuncturedSphereReal hw
  have hHu : ContinuousOn (fun w : ℝ × ℝ ↦ H q w.2 (u (endChart q w)))
      {w : ℝ × ℝ | 0 < q.endSign * w.1} :=
    (hHs q).continuous.comp_continuousOn (continuousOn_snd.prodMk hu')
  exact (continuous_const.mul (hβ.comp (by fun_prop))).continuousOn.mul hHu

/-- Along a map continuous on `S`, the curvature of the pair-of-pants perturbation is integrable
over the image of each end piece. -/
private theorem integrableOn_image_endPiece_hamiltonianCurvature (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) (q : Puncture) (R : ℝ) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (endChart q '' endPiece q R) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_endPiece q R)
    (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    ((injOn_endChart q).mono (endPiece_subset_endStrip q R))]
  -- In the coordinates of the end the integrand is `±β'(±s - 1) H_q(t, u)`, which is continuous
  -- on the compact closure of the end piece.
  have hpos {w : ℝ × ℝ}
      (hw : w ∈ {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)) :
      0 < q.endSign * w.1 := by
    linarith [hw.1.1]
  refine IntegrableOn.mono_set ?_ (prod_mono subset_rfl Ico_subset_Icc_self)
  refine ContinuousOn.integrableOn_compact (isCompact_closedEndPiece q R) ?_
  refine ((continuousOn_endSign_mul_deriv_smoothTransition_mul hHs hu q).mono
    fun w hw ↦ hpos hw).congr fun w hw ↦ ?_
  rw [smul_eq_mul, abs_of_pos (det_fderiv_endChart_pos q w),
    det_mul_hamiltonianCurvature_pairOfPantsPerturbation_endChart ω hH hHs (hpos hw)]

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
  refine (integrableOn_finite_iUnion.2 fun q ↦
    integrableOn_image_endPiece_hamiltonianCurvature ω hH hHs hu q 2).of_forall_sdiff_eq_zero
    isOpen_thricePuncturedSphereReal.measurableSet fun z ⟨hzS, hzA⟩ ↦ ?_
  by_cases h₂ : ∃ q : Puncture, 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
  · obtain ⟨q, hq⟩ := h₂
    exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs hzS hq _
  -- Otherwise `z` lies in the truncation `S_2`, outside the end pieces, hence in its core.
  simp only [not_exists, not_lt] at h₂
  have hzT : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation 2 :=
    mem_truncation.2 ⟨hzS.1, hzS.2, h₂⟩
  refine ω.hamiltonianCurvature_eq_zero_of_forall_endCoord_lt (K := pairOfPantsPerturbation H)
    (fun w hw y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le hw y) hzS (fun q ↦ ?_) (u z)
  by_contra! h
  exact hzA (mem_iUnion.2 ⟨q, mem_image_endPiece hzT h⟩)

section Energy

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- The cylinder-coordinate half of the energy identity over a rectangle of an end, for a
manifold target: over the strip `[a₁, b₁] × [-1/2, 1/2)`, contained in an open set `U` on which
the end sign times the first coordinate is positive, the pulled-back Floer energy is the
symplectic area, plus the Hamiltonian boundary terms, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_endChart_rect
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hU₁ : ∀ {z : ℝ × ℝ}, z.1 ∈ Icc a₁ b₁ → z ∈ U)
    (hpos : ∀ {z : ℝ × ℝ}, z ∈ U → 0 < q.endSign * z.1)
    (hE : IntegrableOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q))
      (Icc a₁ b₁ ×ˢ Ico (-1 / 2 : ℝ) (1 / 2))) :
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
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => hU₁ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`, and its curvature is the
  -- continuous function `±β'(±s - 1) H_q(t)`.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn
      fun _ hw => endChart_mem_thricePuncturedSphereReal (hpos hw)
  have hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry (pairOfPantsEndComponent H q 1)) (U ×ˢ univ) :=
    (contMDiffOn_const (c := (0 : ℝ))).congr fun p hp =>
      pairOfPantsEndComponent_one_of_pos (hH q) (hpos hp.1) p.2
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
      hu.continuousOn q).mono fun w hw ↦ hpos (hIccU hw)).congr fun w hw ↦ ?_
    exact ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) (hpos (hIccU hw))
      ((((hHs q).comp (contMDiff_id.prodMk contMDiff_const)).contDiff.differentiable
        one_ne_zero) w.2)
  rw [hω.integral_floerEnergyDensity hUo hu' hKs hKt (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU
    (hE.congr_set_ae hae.symm) hR]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c)
      ((u ∘ endChart q) (s, c)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (hpos (hU₁ (z := (s, c)) hs)) _
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
`S` of a rectangle `[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, over which the
Floer energy density is integrable, the Floer energy is the symplectic area, plus the integrals of
the Hamiltonian term `β(±s - 1) H_q(t)` over the outgoing boundary circle minus the incoming one,
minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_endChart
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 1 / 2 < q.endSign * a₁)
    (hb : 1 / 2 < q.endSign * b₁)
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)))) :
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
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  -- The rectangle lies in the part `±s > 1/2` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * z.1 := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hsU {z : ℝ × ℝ} (hz : z ∈ s) : z ∈ U := hU₁ hz.1
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := by
    have h : 1 / 2 < q.endSign * z.1 := hz
    linarith
  have hS {z : ℝ × ℝ} (hz : z ∈ U) := endChart_mem_thricePuncturedSphereReal (hpos hz)
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart q).mono fun z hz => mem_endStrip_iff.2 ⟨hsU hz, hz.2⟩
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))).mdifferentiableAt
      one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ U) (v : ℂ) :=
    mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) (u (endChart q w)) v
  -- The energy density, in the coordinates of the end, is integrable over the rectangle.
  have hE' : IntegrableOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q)) s := by
    have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    refine ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas
      (fun w _ ↦ (hφ w).hasFDerivAt.hasFDerivWithinAt) hinj _).1 hE).congr_fun
      (fun w hw ↦ ?_) hmeas
    have h := ω.floerEnergyDensity_perturbationPullback
      (Ks := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      (hφ w) (hud (hsU hw)) (htgt (hsU hw) 1) (htgt (hsU hw) Complex.I)
    rw [perturbationPullback_endChart, perturbationPullback_endChart,
      equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag] at h
    rw [h]
    simp only [smul_eq_mul, abs_of_nonneg (det_fderiv_endChart_nonneg q w)]
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ => hφ w) (fun w _ => det_fderiv_endChart_nonneg q w)
    (fun w hw => hud (hsU hw)) (fun _ _ => mdifferentiableAt_const)
    (fun _ _ => mdifferentiableAt_const)
  have h₀ (v : ℝ × ℝ) : perturbationPullback (endChart q) (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ => hφ w)
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
  exact hω.integral_floerEnergyDensity_endChart_rect hH hHs hu hab hUo hU₁ hpos hE'

/-- **The energy identity on an end piece, for a manifold target.** Over the end piece
`1 ≤ ±s ≤ R` of the end `q`, over which the Floer energy density is integrable, the Floer energy
is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the boundary circle
`±s = R`, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_endPiece
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R)
    (q : Puncture)
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' endPiece q R)) :
    ∫ z in endChart q '' endPiece q R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' endPiece q R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) *
          (q.endSign * ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t)))) -
        ∫ z in endChart q '' endPiece q R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · have hpiece : endPiece q R = Icc 1 R ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp [endPiece, h]
    rw [hpiece] at hE ⊢
    rw [hω.integral_floerEnergyDensity_image_endChart hH hHs hu hR
      (by rw [h]; norm_num) (by rw [h]; linarith) hE]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · have hpiece : endPiece q R = Icc (-R) (-1) ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp only [endPiece, h, mem_prod, mem_ofPred_eq, mem_Icc]
      constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
    rw [hpiece] at hE ⊢
    rw [hω.integral_floerEnergyDensity_image_endChart hH hHs hu (by linarith)
      (by rw [h]; linarith) (by rw [h]; norm_num) hE]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]
    ring

/-- Over a compact part `T` of `S`, along a map which is `C¹` on `S`, the Floer energy density of
the pair-of-pants perturbation is integrable: it differs from the symplectic area density, which is
continuous on `S`, by the exterior derivative `d(K(u))`, which is continuous on `S`, and by the
curvature. -/
private theorem IsNondegenerate.integrableOn_floerEnergyDensity_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {T : Set (ℝ × ℝ)}
    (hT : IsCompact T) (hTS : T ⊆ thricePuncturedSphereReal) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) T := by
  have hmem : MapsTo (fun w ↦ (w, u w)) thricePuncturedSphereReal
      (thricePuncturedSphereReal ×ˢ (univ : Set M)) := fun _ hz ↦ ⟨hz, mem_univ _⟩
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv
    isOpen_thricePuncturedSphereReal hu stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  replace harea := (harea.mono hTS).integrableOn_compact (μ := volume) hT
  -- Each pulled-back component `K(u)` is `C¹` on `S`, so its derivative is continuous on `S`.
  have hd (v : ℂ) (e : ℝ × ℝ) : IntegrableOn (fun z ↦ fderiv ℝ
      (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v) z e) T := by
    have hK : ContDiffOn ℝ 1
        (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v)
        thricePuncturedSphereReal :=
      contMDiffOn_iff_contDiffOn.mp ((contMDiffOn_pairOfPantsPerturbation hH hHs v).comp
        (contMDiffOn_id.prodMk hu) hmem)
    exact (((hK.continuousOn_fderiv_of_isOpen isOpen_thricePuncturedSphereReal le_rfl).clm_apply
      continuousOn_const).mono hTS).integrableOn_compact hT
  have hR := (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs
    hu.continuousOn).mono_set hTS
  refine ((harea.add ((hd Complex.I stdComplexLineReal).sub (hd 1 stdComplexLineImag))).sub
    hR).congr_fun (fun z hz ↦ ?_) hT.isClosed.measurableSet
  have hzS := hTS hz
  have hzS' : (z, u z) ∈ thricePuncturedSphereReal ×ˢ (univ : Set M) := hmem hzS
  have hKz (v : ℂ) := ((contMDiffOn_pairOfPantsPerturbation hH hHs v).contMDiffAt
    ((isOpen_thricePuncturedSphereReal.prod isOpen_univ).mem_nhds hzS')).mdifferentiableAt
      one_ne_zero
  rw [hω.floerEnergyDensity_eq ((hu.contMDiffAt
    (isOpen_thricePuncturedSphereReal.mem_nhds hzS)).mdifferentiableAt one_ne_zero) (hKz 1)
    (hKz Complex.I)]
  rfl

/-- **The energy identity on the truncated pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on a finite-dimensional manifold
with a nondegenerate two-form, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the
global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C¹` on `S`. For `R ≥ 1`,
the Floer energy over the truncation `S_R` of `S` is the symplectic area, plus `β(R - 1)` times
the signed sum over the three ends of the integrals of `H_q(t)` along the boundary circles
`±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. The energy, area and curvature densities are integrable over `S_R` automatically. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
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
  have hT : IsCompact T :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
  have hTS : T ⊆ thricePuncturedSphereReal := fun z hz =>
    mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩
  have hE := hω.integrableOn_floerEnergyDensity_pairOfPantsPerturbation hH hHs hu hT hTS
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv
    isOpen_thricePuncturedSphereReal hu stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  replace harea := (harea.mono hTS).integrableOn_compact (μ := volume) hT
  have hcurv := (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs
    hu.continuousOn).mono_set hTS
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
  -- On the core the perturbation vanishes nearby, so the energy is the area and the curvature
  -- vanishes.
  have hcore {z : ℝ × ℝ} (hz : z ∈ C) :
      ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
    intro q
    by_contra! h
    exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)
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
    Finset.sum_congr rfl fun q _ => hω.integral_floerEnergyDensity_image_endPiece hH hHs hu hR q
      (hE.mono_set (hAT q)),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [intervalIntegral_endChart_boundary_eq hH]
  ring

/-- **The energy bound on the truncated pair of pants, for a manifold target.** If the end
Hamiltonians are bounded, `|H_q| ≤ B_q`, then for every `R ≥ 1` the Floer energy over the
truncation `S_R` differs from the symplectic area plus the Hamiltonian
boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R) :
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
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hu hR, hsub,
    abs_neg]
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
  SmoothTwoForm.differentiableAt_pairOfPantsPerturbation_domain hH
    (contMDiff_uncurry_of_contDiff hHs) hz x v

/-- The components of the perturbation are differentiable in the target point, at points
of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y => pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v)
      x :=
  mdifferentiableAt_iff_differentiableAt.1
    (SmoothTwoForm.mdifferentiableAt_pairOfPantsPerturbation_target hH
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
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
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
