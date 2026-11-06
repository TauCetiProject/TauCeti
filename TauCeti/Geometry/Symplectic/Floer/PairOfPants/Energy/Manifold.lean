/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.EndChart
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The energy identity of the pair of pants for manifold targets

Let `(M, ω)` be a manifold with a nondegenerate two-form, let `H_q` be period-one `C¹`
Hamiltonians on `ℝ × M` attached to the three ends of the pair of pants `S = ℂ ∖ {0, 1}`, and let
`K = TauCeti.Floer.pairOfPantsPerturbation H` be the pair-of-pants perturbation, equal to
`β(±s - 1) H_q(t) dt` in the end coordinates `(s, t)` of the end `q` and to zero off the ends. This
file proves the energy identity `E = ∫ u^*ω + ∫_∂ K(u) - ∫ R_K(u)` for maps `u : S → M` into the
manifold, together with the curvature bound which makes it an energy estimate.

The Floer energy density, the symplectic area density and the curvature `R_K` are those of
`TauCeti.Geometry.Symplectic.Floer.Manifold`, computed in the global coordinate `z = s + i t` of
`S ⊆ ℂ`. The curvature is a two-form on the domain
(`TauCeti.SmoothTwoForm.hamiltonianCurvature_perturbationPullback`), and in the end coordinates of
the end `q` it is the continuation curvature `±β'(±s - 1) H_q(t)`
(`TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsEndComponent`). It vanishes on the core
of `S`, where `K` vanishes, and beyond the collars `1 ≤ ±s ≤ 2` of the ends. Hence:

* if `|H_q| ≤ B_q`, then `∫_S |R_K(z, u(z))| dz ≤ B₀ + B₁ + B_∞` for every map `u : S → M`
  (`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`);
* along a map continuous on `S` the curvature is integrable over `S`, with no bound on the
  Hamiltonians (`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`).

For a map `u` which is `C¹` on `S` and whose energy density is integrable over the truncation
`S_R` (`TauCeti.ThricePuncturedSphere.truncation`), `R ≥ 1`, cutting `S_R` into its core and the
three end pieces `1 ≤ ±s ≤ R` and applying the energy identity on rectangles
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` in the end coordinates gives

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`),
with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The boundary terms
along the angular sides cancel by periodicity. Letting `R → ∞` gives the identity on the whole pair
of pants, with the boundary term evaluated at the asymptotic loops of `u`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`). For a
solution of the Floer equation with tamed almost complex structures the energy is nonnegative, so
the topological part `∫ u^*ω + ∑ ±∫ H_q(x_q)` is at least `-(B₀ + B₁ + B_∞)`.

Neither closedness of `ω` nor any compactness of `M` is used. On a symplectic vector space these
statements recover those of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature`.

## Main results

* `TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt`: the
  curvature vanishes on the cylindrical parts of the ends.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`: the
  integrated curvature bound.
* `TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`: the curvature
  along a continuous map is integrable over `S`.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`:
  the energy identity on the truncated pair of pants.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`:
  the energy identity on the whole pair of pants.
* `TauCeti.SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap`: the
  lower bound on the topological energy of a Floer solution.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends and their energy.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {H : Puncture → ℝ → M → ℝ}

namespace Floer

variable (hH : ∀ q, Periodic (H q) 1)
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
include hH hHs

/-- The components of the perturbation are differentiable in the domain point, at points
of `S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z :=
  (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).differentiableAt_curry_left
    one_ne_zero

/-- The components of the perturbation are differentiable in the target point, at points
of `S`. -/
private theorem mdifferentiableAt_pairOfPantsPerturbation_target {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  ((contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero

/-- On the part `±s > 0` of the end `q`, the components of the perturbation in end coordinates are
`C¹` jointly in the cylinder point and the target point. -/
private theorem contMDiffOn_pairOfPantsEndComponent (q : Puncture) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (pairOfPantsEndComponent H q v))
      ({z : ℝ × ℝ | 0 < q.endSign * z.1} ×ˢ univ) := by
  have hβ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ smoothTransition (q.endSign * p.1.1 - 1)) :=
    (smoothTransition.contDiff.comp (f := fun ζ : ℝ × ℝ ↦ q.endSign * ζ.1 - 1)
      (by fun_prop)).contMDiff.comp contMDiff_fst
  have hHq : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : (ℝ × ℝ) × M ↦ H q p.1.2 p.2) :=
    (hHs q).comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hv : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1 fun _ : (ℝ × ℝ) × M ↦ v.im :=
    contMDiff_const
  refine (hv.smul (hβ.smul hHq)).contMDiffOn.congr fun p hp ↦ ?_
  simp only [Pi.smul_apply', smul_eq_mul]
  exact pairOfPantsEndComponent_of_pos (hH q) hp.1 v p.2

end Floer

namespace SmoothTwoForm

open Floer

variable [IsManifold I (⊤ : ℕ∞) M] {q : Puncture}

variable (hH : ∀ q, Periodic (H q) 1)
  (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))

include hH hHs in
/-- **The curvature in the coordinates of an end.** On the end `q`, where `±s > 0`, the Jacobian
determinant of the end chart times the curvature of the perturbation is `±β'(±s - 1) H_q(t)`. -/
private theorem det_mul_hamiltonianCurvature_endChart (ω : SmoothTwoForm I M) {ζ : ℝ × ℝ}
    (hζ : 0 < q.endSign * ζ.1) (x : M) :
    (fderiv ℝ (endChart q) ζ).det * ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (endChart q ζ) x =
      q.endSign * deriv smoothTransition (q.endSign * ζ.1 - 1) * H q ζ.2 x := by
  have hS := endChart_mem_thricePuncturedSphereReal hζ
  rw [← ω.hamiltonianCurvature_perturbationPullback ((contDiff_endChart q 2).contDiffAt)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS x 1)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS x Complex.I)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS x 1)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS x Complex.I),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hζ
      ((hHs q (ζ.2, x)).differentiableAt_curry_left one_ne_zero)]

/-- **The curvature is supported on the ends.** At a point of `S` where the signed longitudinal
coordinate of every end is less than `1`, the perturbation vanishes nearby, and so does its
curvature. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero (ω : SmoothTwoForm I M)
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (h : ∀ q : Puncture, q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1)
    (x : M) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  have hev : ∀ᶠ z' in 𝓝 z, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z')).re < 1 := by
    refine Filter.eventually_all.2 fun q ↦ ?_
    have hc : ContinuousAt
        (fun z' ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z')).re) z :=
      continuousAt_const.mul
        (((q.contDiffAt_re_endCoord (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)
          (n := 0)).continuousAt).comp
          Complex.equivRealProdCLM.symm.continuous.continuousAt)
    exact hc.eventually (gt_mem_nhds (h q))
  have hK : ∀ᶠ z' in 𝓝 z, ∀ y, pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') y = 0 :=
    hev.mono fun z' hz' y ↦ pairOfPantsPerturbation_eq_zero_of_forall_le (fun q ↦ (hz' q).le) y
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
    (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y])
    (hK.mono fun z' hz' ↦ funext fun y ↦ by simp [hz' y]), hamiltonianCurvature_zero_left]
  simp

include hH hHs in
/-- **The curvature vanishes on the cylindrical parts of the ends.** At a point of `S` where the
signed longitudinal coordinate of some end is greater than `2`, the perturbation is `H_q(t) dt` in
the coordinates of that end, and its curvature vanishes. Together with the vanishing on the core,
this confines the curvature to the collars `1 ≤ ±s ≤ 2` of the three ends, a compact part
of `S`. -/
theorem hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt (ω : SmoothTwoForm I M)
    {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    (hq : 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) (x : M) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  obtain ⟨w, hw, rfl⟩ := mem_image_endChart hz (q := q) (by linarith)
  have hw₂ : 2 < q.endSign * w.1 := by rwa [re_endCoord_endChart] at hq
  have key := det_mul_hamiltonianCurvature_endChart hH hHs ω (by linarith : 0 < q.endSign * w.1) x
  rw [smoothTransition.deriv_of_one_lt (by linarith), mul_zero, zero_mul] at key
  exact (mul_eq_zero.1 key).resolve_left (det_fderiv_endChart_pos q w).ne'

include hH hHs in
/-- The curvature of the perturbation over the image of the strip of the end `q` is at most a
bound `B_q` for the Hamiltonian of that end. -/
private theorem setLIntegral_image_endChart_le (ω : SmoothTwoForm I M) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) (q : Puncture) :
    ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B q) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hmeas := measurableSet_endStrip q
  have hψ : ∀ s, 0 ≤ deriv smoothTransition s := fun _ ↦ smoothTransition.monotone.deriv_nonneg
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
    (fun z _ ↦ (hasFDerivAt_endChart q z).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (injOn_endChart q)]
  calc _ ≤ ∫⁻ z in endStrip q,
        ENNReal.ofReal (deriv smoothTransition (q.endSign * z.1 - 1)) * ENNReal.ofReal (B q) := by
        refine setLIntegral_mono' hmeas fun z hz ↦ ?_
        -- The curvature is a two-form, and in the coordinates of the end it is `±β' H_q`.
        have key := det_mul_hamiltonianCurvature_endChart hH hHs ω
          (endSign_mul_pos_of_mem_endStrip hz) (u (endChart q z))
        rw [← ENNReal.ofReal_mul (hψ _), ← Real.enorm_eq_ofReal_abs, ← enorm_mul, key,
          Real.enorm_eq_ofReal_abs, abs_mul, abs_mul, abs_endSign, abs_of_nonneg (hψ _), one_mul]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB q _ _) (hψ _))
    _ = ∫⁻ s in {s | 1 / 2 < q.endSign * s},
        ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1)) * ENNReal.ofReal (B q) := by
        have hm : Measurable fun z : ℝ × ℝ ↦
            ENNReal.ofReal (deriv smoothTransition (q.endSign * z.1 - 1)) * ENNReal.ofReal (B q) :=
          (ENNReal.continuous_ofReal.comp
            (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
              (by fun_prop))).measurable.mul_const _
        have hvol : volume (Ico (-1 / 2 : ℝ) (1 / 2)) = 1 := by
          rw [Real.volume_Ico]
          norm_num
        rw [Measure.volume_eq_prod, endStrip_def, setLIntegral_prod _ hm.aemeasurable]
        simp only [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1)) * ENNReal.ofReal (B q) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (B q) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          smoothTransition.lintegral_ofReal_deriv_mul_sub 1 (abs_ne_zero.1 (by simp)), abs_endSign,
          inv_one, ENNReal.ofReal_one, one_mul]

include hH hHs in
/-- **The integrated curvature of the pair-of-pants perturbation.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on `ℝ × M`, with `|H_q| ≤ B_q`, and write its
components in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)`. Then for every map `u` into `M`, the integral of `|R_K(z, u(z))|` over the plane
is at most `B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  set N : Set (ℝ × ℝ) := {Complex.equivRealProdCLM 0, Complex.equivRealProdCLM 1}
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  -- Off the two punctures, the curvature is supported in the images of the strips of the ends.
  have hsupp : support (fun z ↦ ‖ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)‖ₑ) ⊆ (⋃ q, endChart q '' endStrip q) ∪ N := by
    intro z hz
    by_cases h₀ : Complex.equivRealProdCLM.symm z = 0
    · exact Or.inr (Or.inl ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₀)))
    by_cases h₁ : Complex.equivRealProdCLM.symm z = 1
    · exact Or.inr (Or.inr ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans
        (congrArg _ h₁)))
    have hS : z ∈ thricePuncturedSphereReal := mem_thricePuncturedSphereReal_iff.2 ⟨h₀, h₁⟩
    by_cases hq : ∃ q : Puncture,
        1 / 2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re
    · obtain ⟨q, hq⟩ := hq
      exact Or.inl (mem_iUnion.2 ⟨q, mem_image_endChart hS hq⟩)
    · simp only [not_exists, not_lt] at hq
      refine absurd ?_ hz
      simp [hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω hS
        (fun q ↦ (hq q).trans_lt (by norm_num))]
  calc _ = ∫⁻ z in (⋃ q, endChart q '' endStrip q) ∪ N, ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)‖ₑ := (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ = _ := tsum_fintype _
    _ ≤ _ := Finset.sum_le_sum fun q _ ↦ setLIntegral_image_endChart_le hH hHs ω hB u q

include hH hHs in
/-- The integral of the curvature of the pair-of-pants perturbation along any map, over any set,
has absolute value at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (u : ℝ × ℝ → M) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, B q := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hB q 0 (u 0))
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q _ ↦ hB₀ q),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_sum_of_nonneg fun q _ ↦ hB₀ q]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le hH hHs ω hB u))

/-! ### Decomposing the truncated pair of pants -/

/-- The part `1 ≤ ±s ≤ R`, `t ∈ [-1/2, 1/2)` of the end `q` in its cylinder coordinates: the
collar and the cylindrical part of the end inside the truncation `S_R`, over one period. -/
private noncomputable def endPiece (q : Puncture) (R : ℝ) : Set (ℝ × ℝ) :=
  {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Ico (-1 / 2) (1 / 2)

/-- On an input end, the longitudinal range `1 ≤ ±s ≤ R` of an end piece is `[1, R]`. -/
private theorem setOf_endSign_mul_eq_Icc_of_endSign_eq_one (h : q.endSign = 1) (R : ℝ) :
    {s : ℝ | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} = Icc 1 R := by
  ext s
  simp [h]

/-- On the output end, the longitudinal range `1 ≤ ±s ≤ R` of an end piece is `[-R, -1]`. -/
private theorem setOf_endSign_mul_eq_Icc_of_endSign_eq_neg_one (h : q.endSign = -1) (R : ℝ) :
    {s : ℝ | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} = Icc (-R) (-1) := by
  ext s
  simp only [h, neg_mul, one_mul, mem_ofPred_eq, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The end pieces lie in the strips of the ends. -/
private theorem endPiece_subset_endStrip (q : Puncture) (R : ℝ) : endPiece q R ⊆ endStrip q :=
  fun z hz ↦ by
    have h : 1 ≤ q.endSign * z.1 := hz.1.1
    exact mem_endStrip_iff.2 ⟨by linarith, hz.2⟩

/-- The end pieces are measurable. -/
private theorem measurableSet_endPiece (q : Puncture) (R : ℝ) : MeasurableSet (endPiece q R) :=
  (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
    (measurableSet_le (measurable_const.mul measurable_id) measurable_const) |>.prod
    measurableSet_Ico

/-- The images of the end pieces are measurable. -/
private theorem measurableSet_image_endPiece (q : Puncture) (R : ℝ) :
    MeasurableSet (endChart q '' endPiece q R) :=
  measurable_image_of_fderivWithin (measurableSet_endPiece q R)
    (fun w _ ↦ (hasFDerivAt_endChart q w).hasFDerivWithinAt)
    ((injOn_endChart q).mono (endPiece_subset_endStrip q R))

/-- The end pieces lie in the truncation. -/
private theorem image_endPiece_subset (q : Puncture) {R : ℝ} (hR : 1 ≤ R) :
    endChart q '' endPiece q R ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (1 ≤ q.endSign * z.1 ∧ q.endSign * z.1 ≤ R) ∧ z.2 ∈ Ico (-1 / 2 : ℝ) (1 / 2) := hz
  have hz₀ : 0 < q.endSign * z.1 := by linarith [hz'.1.1]
  have hS := mem_thricePuncturedSphereReal_iff.1 (endChart_mem_thricePuncturedSphereReal hz₀)
  refine mem_truncation.2 ⟨hS.1, hS.2, fun r ↦ ?_⟩
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

/-- The part of the truncation `S_R` off the three end pieces: there every signed longitudinal
coordinate is less than `1`. -/
private theorem lt_one_of_mem_diff {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R)
    (q : Puncture) : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
  by_contra! h
  exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)

/-! ### Integrability of the curvature -/

omit [IsManifold I (⊤ : ℕ∞) M] in
include hHs in
/-- Along a map continuous on `S`, the end-coordinate curvature `±β'(±s - 1) H_q(t, u(φ_q(s, t)))`
is continuous on the part `±s > 0` of the end `q`. -/
private theorem continuousOn_endCurvature {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) (q : Puncture) :
    ContinuousOn (fun ζ ↦ q.endSign * deriv smoothTransition (q.endSign * ζ.1 - 1) *
      H q ζ.2 (u (endChart q ζ))) {ζ | 0 < q.endSign * ζ.1} := by
  have hβ' : Continuous fun ζ : ℝ × ℝ ↦ deriv smoothTransition (q.endSign * ζ.1 - 1) :=
    ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp (by fun_prop)
  have huφ : ContinuousOn (fun ζ ↦ u (endChart q ζ)) {ζ | 0 < q.endSign * ζ.1} :=
    hu.comp (contDiff_endChart q 0).continuous.continuousOn
      fun ζ hζ ↦ endChart_mem_thricePuncturedSphereReal hζ
  exact (continuous_const.mul hβ').continuousOn.mul
    ((hHs q).continuous.comp_continuousOn (continuous_snd.continuousOn.prodMk huφ))

include hH hHs in
/-- In the coordinates of an end, the curvature along a map continuous on `S`, multiplied by the
Jacobian determinant of the end chart, is integrable over every end piece. -/
private theorem integrableOn_endPiece_det_smul_hamiltonianCurvature (ω : SmoothTwoForm I M)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal) (q : Puncture) (R : ℝ) :
    IntegrableOn (fun ζ ↦ |(fderiv ℝ (endChart q) ζ).det| • ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (endChart q ζ) (u (endChart q ζ))) (endPiece q R) := by
  set U : Set (ℝ × ℝ) := {ζ | 0 < q.endSign * ζ.1}
  set P : Set (ℝ × ℝ) := {s | 1 ≤ q.endSign * s ∧ q.endSign * s ≤ R} ×ˢ Icc (-1 / 2) (1 / 2)
  -- The closure of the end piece is compact and lies in the part `±s > 0` of the end.
  have hPc : IsCompact P := by
    refine IsCompact.prod ?_ isCompact_Icc
    rcases endSign_eq_one_or_eq_neg_one q with h | h
    · rw [setOf_endSign_mul_eq_Icc_of_endSign_eq_one h]
      exact isCompact_Icc
    · rw [setOf_endSign_mul_eq_Icc_of_endSign_eq_neg_one h]
      exact isCompact_Icc
  have hPU : P ⊆ U := fun ζ hζ ↦ by
    have h : 1 ≤ q.endSign * ζ.1 := hζ.1.1
    exact (by linarith : 0 < q.endSign * ζ.1)
  -- There the integrand is the continuous function `±β'(±s - 1) H_q(t, u(φ_q(s, t)))`.
  have hcont := continuousOn_endCurvature hHs hu q
  refine (((hcont.mono hPU).integrableOn_compact hPc).mono_set fun ζ (hζ : ζ ∈ endPiece q R) ↦
    ⟨hζ.1, Ico_subset_Icc_self hζ.2⟩).congr_fun (fun ζ hζ ↦ ?_) (measurableSet_endPiece q R)
  have hζ' : 0 < q.endSign * ζ.1 := by
    have h : 1 ≤ q.endSign * ζ.1 := hζ.1.1
    linarith
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q ζ), smul_eq_mul,
    det_mul_hamiltonianCurvature_endChart hH hHs ω hζ']

include hH hHs in
/-- In the coordinates of an end, the curvature of the end components along `u ∘ φ_q`, for a map
`u` continuous on `S`, is integrable over every compact set of the part `±s > 0` of the end. -/
private theorem integrableOn_hamiltonianCurvature_pairOfPantsEndComponent (ω : SmoothTwoForm I M)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ {ζ | 0 < q.endSign * ζ.1}) :
    IntegrableOn (fun ζ ↦ ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) ζ ((u ∘ endChart q) ζ)) K :=
  (((continuousOn_endCurvature hHs hu q).mono hKU).integrableOn_compact hK).congr_fun
    (fun ζ hζ ↦ (ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) (hKU hζ)
      ((hHs q (ζ.2, u (endChart q ζ))).differentiableAt_curry_left one_ne_zero)).symm)
    hK.measurableSet

include hH hHs in
/-- In the coordinates of an end, the energy density of the end components along `u ∘ φ_q`, for a
map `u` which is `C¹` on `S`, is integrable over a measurable set of the part `±s > 0` of the end
on which `φ_q` is injective, as soon as the energy density along `u` is integrable over its
image. -/
private theorem integrableOn_floerEnergyDensity_pairOfPantsEndComponent (ω : SmoothTwoForm I M)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsU : s ⊆ {ζ | 0 < q.endSign * ζ.1})
    (hinj : InjOn (endChart q) s)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' s)) :
    IntegrableOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q)) s := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    hinj _).1 hE).congr_fun (fun ζ hζ ↦ ?_) hs
  -- In the cylinder coordinates the energy density is the Jacobian times the original one.
  have hS := endChart_mem_thricePuncturedSphereReal (hsU hζ)
  have hud : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q ζ) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt one_ne_zero
  dsimp only
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q ζ), smul_eq_mul,
    ← ω.floerEnergyDensity_perturbationPullback (hasFDerivAt_endChart q ζ).differentiableAt hud
      (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ 1)
      (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ Complex.I),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]

include hH hHs in
/-- Along a map continuous on `S`, the curvature of the pair-of-pants perturbation is integrable
over every truncation. -/
private theorem integrableOn_truncation_hamiltonianCurvature (ω : SmoothTwoForm I M)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal) (R : ℝ) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set A : Puncture → Set (ℝ × ℝ) := fun q ↦ endChart q '' endPiece q R
  have hTm : MeasurableSet T := (isCompact_preimage_truncation R).isClosed.measurableSet
  -- The truncation is covered by its core, where the curvature vanishes, and the end pieces.
  have hcover : T ⊆ (T \ ⋃ q, A q) ∪ ⋃ q, A q := fun z hz ↦ by
    by_cases h : z ∈ ⋃ q, A q
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩
  refine IntegrableOn.mono_set ?_ hcover
  refine (integrableOn_union.2 ⟨?_, integrableOn_finite_iUnion.2 fun q ↦ ?_⟩)
  · refine integrableOn_zero.congr_fun (fun z hz ↦ ?_)
      (hTm.diff (MeasurableSet.iUnion fun q ↦ measurableSet_image_endPiece q R))
    exact (hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω
      (preimage_truncation_subset R hz.1) (lt_one_of_mem_diff hz) _).symm
  · exact (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (measurableSet_endPiece q R)
      (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      ((injOn_endChart q).mono (endPiece_subset_endStrip q R)) _).2
      (integrableOn_endPiece_det_smul_hamiltonianCurvature hH hHs ω hu q R)

include hH hHs in
/-- **The curvature is integrable over the pair of pants.** Along a map `u` which is continuous on
`S`, the curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians is integrable
over `S`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation (ω : SmoothTwoForm I M)
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      thricePuncturedSphereReal := by
  -- Off the truncation `S_2` some signed longitudinal coordinate exceeds `2`, and the curvature
  -- vanishes there.
  refine (integrableOn_truncation_hamiltonianCurvature hH hHs ω hu 2).of_forall_sdiff_eq_zero
    isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦ ?_
  have hS := mem_thricePuncturedSphereReal_iff.1 hz.1
  obtain ⟨q, hq⟩ : ∃ q : Puncture,
      2 < q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
    by_contra! h
    exact hz.2 (mem_truncation.2 ⟨hS.1, hS.2, h⟩)
  exact hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs ω hz.1 hq _

/-! ### The energy identity on the truncated pair of pants -/

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

include hH hHs in
/-- **The energy identity over a rectangle of an end.** Over the image in `S` of a rectangle
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, the Floer energy is the
symplectic area, plus the integrals of the Hamiltonian term `β(±s - 1) H_q(t)` over the outgoing
boundary circle minus the incoming one, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_endChart
    (hω : ω.IsNondegenerate) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {a₁ b₁ : ℝ} (hab : a₁ ≤ b₁) (ha : 1 / 2 < q.endSign * a₁) (hb : 1 / 2 < q.endSign * b₁)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)))) :
    ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)),
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * b₁ - 1) * H q t (u (endChart q (b₁, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2,
            smoothTransition (q.endSign * a₁ - 1) * H q t (u (endChart q (a₁, t)))) -
        ∫ z in endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)), ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  set U : Set (ℝ × ℝ) := {z | 1 / 2 < q.endSign * z.1}
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  -- The rectangle lies in the part `±s > 1/2` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * z.1 := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz ↦ hU₁ (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  have hsU : s ⊆ U := fun z hz ↦ hIccU (by
    rw [Icc_prod_eq]
    exact ⟨hz.1, Ico_subset_Icc_self hz.2⟩)
  have hpos {z : ℝ × ℝ} (hz : z ∈ U) : 0 < q.endSign * z.1 := by
    have h : 1 / 2 < q.endSign * z.1 := hz
    linarith
  have hS {z : ℝ × ℝ} (hz : z ∈ U) := endChart_mem_thricePuncturedSphereReal (hpos hz)
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hinj : InjOn (endChart q) s :=
    (injOn_endChart q).mono fun z hz ↦ mem_endStrip_iff.2 ⟨hsU hz, hz.2⟩
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))).mdifferentiableAt
      one_ne_zero
  have hKd {w : ℝ × ℝ} (hw : w ∈ U) (v : ℂ) :=
    differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS hw) (u (endChart q w)) v
  have hKm {w : ℝ × ℝ} (hw : w ∈ U) (v : ℂ) :=
    mdifferentiableAt_pairOfPantsPerturbation_target hH hHs (hS hw) (u (endChart q w)) v
  -- Change variables to the cylinder coordinates of the end, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ ↦ hφ w) (fun w _ ↦ det_fderiv_endChart_nonneg q w)
    (fun w hw ↦ hud (hsU hw)) (fun _ _ ↦ mdifferentiableAt_const)
    (fun _ _ ↦ mdifferentiableAt_const)
  have h₀ (v : ℝ × ℝ) : perturbationPullback (endChart q) (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero, Function.comp_apply] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ ↦ hφ w)
      (fun w _ ↦ det_fderiv_endChart_nonneg q w) (fun w hw ↦ hud (hsU hw))
      (fun w hw ↦ hKm (hsU hw) 1) (fun w hw ↦ hKm (hsU hw) Complex.I),
    ω.integral_hamiltonianCurvature_image hmeas hinj
      (fun w _ ↦ (contDiff_endChart q 2).contDiffAt)
      (fun w _ ↦ det_fderiv_endChart_nonneg q w)
      (fun w hw ↦ hKd (hsU hw) 1) (fun w hw ↦ hKd (hsU hw) Complex.I)
      (fun w hw ↦ hKm (hsU hw) 1) (fun w hw ↦ hKm (hsU hw) Complex.I),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : s =ᵐ[volume] Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`, its curvature is
  -- `±β'(±s - 1) H_q(t)`, and the energy identity on the rectangle applies.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ endChart q) U :=
    hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn fun w hw ↦ hS hw
  have hUpos : U ×ˢ (univ : Set M) ⊆ {z : ℝ × ℝ | 0 < q.endSign * z.1} ×ˢ univ :=
    prod_mono (fun z hz ↦ hpos hz) subset_rfl
  have hE' := integrableOn_floerEnergyDensity_pairOfPantsEndComponent hH hHs ω hu hmeas
    (fun ζ hζ ↦ hpos (hsU hζ)) hinj hE
  have hrect := hω.integral_floerEnergyDensity hUo hu'
    ((contMDiffOn_pairOfPantsEndComponent hH hHs q 1).mono hUpos)
    ((contMDiffOn_pairOfPantsEndComponent hH hHs q Complex.I).mono hUpos)
    (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU (hE'.congr_set_ae hae.symm)
    (integrableOn_hamiltonianCurvature_pairOfPantsEndComponent hH hHs ω hu.continuousOn
      isCompact_Icc fun ζ hζ ↦ hpos (hIccU hζ))
  simp only [Function.comp_apply] at hrect
  rw [hrect]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c) (u (endChart q (s, c))) =
      0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0) fun s hs ↦ ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (hpos (hU₁ (z := (s, c)) hs)) _
  have ht {c : ℝ} (hc : 1 / 2 < q.endSign * c) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) (u (endChart q (c, t))) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ ↦
      pairOfPantsEndComponent_I_of_pos (hH q) (by linarith : 0 < q.endSign * c) _
  rw [hs₀, hs₀, ht ha, ht hb]
  ring

include hH hHs in
/-- **The energy identity on an end piece.** Over the end piece `1 ≤ ±s ≤ R` of the end `q`, the
Floer energy is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the
boundary circle `±s = R`, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_endPiece
    (hω : ω.IsNondegenerate) {u : ℝ × ℝ → M}
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
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        smoothTransition (R - 1) *
          (q.endSign * ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t)))) -
        ∫ z in endChart q '' endPiece q R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · rw [endPiece, setOf_endSign_mul_eq_Icc_of_endSign_eq_one h] at hE ⊢
    rw [hω.integral_floerEnergyDensity_image_endChart hH hHs hu hR (by rw [h]; norm_num)
      (by rw [h]; linarith) hE]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · rw [endPiece, setOf_endSign_mul_eq_Icc_of_endSign_eq_neg_one h] at hE ⊢
    rw [hω.integral_floerEnergyDensity_image_endChart hH hHs hu (by linarith)
      (by rw [h]; linarith) (by rw [h]; norm_num) hE]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]
    ring

include hH hHs in
/-- Along a map which is `C¹` on `S`, the symplectic area density is integrable over a
truncation as soon as the energy density is: they differ by the curvature and by the exterior
derivative of `K(u)`, which is continuous on `S`. -/
private theorem IsNondegenerate.integrableOn_truncation_area (hω : ω.IsNondegenerate)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ}
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    IntegrableOn (fun z ↦ SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  set S := thricePuncturedSphereReal
  have hSo : IsOpen S := isOpen_thricePuncturedSphereReal
  have hTS := preimage_truncation_subset R
  have hK (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (S ×ˢ univ) := fun p hp ↦
    (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hp.1 p.2 v).contMDiffWithinAt
  -- The components of `K(u)` are `C¹` functions on `S`, so `d(K(u))` is continuous there.
  have hKu (v : ℂ) : ContDiffOn ℝ 1
      (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v) S :=
    contMDiffOn_iff_contDiffOn.mp ((hK v).comp (contMDiffOn_id.prodMk hu)
      fun _ hz ↦ ⟨hz, mem_univ _⟩)
  have hdK : IntegrableOn (fun z ↦
      fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w)
        Complex.I) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) 1) z
        stdComplexLineImag) (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
    ((((hKu Complex.I).continuousOn_fderiv_of_isOpen hSo le_rfl).clm_apply
      continuousOn_const).sub (((hKu 1).continuousOn_fderiv_of_isOpen hSo le_rfl).clm_apply
        continuousOn_const)).mono hTS |>.integrableOn_compact (isCompact_preimage_truncation R)
  refine ((hE.sub hdK).add (integrableOn_truncation_hamiltonianCurvature hH hHs ω
    hu.continuousOn R)).congr_fun (fun z hz ↦ ?_)
      (isCompact_preimage_truncation R).isClosed.measurableSet
  have hzS := hTS hz
  have hz' : (z, u z) ∈ S ×ˢ (univ : Set M) := ⟨hzS, mem_univ _⟩
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hω.floerEnergyDensity_eq ((hu.contMDiffAt (hSo.mem_nhds hzS)).mdifferentiableAt one_ne_zero)
    (((hK 1).contMDiffAt ((hSo.prod isOpen_univ).mem_nhds hz')).mdifferentiableAt one_ne_zero)
    (((hK Complex.I).contMDiffAt ((hSo.prod isOpen_univ).mem_nhds hz')).mdifferentiableAt
      one_ne_zero)]
  ring

include hH hHs in
/-- **The energy identity on the truncated pair of pants.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on `ℝ × M`, for a nondegenerate two-form on
`M`, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate
`z = s + i t` of `ℂ`, and let `u` be a map which is `C¹` on `S`, whose energy density is integrable
over the truncation `S_R` of `S`, `R ≥ 1`. Then the Floer energy of `u` over `S_R` is its
symplectic area, plus `β(R - 1)` times the signed sum over the three ends of the integrals of
`H_q(t)` along the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    (hω : ω.IsNondegenerate) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 1 ≤ R)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set A : Puncture → Set (ℝ × ℝ) := fun q ↦ endChart q '' endPiece q R
  set C := T \ ⋃ q, A q
  have harea := hω.integrableOn_truncation_area hH hHs hu hE
  have hcurv := integrableOn_truncation_hamiltonianCurvature hH hHs ω hu.continuousOn R
  -- The truncation is the disjoint union of its core `C`, where every `±s < 1`, and the three
  -- end pieces.
  have hTm : MeasurableSet T := (isCompact_preimage_truncation R).isClosed.measurableSet
  have hAm (q : Puncture) : MeasurableSet (A q) := measurableSet_image_endPiece q R
  have hAT (q : Puncture) : A q ⊆ T := image_endPiece_subset q hR
  have hAd : Pairwise (Disjoint on A) := fun q r hqr ↦
    (pairwise_disjoint_image_endChart hqr).mono (image_mono (endPiece_subset_endStrip q R))
      (image_mono (endPiece_subset_endStrip r R))
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ q, ∫ z in A q, f z := by
    have hTC : T = C ∪ ⋃ q, A q := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun q ↦ hf.mono_set (hAT q)]
  -- On the core the perturbation vanishes, so the energy is the area and the curvature vanishes.
  have hCm : MeasurableSet C := hTm.diff (MeasurableSet.iUnion hAm)
  have hCE : ∫ z in C, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
    refine setIntegral_congr_fun hCm fun z hz ↦ ?_
    have hK : pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ ↦ 0 :=
      funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦ (lt_one_of_mem_diff hz q).le)
    simp [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
      perturbedMFDeriv_apply_stdComplexLineImag, hK, hamiltonianVectorField_const]
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦
      hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω (preimage_truncation_subset R hz.1)
        (lt_one_of_mem_diff hz) _
  -- The boundary circles: by periodicity, integrate over `[0, 1]` instead of `[-1/2, 1/2]`.
  have hcircle (q : Puncture) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2, H q t (u (endChart q (q.endSign * R, t))) =
        ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
    have hper : Periodic (fun t : ℝ ↦ H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) 1 := fun t ↦ by
      simp only [q.periodic_cylindricalEndLift (q.endSign * R) t, hH q t]
    have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
    norm_num at h
    simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
    convert h using 1 <;> norm_num
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE, hCR,
    Finset.sum_congr rfl fun q _ ↦ hω.integral_floerEnergyDensity_image_endPiece hH hHs hu hR q
      (hE.mono_set (hAT q)),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [hcircle]
  ring

/-! ### The energy identity on the whole pair of pants -/

/-- Integrals over `S` are the limits of the integrals over its truncations. -/
private theorem tendsto_setIntegral_truncation {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f thricePuncturedSphereReal) :
    Tendsto (fun R : ℝ ↦ ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z) atTop
      (𝓝 (∫ z in thricePuncturedSphereReal, f z)) := by
  have hU : ⋃ R : ℝ, Complex.equivRealProdCLM.symm ⁻¹' truncation R =
      thricePuncturedSphereReal := by
    rw [← preimage_iUnion, iUnion_truncation]
    rfl
  rw [← hU] at hf ⊢
  exact tendsto_setIntegral_of_monotone (fun R ↦
    (isCompact_preimage_truncation R).isClosed.measurableSet)
    (fun _ _ h ↦ preimage_mono (truncation_mono h)) hf

omit [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] in
include hHs in
/-- If the loops of `u` along the circles `±s = R` of the end `q` converge pointwise to a loop `x`
as `R → ∞`, then the integrals of a bounded continuous Hamiltonian along them converge to its
integral along `x`. -/
private theorem tendsto_intervalIntegral_endLoop {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture} {x : ℝ → M}
    (hx : ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x t))) :
    Tendsto (fun R : ℝ ↦ ∫ t in (0 : ℝ)..1, H q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, H q t (x t))) := by
  have hHc : Continuous (uncurry (H q)) := (hHs q).continuous
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B q) ?_
    (Eventually.of_forall fun R ↦ ae_of_all _ fun t _ ↦ (Real.norm_eq_abs _).trans_le (hB q _ _))
    intervalIntegrable_const
    (ae_of_all _ fun t _ ↦ (hHc.tendsto (t, x t)).comp (tendsto_const_nhds.prodMk_nhds (hx t)))
  -- For `R > 0` the circle `±s = R` lies in `S`, where `u` is continuous.
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hmem (t : ℝ) : Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)) ∈ thricePuncturedSphereReal := by
    rw [mem_thricePuncturedSphereReal_iff, ContinuousLinearEquiv.symm_apply_apply]
    refine cylindricalEndLift_ne_zero_and_ne_one q ?_
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> simp [h, hR]
  have hloop : Continuous fun t : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))) :=
    hu.comp_continuous (Complex.equivRealProdCLM.continuous.comp
      ((q.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))) hmem
  exact (hHc.comp (continuous_id.prodMk hloop)).aestronglyMeasurable

include hH hHs in
/-- **The energy identity on the pair of pants.** Let `K` be the pair-of-pants perturbation of
bounded period-one `C¹` Hamiltonians `H_q` on `ℝ × M`, for a nondegenerate two-form on `M`, with
components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of
`ℂ`. Let `u` be a map which is `C¹` on `S`, whose loops `t ↦ u(φ_q(±R + i t))` along the circles
of the end `q` converge pointwise to loops `x_q` as `R → ∞`, and whose Floer energy density and
symplectic area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. The middle term is the
boundary integral `∫_∂ K(u)` at the asymptotic orbits, and the curvature term is integrable
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation`). -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in thricePuncturedSphereReal,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- Both sides are the limits as `R → ∞` of the two sides of the identity on the truncation
  -- `S_R`, where the cutoff `β(R - 1)` of the boundary terms equals `1` once `R ≥ 2`.
  have hβ : Tendsto (fun R : ℝ ↦ smoothTransition (R - 1)) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [eventually_ge_atTop 2] with R hR
      exact (smoothTransition.one_of_one_le (by linarith)).symm
  have hrhs := ((tendsto_setIntegral_truncation hA).add (by
      simpa only [one_mul] using hβ.mul (tendsto_finsetSum Finset.univ fun q _ ↦
        (tendsto_intervalIntegral_endLoop hHs hB hu.continuousOn (hx q)).const_mul
          q.endSign))).sub
    (tendsto_setIntegral_truncation
      (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation hH hHs ω hu.continuousOn))
  refine tendsto_nhds_unique (tendsto_setIntegral_truncation hE) (hrhs.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact (hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hu hR
    (hE.mono_set (preimage_truncation_subset R))).symm

include hH hHs in
/-- **The energy bound on the pair of pants.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`, the Floer
energy over `S` differs from its topological part, the symplectic area plus the Hamiltonian terms
at the asymptotic orbits, by at most `B₀ + B₁ + B_∞`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le
    (hω : ω.IsNondegenerate) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) thricePuncturedSphereReal) :
    |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in thricePuncturedSphereReal,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation hH hHs hB hu hx hE hA, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le hH hHs ω hB u _

include hH hHs in
/-- **The topological energy of a pair-of-pants solution is bounded below.** Let `u` solve the
Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost complex structures `J z` on the tangent
spaces `T_{u(z)} M` tamed by `ω`, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`. Since its
energy is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic orbits is
at least `-(B₀ + B₁ + B_∞)`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap
    (hω : ω.IsNondegenerate) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) thricePuncturedSphereReal)
    {J : ∀ z : ℝ × ℝ, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -∑ q, B q ≤
      (∫ z in thricePuncturedSphereReal,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume)
    isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (hω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le hH hHs hB hu hx hE hA)
  linarith [h.2]

end SmoothTwoForm

end TauCeti
