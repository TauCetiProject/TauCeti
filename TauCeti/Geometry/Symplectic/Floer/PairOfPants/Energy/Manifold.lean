/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.EndChart
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The energy identity of the pair of pants for manifold targets

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` built from
period-one Hamiltonians `H_q : ℝ → M → ℝ` on the three ends of the thrice-punctured sphere
`S = ℂ ∖ {0, 1}`, now with values in functions on a manifold `M` carrying a nondegenerate
two-form `ω`. Its components in the global coordinate `z = s + i t` of `S ⊆ ℂ` are
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. This file globalizes the rectangle identity
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity` to the truncations `S_R` of
`S` (`TauCeti.ThricePuncturedSphere.truncation`), on which every signed longitudinal coordinate
`±s` is at most `R`.

The perturbation vanishes off the parts `±s > 1` of the ends, and on the end `q` its pullback
along the end chart `φ_q` is `β(±s - 1) H_q(t) dt`, for the cutoff `β = smoothTransition`. Its
curvature `R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` is a two-form, so it is computed in end
coordinates, where it is the continuation curvature `±β'(±s - 1) H_q(t)`
(`SmoothTwoForm.hamiltonianCurvature_pairOfPantsEndComponent`). Since `∫ β' = 1`, if
`|H_q| ≤ B_q` then

`∫_S |R_K(z, u(z))| dz ≤ B₀ + B₁ + B_∞`

for every map `u : ℝ × ℝ → M`
(`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`).

Splitting `S_R` into its core, where `K` vanishes, and the three end pieces
(`TauCeti.Floer.endPiece`), and applying the rectangle identity in end coordinates on each piece,
gives for a map `u` which is `C¹` on `S` and `R ≥ 1`

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`),
with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`, and `β(R - 1) = 1`
for `R ≥ 2`. Here `E` is the Floer energy density `ω(∂_s u - X_{K_s}, ∂_t u - X_{K_t})` and
`u^*ω` is the symplectic area density `ω(∂_s u, ∂_t u)`, both evaluated in the actual tangent
spaces of `M`. The energy density is assumed integrable over `S_R`; the curvature term is
integrable because it is continuous on each end piece in end coordinates and vanishes on the core.
With the curvature bound, the energy over `S_R` differs from the area plus the Hamiltonian
boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R`.

Neither closedness of `ω` nor the Floer equation is used. The symplectic area is not expressed
through caps of the asymptotic orbits here; on a vector-space target, where every sphere has zero
area, the corresponding statements are in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature`.

## Main results

All results are in the namespace `TauCeti.SmoothTwoForm`.

* `hamiltonianCurvature_pairOfPantsEndComponent`: the curvature in end coordinates.
* `lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`,
  `abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le`: the integrated curvature along
  any map is at most the sum of bounds for the three end Hamiltonians.
* `integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation`: the curvature along a map
  continuous on `S` is integrable over every truncation.
* `IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`: the energy
  identity on the truncated pair of pants.
* `IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le`: the
  resulting energy bound, uniform in the truncation.

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

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M]
  {H : Puncture → ℝ → M → ℝ}

/-! ### Regularity of the perturbation in real coordinates -/

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- In real coordinates, the components of the perturbation are `C¹` jointly in the domain point
of `S` and the target point. -/
private theorem contMDiffAt_pairOfPantsPerturbation_real (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (z, x) := by
  have h := contMDiffAt_pairOfPantsPerturbation (n := 1) hH hHs ⟨_, hz⟩ x
  have hg : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) 1
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.comp contMDiff_fst).prodMk
      contMDiff_snd).contMDiffAt
  exact (h.comp (z, x) hg).clm_apply contMDiffAt_const

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- The components of the perturbation are differentiable in the domain point, at points of
`S`. -/
private theorem differentiableAt_pairOfPantsPerturbation_domain (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z') x v) z :=
  (((contMDiffAt_pairOfPantsPerturbation_real hH hHs hz x v).comp z
    (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).differentiableAt one_ne_zero

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- The components of the perturbation are differentiable in the target point, at points of
`S`. -/
private theorem mdifferentiableAt_pairOfPantsPerturbation_target (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y v) x :=
  ((contMDiffAt_pairOfPantsPerturbation_real hH hHs hz x v).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- A `C¹` Hamiltonian is differentiable in time. -/
private theorem differentiableAt_hamiltonian
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (q : Puncture) (t : ℝ)
    (x : M) : DifferentiableAt ℝ (fun t ↦ H q t x) t :=
  (((hHs q).contMDiffAt.comp t
    (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).differentiableAt one_ne_zero

/-! ### The curvature of the perturbation -/

/-- **The curvature on an end.** On the part `±s > 0` of the end `q`, the curvature of the
pair-of-pants perturbation in end coordinates is `±β'(±s - 1) H_q(t)`. -/
theorem hamiltonianCurvature_pairOfPantsEndComponent (ω : SmoothTwoForm I M) {q : Puncture}
    (hH : Periodic (H q) 1) {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) {x : M}
    (hHx : DifferentiableAt ℝ (fun t ↦ H q t x) z.2) :
    ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) z x =
      q.endSign * deriv smoothTransition (q.endSign * z.1 - 1) * H q z.2 x := by
  obtain ⟨hs, ht⟩ := eventuallyEq_pairOfPantsEndComponent hH hz
  have hβ : HasDerivAt (fun s ↦ smoothTransition (q.endSign * s - 1))
      (deriv smoothTransition (q.endSign * z.1 - 1) * q.endSign) z.1 :=
    (((hasDerivAt_id z.1).const_mul q.endSign).sub_const 1).smoothTransition.congr_deriv
      (by simp)
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht,
    ω.hamiltonianCurvature_continuation hβ.differentiableAt hHx, hβ.deriv]
  ring

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

/-- **The curvature in the coordinates of an end.** On the part `±s > 0` of the end `q`, the
Jacobian determinant of the end chart times the curvature at the image point is
`±β'(±s - 1) H_q(t)`: the curvature is a two-form. -/
private theorem det_mul_hamiltonianCurvature_endChart (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {q : Puncture} {w : ℝ × ℝ} (hw : 0 < q.endSign * w.1) (x : M) :
    (fderiv ℝ (endChart q) w).det * ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (endChart q w) x =
      q.endSign * deriv smoothTransition (q.endSign * w.1 - 1) * H q w.2 x := by
  have hS := endChart_mem_thricePuncturedSphereReal hw
  rw [← ω.hamiltonianCurvature_perturbationPullback ((contDiff_endChart q 2).contDiffAt)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS x 1)
    (differentiableAt_pairOfPantsPerturbation_domain hH hHs hS x Complex.I)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS x 1)
    (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS x Complex.I),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hw
      (differentiableAt_hamiltonian hHs q _ x)]

/-- **The integrated curvature of the pair-of-pants perturbation.** Let `K` be the pair-of-pants
perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, with
values in functions on a manifold `M` and with `|H_q| ≤ B_q`, and write its components in the
global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for
every map `u` into `M`, the integral of `|R_K(z, u(z))|` over the plane is at most
`B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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
  -- On the strip of the end `q` the curvature density in end coordinates is `±β' H_q`.
  have hend (q : Puncture) : ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)‖ₑ ≤ ENNReal.ofReal (B q) := by
    refine lintegral_image_endStrip_le fun z hz ↦ ?_
    have hψ : 0 ≤ deriv smoothTransition (q.endSign * z.1 - 1) :=
      smoothTransition.monotone.deriv_nonneg
    rw [← abs_of_nonneg (det_fderiv_endChart_nonneg q z), ← abs_mul,
      det_mul_hamiltonianCurvature_endChart ω hH hHs (endSign_mul_pos_of_mem_endStrip hz),
      abs_mul, abs_mul, abs_endSign, abs_of_nonneg hψ, one_mul]
    exact mul_le_mul_of_nonneg_left (hB q _ _) hψ
  calc _ = ∫⁻ z in (⋃ q, endChart q '' endStrip q) ∪ N, ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)‖ₑ := (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ = _ := tsum_fintype _
    _ ≤ _ := Finset.sum_le_sum fun q _ ↦ hend q

/-- The integral of the curvature of the pair-of-pants perturbation along any map into `M`, over
any set, has absolute value at most `B₀ + B₁ + B_∞` when `|H_q| ≤ B_q`. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
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

/-! ### The energy identity on the truncated pair of pants -/

/-- In end coordinates, the curvature of the perturbation along `u ∘ φ_q` is continuous on the
part `±s > 0` of the end, where it is `±β'(±s - 1) H_q(t, u(φ_q(s, t)))`. -/
private theorem continuousOn_hamiltonianCurvature_pairOfPantsEndComponent (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal) (q : Puncture) :
    ContinuousOn (fun w ↦ ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) w (u (endChart q w)))
      {w : ℝ × ℝ | 0 < q.endSign * w.1} := by
  have hloop : ContinuousOn (fun w : ℝ × ℝ ↦ (w.2, u (endChart q w)))
      {w : ℝ × ℝ | 0 < q.endSign * w.1} :=
    continuous_snd.continuousOn.prodMk (hu.comp (contDiff_endChart q 0).continuous.continuousOn
      fun _ hw ↦ endChart_mem_thricePuncturedSphereReal hw)
  have hβ : Continuous fun w : ℝ × ℝ ↦ deriv smoothTransition (q.endSign * w.1 - 1) :=
    ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp (by fun_prop)
  have hc : ContinuousOn (fun w : ℝ × ℝ ↦ q.endSign * deriv smoothTransition (q.endSign * w.1 - 1) *
      H q w.2 (u (endChart q w))) {w : ℝ × ℝ | 0 < q.endSign * w.1} :=
    (continuousOn_const.mul hβ.continuousOn).mul ((hHs q).continuous.comp_continuousOn hloop)
  refine hc.congr fun w hw ↦ ?_
  exact ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hw
    (differentiableAt_hamiltonian hHs q _ _)

/-- The curvature of the perturbation along a map continuous on `S` is integrable over the image
of a rectangle `[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`. -/
private theorem integrableOn_hamiltonianCurvature_image_endChart (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContinuousOn u thricePuncturedSphereReal)
    {q : Puncture} {a₁ b₁ : ℝ} (ha : 1 / 2 < q.endSign * a₁) (hb : 1 / 2 < q.endSign * b₁) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (endChart q '' (Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2))) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  have hpos {w : ℝ × ℝ} (hw : w.1 ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * w.1 := by
    obtain ⟨h₁, h₂⟩ := hw
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hsK : s ⊆ Icc (a₁, -1 / 2) (b₁, 1 / 2) := fun w hw ↦ by
    rw [Icc_prod_eq]
    exact ⟨hw.1, Ico_subset_Icc_self hw.2⟩
  have hKU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ {w : ℝ × ℝ | 0 < q.endSign * w.1} :=
    fun w hw ↦ by
      rw [Icc_prod_eq] at hw
      have := hpos hw.1
      simp only [mem_ofPred_eq]
      linarith
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_Icc.prod measurableSet_Ico)
    (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    ((injOn_endChart q).mono fun w (hw : w ∈ s) ↦ mem_endStrip_iff.2 ⟨hpos hw.1, hw.2⟩)]
  refine ((((continuousOn_hamiltonianCurvature_pairOfPantsEndComponent ω hH hHs hu q).mono
    hKU).integrableOn_compact isCompact_Icc).mono_set hsK).congr_fun (fun w hw ↦ ?_)
    (measurableSet_Icc.prod measurableSet_Ico)
  have hw' : 0 < q.endSign * w.1 := by linarith [hpos hw.1]
  dsimp only
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q w), smul_eq_mul,
    det_mul_hamiltonianCurvature_endChart ω hH hHs hw',
    ← ω.hamiltonianCurvature_pairOfPantsEndComponent (hH q) hw'
      (differentiableAt_hamiltonian hHs q _ _)]

/-- In end coordinates, the energy density of `u ∘ φ_q` for the components of the perturbation is
the Jacobian determinant of the end chart times the energy density of `u`. -/
private theorem floerEnergyDensity_pairOfPantsEndComponent (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {w : ℝ × ℝ} (hw : 0 < q.endSign * w.1) :
    ω.floerEnergyDensity (pairOfPantsEndComponent H q 1) (pairOfPantsEndComponent H q Complex.I)
        (u ∘ endChart q) w =
      (fderiv ℝ (endChart q) w).det * ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (endChart q w) := by
  have hS := endChart_mem_thricePuncturedSphereReal hw
  rw [← ω.floerEnergyDensity_perturbationPullback (hasFDerivAt_endChart q w).differentiableAt
      ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hS)).mdifferentiableAt
        one_ne_zero)
      (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ 1)
      (mdifferentiableAt_pairOfPantsPerturbation_target hH hHs hS _ _),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]

/-- **Change of variables to end coordinates.** Over the image of a measurable part `s` of the
strip of the end `q`, the energy, the symplectic area and the integrated curvature of `u` are those
of `u ∘ φ_q` for the components of the perturbation in end coordinates, over `s`. -/
private theorem integral_image_endChart (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsq : s ⊆ endStrip q) :
    (∫ z in endChart q '' s, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) =
      ∫ w in s, ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q) w ∧
    (∫ z in endChart q '' s,
        SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) =
      ∫ w in s, SmoothBundleForm.eval₂ ω (u (endChart q w))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ endChart q) w stdComplexLineImag) ∧
    (∫ z in endChart q '' s, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) =
      ∫ w in s, ω.hamiltonianCurvature (pairOfPantsEndComponent H q 1)
        (pairOfPantsEndComponent H q Complex.I) w (u (endChart q w)) := by
  have hinj : InjOn (endChart q) s := (injOn_endChart q).mono hsq
  have hS {w : ℝ × ℝ} (hw : w ∈ s) :=
    endChart_mem_thricePuncturedSphereReal (endSign_mul_pos_of_mem_endStrip (hsq hw))
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (endChart q) w :=
    (hasFDerivAt_endChart q w).differentiableAt
  have hud {w : ℝ × ℝ} (hw : w ∈ s) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (endChart q w) :=
    (hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds (hS hw))).mdifferentiableAt
      one_ne_zero
  have hKt {w : ℝ × ℝ} (hw : w ∈ s) (v : ℂ) := mdifferentiableAt_pairOfPantsPerturbation_target
    hH hHs (hS hw) (u (endChart q w)) v
  refine ⟨?_, ?_, ?_⟩
  · rw [ω.integral_floerEnergyDensity_image hs hinj (fun w _ => hφ w)
      (fun w _ => det_fderiv_endChart_nonneg q w) (fun w hw => hud hw)
      (fun w hw => hKt hw 1) (fun w hw => hKt hw _),
      perturbationPullback_endChart, perturbationPullback_endChart,
      equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
  · -- The area is the energy for the zero perturbation, whose pullback is again zero.
    have h₀ (v : ℝ × ℝ) : perturbationPullback (endChart q)
        (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ)) (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
      funext w x
      simp [perturbationPullback_apply]
    have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
      hs hinj (fun w _ => hφ w) (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => hud hw) (fun _ _ => mdifferentiableAt_const)
      (fun _ _ => mdifferentiableAt_const)
    simpa only [h₀, floerEnergyDensity_zero, Function.comp_apply] using harea
  · rw [ω.integral_hamiltonianCurvature_image hs hinj
      (fun w _ => (contDiff_endChart q 2).contDiffAt)
      (fun w _ => det_fderiv_endChart_nonneg q w)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS hw) _ 1)
      (fun w hw => differentiableAt_pairOfPantsPerturbation_domain hH hHs (hS hw) _ _)
      (fun w hw => hKt hw 1) (fun w hw => hKt hw _),
      perturbationPullback_endChart, perturbationPullback_endChart,
      equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]

/-- If the energy density of `u` is integrable over the image of a measurable part `s` of the strip
of the end `q`, then the energy density of `u ∘ φ_q` in end coordinates is integrable over `s`. -/
private theorem integrableOn_floerEnergyDensity_pairOfPantsEndComponent (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {q : Puncture} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) (hsq : s ⊆ endStrip q)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (endChart q '' s)) :
    IntegrableOn (ω.floerEnergyDensity (pairOfPantsEndComponent H q 1)
      (pairOfPantsEndComponent H q Complex.I) (u ∘ endChart q)) s := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    ((injOn_endChart q).mono hsq) _).1 hE).congr_fun (fun w hw ↦ ?_) hs
  dsimp only
  rw [abs_of_nonneg (det_fderiv_endChart_nonneg q w), smul_eq_mul,
    floerEnergyDensity_pairOfPantsEndComponent ω hH hHs hu
      (endSign_mul_pos_of_mem_endStrip (hsq hw))]

omit [IsManifold I (⊤ : ℕ∞) M] in
/-- On the part `±s > 0` of the end `q`, the components `0` and `β(±s - 1) H_q(t)` of the
perturbation in end coordinates are `C¹` jointly in the domain and target points. -/
private theorem contMDiffOn_pairOfPantsEndComponent (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) (q : Puncture) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (pairOfPantsEndComponent H q 1))
        ({w : ℝ × ℝ | 0 < q.endSign * w.1} ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (uncurry (pairOfPantsEndComponent H q Complex.I))
        ({w : ℝ × ℝ | 0 < q.endSign * w.1} ×ˢ univ) := by
  have hβ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) 1
      fun z : ℝ × ℝ => smoothTransition (q.endSign * z.1 - 1) :=
    (smoothTransition.contDiff.comp (by fun_prop)).contMDiff
  have hsnd : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) 1 (Prod.snd : ℝ × ℝ → ℝ) := contDiff_snd.contMDiff
  have hβH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1 fun p : (ℝ × ℝ) × M =>
      smoothTransition (q.endSign * p.1.1 - 1) * H q p.1.2 p.2 :=
    (hβ.comp contMDiff_fst).mul ((hHs q).comp ((hsnd.comp contMDiff_fst).prodMk contMDiff_snd))
  exact ⟨(contMDiffOn_const (c := (0 : ℝ))).congr fun p hp =>
      pairOfPantsEndComponent_one_of_pos (hH q) hp.1 p.2,
    hβH.contMDiffOn.congr fun p hp => pairOfPantsEndComponent_I_of_pos (hH q) hp.1 p.2⟩

/-- **The energy identity over a rectangle of an end.** Over the image in `S` of a rectangle
`[a₁, b₁] × [-1/2, 1/2)` of the part `±s > 1/2` of the end `q`, the Floer energy is the
symplectic area, plus the integrals of the Hamiltonian term `β(±s - 1) H_q(t)` over the outgoing
boundary circle minus the incoming one, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endChart [FiniteDimensional ℝ E]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
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
  set s : Set (ℝ × ℝ) := Icc a₁ b₁ ×ˢ Ico (-1 / 2) (1 / 2)
  set U : Set (ℝ × ℝ) := {z | 0 < q.endSign * z.1}
  -- The rectangle lies in the part `±s > 1/2` of the end.
  have hU₁ {z : ℝ × ℝ} (hz : z.1 ∈ Icc a₁ b₁) : 1 / 2 < q.endSign * z.1 := by
    obtain ⟨h₁, h₂⟩ := hz
    rcases endSign_eq_one_or_eq_neg_one q with h | h <;> rw [h] at ha hb ⊢ <;> linarith
  have hIccU : Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) ⊆ U := fun z hz => by
    rw [Icc_prod_eq] at hz
    have := hU₁ hz.1
    simp only [U, mem_ofPred_eq]
    linarith
  have hsq : s ⊆ endStrip q := fun z hz => mem_endStrip_iff.2 ⟨hU₁ hz.1, hz.2⟩
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  obtain ⟨hcE, hcA, hcR⟩ := integral_image_endChart ω hH hHs hu hmeas hsq
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : s =ᵐ[volume] Icc ((a₁, -1 / 2) : ℝ × ℝ) (b₁, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  rw [hcE, hcA, hcR]
  simp only [setIntegral_congr_set hae]
  -- In the cylinder coordinates the datum is `β(±s - 1) H_q(t) dt`: apply the energy identity on
  -- the rectangle.
  obtain ⟨hKs, hKt⟩ := contMDiffOn_pairOfPantsEndComponent hH hHs q
  have hrect := hω.integral_floerEnergyDensity
    (isOpen_lt continuous_const (continuous_const.mul continuous_fst))
    (hu.comp (contDiff_endChart q 1).contMDiff.contMDiffOn
      fun w hw => endChart_mem_thricePuncturedSphereReal hw) hKs hKt
    (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩) hIccU
    ((integrableOn_floerEnergyDensity_pairOfPantsEndComponent ω hH hHs hu hmeas hsq
      hE).congr_set_ae hae.symm)
    (((continuousOn_hamiltonianCurvature_pairOfPantsEndComponent ω hH hHs hu.continuousOn
      q).mono hIccU).integrableOn_compact isCompact_Icc)
  simp only [Function.comp_apply] at hrect ⊢
  rw [hrect]
  -- The `ds` components vanish, and the `dt` components are `β(±s - 1) H_q(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, pairOfPantsEndComponent H q 1 (s, c) (u (endChart q (s, c))) =
      0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun s hs => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs
    exact pairOfPantsEndComponent_one_of_pos (hH q) (by linarith [hU₁ (z := (s, c)) hs]) _
  have ht {c : ℝ} (hc : 1 / 2 < q.endSign * c) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2,
          pairOfPantsEndComponent H q Complex.I (c, t) (u (endChart q (c, t))) =
        ∫ t in (-1 / 2 : ℝ)..1 / 2,
          smoothTransition (q.endSign * c - 1) * H q t (u (endChart q (c, t))) :=
    intervalIntegral.integral_congr fun t _ =>
      pairOfPantsEndComponent_I_of_pos (hH q) (by linarith : 0 < q.endSign * c) _
  rw [hs₀, hs₀, ht ha, ht hb]
  ring

/-- For `R ≥ 1`, the end piece of the end `q` is a rectangle `[a, b] × [-1/2, 1/2)` in the part
`±s > 1/2` of the end. -/
private theorem exists_endPiece_eq {R : ℝ} (hR : 1 ≤ R) (q : Puncture) :
    ∃ a b : ℝ, 1 / 2 < q.endSign * a ∧ 1 / 2 < q.endSign * b ∧
      endPiece q R = Icc a b ×ˢ Ico (-1 / 2) (1 / 2) := by
  rcases endSign_eq_one_or_eq_neg_one q with h | h
  · refine ⟨1, R, by rw [h]; norm_num, by rw [h]; linarith, ?_⟩
    ext ⟨s, t⟩
    simp [endPiece_def, h]
  · refine ⟨-R, -1, by rw [h]; linarith, by rw [h]; norm_num, ?_⟩
    ext ⟨s, t⟩
    simp only [endPiece_def, h, mem_prod, mem_ofPred_eq, mem_Icc]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩

/-- **The energy identity on an end piece.** Over the end piece `1 ≤ ±s ≤ R` of the end `q`, the
Floer energy is the symplectic area, plus `±β(R - 1)` times the integral of `H_q(t)` over the
boundary circle `±s = R`, minus the integrated curvature. -/
private theorem integral_floerEnergyDensity_image_endPiece [FiniteDimensional ℝ E]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R) (q : Puncture)
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
  · have hpiece : endPiece q R = Icc 1 R ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp [endPiece_def, h]
    rw [hpiece] at hE ⊢
    rw [integral_floerEnergyDensity_image_endChart hω hH hHs hu hR
      (by rw [h]; norm_num) (by rw [h]; linarith) hE]
    simp only [h, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · have hpiece : endPiece q R = Icc (-R) (-1) ×ˢ Ico (-1 / 2) (1 / 2) := by
      ext ⟨s, t⟩
      simp only [endPiece_def, h, mem_prod, mem_ofPred_eq, mem_Icc]
      constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
    rw [hpiece] at hE ⊢
    rw [integral_floerEnergyDensity_image_endChart hω hH hHs hu (by linarith)
      (by rw [h]; linarith) (by rw [h]; norm_num) hE]
    simp only [h, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]
    ring

/-- At a point of the truncation `S_R` outside the three end pieces, every signed longitudinal
coordinate is less than `1`. -/
private theorem endSign_mul_re_endCoord_lt_one {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R)
    (q : Puncture) : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < 1 := by
  by_contra! h
  exact hz.2 (mem_iUnion.2 ⟨q, mem_image_endPiece hz.1 h⟩)

/-- The truncation `S_R`, in real coordinates, is a compact part of `S`. -/
private theorem isCompact_preimage_truncation (R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)

private theorem preimage_truncation_subset (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ thricePuncturedSphereReal := fun _ hz =>
  mem_thricePuncturedSphereReal_iff.2 ⟨(mem_truncation.1 hz).1, (mem_truncation.1 hz).2.1⟩

/-- **The curvature is integrable over the truncations.** Along a map continuous on `S`, the
curvature of the pair-of-pants perturbation of period-one `C¹` Hamiltonians is integrable over
every truncation `S_R`. No bound on the Hamiltonians is needed: the curvature is continuous on
each end piece in end coordinates and vanishes on the rest of `S_R`. -/
theorem integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u thricePuncturedSphereReal) (R : ℝ) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  -- It suffices to treat `R ≥ 1`, since the truncations increase with `R`.
  refine IntegrableOn.mono_set ?_ (preimage_mono (truncation_mono (le_max_left R 1)))
  set R' := max R 1
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R'
  set A : Puncture → Set (ℝ × ℝ) := fun q => endChart q '' endPiece q R'
  have hCm : MeasurableSet (T \ ⋃ q, A q) :=
    (isCompact_preimage_truncation R').isClosed.measurableSet.diff
      (MeasurableSet.iUnion fun q => measurableSet_image_endPiece q R')
  refine IntegrableOn.mono_set (t := (T \ ⋃ q, A q) ∪ ⋃ q, A q) ?_ fun z hz => ?_
  · refine IntegrableOn.union ?_ (integrableOn_finite_iUnion.2 fun q => ?_)
    · -- On the core the curvature vanishes.
      refine integrableOn_zero.congr_fun (fun z hz => ?_) hCm
      exact (hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω
        (preimage_truncation_subset R' hz.1) (endSign_mul_re_endCoord_lt_one hz) _).symm
    · obtain ⟨a, b, ha, hb, he⟩ := exists_endPiece_eq (R := R') (le_max_right R 1) q
      simp only [A]
      rw [he]
      exact integrableOn_hamiltonianCurvature_image_endChart ω hH hHs hu ha hb
  · by_cases h : z ∈ ⋃ q, A q
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩

/-- For `R ≥ 1`, an integral over the truncation `S_R` splits into the integral over its core,
where every signed longitudinal coordinate is less than `1`, and the integrals over the three end
pieces. -/
private theorem integral_preimage_truncation_eq {R : ℝ} (hR : 1 ≤ R) {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, f z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R,
        f z) + ∑ q, ∫ z in endChart q '' endPiece q R, f z := by
  have hAm (q : Puncture) := measurableSet_image_endPiece q R
  have hAT (q : Puncture) := image_endPiece_subset_truncation q hR
  conv_lhs => rw [(sdiff_union_of_subset (iUnion_subset hAT)).symm]
  rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
    (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
    integral_iUnion_fintype hAm (fun q r hqr => disjoint_image_endPiece hqr)
      fun q => hf.mono_set (hAT q)]

/-- On the core of the truncation `S_R`, where the perturbation vanishes, the energy of `u` is its
symplectic area and its integrated curvature vanishes. -/
private theorem setIntegral_core (ω : SmoothTwoForm I M) (u : ℝ × ℝ → M) (R : ℝ) :
    (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R,
        ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R,
        SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) ∧
    (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R,
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) = 0 := by
  have hCm : MeasurableSet
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R \ ⋃ q, endChart q '' endPiece q R) :=
    (isCompact_preimage_truncation R).isClosed.measurableSet.diff
      (MeasurableSet.iUnion fun q => measurableSet_image_endPiece q R)
  refine ⟨setIntegral_congr_fun hCm fun z hz => ?_,
    setIntegral_eq_zero_of_forall_eq_zero fun z hz =>
      hamiltonianCurvature_pairOfPantsPerturbation_eq_zero ω (preimage_truncation_subset R hz.1)
        (endSign_mul_re_endCoord_lt_one hz) _⟩
  have hK0 : pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) = fun _ => 0 :=
    funext (pairOfPantsPerturbation_eq_zero_of_forall_le fun q ↦
      (endSign_mul_re_endCoord_lt_one hz q).le)
  simp [floerEnergyDensity_def, hK0]

/-- **The area is integrable over the truncations.** If the energy density of a map `u` which is
`C¹` on `S` is integrable over `S_R`, then so is its symplectic area density: the two differ by the
curvature, which is integrable, and the exterior derivative of `K(u)`, which is continuous on
`S`. -/
private theorem integrableOn_area_truncation [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ}
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    IntegrableOn (fun z ↦ SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag))
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  have hTS := preimage_truncation_subset R
  -- The components `K_s(u)` and `K_t(u)` of the pulled-back one-form are `C¹` on `S`.
  have hK (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := fun p hp =>
    (contMDiffAt_pairOfPantsPerturbation_real hH hHs hp.1 p.2 v).contMDiffWithinAt
  have hKu (v : ℂ) : ContDiffOn ℝ 1
      (fun w ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm w) (u w) v)
      thricePuncturedSphereReal :=
    contMDiffOn_iff_contDiffOn.mp ((hK v).comp (contMDiffOn_id.prodMk hu)
      fun _ hz ↦ ⟨hz, mem_univ _⟩)
  have hdK (v : ℂ) (e : ℝ × ℝ) := ((hKu v).continuousOn_fderiv_of_isOpen
    isOpen_thricePuncturedSphereReal le_rfl).clm_apply (continuousOn_const (c := e))
  have hd := (((hdK Complex.I stdComplexLineReal).sub (hdK 1 stdComplexLineImag)).mono
    hTS).integrableOn_compact (μ := volume) (isCompact_preimage_truncation R)
  refine ((hE.sub hd).add (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation
    ω hH hHs hu.continuousOn R)).congr_fun (fun z hz => ?_)
    (isCompact_preimage_truncation R).isClosed.measurableSet
  have hz' := hTS hz
  simp only [Pi.add_apply, Pi.sub_apply, hω.floerEnergyDensity_eq
    ((hu.contMDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz')).mdifferentiableAt
      one_ne_zero)
    ((contMDiffAt_pairOfPantsPerturbation_real hH hHs hz' _ 1).mdifferentiableAt one_ne_zero)
    ((contMDiffAt_pairOfPantsPerturbation_real hH hHs hz' _ _).mdifferentiableAt one_ne_zero)]
  ring

omit [TopologicalSpace M] [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M] in
/-- By periodicity, the integral of `H_q` along the circle `±s = R` of the end `q` may be taken over
`[0, 1]` instead of `[-1/2, 1/2]`. -/
private theorem intervalIntegral_endCircle (hH : ∀ q, Periodic (H q) 1) (u : ℝ × ℝ → M)
    (q : Puncture) (R : ℝ) :
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

/-- **The energy identity on the truncated pair of pants, for a manifold target.** Let `K` be the
pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` on the three ends of
`S = ℂ ∖ {0, 1}`, with values in functions on a manifold `M` with a nondegenerate two-form `ω`,
and with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate
`z = s + i t` of `ℂ`. Let `u : ℝ × ℝ → M` be `C¹` on `S`, with Floer energy density integrable over
the truncation `S_R`, for some `R ≥ 1`. Then over `S_R` the Floer energy of `u` is its symplectic
area, plus `β(R - 1)` times the signed sum over the three ends of the integrals of `H_q(t)` along
the boundary circles `±s = R`, minus the integrated curvature:

`∫_{S_R} E = ∫_{S_R} u^*ω + β(R - 1) ∑ q, ±∫₀¹ H_q(t, u(φ_q(±R + i t))) dt - ∫_{S_R} R_K(u)`.

Here `φ_q` is the end lift of `q`, the sign is `+` on the input ends `0` and `1` and `-` on the
output end `∞`, and `β = smoothTransition` is the cutoff of the perturbation, so `β(R - 1) = 1`
for `R ≥ 2`. The area and curvature terms are integrable over `S_R`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation
    [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R)
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
  -- Split `S_R` into its core, where the energy is the area and the curvature vanishes, and the
  -- three end pieces, on each of which the identity holds in end coordinates.
  obtain ⟨hCE, hCR⟩ := setIntegral_core (H := H) ω u R
  rw [integral_preimage_truncation_eq hR hE,
    integral_preimage_truncation_eq hR (integrableOn_area_truncation hω hH hHs hu hE),
    integral_preimage_truncation_eq hR
      (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation ω hH hHs
        hu.continuousOn R),
    hCE, hCR, Finset.sum_congr rfl fun q _ => integral_floerEnergyDensity_image_endPiece hω hH hHs
      hu hR q (hE.mono_set (image_endPiece_subset_truncation q hR)),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [intervalIntegral_endCircle hH u]
  ring

/-- **The energy bound on the truncated pair of pants, for a manifold target.** If the end
Hamiltonians are bounded, `|H_q| ≤ B_q`, then under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation` the
Floer energy over the truncation `S_R` differs from the symplectic area plus the Hamiltonian
boundary terms by at most `B₀ + B₁ + B_∞`, uniformly in `R ≥ 1`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_le
    [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {R : ℝ} (hR : 1 ≤ R)
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R)) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)) -
        smoothTransition (R - 1) * (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))))| ≤ ∑ q, B q := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs hu hR hE, hsub,
    abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

end SmoothTwoForm

end TauCeti
