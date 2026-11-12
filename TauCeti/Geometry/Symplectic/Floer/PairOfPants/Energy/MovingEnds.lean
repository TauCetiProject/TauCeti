/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The energy identity on spheres with moving input ends

The associativity of the pair-of-pants product compares the two broken products through a family
of four-punctured spheres whose inputs sit at moving punctures of `ℂ`, carrying the perturbation
datum `TauCeti.Floer.puncturedSpherePerturbation` of input ends with centers `c i`, scales `a i`
and Hamiltonians `H i`, and of an output end at `∞` with Hamiltonian `Hout`. Finiteness of the
counts below each energy level over that family needs the energy identity of its maps, with
bounds uniform in the configuration of the input ends. This file proves it for a manifold target.

Suppose the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise disjoint and lie in the disc
`‖w‖ ≤ 2 exp (2π)`, and the scales are nonzero. For `R ≥ 1` the truncation `Σ_R`
(`TauCeti.Floer.puncturedSphereTruncation`) cuts the sphere along the circle `s = R` of every input
end and the circle `s = -R` of the output end. For a map `u` which is `C¹` on an open set containing
`Σ_R`, into a finite-dimensional manifold with a nondegenerate two-form `ω`,

`∫_{Σ_R} E = ∫_{Σ_R} u^*ω + β(R - 1) (∑ i, ∫₀¹ H_i(t, u(φ_i(R + i t))) dt -`
`  ∫₀¹ Hout(t, u(φ_∞(-R + i t))) dt) - ∫_{Σ_R} R_K(u)`,

where `φ_i(z) = c i + a i φ₀(z)` is the end lift of the input `i`, `φ_∞` that of the output, and
`β = smoothTransition`, so `β(R - 1) = 1` for `R ≥ 2`. With `|H i| ≤ B i` and `|Hout| ≤ Bout`,
the energy therefore differs from its topological part by at most `∑ i, B i + Bout`, uniformly in
`R` and in the configuration.

The truncation is the disjoint union of the pieces `1 ≤ s ≤ R` of the input ends, the piece
`-R ≤ s ≤ -1` of the output end, and a core on which the datum vanishes nearby. In the coordinates
of each end the datum is the continuation datum `β(±s - 1) H(t) dt`, so each piece is handled by
one general statement,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback`: for a
datum whose pullback along an orientation-preserving `C²` chart `φ` is `P(s) H(t) dt`, the
energy over the image of a rectangle `[a₁, b₁] × [t₀, t₀ + 1)` is the area plus the boundary terms
`P(b₁) ∫ H(t, u(φ(b₁, t))) dt - P(a₁) ∫ H(t, u(φ(a₁, t))) dt` minus the integrated curvature.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback`,
  `integrableOn_hamiltonianCurvature_image_of_perturbationPullback`: the energy identity, and the
  integrability of the curvature, over the image of a rectangle of an end chart.
* `IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`: the energy
  identity on `Σ_R`.
* `IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`:
  the resulting energy bound, uniform in `R` and in the configuration.

In the namespace `TauCeti.Floer`:

* `puncturedSphereTruncation`: the truncation `Σ_R`, with `isCompact_puncturedSphereTruncation`;
  `add_mul_cylindricalEndLift_mem_puncturedSphereTruncation` and
  `cylindricalEndLift_inf_mem_puncturedSphereTruncation` place the end pieces in it.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for operations on punctured spheres.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 8–10, on
  families of punctured surfaces with cylindrical ends and consistent perturbation data over them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations on punctured surfaces.
-/

public section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]

section EndChart

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {φ : ℝ × ℝ → ℝ × ℝ} {P : ℝ → ℝ}
  {Hφ : ℝ → M → ℝ} {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}

/-- A datum `K` whose pullback along `φ` is `P(s) H(t) dt` on an open set `U` has, in the
coordinates of `φ`, the curvature `P'(s) H(t)` of a continuation datum on `U`. -/
theorem hamiltonianCurvature_perturbationPullback_eq_deriv_mul (ω : SmoothTwoForm I M)
    (hUo : IsOpen U)
    (hs : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineReal w = 0)
    (ht : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineImag w = fun x ↦ P w.1 * Hφ w.2 x)
    (hP : Differentiable ℝ P) (hH : ∀ x, Differentiable ℝ fun t ↦ Hφ t x) {w : ℝ × ℝ}
    (hw : w ∈ U) (x : M) :
    ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w x =
      deriv P w.1 * Hφ w.2 x := by
  have hev : ∀ᶠ w' in 𝓝 w, w' ∈ U := hUo.mem_nhds hw
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0)
    (Kt' := fun w y ↦ P w.1 * Hφ w.2 y) (hev.mono hs) (hev.mono ht)]
  exact ω.hamiltonianCurvature_continuation (hP _) (hH x _)

omit [IsManifold I ⊤ M] in
/-- A datum differentiable jointly at `(z, x)` is differentiable in the target point at `x`. -/
private theorem mdifferentiableAt_of_mdifferentiableAt_uncurry {K : ℝ × ℝ → M → ℝ} {z : ℝ × ℝ}
    {x : M} (hK : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry K) (z, x)) :
    MDifferentiableAt I 𝓘(ℝ) (K z) x :=
  hK.comp (f := fun y : M ↦ (z, y)) x (mdifferentiableAt_const.prodMk mdifferentiableAt_id)

omit [IsManifold I ⊤ M] in
/-- A datum differentiable jointly at `(z, x)` is differentiable in the domain point at `z`. -/
private theorem differentiableAt_of_mdifferentiableAt_uncurry {K : ℝ × ℝ → M → ℝ} {z : ℝ × ℝ}
    {x : M} (hK : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry K) (z, x)) :
    DifferentiableAt ℝ (fun z' ↦ K z' x) z :=
  (hK.comp (f := fun z' : ℝ × ℝ ↦ (z', x)) z
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt

/-- **The curvature over the image of a rectangle of an end chart is integrable.** Let `K` be a
datum whose pullback along a `C²` orientation-preserving chart `φ` is the continuation datum
`P(s) H(t) dt` on an open set `U` containing the strip `[a₁, b₁] × ℝ`, and let `u` be continuous
on a set containing `φ(U)`. Then the curvature `R_K(u)` is integrable over the image under `φ` of
the rectangle `[a₁, b₁] × [t₀, t₀ + 1)` on which `φ` is injective. -/
theorem integrableOn_hamiltonianCurvature_image_of_perturbationPullback (ω : SmoothTwoForm I M)
    {V : Set (ℝ × ℝ)} (hUo : IsOpen U) (hφ : ContDiff ℝ 2 φ)
    (hdet : ∀ w ∈ U, 0 ≤ (fderiv ℝ φ w).det) (hUV : MapsTo φ U V) (hu : ContinuousOn u V)
    (hKs : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Ks) (φ w, x))
    (hKt : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Kt) (φ w, x))
    (hs : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineReal w = 0)
    (ht : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineImag w = fun x ↦ P w.1 * Hφ w.2 x)
    (hP : ContDiff ℝ 1 P) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hφ))
    {a₁ b₁ t₀ : ℝ} (hstrip : ∀ z : ℝ × ℝ, z.1 ∈ Icc a₁ b₁ → z ∈ U)
    (hinj : InjOn φ (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1))) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z))
      (φ '' (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1))) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hmeas : MeasurableSet (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1)) :=
    measurableSet_Icc.prod measurableSet_Ico
  have hφd (w : ℝ × ℝ) : DifferentiableAt ℝ φ w := hφ.differentiable (by norm_num) w
  have hHt (x : M) : Differentiable ℝ fun t ↦ Hφ t x :=
    ((hH.comp (f := fun t : ℝ ↦ (t, x)) (contMDiff_id.prodMk contMDiff_const)).contDiff
      ).differentiable one_ne_zero
  -- In the coordinates of `φ` the curvature, times the Jacobian, is `P'(s) H(t, u ∘ φ)`, which is
  -- continuous on `U`.
  have hcont : ContinuousOn (fun w : ℝ × ℝ ↦ deriv P w.1 * Hφ w.2 (u (φ w))) U :=
    ((hP.continuous_deriv le_rfl).comp continuous_fst).continuousOn.mul
      (hH.continuous.comp_continuousOn (continuousOn_snd.prodMk
        (hu.comp hφ.continuous.continuousOn hUV)))
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas
    (fun w _ ↦ (hφd w).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine (((hcont.mono fun (w : ℝ × ℝ) (hw : w ∈ Icc a₁ b₁ ×ˢ Icc t₀ (t₀ + 1)) ↦
    hstrip w hw.1).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono subset_rfl Ico_subset_Icc_self)).congr_fun (fun w hw ↦ ?_) hmeas
  have hwU := hstrip w hw.1
  rw [abs_of_nonneg (hdet w hwU), smul_eq_mul, ← ω.hamiltonianCurvature_perturbationPullback
    hφ.contDiffAt (differentiableAt_of_mdifferentiableAt_uncurry (hKs w hwU _))
    (differentiableAt_of_mdifferentiableAt_uncurry (hKt w hwU _))
    (mdifferentiableAt_of_mdifferentiableAt_uncurry (hKs w hwU _))
    (mdifferentiableAt_of_mdifferentiableAt_uncurry (hKt w hwU _)),
    ω.hamiltonianCurvature_perturbationPullback_eq_deriv_mul hUo hs ht
      (hP.differentiable one_ne_zero) hHt hwU]

variable [FiniteDimensional ℝ E]

/-- **The energy identity over the image of a rectangle of an end chart, for a manifold target.**
Let `φ` be a `C²` orientation-preserving change of coordinates of the plane, and `K` a datum
whose pullback along `φ` is the continuation datum `P(s) H(t) dt` on an open set `U` containing
the strip `[a₁, b₁] × ℝ`, as on a cylindrical end of a punctured surface in the end coordinates.
Let `u` be `C¹` on an open set `V ⊇ φ(U)`, for a nondegenerate two-form on a finite-dimensional
manifold. Over the image under `φ` of the rectangle `[a₁, b₁] × [t₀, t₀ + 1)`, on which `φ` is
injective, the Floer energy is the symplectic area, plus the boundary term
`P(b₁) ∫ H(t, u(φ(b₁, t))) dt - P(a₁) ∫ H(t, u(φ(a₁, t))) dt` of the two boundary circles, minus
the integrated curvature. The densities are integrable automatically. -/
theorem IsNondegenerate.integral_floerEnergyDensity_image_of_perturbationPullback
    (hω : ω.IsNondegenerate) {V : Set (ℝ × ℝ)} (hUo : IsOpen U) (hVo : IsOpen V)
    (hφ : ContDiff ℝ 2 φ) (hdet : ∀ w ∈ U, 0 ≤ (fderiv ℝ φ w).det) (hUV : MapsTo φ U V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    (hKs : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Ks) (φ w, x))
    (hKt : ∀ w ∈ U, ∀ x, MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Kt) (φ w, x))
    (hs : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineReal w = 0)
    (ht : ∀ w ∈ U, perturbationPullback φ Ks Kt stdComplexLineImag w = fun x ↦ P w.1 * Hφ w.2 x)
    (hP : ContDiff ℝ 1 P) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hφ))
    {a₁ b₁ t₀ : ℝ} (hab : a₁ ≤ b₁) (hstrip : ∀ z : ℝ × ℝ, z.1 ∈ Icc a₁ b₁ → z ∈ U)
    (hinj : InjOn φ (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1))) :
    ∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1)), ω.floerEnergyDensity Ks Kt u z =
      (∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1)), (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (P b₁ * (∫ t in t₀..t₀ + 1, Hφ t (u (φ (b₁, t)))) -
          P a₁ * ∫ t in t₀..t₀ + 1, Hφ t (u (φ (a₁, t)))) -
        ∫ z in φ '' (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1)), ω.hamiltonianCurvature Ks Kt z (u z) := by
  set Ks' := perturbationPullback φ Ks Kt stdComplexLineReal
  set Kt' := perturbationPullback φ Ks Kt stdComplexLineImag
  have hmeas : MeasurableSet (Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1)) :=
    measurableSet_Icc.prod measurableSet_Ico
  have hφd (w : ℝ × ℝ) : DifferentiableAt ℝ φ w := hφ.differentiable (by norm_num) w
  have hud {w : ℝ × ℝ} (hw : w ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w) :=
    (hu.contMDiffAt (hVo.mem_nhds (hUV hw))).mdifferentiableAt one_ne_zero
  have hsU {w : ℝ × ℝ} (hw : w ∈ Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1)) : w ∈ U := hstrip w hw.1
  -- Change variables to the coordinates of `φ`, in each of the three integrals.
  rw [ω.integral_eval₂_mfderiv_stdComplexLine_image hmeas hinj (fun w _ ↦ hφd w)
      (fun w hw ↦ hdet w (hsU hw)) (fun w hw ↦ hud (hsU hw)),
    ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ ↦ hφd w)
      (fun w hw ↦ hdet w (hsU hw)) (fun w hw ↦ hud (hsU hw))
      (fun w hw ↦ mdifferentiableAt_of_mdifferentiableAt_uncurry (hKs w (hsU hw) _))
      (fun w hw ↦ mdifferentiableAt_of_mdifferentiableAt_uncurry (hKt w (hsU hw) _)),
    ω.integral_hamiltonianCurvature_image hmeas hinj (fun w _ ↦ hφ.contDiffAt)
      (fun w hw ↦ hdet w (hsU hw))
      (fun w hw ↦ differentiableAt_of_mdifferentiableAt_uncurry (hKs w (hsU hw) _))
      (fun w hw ↦ differentiableAt_of_mdifferentiableAt_uncurry (hKt w (hsU hw) _))
      (fun w hw ↦ mdifferentiableAt_of_mdifferentiableAt_uncurry (hKs w (hsU hw) _))
      (fun w hw ↦ mdifferentiableAt_of_mdifferentiableAt_uncurry (hKt w (hsU hw) _))]
  -- The half-open rectangle and the closed one differ by a null set.
  have hae : Icc a₁ b₁ ×ˢ Ico t₀ (t₀ + 1) =ᵐ[volume] Icc ((a₁, t₀) : ℝ × ℝ) (b₁, t₀ + 1) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  have hIccU : Icc ((a₁, t₀) : ℝ × ℝ) (b₁, t₀ + 1) ⊆ U := fun z hz ↦ hstrip z (by
    rw [Icc_prod_eq] at hz
    exact hz.1)
  -- In the coordinates of `φ` the datum is `P(s) H(t) dt`, and its curvature is `P'(s) H(t)`.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ φ) U :=
    hu.comp (hφ.of_le (by norm_num)).contMDiff.contMDiffOn hUV
  have hKs' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks') (U ×ˢ univ) :=
    (contMDiffOn_const (c := (0 : ℝ))).congr fun p hp ↦ congrFun (hs p.1 hp.1) p.2
  have hPH : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 fun p : (ℝ × ℝ) × M ↦
      P p.1.1 * Hφ p.1.2 p.2 :=
    ((hP.comp contDiff_fst).contMDiff.comp contMDiff_fst).smul
      (hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
  have hKt' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt') (U ×ˢ univ) :=
    hPH.contMDiffOn.congr fun p hp ↦ congrFun (ht p.1 hp.1) p.2
  have hHt (x : M) : Differentiable ℝ fun t ↦ Hφ t x :=
    ((hH.comp (f := fun t : ℝ ↦ (t, x)) (contMDiff_id.prodMk contMDiff_const)).contDiff
      ).differentiable one_ne_zero
  have hR : IntegrableOn (fun w ↦ ω.hamiltonianCurvature Ks' Kt' w ((u ∘ φ) w))
      (Icc ((a₁, t₀) : ℝ × ℝ) (b₁, t₀ + 1)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ((((hP.continuous_deriv le_rfl).comp continuous_fst).continuousOn.mul
      (hH.continuous.comp_continuousOn (continuousOn_snd.prodMk hu'.continuousOn))).mono
      hIccU).congr fun w hw ↦ ?_
    exact ω.hamiltonianCurvature_perturbationPullback_eq_deriv_mul hUo hs ht
      (hP.differentiable one_ne_zero) hHt (hIccU hw) _
  have hE := hω.integrableOn_floerEnergyDensity hUo hu' hKs' hKt' isCompact_Icc hIccU hR
  rw [hω.integral_floerEnergyDensity hUo hu' hKs' hKt' (Prod.mk_le_mk.2 ⟨hab, by linarith⟩) hIccU
    hE hR]
  -- The `ds` components vanish, and the `dt` components are `P(s) H(t)`.
  have hs₀ (c : ℝ) : ∫ s in a₁..b₁, Ks' (s, c) ((u ∘ φ) (s, c)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0) fun s hs' ↦ ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hab] at hs'
    exact congrFun (hs (s, c) (hstrip (s, c) hs')) _
  have ht₀ {c : ℝ} (hc : c ∈ Icc a₁ b₁) :
      ∫ t in t₀..t₀ + 1, Kt' (c, t) ((u ∘ φ) (c, t)) =
        P c * ∫ t in t₀..t₀ + 1, Hφ t (u (φ (c, t))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ ↦ congrFun (ht (c, t) (hstrip (c, t) hc)) _
  rw [hs₀, hs₀, ht₀ ⟨le_rfl, hab⟩, ht₀ ⟨hab, le_rfl⟩]
  simp only [Function.comp_apply, Ks', Kt']
  ring

end EndChart

end TauCeti.SmoothTwoForm

namespace TauCeti.Floer

section Truncation

variable {ι : Type*} {c a : ι → ℂ} {R : ℝ}

/-- **The truncation of a sphere with moving input ends.** For input ends with centers `c i` and
scales `a i`, the part of the plane cut off along the circle `s = R` of every input end and the
circle `s = -R` of the output end at `∞`: the points at distance at least `‖a i‖ exp (-2πR) / 2`
from every center `c i`, in the disc `‖w‖ ≤ 2 exp (2πR)`. -/
def puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) : Set ℂ :=
  {w | (∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖) ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R)}

/-- Membership in the truncation `Σ_R` of a sphere with moving input ends. -/
@[simp]
theorem mem_puncturedSphereTruncation {w : ℂ} :
    w ∈ puncturedSphereTruncation c a R ↔
      (∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖) ∧ ‖w‖ ≤ 2 * Real.exp (2 * π * R) :=
  Iff.rfl

/-- The truncation of a sphere with moving input ends is compact. -/
theorem isCompact_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (puncturedSphereTruncation c a R) := by
  refine (isCompact_closedBall (0 : ℂ) (2 * Real.exp (2 * π * R))).of_isClosed_subset ?_
    fun w hw ↦ by simpa using hw.2
  simp only [puncturedSphereTruncation, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- For nonzero scales, the truncation avoids the centers of the input ends. -/
theorem ne_of_mem_puncturedSphereTruncation {i : ι} (ha : a i ≠ 0) {w : ℂ}
    (hw : w ∈ puncturedSphereTruncation c a R) : w ≠ c i := by
  rintro rfl
  have h := hw.1 i
  have hpos : 0 < ‖a i‖ * Real.exp (-(2 * π * R)) / 2 := by
    have := norm_pos_iff.2 ha
    positivity
  rw [sub_self, norm_zero] at h
  linarith

/-- A point of the input end with center `c` and scale `a`, at longitudinal coordinate `s`, lies
at distance `‖a‖ exp (-2πs) / 2` from the center. -/
theorem norm_add_mul_cylindricalEndLift_sub (c a z : ℂ) :
    ‖c + a * zero.cylindricalEndLift z - c‖ = ‖a‖ * Real.exp (-(2 * π * z.re)) / 2 := by
  have h := norm_cylindricalEndLift_sub_endCenter zero z
  rw [endCenter_zero, sub_zero, endScale_zero] at h
  rw [add_sub_cancel_left, norm_mul, h]
  norm_num
  ring

/-- The part `1 ≤ s ≤ R` of an input end lies in the truncation `Σ_R`, at distance at most
`‖a i‖ exp (-2π) / 2` from the center of the end. -/
theorem add_mul_cylindricalEndLift_mem_puncturedSphereTruncation
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) (hR : 1 ≤ R) {i : ι} {z : ℂ}
    (h₁ : 1 ≤ z.re) (h₂ : z.re ≤ R) :
    c i + a i * zero.cylindricalEndLift z ∈ puncturedSphereTruncation c a R := by
  set w := c i + a i * zero.cylindricalEndLift z
  have hd := norm_add_mul_cylindricalEndLift_sub (c i) (a i) z
  have hπ := Real.pi_pos
  have hR₁ : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π * z.re)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hR₂ : Real.exp (-(2 * π * z.re)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hR₄ : Real.exp (2 * π) ≤ Real.exp (2 * π * R) := Real.exp_le_exp.2 (by nlinarith)
  have hai := norm_nonneg (a i)
  have hdi : ‖w - c i‖ ≤ ‖a i‖ / 2 := by rw [hd]; nlinarith
  refine ⟨fun j ↦ ?_, ?_⟩
  · rcases eq_or_ne j i with rfl | hji
    · rw [hd]
      gcongr
    · have h := hsep hji.symm
      have htri : ‖c i - c j‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
        simpa [norm_sub_rev] using norm_sub_le (c i - w) (c j - w)
      have : ‖a j‖ * Real.exp (-(2 * π * R)) ≤ ‖a j‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 (by nlinarith))
      linarith
  · have htri : ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by simpa using norm_add_le (c i) (w - c i)
    linarith [hout i]

/-- The part `-R ≤ s ≤ -1` of the output end lies in the truncation `Σ_R`, outside the open disc
`‖w‖ < 2 exp (2π)`. -/
theorem cylindricalEndLift_inf_mem_puncturedSphereTruncation
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {z : ℂ} (h₁ : -R ≤ z.re)
    (h₂ : z.re ≤ -1) :
    inf.cylindricalEndLift z ∈ puncturedSphereTruncation c a R := by
  have hd := norm_cylindricalEndLift_sub_endCenter inf z
  rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at hd
  have hπ := Real.pi_pos
  have hlow : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ :=
    two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1) (by linarith) |>.trans_eq' (by ring_nf)
  refine ⟨fun i ↦ ?_, ?_⟩
  · have htri : ‖inf.cylindricalEndLift z‖ ≤ ‖c i‖ + ‖inf.cylindricalEndLift z - c i‖ := by
      simpa using norm_add_le (c i) (inf.cylindricalEndLift z - c i)
    have : ‖a i‖ * Real.exp (-(2 * π * R)) ≤ ‖a i‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 (by nlinarith))
    linarith [hout i]
  · rw [hd]
    gcongr
    nlinarith

/-- A point at distance between `‖a‖ exp (-2πR) / 2` and `‖a‖ exp (-2π) / 2` from `c` is the image
of a point with `1 ≤ s ≤ R` and `t ∈ [-1/2, 1/2)` on the input end with center `c` and scale
`a`. -/
theorem exists_add_mul_cylindricalEndLift_eq {c a w : ℂ} (ha : a ≠ 0)
    (h₁ : ‖a‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c‖)
    (h₂ : ‖w - c‖ ≤ ‖a‖ * Real.exp (-(2 * π)) / 2) :
    ∃ z : ℂ, z.re ∈ Icc 1 R ∧ z.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      c + a * zero.cylindricalEndLift z = w := by
  have hapos := norm_pos_iff.2 ha
  set ζ := (w - c) / a
  have hζn : ‖ζ‖ = ‖w - c‖ / ‖a‖ := norm_div _ _
  have hζ : ζ ≠ zero.endCenter := by
    rw [endCenter_zero]
    intro h
    rw [h, norm_zero, eq_comm, div_eq_zero_iff] at hζn
    have : 0 < ‖a‖ * Real.exp (-(2 * π * R)) / 2 := by positivity
    rcases hζn with h | h <;> linarith
  refine ⟨zero.endCoord ζ, ⟨?_, ?_⟩, zero.im_endCoord_mem_Ico ζ, ?_⟩
  · refine le_re_endCoord_of_norm_sub_endCenter_le (by decide) hζ ?_
    rw [endCenter_zero, sub_zero, hζn, div_le_iff₀ hapos, mul_one]
    linarith
  · refine (re_endCoord_le_iff (by decide) hζ).2 ?_
    rw [endCenter_zero, sub_zero, hζn, le_div_iff₀ hapos]
    linarith
  · rw [cylindricalEndLift_endCoord zero hζ, mul_div_cancel₀ _ ha, add_sub_cancel]

/-- A point of the closed annulus `2 exp (2π) ≤ ‖w‖ ≤ 2 exp (2πR)` is the image of a point with
`-R ≤ s ≤ -1` and `t ∈ [-1/2, 1/2)` on the output end. -/
theorem exists_cylindricalEndLift_inf_eq (hR : 0 ≤ R) {w : ℂ}
    (h₁ : 2 * Real.exp (2 * π) ≤ ‖w‖) (h₂ : ‖w‖ ≤ 2 * Real.exp (2 * π * R)) :
    ∃ z : ℂ, z.re ∈ Icc (-R) (-1) ∧ z.im ∈ Ico (-1 / 2 : ℝ) (1 / 2) ∧
      inf.cylindricalEndLift z = w := by
  have hw : w ≠ inf.endCenter := by
    rw [endCenter_inf]
    rintro rfl
    rw [norm_zero] at h₁
    linarith [Real.exp_pos (2 * π)]
  refine ⟨inf.endCoord w, ⟨by linarith [neg_re_endCoord_inf_le hR h₂], ?_⟩,
    inf.im_endCoord_mem_Ico w, inf.cylindricalEndLift_endCoord hw⟩
  rw [re_endCoord, endCenter_inf, endScale_inf, sub_zero, norm_div, Complex.norm_ofNat,
    neg_div, neg_le_neg_iff, le_div_iff₀ Real.two_pi_pos, one_mul,
    Real.le_log_iff_exp_le (by linarith [Real.exp_pos (2 * π)]), le_div_iff₀ two_pos]
  linarith

/-- A point with `s > 0` on an input end is not the center of any input end. -/
theorem add_mul_cylindricalEndLift_ne
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖) {i : ι} (ha : a i ≠ 0)
    {z : ℂ} (hz : 0 < z.re) (j : ι) : c i + a i * zero.cylindricalEndLift z ≠ c j := by
  have hd := norm_add_mul_cylindricalEndLift_sub (c i) (a i) z
  have hapos := norm_pos_iff.2 ha
  have hlt : ‖a i‖ * Real.exp (-(2 * π * z.re)) / 2 < ‖a i‖ / 2 := by
    have : Real.exp (-(2 * π * z.re)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
    nlinarith
  intro h
  rcases eq_or_ne j i with rfl | hji
  · rw [h, sub_self, norm_zero] at hd
    have : 0 < ‖a j‖ * Real.exp (-(2 * π * z.re)) / 2 := by positivity
    linarith
  · rw [h] at hd
    have := hsep hji
    linarith [norm_nonneg (a j), norm_sub_rev (c j) (c i)]

end Truncation

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer
open TauCeti.Complex (realChart realChart_equivRealProdCLM equivRealProdCLM_symm_realChart
  contDiff_realChart det_fderiv_realChart_nonneg)

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- The end lift `z ↦ c + a φ₀(z)` of an input end, in real coordinates, is injective on every
horizontal strip of height one. -/
private theorem injOn_realChart_add_mul_cylindricalEndLift {c a : ℂ} (ha : a ≠ 0) {S : Set ℝ}
    {t₀ : ℝ} :
    InjOn (realChart fun z ↦ c + a * zero.cylindricalEndLift z) (S ×ˢ Ico t₀ (t₀ + 1)) := by
  intro p hp q hq hpq
  have h := congrArg Complex.equivRealProdCLM.symm hpq
  simp only [equivRealProdCLM_symm_realChart, add_right_inj, mul_right_inj' ha] at h
  exact Complex.equivRealProdCLM.symm.injective
    (zero.injOn_cylindricalEndLift t₀ (by simpa using hp.2) (by simpa using hq.2) h)

omit [IsManifold I ⊤ M] in
/-- Off the centers of the input ends, the components of the datum on a sphere with moving input
ends are `C¹` jointly in the domain point, in real coordinates, and the target point. -/
private theorem contMDiffAt_puncturedSpherePerturbation_real (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    {z : ℝ × ℝ} (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦
        puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x v) (z, x) := by
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I)
      (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 1
      (fun p : (ℝ × ℝ) × M ↦ ((c, a), (Complex.equivRealProdCLM.symm p.1, p.2))) (z, x) :=
    contMDiffAt_const.prodMk
      ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _
        contMDiffAt_fst).prodMk contMDiffAt_snd)
  exact ((contMDiffAt_puncturedSpherePerturbation hH hHs hHout hHouts ha hz x).comp (z, x)
    hφ).clm_apply contMDiffAt_const

/-- On a period of length one, the integral of a function of period one may be taken over
`[0, 1]`. -/
private theorem intervalIntegral_neg_half_eq {f : ℝ → ℝ} (hf : Periodic f 1) :
    ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, f t = ∫ t in (0 : ℝ)..1, f t := by
  simpa using hf.intervalIntegral_add_eq (-1 / 2) 0

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- The energy identity on the piece `1 ≤ s ≤ R`, `t ∈ [-1/2, 1/2)` of the input end `i` of a
sphere with moving input ends, in the coordinates of its end lift `z ↦ c i + a i φ₀(z)`, together
with the integrability of the curvature over that piece. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_inputPiece
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) (i : ι) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) ∧
    ∫ z in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
          (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
        ∫ z in realChart (fun z ↦ c i + a i * zero.cylindricalEndLift z) ''
        (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  classical
  set K := puncturedSpherePerturbation c a H Hout
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I
  have hK (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :=
    contMDiffAt_puncturedSpherePerturbation_real hH hHs hHout hHouts ha hz x v
  set Φ : ℝ × ℝ → ℝ × ℝ := realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  set Ri : Set (ℝ × ℝ) := Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)
  have hf (w : ℝ × ℝ) : HasDerivAt (fun z ↦ c i + a i * zero.cylindricalEndLift z)
      (a i * deriv zero.cylindricalEndLift (Complex.equivRealProdCLM.symm w))
      (Complex.equivRealProdCLM.symm w) :=
    ((zero.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt.const_mul (a i)).const_add
      (c i)
  have hΦ : ContDiff ℝ 2 Φ := contDiff_realChart (by fun_prop)
  have hΦinj : InjOn Φ Ri := injOn_realChart_add_mul_cylindricalEndLift (ha i)
  have hβ : ContDiff ℝ 1 fun s : ℝ ↦ smoothTransition (s - 1) :=
    smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  -- On the input end `i`, the datum is `β(s - 1) H i(t) dt` in the coordinates of `Φ`.
  have hpullIn {w : ℝ × ℝ} (hw : 0 < w.1) (v : ℝ × ℝ) (x : M) :
      perturbationPullback Φ Ks Kt v w x =
        (Complex.equivRealProdCLM.symm v).im * (smoothTransition (w.1 - 1) * H i w.2 x) := by
    rw [perturbationPullback_realChart K (hf w), mul_assoc,
      puncturedSpherePerturbation_cylindricalEndLift_of_pos hsep (fun i ↦ by
        linarith [hout i, norm_nonneg (a i)]) (hH i) (ha i) (by simpa using hw)]
    simp
  set U : Set (ℝ × ℝ) := {w | 1 / 2 < w.1 ∧ Φ w ∈ V}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter (hVo.preimage hΦ.continuous)
  have hne {w : ℝ × ℝ} (hw : w ∈ U) (j : ι) :
      Complex.equivRealProdCLM.symm (Φ w) ≠ c j := by
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_ne hsep (ha i) (by simp; linarith [hw.1]) j
  have hKs (w : ℝ × ℝ) (hw : w ∈ U) (x : M) :=
    (hK _ (hne hw) x 1).mdifferentiableAt one_ne_zero
  have hKt (w : ℝ × ℝ) (hw : w ∈ U) (x : M) :=
    (hK _ (hne hw) x Complex.I).mdifferentiableAt one_ne_zero
  have hs (w : ℝ × ℝ) (hw : w ∈ U) :
      perturbationPullback Φ Ks Kt stdComplexLineReal w = 0 :=
    funext fun x ↦ by
      rw [hpullIn (by linarith [hw.1])]
      simp
  have ht (w : ℝ × ℝ) (hw : w ∈ U) :
      perturbationPullback Φ Ks Kt stdComplexLineImag w =
        fun x ↦ smoothTransition (w.1 - 1) * H i w.2 x :=
    funext fun x ↦ by
      rw [hpullIn (by linarith [hw.1])]
      simp
  have hstrip (z : ℝ × ℝ) (hz : z.1 ∈ Icc 1 R) : z ∈ U := ⟨by linarith [hz.1], hTV (by
    refine mem_preimage.2 ?_
    rw [equivRealProdCLM_symm_realChart]
    exact add_mul_cylindricalEndLift_mem_puncturedSphereTruncation
      (z := Complex.equivRealProdCLM.symm z) hsep hout hR
      (by simpa using hz.1) (by simpa using hz.2))⟩
  refine ⟨ω.integrableOn_hamiltonianCurvature_image_of_perturbationPullback hUo hΦ
    (fun w _ ↦ det_fderiv_realChart_nonneg (hf w)) (fun w hw ↦ hw.2) hu.continuousOn
    hKs hKt hs ht hβ (hHs i) hstrip hΦinj, ?_⟩
  have h := hω.integral_floerEnergyDensity_image_of_perturbationPullback hUo hVo hΦ
    (fun w _ ↦ det_fderiv_realChart_nonneg (hf w)) (fun w hw ↦ hw.2) hu hKs hKt hs ht hβ
    (hHs i) hR hstrip hΦinj
  have hloop : ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, H i t (u (Φ (R, t))) =
      ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
        (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) := by
    simp only [Φ, TauCeti.Complex.realChart_apply, Complex.equivRealProdCLM_symm_apply]
    exact intervalIntegral_neg_half_eq fun t ↦ by
      simp only [zero.periodic_cylindricalEndLift R t, hH i t]
  rw [h, hloop, sub_self, smoothTransition.zero, zero_mul, sub_zero]

/-- The energy identity on the piece `-R ≤ s ≤ -1`, `t ∈ [-1/2, 1/2)` of the output end of a
sphere with moving input ends, in the coordinates of its end lift, together with the integrability
of the curvature over that piece. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_outputPiece
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1))) ∧
    ∫ z in endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
          (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)),
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z) := by
  classical
  set K := puncturedSpherePerturbation c a H Hout
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I
  have hπ := Real.pi_pos
  have hK (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :=
    contMDiffAt_puncturedSpherePerturbation_real hH hHs hHout hHouts ha hz x v
  set Ro : Set (ℝ × ℝ) := Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)
  have hβ' : ContDiff ℝ 1 fun s : ℝ ↦ smoothTransition (-s - 1) :=
    smoothTransition.contDiff.comp (contDiff_neg.sub contDiff_const)
  -- On the output end, the datum is `β(-s - 1) Hout(t) dt` in the coordinates of its end chart.
  have hcont : Continuous fun w : ℝ × ℝ ↦
      ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖ :=
    ((inf.contDiff_cylindricalEndLift 0).continuous.comp
      Complex.equivRealProdCLM.symm.continuous).norm
  set Uo : Set (ℝ × ℝ) := {w | (∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 <
    ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)‖) ∧ endChart inf w ∈ V}
  have hUoo : IsOpen Uo := by
    simp only [Uo, ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const hcont).inter
      (hVo.preimage (contDiff_endChart inf 0).continuous)
  have hpullOut {w : ℝ × ℝ} (hw : w ∈ Uo) (v : ℝ × ℝ) (x : M) :
      perturbationPullback (endChart inf) Ks Kt v w x =
        (Complex.equivRealProdCLM.symm v).im * (smoothTransition (-w.1 - 1) * Hout w.2 x) := by
    rw [perturbationPullback_endChart_eq_cylindricalEndLift K inf v]
    simp only [K]
    rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i ↦ ?_,
      negativePlanePerturbation_cylindricalEndLift_apply hHout]
    · simp
    · have h := hw.1 i
      have htri :=
        norm_sub_norm_le (inf.cylindricalEndLift (Complex.equivRealProdCLM.symm w)) (c i)
      linarith
  have hne {w : ℝ × ℝ} (hw : w ∈ Uo) (j : ι) :
      Complex.equivRealProdCLM.symm (endChart inf w) ≠ c j := by
    rw [equivRealProdCLM_symm_endChart]
    intro h
    have := hw.1 j
    rw [h] at this
    linarith [mul_nonneg (norm_nonneg (a j)) (Real.exp_pos (-(2 * π))).le]
  have hKs (w : ℝ × ℝ) (hw : w ∈ Uo) (x : M) :=
    (hK _ (hne hw) x 1).mdifferentiableAt one_ne_zero
  have hKt (w : ℝ × ℝ) (hw : w ∈ Uo) (x : M) :=
    (hK _ (hne hw) x Complex.I).mdifferentiableAt one_ne_zero
  have hs (w : ℝ × ℝ) (hw : w ∈ Uo) :
      perturbationPullback (endChart inf) Ks Kt stdComplexLineReal w = 0 :=
    funext fun x ↦ by
      rw [hpullOut hw]
      simp
  have ht (w : ℝ × ℝ) (hw : w ∈ Uo) :
      perturbationPullback (endChart inf) Ks Kt stdComplexLineImag w =
        fun x ↦ smoothTransition (-w.1 - 1) * Hout w.2 x :=
    funext fun x ↦ by
      rw [hpullOut hw]
      simp
  have hstrip (z : ℝ × ℝ) (hz : z.1 ∈ Icc (-R) (-1)) : z ∈ Uo := by
    refine ⟨fun i ↦ ?_, hTV (by
      refine mem_preimage.2 ?_
      rw [equivRealProdCLM_symm_endChart]
      exact cylindricalEndLift_inf_mem_puncturedSphereTruncation
        (z := Complex.equivRealProdCLM.symm z) hout (by simpa using hz.1)
        (by simpa using hz.2))⟩
    have h₁ : 2 * Real.exp (2 * π) ≤
        ‖inf.cylindricalEndLift (Complex.equivRealProdCLM.symm z)‖ := by
      simpa using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
        (z := Complex.equivRealProdCLM.symm z) (by simpa using hz.2)
    have h₂ : ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖a i‖ / 2 := by
      have := norm_pos_iff.2 (ha i)
      have : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      nlinarith
    linarith [hout i]
  have hinj : InjOn (endChart inf) Ro :=
    (injOn_endChart_univ_prod_Ico inf (-1 / 2)).mono (prod_mono (subset_univ _) subset_rfl)
  refine ⟨ω.integrableOn_hamiltonianCurvature_image_of_perturbationPullback hUoo
    (contDiff_endChart inf 2) (fun w _ ↦ det_fderiv_endChart_nonneg inf w) (fun w hw ↦ hw.2)
    hu.continuousOn hKs hKt hs ht hβ' hHouts hstrip hinj, ?_⟩
  have h := hω.integral_floerEnergyDensity_image_of_perturbationPullback hUoo hVo
    (contDiff_endChart inf 2) (fun w _ ↦ det_fderiv_endChart_nonneg inf w) (fun w hw ↦ hw.2)
    hu hKs hKt hs ht hβ' hHouts (by linarith) hstrip hinj
  have hloop : ∫ t in (-1 / 2 : ℝ)..-1 / 2 + 1, Hout t (u (endChart inf (-R, t))) =
      ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) := by
    simp only [endChart_apply, Complex.equivRealProdCLM_symm_apply]
    exact intervalIntegral_neg_half_eq fun t ↦ by
      simp only [inf.periodic_cylindricalEndLift (-R) t, hHout t]
  rw [h, hloop]
  simp only [neg_neg, sub_self, smoothTransition.zero, zero_mul, zero_sub]
  ring

/-- **The energy identity on the truncated sphere with moving input ends, for a manifold
target.** Let `K` be the datum `puncturedSpherePerturbation c a H Hout` of input ends with centers
`c i`, nonzero scales `a i` and period-one `C¹` Hamiltonians `H i` on a finite-dimensional
manifold with a nondegenerate two-form, and of the output end at `∞` with the period-one `C¹`
Hamiltonian `Hout`. Write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Suppose the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`, and let `u` be `C¹` on an open set `V` containing
the truncation `Σ_R`, `R ≥ 1`. Then the Floer energy over `Σ_R` is the symplectic area, plus
`β(R - 1)` times the integrals of the input Hamiltonians along the circles `s = R` of the input
ends minus that of the output Hamiltonian along the circle `s = -R` of the output end, minus the
integrated curvature. The densities are integrable over `Σ_R` automatically, and nothing is assumed
about `u` off `V`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  classical
  -- The truncation `T` is the disjoint union of the pieces `A o` of the ends, indexed by
  -- `o : Option ι` with `none` the output end, and of the core `C`. The energy identity holds on
  -- each piece by the piece lemmas, the datum vanishes near every point of the core, and the three
  -- integrals over `T` split accordingly.
  set K := puncturedSpherePerturbation c a H Hout
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  set Φ : ι → ℝ × ℝ → ℝ × ℝ := fun i ↦ realChart fun z ↦ c i + a i * zero.cylindricalEndLift z
  set Ri : Set (ℝ × ℝ) := Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)
  set Ro : Set (ℝ × ℝ) := Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (-1 / 2 + 1)
  set A : Option ι → Set (ℝ × ℝ) := fun o ↦ o.elim (endChart inf '' Ro) fun i ↦ Φ i '' Ri
  set C := T \ ⋃ o, A o
  have hπ := Real.pi_pos
  have hT : IsCompact T :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)
  have hTc {z : ℝ × ℝ} (hz : z ∈ T) (i : ι) : Complex.equivRealProdCLM.symm z ≠ c i :=
    ne_of_mem_puncturedSphereTruncation (ha i) hz
  have hK (z : ℝ × ℝ) (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠ c i) (x : M) (v : ℂ) :=
    contMDiffAt_puncturedSpherePerturbation_real hH hHs hHout hHouts ha hz x v
  have hΦ (i : ι) : ContDiff ℝ 2 (Φ i) := contDiff_realChart (by fun_prop)
  have hΦinj (i : ι) : InjOn (Φ i) Ri := injOn_realChart_add_mul_cylindricalEndLift (ha i)
  -- The energy identity and the integrability of the curvature on the pieces of the ends.
  have hEin (i : ι) :
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (A (some i)) ∧
      ∫ z in A (some i), ω.floerEnergyDensity Ks Kt u z =
        (∫ z in A (some i), (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ z in A (some i), ω.hamiltonianCurvature Ks Kt z (u z) :=
    hω.integral_floerEnergyDensity_puncturedSpherePerturbation_inputPiece hH hHs hHout hHouts ha
      hsep hout hVo hTV hu hR i
  have hEout :
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (A none) ∧
      ∫ z in A none, ω.floerEnergyDensity Ks Kt u z =
        (∫ z in A none, (SmoothBundleForm.eval₂ ω (u z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
          smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
          ∫ z in A none, ω.hamiltonianCurvature Ks Kt z (u z) :=
    hω.integral_floerEnergyDensity_puncturedSpherePerturbation_outputPiece hH hHs hHout hHouts ha
      hout hVo hTV hu hR
  -- The pieces lie in the truncation, are measurable, and are pairwise disjoint: the piece of the
  -- input end `i` lies in the disc `‖w - c i‖ ≤ ‖a i‖ exp (-2π) / 2`, and the piece of the output
  -- end off the disc `‖w‖ < 2 exp (2π)`.
  have hIco : Ico (-1 / 2 : ℝ) (-1 / 2 + 1) = Ico (-1 / 2) (1 / 2) := by norm_num
  have hAin (i : ι) {z : ℝ × ℝ} (hz : z ∈ A (some i)) :
      ‖Complex.equivRealProdCLM.symm z - c i‖ ≤ ‖a i‖ * Real.exp (-(2 * π)) / 2 := by
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [Φ, equivRealProdCLM_symm_realChart, norm_add_mul_cylindricalEndLift_sub]
    have h₁ : 1 ≤ (Complex.equivRealProdCLM.symm p).re := by simpa using hp.1.1
    have h₂ : Real.exp (-(2 * π * (Complex.equivRealProdCLM.symm p).re)) ≤
        Real.exp (-(2 * π)) := Real.exp_le_exp.2 (by nlinarith)
    nlinarith [norm_nonneg (a i)]
  have hAout {z : ℝ × ℝ} (hz : z ∈ A none) :
      2 * Real.exp (2 * π) ≤ ‖Complex.equivRealProdCLM.symm z‖ := by
    obtain ⟨p, hp, rfl⟩ := hz
    rw [equivRealProdCLM_symm_endChart]
    simpa using two_mul_exp_le_norm_cylindricalEndLift_inf (R := 1)
      (z := Complex.equivRealProdCLM.symm p) (by simpa using hp.1.2)
  have hAT (o : Option ι) : A o ⊆ T := by
    cases o with
    | none =>
      rintro _ ⟨p, hp, rfl⟩
      refine mem_preimage.2 ?_
      rw [equivRealProdCLM_symm_endChart]
      exact cylindricalEndLift_inf_mem_puncturedSphereTruncation hout (by simpa using hp.1.1)
        (by simpa using hp.1.2)
    | some i =>
      rintro _ ⟨p, hp, rfl⟩
      refine mem_preimage.2 ?_
      rw [equivRealProdCLM_symm_realChart]
      exact add_mul_cylindricalEndLift_mem_puncturedSphereTruncation hsep hout hR
        (by simpa using hp.1.1) (by simpa using hp.1.2)
  have hAm (o : Option ι) : MeasurableSet (A o) := by
    cases o with
    | none =>
      exact measurable_image_of_fderivWithin (measurableSet_Icc.prod measurableSet_Ico)
        (fun w _ ↦ (hasFDerivAt_endChart inf w).hasFDerivWithinAt)
        ((injOn_endChart_univ_prod_Ico inf (-1 / 2)).mono (prod_mono (subset_univ _) subset_rfl))
    | some i =>
      exact measurable_image_of_fderivWithin (measurableSet_Icc.prod measurableSet_Ico)
        (fun w _ ↦ ((hΦ i).differentiable (by norm_num) w).hasFDerivAt.hasFDerivWithinAt)
        (hΦinj i)
  have hr (i : ι) : ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖a i‖ / 2 := by
    have := norm_pos_iff.2 (ha i)
    have : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    nlinarith
  have hdisj {i : ι} {z : ℝ × ℝ} (hz : z ∈ A (some i)) (hz' : z ∈ A none) : False := by
    have htri : ‖Complex.equivRealProdCLM.symm z‖ ≤
        ‖c i‖ + ‖Complex.equivRealProdCLM.symm z - c i‖ := by
      simpa using norm_add_le (c i) (Complex.equivRealProdCLM.symm z - c i)
    linarith [hAin i hz, hAout hz', hr i, hout i]
  have hAd : Pairwise (Disjoint on A) := by
    intro o o' hoo'
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    cases o with
    | none =>
      cases o' with
      | none => exact hoo' rfl
      | some j => exact hdisj hz' hz
    | some i =>
      cases o' with
      | none => exact hdisj hz hz'
      | some j =>
        have hij : i ≠ j := fun h ↦ hoo' (h ▸ rfl)
        have htri := norm_sub_le_norm_sub_add_norm_sub (c i) (Complex.equivRealProdCLM.symm z)
          (c j)
        rw [norm_sub_rev (c i) (Complex.equivRealProdCLM.symm z)] at htri
        linarith [hAin i hz, hAin j hz', hr i, hr j, hsep hij]
  -- Off the pieces, the datum vanishes near every point of the truncation.
  set O : Set (ℝ × ℝ) := {z | (∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 <
    ‖Complex.equivRealProdCLM.symm z - c i‖) ∧ ‖Complex.equivRealProdCLM.symm z‖ <
      2 * Real.exp (2 * π)}
  have hOo : IsOpen O := by
    simp only [O, ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have hKO {z : ℝ × ℝ} (hz : z ∈ O) : K (Complex.equivRealProdCLM.symm z) = fun _ ↦ 0 :=
    funext fun x ↦ by
      simp only [K]
      rw [puncturedSpherePerturbation_eq_negativePlanePerturbation fun i ↦ (hz.1 i).le,
        negativePlanePerturbation_eq_zero_of_norm_le hz.2.le]
  have hCO {z : ℝ × ℝ} (hz : z ∈ C) : z ∈ O := by
    refine ⟨fun i ↦ ?_, ?_⟩
    · by_contra! h
      obtain ⟨ζ, hζre, hζim, hζ⟩ := exists_add_mul_cylindricalEndLift_eq (ha i) (hz.1.1 i) h
      refine hz.2 (mem_iUnion.2 ⟨some i, Complex.equivRealProdCLM ζ,
        ⟨by simpa using hζre, by rw [hIco]; simpa using hζim⟩, ?_⟩)
      simp only [Φ, realChart_equivRealProdCLM, hζ, ContinuousLinearEquiv.apply_symm_apply]
    · by_contra! h
      obtain ⟨ζ, hζre, hζim, hζ⟩ := exists_cylindricalEndLift_inf_eq (by linarith) h hz.1.2
      refine hz.2 (mem_iUnion.2 ⟨none, Complex.equivRealProdCLM ζ,
        ⟨by simpa using hζre, by rw [hIco]; simpa using hζim⟩, ?_⟩)
      simp only [endChart_apply, ContinuousLinearEquiv.symm_apply_apply, hζ,
        ContinuousLinearEquiv.apply_symm_apply]
  have hCm : MeasurableSet C := hT.isClosed.measurableSet.diff (MeasurableSet.iUnion hAm)
  have hCE : ∫ z in C, ω.floerEnergyDensity Ks Kt u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by
    refine setIntegral_congr_fun hCm fun z hz ↦ ?_
    have h := hKO (hCO hz)
    simp [Ks, Kt, floerEnergyDensity_def, h, hamiltonianVectorField_const]
  have hCR0 {z : ℝ × ℝ} (hz : z ∈ C) : ω.hamiltonianCurvature Ks Kt z (u z) = 0 := by
    have hev : ∀ᶠ w in 𝓝 z, w ∈ O := hOo.mem_nhds (hCO hz)
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0)
      (Kt' := fun _ _ ↦ 0) (hev.mono fun w hw ↦ funext fun x ↦ by simp [Ks, hKO hw])
      (hev.mono fun w hw ↦ funext fun x ↦ by simp [Kt, hKO hw]), hamiltonianCurvature_zero]
  -- The densities are integrable over the truncation.
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv hVo hu
    stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  replace harea := (harea.mono hTV).integrableOn_compact (μ := volume) hT
  have hcurv : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) T := by
    have hA (o : Option ι) :
        IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (A o) := by
      cases o with
      | none => exact hEout.1
      | some i => exact (hEin i).1
    refine ((integrableOn_zero.congr_fun (fun z hz ↦ (hCR0 hz).symm) hCm).union
      (integrableOn_finite_iUnion.2 hA)).mono_set fun z hz ↦ ?_
    by_cases h : z ∈ ⋃ o, A o
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩
  set P : Set (ℝ × ℝ) := {z | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  have hPo : IsOpen P := by
    simp only [P, ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (by fun_prop) continuous_const
  have hKP (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) ((V ∩ P) ×ˢ univ) :=
    fun p hp ↦ (hK p.1 hp.1.2 p.2 v).contMDiffWithinAt
  have hE := hω.integrableOn_floerEnergyDensity (hVo.inter hPo) (hu.mono inter_subset_left)
    (hKP 1) (hKP Complex.I) hT (subset_inter hTV fun z hz ↦ hTc hz) hcurv
  -- The truncation is the disjoint union of the core `C` and the pieces.
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ∑ o, ∫ z in A o, f z := by
    have hTC : T = C ∪ ⋃ o, A o := (sdiff_union_of_subset (iUnion_subset hAT)).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (MeasurableSet.iUnion hAm)
      (hf.mono_set sdiff_subset) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun o ↦ hf.mono_set (hAT o)]
  rw [hsplit _ hE, hsplit _ harea, hsplit _ hcurv, hCE,
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ hCR0 hz, Fintype.sum_option,
    Fintype.sum_option, Fintype.sum_option, hEout.2, Finset.sum_congr rfl fun i _ ↦ (hEin i).2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **The energy bound on the truncated sphere with moving input ends, for a manifold target.**
Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`,
if the Hamiltonians are bounded, `|H i| ≤ B i` and `|Hout| ≤ Bout`, then the Floer energy over the
truncation `Σ_R` differs from the symplectic area plus the Hamiltonian boundary terms by at most
`∑ i, B i + Bout`, uniformly in `R` and in the configuration of the input ends. -/
theorem
    IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M} {R : ℝ}
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) (hR : 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ i, B i + Bout := by
  have hsub (x y z : ℝ) : x + y - z - x - y = -z := by ring
  rw [hω.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout hHouts ha
    hsep hout hVo hTV hu hR, hsub, abs_neg]
  have hB₀ (i : ι) : 0 ≤ B i := (abs_nonneg _).trans (hB i 0 (u 0))
  have hBout₀ : 0 ≤ Bout := (abs_nonneg _).trans (hBout 0 (u 0))
  have hsum₀ : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ ↦ hB₀ i
  -- The supports of the input end data lie in the discs `‖w - c i‖ < ‖a i‖ / 2`.
  have hr (i : ι) : ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖a i‖ / 2 := by
    have : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [Real.pi_pos])
    nlinarith [norm_nonneg (a i)]
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg hsum₀ hBout₀), ← Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_add hsum₀ hBout₀, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hB₀ i]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
      (fun i j hij ↦ by linarith [hr i, hr j, hsep hij]) (fun i ↦ by linarith [hr i, hout i]) hB
      hBout u))

end TauCeti.SmoothTwoForm
