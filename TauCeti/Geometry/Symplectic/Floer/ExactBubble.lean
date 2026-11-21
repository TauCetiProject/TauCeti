/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Symplectic.TameMetric

/-!
# No disc or sphere bubbles in an exact symplectic manifold

Let `ω = dα` be a nondegenerate exact two-form on a manifold `M`, such as the symplectic form of a
Liouville domain or of its completion. This file shows that a pseudoholomorphic disc in `M` is
constant as soon as its boundary lies on an exact Lagrangian, and that a pseudoholomorphic sphere
in `M` is constant. These are the bubbles that can appear in the
compactness theory of Floer strips between exact Lagrangians: their absence is why the Floer
differential of an exact pair is defined without further assumptions.

Discs are maps `u : ℝ × ℝ → M` of the plane, considered on the closed unit disc
`{z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}`, which solve the Cauchy–Riemann equation `∂_t u = J ∂_s u` on the
open unit disc for almost complex structures `J z` on `T_{u z} M` tamed by `ω`. Their boundary loop
is `t ↦ u (cos 2πt, sin 2πt)`.

* **Area is the boundary integral.** Every `C²` map `u` of the plane gives a cap of its boundary
  loop by polar coordinates, `(s, t) ↦ u ((1 - s) cos 2πt, (1 - s) sin 2πt)`
  (`TauCeti.isLoopCylinder_comp_polar`), so by Stokes' formula the symplectic area of the disc is
  the line integral of `α` along the boundary loop.
* **Positivity.** In polar coordinates the area density of a pseudoholomorphic disc is
  `r ω(∂_r u, J ∂_r u)`, which is nonnegative by tameness; so the line integral of `α` along the
  boundary loop of a pseudoholomorphic disc is nonnegative
  (`TauCeti.SmoothTwoForm.IsNondegenerate.pathIntegral_disc_boundary_nonneg`), and it vanishes
  only if the disc is constant
  (`TauCeti.SmoothTwoForm.IsNondegenerate.apply_eq_apply_zero_of_pathIntegral_eq_zero`).
* **Discs on exact Lagrangians.** If the boundary loop is `i ∘ c` for a closed `C¹` curve `c` in a
  manifold `N` and a map `i : N → M` with `i^* α = df`, for instance an exact Lagrangian map, the
  line integral of `α` along the boundary is `f (c 1) - f (c 0) = 0`. Hence the disc is constant
  (`TauCeti.SmoothTwoForm.IsNondegenerate.apply_eq_apply_zero_of_boundary_exact`). The lift `c`
  must be closed: discs on an immersed exact Lagrangian whose boundary switches branches at a
  self-intersection need not be constant.
* **Spheres.** A pseudoholomorphic sphere is presented by two pseudoholomorphic discs `u₁` and
  `u₂`, its restrictions to the two hemispheres in the charts `z` and `1 / z`, whose boundary
  loops agree with opposite orientations: `u₂ (cos 2πt, sin 2πt) = u₁ (cos 2πt, -sin 2πt)`. The two
  boundary integrals are then opposite and both nonnegative, so both vanish and both discs are
  constant with the same value
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_forall_eq_of_disc_pair`).

## References

* A. Floer, *Morse theory for Lagrangian intersections*, J. Differential Geom. **28** (1988),
  513–547 (the exclusion of disc and sphere bubbles by the vanishing of symplectic area).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Lemma 2.2.1 (energy and area of `J`-holomorphic curves).
* D. Auroux, *A beginner's introduction to Fukaya categories*, arXiv:1301.7056, §1.2 (exact
  Lagrangians in exact symplectic manifolds bound no nonconstant discs).
-/

public noncomputable section

open Set MeasureTheory Function Filter Real
open scoped Manifold Interval Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The polar cap of a disc -/

/-- The polar parametrization of the closed unit disc by the unit square: `(s, t)` goes to the point
of radius `1 - s` and angle `2πt`. -/
private def polarCap (z : ℝ × ℝ) : ℝ × ℝ :=
  polarCoord.symm (1 - z.1, 2 * π * z.2)

private theorem polarCap_apply (z : ℝ × ℝ) :
    polarCap z = ((1 - z.1) * cos (2 * π * z.2), (1 - z.1) * sin (2 * π * z.2)) :=
  polarCoord_symm_apply _

/-- The polar parametrization is the polar cap of the identity map of the plane; its smoothness and
periodicity are read off from `TauCeti.isLoopCylinder_comp_polar`. -/
private theorem isLoopCylinder_polarCap :
    IsLoopCylinder 𝓘(ℝ, ℝ × ℝ) polarCap (fun t ↦ (cos (2 * π * t), sin (2 * π * t)))
      fun _ ↦ 0 := by
  rw [funext polarCap_apply]
  exact isLoopCylinder_comp_polar contMDiff_id

private theorem contDiff_polarCap : ContDiff ℝ 2 polarCap :=
  contMDiff_iff_contDiff.1 isLoopCylinder_polarCap.contMDiff

/-- The derivative of the polar parametrization: the inverse polar map after the affine map
`(s, t) ↦ (1 - s, 2πt)`. -/
private theorem hasFDerivAt_polarCap (z : ℝ × ℝ) :
    HasFDerivAt polarCap ((fderivPolarCoordSymm (1 - z.1, 2 * π * z.2)).comp
      ((-ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((2 * π) • ContinuousLinearMap.snd ℝ ℝ ℝ))) z :=
  (hasFDerivAt_polarCoord_symm _).comp z
    ((hasFDerivAt_fst.const_sub 1).prodMk (hasFDerivAt_snd.const_mul (2 * π)))

/-- The `s`-direction goes to the inward radial vector. -/
private theorem fderiv_polarCap_apply_fst (z : ℝ × ℝ) :
    fderiv ℝ polarCap z (1, 0) = -(cos (2 * π * z.2), sin (2 * π * z.2)) := by
  rw [(hasFDerivAt_polarCap z).fderiv]
  simp [fderivPolarCoordSymm]

/-- The `t`-direction goes to `2π (1 - s)` times the counterclockwise tangent vector. -/
private theorem fderiv_polarCap_apply_snd (z : ℝ × ℝ) :
    fderiv ℝ polarCap z (0, 1) =
      (2 * π * (1 - z.1)) • (-sin (2 * π * z.2), cos (2 * π * z.2)) := by
  rw [(hasFDerivAt_polarCap z).fderiv]
  ext <;> simp [fderivPolarCoordSymm] <;> ring

private theorem polarCap_add_one (z : ℝ × ℝ) : polarCap (z.1, z.2 + 1) = polarCap z :=
  isLoopCylinder_polarCap.apply_add_one z

private theorem polarCap_norm_sq (z : ℝ × ℝ) :
    (polarCap z).1 ^ 2 + (polarCap z).2 ^ 2 = (1 - z.1) ^ 2 := by
  simp only [polarCap_apply]
  nlinarith [sin_sq_add_cos_sq (2 * π * z.2)]

/-- The derivative of a disc read in polar coordinates. -/
private theorem mfderiv_comp_polarCap_apply {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (polarCap z)) (v : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ polarCap) z v =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) (fderiv ℝ polarCap z v) := by
  rw [mfderiv_comp z hu (hasFDerivAt_polarCap z).differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv]
  -- The identifications of the tangent spaces of `ℝ × ℝ` with `ℝ × ℝ` are the identity.
  rfl

/-- The partial derivatives of the polar cap of a pseudoholomorphic disc at `(s, t)`: the
`s`-derivative is `-v` and the `t`-derivative `2π (1 - s) J v`, for the image `v` of the radial
vector `(cos 2πt, sin 2πt)`. -/
private theorem mfderiv_comp_polarCap_apply_fst_snd {u : ℝ × ℝ → M} {z : ℝ × ℝ}
    {J : AlmostComplexStructure (TangentSpace I (u (polarCap z)))}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (polarCap z))
    (hhol : mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) stdComplexLineImag =
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) stdComplexLineReal)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ polarCap) z (1, 0) =
        -mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) (cos (2 * π * z.2), sin (2 * π * z.2)) ∧
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ polarCap) z (0, 1) = (2 * π * (1 - z.1)) •
        J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) (cos (2 * π * z.2), sin (2 * π * z.2))) := by
  set D := mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z)
  refine ⟨?_, ?_⟩
  · rw [mfderiv_comp_polarCap_apply hu, fderiv_polarCap_apply_fst]
    exact map_neg D _
  · rw [mfderiv_comp_polarCap_apply hu, fderiv_polarCap_apply_snd]
    -- The Cauchy–Riemann equation makes `D` complex linear, and `(-sin θ, cos θ)` is the
    -- rotation of `(cos θ, sin θ)` by the standard complex structure of the plane.
    exact (map_smul D _ _).trans (congrArg _ ((isComplexLinearMap_iff_apply _ J D.toLinearMap).1
      (IsComplexLinearMap.of_apply_stdComplexLineImag hhol)
      (cos (2 * π * z.2), sin (2 * π * z.2))))

/-- The open unit square is sent by polar coordinates into the open unit disc. -/
private theorem polarCap_mem_disc {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    (polarCap z).1 ^ 2 + (polarCap z).2 ^ 2 < 1 := by
  rw [polarCap_norm_sq]
  nlinarith [hz.1.1, hz.1.2]

/-- Every point of the closed unit disc is the image under polar coordinates of a point
`(s, t)` with `s ∈ [0, 1]`. -/
private theorem exists_polarCap_eq {z : ℝ × ℝ} (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) :
    ∃ p : ℝ × ℝ, p.1 ∈ Icc (0 : ℝ) 1 ∧ polarCap p = z := by
  set c : ℂ := Complex.equivRealProd.symm z
  have hc : ‖c‖ ≤ 1 := by
    rw [← sq_le_one_iff₀ (norm_nonneg c), Complex.sq_norm, Complex.normSq_apply]
    simpa [c, ← sq] using hz
  refine ⟨(1 - ‖c‖, Complex.arg c / (2 * π)), ⟨by linarith, by linarith [norm_nonneg c]⟩, ?_⟩
  have h2π : 2 * π * (Complex.arg c / (2 * π)) = Complex.arg c := by
    field_simp
  ext
  · simp only [polarCap_apply, sub_sub_cancel, h2π, Complex.norm_mul_cos_arg]
    simp [c]
  · simp only [polarCap_apply, sub_sub_cancel, h2π, Complex.norm_mul_sin_arg]
    simp [c]

/-! ### Pseudoholomorphic discs in an exact symplectic manifold -/

namespace SmoothTwoForm

variable [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1}
  {u : ℝ × ℝ → M}

/-- The area density of the polar cap of a disc, as a function of `(s, t)`. -/
private abbrev polarDensity (ω : SmoothTwoForm I M) (u : ℝ × ℝ → M) (z : ℝ × ℝ) : ℝ :=
  ω.val ((u ∘ polarCap) z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ polarCap) z (1, 0),
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ polarCap) z (0, 1)]

private theorem continuous_polarDensity (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) :
    Continuous (polarDensity ω u) :=
  (ω.isSmoothForm.of_le (by simp)).continuous_apply_mfderiv
    (hu.comp (contDiff_polarCap.of_le one_le_two).contMDiff) (1, 0) (0, 1)

variable {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}

/-- **The area density of a disc in polar coordinates.** Where the disc solves the Cauchy–Riemann
equation, the area density of its polar cap at `(s, t)` is `-2π (1 - s) ω(v, J v)`, for the image
`v` of the radial vector `(cos 2πt, sin 2πt)`. -/
private theorem polarDensity_eq {z : ℝ × ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (polarCap z))
    (hhol : mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) stdComplexLineImag =
      J (polarCap z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) stdComplexLineReal)) :
    polarDensity ω u z = -(2 * π * (1 - z.1)) * ω.eval₂ (u (polarCap z))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) (cos (2 * π * z.2), sin (2 * π * z.2)))
        (J (polarCap z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z)
          (cos (2 * π * z.2), sin (2 * π * z.2)))) := by
  obtain ⟨h₁, h₂⟩ := mfderiv_comp_polarCap_apply_fst_snd hu hhol
  rw [polarDensity, ← SmoothBundleForm.eval₂_apply, Function.comp_apply, h₁, h₂,
    SmoothBundleForm.eval₂_neg_left, SmoothBundleForm.eval₂_smul_right, smul_eq_mul]
  ring

/-- **The area of a disc is the line integral along its boundary.** For `ω = dα`, the integral of
the area density of the polar cap of a `C²` disc over the unit square is minus the line integral of
`α` along the boundary loop. -/
private theorem integral_polarDensity (hα : mextDeriv α.val = ω.val)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) :
    ∫ z in Icc (0, 0) (1, 1), polarDensity ω u z =
      -pathIntegral α.val (fun t ↦ u (cos (2 * π * t), sin (2 * π * t))) 0 1 := by
  rw [(ω.isSmoothForm.of_le (by simp)).setIntegral_eq_rectangleIntegral
    ((hu.comp contDiff_polarCap.contMDiff).of_le one_le_two)
    (Prod.mk_le_mk.2 ⟨zero_le_one, zero_le_one⟩), ← hα]
  -- Unfold the polar cap to the explicit polar formula of `TauCeti.isLoopCylinder_comp_polar`.
  simp only [comp_def, polarCap_apply]
  refine ((isLoopCylinder_comp_polar hu).rectangleIntegral_mextDeriv
    (α.isSmoothForm.of_le (by simp))).trans ?_
  rw [pathIntegral_const_curve, zero_sub]

/-- On the open unit square the area density of the polar cap of a pseudoholomorphic disc is
nonpositive. -/
private theorem polarDensity_nonpos_of_mem_Ioo (hω : ω.IsNondegenerate)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : polarDensity ω u z ≤ 0 := by
  have hdisc := polarCap_mem_disc hz
  rw [polarDensity_eq ((hu _).mdifferentiableAt one_ne_zero) (hhol _ hdisc)]
  have hpos : 0 < 2 * π * (1 - z.1) := by have := hz.1.2; positivity
  refine mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hpos.le) ?_
  simpa using SymplecticForm.Tames.symplecticForm_apply_apply_self_nonneg (hJ _ hdisc)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) (cos (2 * π * z.2), sin (2 * π * z.2)))

/-- On the closed unit square the area density of the polar cap of a pseudoholomorphic disc is
nonpositive, by continuity. -/
private theorem polarDensity_nonpos_of_mem_Icc (hω : ω.IsNondegenerate)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    {z : ℝ × ℝ} (hz : z ∈ Icc (0, 0) (1, 1)) : polarDensity ω u z ≤ 0 := by
  have hsub : Icc ((0 : ℝ), (0 : ℝ)) (1, 1) ⊆ closure (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [closure_prod_eq, closure_Ioo zero_ne_one, Icc_prod_Icc]
  exact (isClosed_le (continuous_polarDensity hu) continuous_const).closure_subset_iff.2
    (fun _ hz ↦ polarDensity_nonpos_of_mem_Ioo hω hu hJ hhol hz) (hsub hz)

/-- **The boundary integral of a pseudoholomorphic disc is nonnegative.** Let `ω = dα` be a
nondegenerate exact two-form and `u` a `C²` map of the plane solving the Cauchy–Riemann equation
`∂_t u = J ∂_s u` on the open unit disc, for almost complex structures `J z` on `T_{u z} M` tamed
by `ω`. Then the line integral of `α` along the boundary loop `t ↦ u (cos 2πt, sin 2πt)`, which is
the symplectic area of the disc, is nonnegative. -/
theorem IsNondegenerate.pathIntegral_disc_boundary_nonneg (hω : ω.IsNondegenerate)
    (hα : mextDeriv α.val = ω.val) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)) :
    0 ≤ pathIntegral α.val (fun t ↦ u (cos (2 * π * t), sin (2 * π * t))) 0 1 := by
  have h := setIntegral_nonpos (μ := volume) measurableSet_Icc fun z hz ↦
    polarDensity_nonpos_of_mem_Icc hω (hu.of_le one_le_two) hJ hhol hz
  rw [integral_polarDensity hα hu] at h
  linarith

/-- If the area density of the polar cap of a pseudoholomorphic disc vanishes at a point of the
open unit square, the derivative of the polar cap vanishes there. -/
private theorem mfderiv_comp_polarCap_eq_zero (hω : ω.IsNondegenerate)
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    {z : ℝ × ℝ} (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (hzero : polarDensity ω u z = 0) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ polarCap) z = 0 := by
  have hdisc := polarCap_mem_disc hz
  have hdiff := (hu (polarCap z)).mdifferentiableAt one_ne_zero
  have hpos : 2 * π * (1 - z.1) ≠ 0 := by have := hz.1.2; positivity
  rw [polarDensity_eq hdiff (hhol _ hdisc), mul_eq_zero, neg_eq_zero, or_iff_right hpos] at hzero
  replace hzero :
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u (polarCap z) (cos (2 * π * z.2), sin (2 * π * z.2)) = 0 :=
    by_contra fun hv ↦ ((hJ _ hdisc) _ hv).ne' (by simpa using hzero)
  obtain ⟨h₁, h₂⟩ := mfderiv_comp_polarCap_apply_fst_snd hdiff (hhol _ hdisc)
  rw [hzero, neg_zero] at h₁
  rw [hzero, map_zero, smul_zero] at h₂
  exact ContinuousLinearMap.prod_ext (ContinuousLinearMap.ext_ring h₁)
    (ContinuousLinearMap.ext_ring h₂)

/-- **A pseudoholomorphic disc with vanishing boundary integral is constant.** Under the hypotheses
of `IsNondegenerate.pathIntegral_disc_boundary_nonneg`, if the line integral of `α` along the
boundary loop `t ↦ u (cos 2πt, sin 2πt)` vanishes, then `u` is constant on the closed unit
disc. -/
theorem IsNondegenerate.apply_eq_apply_zero_of_pathIntegral_eq_zero (hω : ω.IsNondegenerate)
    (hα : mextDeriv α.val = ω.val) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    (h0 : pathIntegral α.val (fun t ↦ u (cos (2 * π * t), sin (2 * π * t))) 0 1 = 0) {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) : u z = u 0 := by
  have hu₁ := hu.of_le one_le_two
  set U := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUsub : U ⊆ Icc (0, 0) (1, 1) := by
    rw [← Icc_prod_Icc]
    exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hcont := continuous_polarDensity (ω := ω) hu₁
  -- The density is nonpositive with zero integral, so it vanishes on the open square.
  have hae : (fun z ↦ -polarDensity ω u z) =ᵐ[volume.restrict (Icc (0, 0) (1, 1))] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Icc fun z hz ↦
        neg_nonneg.2 (polarDensity_nonpos_of_mem_Icc hω hu₁ hJ hhol hz))
      (hcont.neg.continuousOn.integrableOn_compact isCompact_Icc)).1
      (by rw [integral_neg, integral_polarDensity hα hu, h0, neg_zero, neg_zero])
  have hzero : ∀ z ∈ U, polarDensity ω u z = 0 := fun z hz ↦ by
    simpa using Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hUsub hae)
      hUopen hcont.neg.continuousOn continuousOn_const hz
  -- Hence the polar cap has zero derivative on the open square and is constant there.
  have hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ polarCap) :=
    hu₁.comp (contDiff_polarCap.of_le one_le_two).contMDiff
  have hhalf : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ U :=
    ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  have hconst : EqOn (u ∘ polarCap) (fun _ ↦ (u ∘ polarCap) (1 / 2, 1 / 2)) U := fun p hp ↦
    (hw.mdifferentiable one_ne_zero).mdifferentiableOn.apply_eq_of_mfderiv_eq_zero hUopen
      ((convex_Ioo 0 1).prod (convex_Ioo 0 1)).isPreconnected
      (fun q hq ↦ mfderiv_comp_polarCap_eq_zero hω hu₁ hJ hhol hq (hzero q hq)) hp hhalf
  -- By continuity it is constant on the closed square, as points are closed in the manifold `M`;
  -- at `s = 1` it takes the value `u 0`.
  have : T1Space M := I.t1Space M
  have hconst' : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      (u ∘ polarCap) p = (u ∘ polarCap) (1 / 2, 1 / 2) := by
    rw [← closure_Ioo zero_ne_one, ← closure_prod_eq]
    exact (isClosed_singleton.preimage hw.continuous).closure_subset_iff.2 hconst
  have hcentre : (u ∘ polarCap) (1, 0) = u 0 := by simp [polarCap_apply, ← Prod.mk_zero_zero]
  -- Every point of the closed disc is on the polar cap, up to the period of the angle.
  obtain ⟨p, hp, rfl⟩ := exists_polarCap_eq hz
  have hper : Periodic (fun t ↦ (u ∘ polarCap) (p.1, t)) 1 := fun t ↦
    congrArg u (polarCap_add_one (p.1, t))
  have hfract : (u ∘ polarCap) (p.1, Int.fract p.2) = (u ∘ polarCap) p := by
    simpa [← Int.self_sub_floor] using hper.sub_int_mul_eq ⌊p.2⌋
  calc u (polarCap p) = (u ∘ polarCap) (p.1, Int.fract p.2) := hfract.symm
    _ = (u ∘ polarCap) (1, 0) :=
      (hconst' (p.1, Int.fract p.2) ⟨hp, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩).trans
        (hconst' (1, 0) ⟨⟨zero_le_one, le_rfl⟩, le_rfl, zero_le_one⟩).symm
    _ = u 0 := hcentre

/-- **No disc bubbles on exact Lagrangians.** Let `ω = dα` be a nondegenerate exact two-form and
`i : N → M` a map with `i^* α = df`, for instance an exact Lagrangian map with primitive `f`. A
`C²` map `u` of the plane solving the Cauchy–Riemann equation `∂_t u = J ∂_s u` on the open unit
disc, for almost complex structures `J z` tamed by `ω`, whose boundary loop
`t ↦ u (cos 2πt, sin 2πt)` is `i ∘ c` on `[0, 1]` for a `C¹` curve `c` with `c 0 = c 1`, is
constant on the closed unit disc. -/
theorem IsNondegenerate.apply_eq_apply_zero_of_boundary_exact {E₀ H₀ N : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
    [TopologicalSpace N] [ChartedSpace H₀ N] {i : N → M} {f : N → ℝ} {c : ℝ → N}
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.val = ω.val) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u z)).Tames (J z))
    (hhol : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag =
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal))
    (hi : MDifferentiable I₀ I i) (hf : ContMDiff I₀ 𝓘(ℝ) 1 f)
    (hL : mpullback I₀ I i α.val = mextDeriv (RoughForm.ofFunction I₀ f))
    (hc : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c) (hc₀₁ : c 0 = c 1)
    (hbd : ∀ t ∈ Icc (0 : ℝ) 1, u (cos (2 * π * t), sin (2 * π * t)) = i (c t)) {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) : u z = u 0 := by
  refine hω.apply_eq_apply_zero_of_pathIntegral_eq_zero hα hu J hJ hhol ?_ hz
  rw [pathIntegral_congr_of_eqOn_uIoo (γ' := i ∘ c) fun t ht ↦
      hbd t (Ioo_subset_Icc_self (by rwa [uIoo_of_le zero_le_one] at ht)),
    pathIntegral_comp_eq_sub_of_mpullback_eq hi hf hL hc, hc₀₁, sub_self]

/-- **No sphere bubbles in an exact symplectic manifold.** Let `ω = dα` be a nondegenerate exact
two-form. A pseudoholomorphic sphere is presented by its two hemispheres `u₁` and `u₂`, read in
the charts `z` and `1 / z`: `C²` maps of the plane solving the Cauchy–Riemann equation on the open
unit disc for almost complex structures tamed by `ω`, whose boundary loops agree with opposite
orientations, `u₂ (cos 2πt, sin 2πt) = u₁ (cos 2πt, -sin 2πt)`. Then both are constant on the
closed unit disc, with the same value. -/
theorem IsNondegenerate.exists_forall_eq_of_disc_pair (hω : ω.IsNondegenerate)
    (hα : mextDeriv α.val = ω.val) {u₁ u₂ : ℝ × ℝ → M} (hu₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₁)
    (hu₂ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u₂)
    (J₁ : ∀ z, AlmostComplexStructure (TangentSpace I (u₁ z)))
    (J₂ : ∀ z, AlmostComplexStructure (TangentSpace I (u₂ z)))
    (hJ₁ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u₁ z)).Tames (J₁ z))
    (hJ₂ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 → (hω.symplecticFormAt (u₂ z)).Tames (J₂ z))
    (hhol₁ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 →
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u₁ z stdComplexLineImag =
        J₁ z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u₁ z stdComplexLineReal))
    (hhol₂ : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < 1 →
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u₂ z stdComplexLineImag =
        J₂ z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u₂ z stdComplexLineReal))
    (hglue : ∀ t : ℝ, u₂ (cos (2 * π * t), sin (2 * π * t)) =
      u₁ (cos (2 * π * t), -sin (2 * π * t))) :
    ∃ x : M, ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 ≤ 1 → u₁ z = x ∧ u₂ z = x := by
  set γ₁ : ℝ → M := fun t ↦ u₁ (cos (2 * π * t), sin (2 * π * t))
  have hγ₁ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ₁ :=
    (hu₁.of_le one_le_two).comp (by fun_prop : ContDiff ℝ 1 fun t : ℝ ↦
      (cos (2 * π * t), sin (2 * π * t))).contMDiff
  -- The boundary loop of `u₂` is that of `u₁` run backwards, so the boundary integrals are
  -- opposite; both are nonnegative, hence both vanish.
  have hrev : (fun t ↦ u₂ (cos (2 * π * t), sin (2 * π * t))) = fun t ↦ γ₁ (1 - t) := by
    funext t
    simp only [γ₁, hglue, mul_sub, mul_one, cos_two_pi_sub, sin_two_pi_sub]
  have h₂ : pathIntegral α.val (fun t ↦ u₂ (cos (2 * π * t), sin (2 * π * t))) 0 1 =
      -pathIntegral α.val γ₁ 0 1 := by
    rw [hrev, pathIntegral_comp_sub_left (α.isSmoothForm.of_le (by simp)) hγ₁, sub_self, sub_zero]
  have hn₁ := hω.pathIntegral_disc_boundary_nonneg hα hu₁ J₁ hJ₁ hhol₁
  have hn₂ := hω.pathIntegral_disc_boundary_nonneg hα hu₂ J₂ hJ₂ hhol₂
  have hz₁ : pathIntegral α.val γ₁ 0 1 = 0 := by linarith
  have hz₂ : pathIntegral α.val (fun t ↦ u₂ (cos (2 * π * t), sin (2 * π * t))) 0 1 = 0 := by
    rw [h₂, hz₁, neg_zero]
  -- The two constants agree at the common boundary point `(1, 0)`.
  have hone : ((1 : ℝ), (0 : ℝ)).1 ^ 2 + ((1 : ℝ), (0 : ℝ)).2 ^ 2 ≤ 1 := by norm_num
  have hagree : u₂ 0 = u₁ 0 := by
    have := hglue 0
    simp only [mul_zero, cos_zero, sin_zero, neg_zero] at this
    rw [← hω.apply_eq_apply_zero_of_pathIntegral_eq_zero hα hu₂ J₂ hJ₂ hhol₂ hz₂ hone,
      ← hω.apply_eq_apply_zero_of_pathIntegral_eq_zero hα hu₁ J₁ hJ₁ hhol₁ hz₁ hone, this]
  exact ⟨u₁ 0, fun z hz ↦
    ⟨hω.apply_eq_apply_zero_of_pathIntegral_eq_zero hα hu₁ J₁ hJ₁ hhol₁ hz₁ hz,
      (hω.apply_eq_apply_zero_of_pathIntegral_eq_zero hα hu₂ J₂ hJ₂ hhol₂ hz₂ hz).trans hagree⟩⟩

end SmoothTwoForm

end TauCeti
