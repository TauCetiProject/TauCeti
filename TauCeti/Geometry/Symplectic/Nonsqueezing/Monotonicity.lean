/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.RiemannSphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.RiemannSurface.MappingDegree
import TauCeti.Geometry.Manifold.Degree.Global
import TauCeti.Geometry.Symplectic.Manifold.CurvePairing
import TauCeti.Analysis.Complex.AreaMonotonicity
import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Pseudoholomorphic spheres through a standard ball have area at least `π r²`

Let `σ` be a smooth two-form taming a smooth almost complex structure `J` on a manifold `M`, and
let `φ` be a partial diffeomorphism from a complex inner product space `E`, such as `ℂⁿ`, into
`M`, defined on the ball `B(c, r)`. Suppose that on this ball `φ` pulls `σ` back to the standard
symplectic form `Im ⟪v, w⟫` of `E`, and that `J` is standard there: `dφ (i v) = J (dφ v)`. This is
the situation of Gromov's proof of the nonsqueezing theorem, where `φ` is a symplectic embedding
of a ball into `S²(a) × T²ⁿ⁻²` and `J` is chosen to extend the pushed-forward standard structure.

This file proves that every smooth `J`-holomorphic sphere `u : OnePoint ℂ → M` through the centre
`φ c` has symplectic area `∫ u^*σ` at least `π r²`
(`TauCeti.pi_mul_sq_le_integralTopForm_mpullback`), provided that `u` is not constant. The area
is taken over the Riemann sphere with the orientation of its complex structure.

The proof reads `u` in the affine coordinate `ℂ ⊆ OnePoint ℂ`, where the area is the planar
integral of the density `σ(∂ₓu, ∂ᵧu)` (`OnePoint.integralTopForm_eq_integral_apply_coe`).

* **Outside the ball.** The density is nonnegative everywhere, since `∂ᵧu = J ∂ₓu` and `σ` tames
  `J`.
* **Inside the ball.** Over the open set `U` of points `z` with `u z ∈ φ(B(c, r))`, the map
  `w = φ⁻¹ ∘ u` is holomorphic, because `dφ` intertwines `i` with `J`. Since `φ` pulls `σ` back
  to `Im ⟪·, ·⟫`, the density there is `Im ⟪w', i w'⟫ = ‖w'‖²`.
* **Monotonicity.** If `u ∞` lies outside `φ(B(c, r))`, the sets
  `{z ∈ U | ‖w z - c‖ ≤ t}`, `t < r`, are the preimages under `u` of the images under `φ` of the
  closed balls of radius `t` about `c`. These images are compact and avoid `u ∞`, so the sets are
  compact subsets of `ℂ`. The monotonicity theorem for holomorphic curves
  (`TauCeti.ofReal_pi_mul_sq_le_setLIntegral_enorm_deriv_sq`) then bounds the area of `w` over `U`
  below by `π r²`, also when `u` is critical at the centre
  (`TauCeti.pi_mul_sq_le_integralTopForm_mpullback_of_apply_infty_notMem`).
* **Moving `∞` out of the ball.** A nonconstant sphere does not lie in `φ(B(c, r))`: read through
  `φ⁻¹` it would be a bounded entire function, constant by Liouville's theorem. Precomposing `u`
  with a Möbius transformation sending `∞` to a point mapped outside the ball does not change the
  area, since a Möbius transformation has mapping degree one.

## Main results

* `TauCeti.pi_mul_sq_le_integralTopForm_mpullback`: a nonconstant pseudoholomorphic sphere
  through `φ c` has area at least `π r²`.
* `TauCeti.pi_mul_sq_le_integralTopForm_mpullback_of_apply_infty_notMem`: the same bound for a
  sphere mapping `∞` outside `φ(B(c, r))`, the form in which the affine coordinate sees the whole
  preimage of the ball.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A (the nonsqueezing theorem).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 9.3 (the proof of nonsqueezing through the
  monotonicity of the area of a holomorphic sphere in a standard ball).
-/

public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Real TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞} {c : E} {r : ℝ} {u : OnePoint ℂ → M}

/-- The derivative of `u` read through the inverse of `φ`, as a real-linear map on `ℂ`. -/
private def symmDeriv (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (u : OnePoint ℂ → M) (z : ℂ) :
    ℂ →L[ℝ] E :=
  (mvfderiv I φ.symm (u (z : OnePoint ℂ))).comp (mfderiv 𝓘(ℝ, ℂ) I u (z : OnePoint ℂ))

omit [IsManifold I ∞ M] in
private theorem symmDeriv_apply (z v : ℂ) :
    symmDeriv φ u z v = mvfderiv I φ.symm (u z) (mfderiv 𝓘(ℝ, ℂ) I u z v) := rfl

omit [IsManifold I ∞ M] in
/-- Near a point whose image lies in the target of `φ`, the map `φ⁻¹ ∘ u` on `ℂ` has derivative
`TauCeti.symmDeriv`. -/
private theorem hasFDerivAt_symm_comp (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u) {z : ℂ}
    (hz : u (z : OnePoint ℂ) ∈ φ.target) :
    HasFDerivAt (fun z : ℂ ↦ φ.symm (u (z : OnePoint ℂ))) (symmDeriv φ u z) z := by
  have hs : MDifferentiableAt I 𝓘(ℝ, E) φ.symm (u (z : OnePoint ℂ)) :=
    φ.symm.mdifferentiableAt (by simp) hz
  have hcoe := OnePoint.hasMFDerivAt_coe z
  have hu' := (hu.mdifferentiableAt (by simp) (x := (z : OnePoint ℂ))).hasMFDerivAt
  have h := hs.hasMFDerivAt.comp z (hu'.comp z hcoe)
  exact hasMFDerivAt_iff_hasFDerivAt.1 h

/-- The Cauchy–Riemann equation of a pseudoholomorphic sphere in the affine coordinate: its
derivative maps `i` to `J` of the image of `1`. -/
private theorem mfderiv_apply_I_eq (hhol : IsPseudoholomorphic
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) J u) (z : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) I u z Complex.I = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)) := by
  simpa using (hhol.isPseudoholomorphicAt z).mfderiv_apply_commute (1 : ℂ)

/-- Where `dφ` intertwines `i` with `J`, the inverse differential carries a pair `(b, J b)` of
tangent vectors at a point `φ x` to a pair `(a, i a)`. -/
private theorem mfderiv_symm_apply_eq_I_smul
    (hJ : ∀ x ∈ ball c r, ∀ v : E,
      mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v))
    (hball : ball c r ⊆ φ.source) {x : E} (hx : x ∈ ball c r) {y : M} (hxy : φ x = y)
    (b : TangentSpace I y) :
    mvfderiv I φ.symm y (J y b) = Complex.I • mvfderiv I φ.symm y b := by
  subst hxy
  obtain ⟨a, rfl⟩ := (φ.isInvertible_mfderiv (by simp) (hball hx)).surjective b
  rw [← hJ x hx a, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
    φ.mfderiv_symm_apply_mfderiv_apply (by simp) (hball hx)]
  exact φ.mfderiv_symm_apply_mfderiv_apply (by simp) (hball hx) _

/-- Where `φ` pulls `σ` back to `Im ⟪·, ·⟫` and `dφ` intertwines `i` with `J`, the density
`σ(b, J b)` at a point `φ x` is the squared norm of the vector `dφ⁻¹ b`. -/
private theorem eval₂_apply_eq_norm_mvfderiv_symm_sq
    (hσ : ∀ x ∈ ball c r, ∀ v w : E,
      σ.eval₂ (φ x) (mfderiv 𝓘(ℝ, E) I φ x v) (mfderiv 𝓘(ℝ, E) I φ x w) = (⟪v, w⟫_ℂ).im)
    (hJ : ∀ x ∈ ball c r, ∀ v : E,
      mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v))
    (hball : ball c r ⊆ φ.source) {x : E} (hx : x ∈ ball c r) {y : M} (hxy : φ x = y)
    (b : TangentSpace I y) :
    σ.eval₂ y b (J y b) = ‖mvfderiv I φ.symm y b‖ ^ 2 := by
  subst hxy
  obtain ⟨a, rfl⟩ : ∃ a : E, mfderiv 𝓘(ℝ, E) I φ x a = b :=
    (φ.isInvertible_mfderiv (by simp) (hball hx)).surjective b
  rw [← hJ x hx a, hσ x hx, mvfderiv_apply_eq_mfderiv_apply,
    φ.mfderiv_symm_apply_mfderiv_apply (by simp) (hball hx) a, inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Over the points mapped into `φ(B(c, r))`, the map `φ⁻¹ ∘ u` on `ℂ` is holomorphic, with
derivative `dφ⁻¹ (∂ₓu)`. -/
private theorem hasDerivAt_symm_comp (hball : ball c r ⊆ φ.source)
    (hJ : ∀ x ∈ ball c r, ∀ v : E,
      mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v))
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u) {z : ℂ} (hz : u z ∈ φ '' ball c r) :
    HasDerivAt (fun z : ℂ ↦ φ.symm (u z)) (symmDeriv φ u z 1) z := by
  obtain ⟨x, hx, hxz⟩ := hz
  have h₁ := hasFDerivAt_symm_comp hu (hxz ▸ φ.map_source (hball hx))
  have h₂ : symmDeriv φ u z Complex.I = Complex.I • symmDeriv φ u z 1 := by
    rw [symmDeriv_apply, symmDeriv_apply, mfderiv_apply_I_eq hhol z]
    exact mfderiv_symm_apply_eq_I_smul hJ hball hx hxz _
  exact (h₁.complexOfReal_hasFDerivAt h₂).hasDerivAt

/-- A pseudoholomorphic sphere whose image lies in `φ(B(c, r))` is constant: read through `φ⁻¹`
it is a bounded entire function, constant by Liouville's theorem. -/
private theorem exists_apply_notMem_image [T2Space M] (hball : ball c r ⊆ φ.source)
    (hJ : ∀ x ∈ ball c r, ∀ v : E,
      mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v))
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u) (hnc : ∃ y y', u y ≠ u y') : ∃ y, u y ∉ φ '' ball c r := by
  by_contra! h
  have hw : Differentiable ℂ fun z : ℂ ↦ φ.symm (u z) := fun z ↦
    (hasDerivAt_symm_comp hball hJ hu hhol (h z)).differentiableAt
  have hmem (z : ℂ) : φ.symm (u z) ∈ ball c r ∧ φ (φ.symm (u z)) = u z := by
    obtain ⟨x, hx, hxz⟩ := h z
    have hl : φ.symm (u z) = x := hxz ▸ φ.left_inv (hball hx)
    exact ⟨hl ▸ hx, hl ▸ hxz⟩
  have hb : Bornology.IsBounded (range fun z : ℂ ↦ φ.symm (u z)) :=
    isBounded_ball.subset (range_subset_iff.2 fun z ↦ (hmem z).1)
  -- On `ℂ` the sphere is constant, and `ℂ` is dense in the sphere.
  have hconst : u = fun _ ↦ u (0 : ℂ) := OnePoint.denseRange_coe.equalizer hu.continuous
    continuous_const (funext fun z ↦ by
      simp only [Function.comp_apply]
      rw [← (hmem z).2, ← (hmem 0).2, hw.apply_eq_apply_of_bounded hb z 0])
  obtain ⟨y, y', h⟩ := hnc
  rw [hconst] at h
  exact h rfl

/-- The area density `σ(∂ₓu, ∂ᵧu) = σ(∂ₓu, J ∂ₓu)` of a pseudoholomorphic sphere `u` in the affine
coordinate. -/
private def areaDensity (σ : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M)
    (u : OnePoint ℂ → M) (z : ℂ) : ℝ :=
  σ.eval₂ (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)) (J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))

/-- The area of a pseudoholomorphic sphere is the planar integral of its area density, which is
integrable. -/
private theorem integrable_areaDensity_and_integralTopForm_eq (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u) :
    Integrable (areaDensity σ J u) ∧
      integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
        (SmoothForm.mpullback u hu σ).val = ∫ z, areaDensity σ J u z := by
  have hDeq : (fun z : ℂ ↦ (SmoothForm.mpullback u hu σ).val (z : OnePoint ℂ)
      ![(1 : ℂ), Complex.I]) = areaDensity σ J u := by
    funext z
    simp only [areaDensity, SmoothForm.coe_mpullback, mpullback_apply,
      SmoothBundleForm.eval₂_apply, ← mfderiv_apply_I_eq hhol z]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hi : IntegrableTopForm (SmoothForm.mpullback u hu σ).val :=
    (SmoothForm.mpullback u hu σ).isSmoothForm.integrableTopForm
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)) Complex.basisOneI
  exact hDeq ▸ ⟨OnePoint.integrable_apply_coe hi, OnePoint.integralTopForm_eq_integral_apply_coe hi⟩

omit [IsManifold I ∞ M] in
/-- If `u ∞` lies outside `φ(B(c, r))`, the points of `ℂ` mapped into the image under `φ` of the
closed ball of radius `t < r` about `c` form a compact set: the preimage of a compact set under
`u`, avoiding `∞`. They are the points of the preimage of `φ(B(c, r))` at which `φ⁻¹ ∘ u` lies
within `t` of `c`. -/
private theorem isCompact_sep_norm_symm_sub_le [FiniteDimensional ℂ E] [T2Space M]
    (hball : ball c r ⊆ φ.source) (hu : Continuous u) (hinf : u OnePoint.infty ∉ φ '' ball c r)
    {t : ℝ} (ht : t < r) :
    IsCompact {z ∈ {z : ℂ | u z ∈ φ '' ball c r} | ‖φ.symm (u z) - c‖ ≤ t} := by
  have hset : {z ∈ {z : ℂ | u z ∈ φ '' ball c r} | ‖φ.symm (u z) - c‖ ≤ t} =
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' (u ⁻¹' (φ '' closedBall c t)) := by
    ext z
    constructor
    · rintro ⟨⟨x, hx, hxz⟩, hzt⟩
      have hl : φ.symm (u z) = x := hxz ▸ φ.left_inv (hball hx)
      exact ⟨x, by rwa [mem_closedBall, dist_eq_norm, ← hl], hxz⟩
    · rintro ⟨x, hx, hxz⟩
      have hxr : x ∈ ball c r := closedBall_subset_ball ht hx
      have hl : φ.symm (u z) = x := hxz ▸ φ.left_inv (hball hxr)
      exact ⟨⟨x, hxr, hxz⟩, by rwa [hl, ← dist_eq_norm, ← mem_closedBall]⟩
  rw [hset]
  have hcK : IsCompact (φ '' closedBall c t) :=
    (isCompact_closedBall c t).image_of_continuousOn
      (φ.contMDiffOn.continuousOn.mono ((closedBall_subset_ball ht).trans hball))
  refine (OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage_iff ?_).2
    (hcK.isClosed.preimage hu).isCompact
  intro y hy
  induction y using OnePoint.rec with
  | infty => exact absurd (image_mono (closedBall_subset_ball ht) hy) hinf
  | coe z => exact mem_range_self z

/-- **Pseudoholomorphic spheres through a standard ball have area at least `π r²`.** Let `σ` tame
`J`, and let `φ` be a partial diffeomorphism from a complex inner product space `E` into `M`,
defined on the ball `B(c, r)`, which pulls `σ` back to `Im ⟪·, ·⟫` and intertwines `i` with `J`
on that ball. Let `u` be a smooth `J`-holomorphic sphere through `φ c` with `u ∞` outside
`φ(B(c, r))`. Then the symplectic area of `u` is at least `π r²`. -/
theorem pi_mul_sq_le_integralTopForm_mpullback_of_apply_infty_notMem [FiniteDimensional ℂ E]
    [T2Space M]
    (hσJ : σ.Tames J) (hball : ball c r ⊆ φ.source)
    (hσ : ∀ x ∈ ball c r, ∀ v w : E,
      σ.eval₂ (φ x) (mfderiv 𝓘(ℝ, E) I φ x v) (mfderiv 𝓘(ℝ, E) I φ x w) = (⟪v, w⟫_ℂ).im)
    (hJ : ∀ x ∈ ball c r, ∀ v : E,
      mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v))
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u)
    (hr : 0 ≤ r) {z₀ : ℂ} (hz₀ : u z₀ = φ c) (hinf : u OnePoint.infty ∉ φ '' ball c r) :
    π * r ^ 2 ≤ integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu σ).val := by
  -- The area is the planar integral of the density `D = σ(∂ₓu, J ∂ₓu)`, which is nonnegative.
  obtain ⟨hDint, harea⟩ := integrable_areaDensity_and_integralTopForm_eq (σ := σ) hu hhol
  have hD0 (z : ℂ) : 0 ≤ areaDensity σ J u z := hσJ.eval₂_nonneg _ _
  rw [harea]
  rcases hr.eq_or_lt with rfl | hr0
  · simpa using integral_nonneg hD0
  -- Over the open set `U` of points mapped into `φ(B(c, r))`, read `u` through `φ⁻¹` as `w`.
  set U : Set ℂ := {z : ℂ | u z ∈ φ '' ball c r}
  set w : ℂ → E := fun z ↦ φ.symm (u z)
  have hwapp (z : ℂ) : w z = φ.symm (u z) := rfl
  have hUo : IsOpen U :=
    (φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hball).preimage
      (hu.continuous.comp OnePoint.continuous_coe)
  have hwU (z : ℂ) (hz : z ∈ U) : w z ∈ ball c r ∧ φ (w z) = u z := by
    obtain ⟨x, hx, hxz⟩ := hz
    have hl : w z = x := by rw [hwapp, ← hxz]; exact φ.left_inv (hball hx)
    exact ⟨hl ▸ hx, hl ▸ hxz⟩
  have hwz₀ : w z₀ = c := by rw [hwapp, hz₀]; exact φ.left_inv (hball (mem_ball_self hr0))
  have hz₀U : z₀ ∈ U := ⟨c, mem_ball_self hr0, hz₀.symm⟩
  -- `w` is holomorphic on `U`, and the density there is `‖w'‖²`.
  have hderiv (z : ℂ) (hz : z ∈ U) : HasDerivAt w (symmDeriv φ u z 1) z :=
    hasDerivAt_symm_comp hball hJ hu hhol hz
  have hdens (z : ℂ) (hz : z ∈ U) : areaDensity σ J u z = ‖deriv w z‖ ^ 2 := by
    rw [(hderiv z hz).deriv]
    exact eval₂_apply_eq_norm_mvfderiv_symm_sq hσ hJ hball (hwU z hz).1 (hwU z hz).2 _
  -- Monotonicity bounds the area of `w` over `U`, which is the integral of `D` over `U`.
  have hmono := ofReal_pi_mul_sq_le_setLIntegral_enorm_deriv_sq hUo
    (fun z hz ↦ (hderiv z hz).differentiableAt.differentiableWithinAt) hz₀U hr fun t ht ↦ by
      simpa only [hwz₀] using isCompact_sep_norm_symm_sub_le hball hu.continuous hinf ht
  have hV : {z ∈ U | ‖w z - w z₀‖ < r} = U := sep_eq_self_iff_mem_true.2 fun z hz ↦ by
    rw [hwz₀, ← dist_eq_norm]
    exact (hwU z hz).1
  rw [hV] at hmono
  have hle : ∫⁻ z in U, ‖deriv w z‖ₑ ^ 2 ≤ ENNReal.ofReal (∫ z, areaDensity σ J u z) := by
    rw [ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall hD0)]
    calc ∫⁻ z in U, ‖deriv w z‖ₑ ^ 2 = ∫⁻ z in U, ENNReal.ofReal (areaDensity σ J u z) :=
          setLIntegral_congr_fun hUo.measurableSet fun z hz ↦ by
            rw [hdens z hz, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ ∫⁻ z, ENNReal.ofReal (areaDensity σ J u z) := setLIntegral_le_lintegral _ _
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hD0)).1 (hmono.trans hle)

/-- **Pseudoholomorphic spheres through a standard ball have area at least `π r²`.** Let `σ` tame
`J`, and let `φ` be a partial diffeomorphism from a complex inner product space `E` into `M`,
defined on the ball `B(c, r)`, which pulls `σ` back to `Im ⟪·, ·⟫` and intertwines `i` with `J`
on that ball. Then every nonconstant smooth `J`-holomorphic sphere `u` through `φ c` has
symplectic area `∫ u^*σ` at least `π r²`. -/
theorem pi_mul_sq_le_integralTopForm_mpullback [FiniteDimensional ℂ E] [T2Space M]
    (hσJ : σ.Tames J) (hball : ball c r ⊆ φ.source)
    (hσ : ∀ x ∈ ball c r, ∀ v w : E,
      σ.eval₂ (φ x) (mfderiv 𝓘(ℝ, E) I φ x v) (mfderiv 𝓘(ℝ, E) I φ x w) = (⟪v, w⟫_ℂ).im)
    (hJ : ∀ x ∈ ball c r, ∀ v : E,
      mfderiv 𝓘(ℝ, E) I φ x (Complex.I • v) = J (φ x) (mfderiv 𝓘(ℝ, E) I φ x v))
    (hu : ContMDiff 𝓘(ℝ, ℂ) I ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      J u)
    (hr : 0 ≤ r) {z₀ : OnePoint ℂ} (hz₀ : u z₀ = φ c) (hnc : ∃ y, u y ≠ φ c) :
    π * r ^ 2 ≤ integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      (SmoothForm.mpullback u hu σ).val := by
  rcases hr.eq_or_lt with rfl | hr0
  · simpa using integralTopForm_mpullback_nonneg hu
      (SmoothAlmostComplexStructure.orientation_eq_orientationAt_of_apply_one_eq_ofComplexManifold
        _) hhol.isPseudoholomorphicAt (fun _ ↦ hσJ.eval₂_nonneg _)
  -- Some point `y` is mapped outside `φ(B(c, r))`; rotate the sphere so that `∞` goes to `y`.
  obtain ⟨y, hy⟩ := exists_apply_notMem_image hball hJ hu hhol
    (by obtain ⟨y, hy⟩ := hnc; exact ⟨y, z₀, hz₀ ▸ hy⟩)
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) ℂ, g • (OnePoint.infty : OnePoint ℂ) = y := by
    induction y using OnePoint.rec with
    | infty => exact ⟨1, one_smul _ _⟩
    | coe b =>
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![b, 1; 1, 0]
        (by simp [Matrix.det_fin_two]), ?_⟩
      rw [OnePoint.smul_infty_eq_ite]
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hgs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : OnePoint ℂ ↦ g • z) := by
    -- The Möbius action is holomorphic, hence smooth for the underlying real structure.
    have := ContMDiffConstSMul.restrictScalars ℝ
      (inferInstance : ContMDiffConstSMul 𝓘(ℂ) ∞ (GL (Fin 2) ℂ) (OnePoint ℂ))
    exact contMDiff_const_smul g
  have hgd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : OnePoint ℂ ↦ g • z) :=
    (contMDiff_const_smul (I := 𝓘(ℂ)) (n := ∞) g).mdifferentiable (by simp)
  -- The centre is reached from a finite point after the rotation.
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : ℂ, g • (z₁ : OnePoint ℂ) = z₀ := by
    induction hp : g⁻¹ • z₀ using OnePoint.rec with
    | infty =>
      rw [inv_smul_eq_iff, hg] at hp
      exact absurd (hp ▸ hz₀ ▸ mem_image_of_mem φ (mem_ball_self hr0)) hy
    | coe z₁ => exact ⟨z₁, by rw [← hp, smul_inv_smul]⟩
  have key := pi_mul_sq_le_integralTopForm_mpullback_of_apply_infty_notMem hσJ hball hσ hJ
    (hu.comp hgs) (hhol.comp (isPseudoholomorphic_ofComplexManifold_iff.2 hgd)) hr
    (z₀ := z₁) (by simp [hz₁, hz₀]) (by simpa [hg] using hy)
  -- A Möbius transformation has degree one, so the rotation does not change the area.
  rwa [integralTopForm_mpullback_comp_eq_degree_mul _ _ hgs hgs.continuous.isProperMap hu σ,
    (hgd.degree_reindex_complexManifoldOrientation_eq_one_iff_exists_smul).2 ⟨g, rfl⟩,
    Int.cast_one, one_mul] at key

end TauCeti
