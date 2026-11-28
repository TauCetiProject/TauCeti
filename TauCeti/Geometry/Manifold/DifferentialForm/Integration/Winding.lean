/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Euclidean
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes.Winding
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# The cutoff integral of an angle form around a puncture

Let `M` be an oriented surface and `z₀, z₁` real functions with `z₀² + z₁² = 1` near a point `p`,
except at `p` itself. The **angle form** `z₀ dz₁ - z₁ dz₀` is the pullback of the angle form `dθ`
of the circle along `z = (z₀, z₁)`. For a cutoff `ψ` equal to `1` near `p` and supported in an
oriented parametrization `g` of a disc about `p`,

`∫_M dψ ∧ (z₀ dz₁ - z₁ dz₀) = -2π deg`,

where `deg` is the degree of the loop `ζ ↦ z (g (r ζ))` of directions of `z` along any small
circle about `p` on which `ψ = 1`
(`TauCeti.integralTopForm_mextDeriv_ofFunction_wedge_eq_neg_two_pi_mul_degree`).

The parametrization moves the integral to the plane
(`TauCeti.integralTopForm_eq_setIntegral_mpullback`), where the integrand is that of the cutoff
integral of the phase form of `z ∘ g`, read in `ℂ` through `Complex.orthonormalBasisOneI`.
Stokes' formula on the annulus between the small circle and the boundary of the support then gives
the degree
(`TauCeti.setIntegral_annulus_fderiv_mul_phaseForm_sub_eq_neg_two_pi_mul_degree`).

This is the local computation in Chern's proof of the Gauss–Bonnet theorem. Near a zero of a
vector field `X`, the connection forms of the frame of `X / ‖X‖` and of a frame defined across
the zero differ by the angle form of the coordinates `z` of `X / ‖X‖` in the second frame
(`IsLocalFrameOn.connectionForm_zero_one_eq_add_smul_sub_smul_of_riemannianVolumeForm_eq_one`).
The Stokes step `IsLocalFrameOn.integralTopForm_mextDeriv_ofFunction_wedge_connectionForm` thus
reduces the total curvature to a sum of the integrals computed here, one at each zero.

## Main results

* `TauCeti.integralTopForm_mextDeriv_ofFunction_wedge_eq_neg_two_pi_mul_degree`: the cutoff
  integral of the angle form of a circle-valued function around a puncture is `-2π` times its
  degree on a small circle.

## References

* S.-S. Chern, *A simple intrinsic proof of the Gauss–Bonnet formula for closed Riemannian
  manifolds*, Ann. of Math. 45 (1944), 747–752.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapter 9.
-/

public section

noncomputable section

open Bundle MeasureTheory Metric Set Topology TopologicalSpace
open scoped ContDiff Manifold Real Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The value of `dψ ∧ (z₀ dz₁ - z₁ dz₀)` on a pair of tangent vectors. -/
private theorem wedge_angleForm_apply (ψ z₀ z₁ : M → ℝ) (y : M) (p q : TangentSpace I y) :
    (mextDeriv (RoughForm.ofFunction I ψ)).wedge (fun x ↦
        z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
          z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x) y ![p, q] =
      mvfderiv I ψ y p * (z₀ y * mvfderiv I z₁ y q - z₁ y * mvfderiv I z₀ y q) -
        mvfderiv I ψ y q * (z₀ y * mvfderiv I z₁ y p - z₁ y * mvfderiv I z₀ y p) := by
  rw [RoughForm.wedge_apply_one_one]
  simp only [mextDeriv_ofFunction, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Matrix.cons_val_zero, smul_eq_mul]

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The chain rule through a map `g` from `ℝ²` read on `ℂ` by `Complex.orthonormalBasisOneI`. -/
private theorem mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr {g : EuclideanSpace ℝ (Fin 2) → M}
    {φ : M → ℝ} {w : ℂ}
    (hg : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g
      (Complex.orthonormalBasisOneI.repr w))
    (hφ : MDifferentiableAt I 𝓘(ℝ) φ (g (Complex.orthonormalBasisOneI.repr w))) (v : ℂ) :
    mvfderiv I φ (g (Complex.orthonormalBasisOneI.repr w))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g (Complex.orthonormalBasisOneI.repr w)
          (Complex.orthonormalBasisOneI.repr v)) =
      fderiv ℝ (fun w ↦ φ (g (Complex.orthonormalBasisOneI.repr w))) w v :=
  -- `mfderiv_eq_fderiv` identifies tangent spaces of model spaces with the model spaces, which
  -- they are by definition.
  (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans <| congrArg (fun L ↦ L v)
    ((hφ.hasMFDerivAt.comp w (hg.hasMFDerivAt.comp w
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.hasMFDerivAt)).mfderiv.symm.trans
      mfderiv_eq_fderiv)

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- Where `ψ` is locally constant, `dψ ∧ (z₀ dz₁ - z₁ dz₀)` vanishes. -/
private theorem wedge_angleForm_eq_zero {ψ : M → ℝ} (z₀ z₁ : M → ℝ) {y : M}
    (h : ∀ᶠ y' in 𝓝 y, ψ y' = ψ y) :
    (mextDeriv (RoughForm.ofFunction I ψ)).wedge (fun x ↦
        z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
          z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x) y = 0 := by
  have hdψ : mextDeriv (RoughForm.ofFunction I ψ) y = 0 :=
    mextDeriv_ofFunction_apply_eq_zero_iff.2
      ((hasMFDerivAt_const (ψ y) y).congr_of_eventuallyEq h).mfderiv
  rw [RoughForm.wedge_def, RoughForm.wedgeWith_apply', hdψ,
    ContinuousAlternatingMap.pairedWedge_zero_left]

omit [FiniteDimensional ℝ E] in
/-- `dψ ∧ (z₀ dz₁ - z₁ dz₀)` is continuous when `ψ` is `C¹`, provided that at every point either
`ψ` is locally constant or `z₀` and `z₁` are `C²`. -/
private theorem isSmoothForm_wedge_angleForm {ψ z₀ z₁ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ) 1 ψ)
    (h : ∀ y, (∀ᶠ y' in 𝓝 y, ψ y' = ψ y) ∨
      (ContMDiffAt I 𝓘(ℝ) 2 z₀ y ∧ ContMDiffAt I 𝓘(ℝ) 2 z₁ y)) :
    IsSmoothForm I 0 ((mextDeriv (RoughForm.ofFunction I ψ)).wedge (fun x ↦
        z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
          z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x)) := by
  rw [isSmoothForm_def]
  intro y
  rcases h y with hy | ⟨hz₀, hz₁⟩
  · refine (Bundle.contMDiffAt_zeroSection ..).congr_of_eventuallyEq ?_
    filter_upwards [hy.eventually_nhds, hy] with y' hy' hy'y
    rw [wedge_angleForm_eq_zero z₀ z₁ (hy'.mono fun _ h ↦ h.trans hy'y.symm)]
    -- The zero section is `y ↦ (y, 0)`.
    rfl
  · have hdz (j : M → ℝ) (hj : ContMDiffAt I 𝓘(ℝ) 2 j y) :=
      (contMDiffAt_mextDeriv_ofFunction hj).of_le zero_le_one
    rw [RoughForm.wedge_def]
    exact ((IsSmoothForm.continuous_mextDeriv (isSmoothForm_ofFunction_iff.2 hψ)).contMDiff
      y).wedgeWith_form _ (((hz₀.of_le (by norm_num)).smul_section (hdz z₁ hz₁)).sub_section
        ((hz₁.of_le (by norm_num)).smul_section (hdz z₀ hz₀)))

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **The angle-form integrand in the plane.** Read through `g` and `Complex.orthonormalBasisOneI`,
`dψ ∧ (z₀ dz₁ - z₁ dz₀)` on the standard basis is `dΨ ∧ Im (f⁻¹ df)` on `(1, i)`, for
`Ψ = ψ ∘ g` and `f = z₀ ∘ g + i z₁ ∘ g`, at a point where `z₀² + z₁² = 1`. -/
private theorem mpullback_wedge_angleForm_apply {g : EuclideanSpace ℝ (Fin 2) → M}
    {ψ z₀ z₁ : M → ℝ} {w : ℂ}
    (hg : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I 2 g (Complex.orthonormalBasisOneI.repr w))
    (hψ : ContMDiffAt I 𝓘(ℝ) 1 ψ (g (Complex.orthonormalBasisOneI.repr w)))
    (hz₀ : ContMDiffAt I 𝓘(ℝ) 2 z₀ (g (Complex.orthonormalBasisOneI.repr w)))
    (hz₁ : ContMDiffAt I 𝓘(ℝ) 2 z₁ (g (Complex.orthonormalBasisOneI.repr w)))
    (hz : z₀ (g (Complex.orthonormalBasisOneI.repr w)) ^ 2 +
      z₁ (g (Complex.orthonormalBasisOneI.repr w)) ^ 2 = 1) :
    mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g ((mextDeriv (RoughForm.ofFunction I ψ)).wedge
        (fun x ↦ z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
          z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x)) (Complex.orthonormalBasisOneI.repr w)
        (fun i ↦ EuclideanSpace.single i 1) =
      fderiv ℝ (fun w ↦ ψ (g (Complex.orthonormalBasisOneI.repr w))) w 1 *
          phaseForm (fun w ↦ (z₀ (g (Complex.orthonormalBasisOneI.repr w)) : ℂ) +
            z₁ (g (Complex.orthonormalBasisOneI.repr w)) * Complex.I) w (fun _ ↦ Complex.I) -
        fderiv ℝ (fun w ↦ ψ (g (Complex.orthonormalBasisOneI.repr w))) w Complex.I *
          phaseForm (fun w ↦ (z₀ (g (Complex.orthonormalBasisOneI.repr w)) : ℂ) +
            z₁ (g (Complex.orthonormalBasisOneI.repr w)) * Complex.I) w (fun _ ↦ 1) := by
  set e := Complex.orthonormalBasisOneI.repr
  have hgw := hg.mdifferentiableAt two_ne_zero
  have hZ {j : M → ℝ} (hj : ContMDiffAt I 𝓘(ℝ) 2 j (g (e w))) :
      DifferentiableAt ℝ (fun w ↦ j (g (e w))) w :=
    (contMDiffAt_iff_contDiffAt.1 (hj.comp w (hg.comp w
      (e.toContinuousLinearEquiv.contDiff.contMDiff w)))).differentiableAt two_ne_zero
  have hD : (fun i : Fin 2 ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g (e w)
      (EuclideanSpace.single i 1)) = ![mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g (e w) (e 1),
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g (e w) (e Complex.I)] := by
    funext i
    fin_cases i
    · simpa using congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g (e w))
        (Complex.orthonormalBasisOneI.repr_self 0).symm
    · simpa using congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g (e w))
        (Complex.orthonormalBasisOneI.repr_self 1).symm
  refine (mpullback_apply _ _ _ _).trans ?_
  rw [hD, wedge_angleForm_apply,
    mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr hgw (hψ.mdifferentiableAt one_ne_zero),
    mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr hgw (hψ.mdifferentiableAt one_ne_zero),
    mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr hgw (hz₀.mdifferentiableAt two_ne_zero),
    mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr hgw (hz₀.mdifferentiableAt two_ne_zero),
    mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr hgw (hz₁.mdifferentiableAt two_ne_zero),
    mvfderiv_apply_mfderiv_orthonormalBasisOneI_repr hgw (hz₁.mdifferentiableAt two_ne_zero),
    phaseForm_ofReal_add_ofReal_mul_I_apply (hZ hz₀) (hZ hz₁) hz,
    phaseForm_ofReal_add_ofReal_mul_I_apply (hZ hz₀) (hZ hz₁) hz]

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The planar step: the integrand read in `ℂ` integrates over the annulus to `-2π deg`, by the
cutoff integral of the phase form of `z ∘ g`. -/
private theorem setIntegral_annulus_angleForm_eq {g : EuclideanSpace ℝ (Fin 2) → M} {r b : ℝ}
    (hginj : InjOn g (closedBall 0 b))
    (hg₂ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) b,
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I 2 g x)
    (hr : 0 < r) (hrb : r ≤ b) {ψ z₀ z₁ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ) 1 ψ)
    (hψr : ∀ x ∈ closedBall 0 r, ψ (g x) = 1) (hψb : tsupport ψ ⊆ g '' ball 0 b)
    (hz₀ : ∀ x ∈ closedBall 0 b, x ≠ 0 → ContMDiffAt I 𝓘(ℝ) 2 z₀ (g x))
    (hz₁ : ∀ x ∈ closedBall 0 b, x ≠ 0 → ContMDiffAt I 𝓘(ℝ) 2 z₁ (g x))
    (hz : ∀ x ∈ closedBall 0 b, x ≠ 0 → z₀ (g x) ^ 2 + z₁ (g x) ^ 2 = 1)
    (d : C(Circle, Circle)) (hd : ∀ ζ : Circle,
      (d ζ : ℂ) = z₀ (g (Complex.orthonormalBasisOneI.repr (r * ζ))) +
        z₁ (g (Complex.orthonormalBasisOneI.repr (r * ζ))) * Complex.I) :
    ∫ w in {w : ℂ | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ b},
        (fderiv ℝ (fun w ↦ ψ (g (Complex.orthonormalBasisOneI.repr w))) w 1 *
            phaseForm (fun w ↦ (z₀ (g (Complex.orthonormalBasisOneI.repr w)) : ℂ) +
              z₁ (g (Complex.orthonormalBasisOneI.repr w)) * Complex.I) w (fun _ ↦ Complex.I) -
          fderiv ℝ (fun w ↦ ψ (g (Complex.orthonormalBasisOneI.repr w))) w Complex.I *
            phaseForm (fun w ↦ (z₀ (g (Complex.orthonormalBasisOneI.repr w)) : ℂ) +
              z₁ (g (Complex.orthonormalBasisOneI.repr w)) * Complex.I) w (fun _ ↦ 1)) =
      -(2 * π * Circle.degree d.toBasedLoop) := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  set f : ℂ → ℂ := fun w ↦ (z₀ (g (e w)) : ℂ) + z₁ (g (e w)) * Complex.I
  have hAb {w : ℂ} (hw : r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ b) : e w ∈ closedBall 0 b := by
    simpa using hw.2
  have hA0 {w : ℂ} (hw : r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ b) : e w ≠ 0 := by
    intro h
    have h1 := hw.1
    rw [sub_zero, ← e.norm_map, h, norm_zero] at h1
    linarith
  have hcomp {w : ℂ} (hw : r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ b) {φ : M → ℝ} {n : WithTop ℕ∞} (hn : n ≤ 2)
      (hφ : ContMDiffAt I 𝓘(ℝ) n φ (g (e w))) : ContDiffAt ℝ n (fun w ↦ φ (g (e w))) w :=
    contMDiffAt_iff_contDiffAt.1 (hφ.comp w (((hg₂ _ (hAb hw)).of_le hn).comp w
      (e.toContinuousLinearEquiv.contDiff.contMDiff w)))
  have hnorm {w : ℂ} (hw : r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ b) : Complex.normSq (f w) = 1 := by
    simp only [f, Complex.normSq_add_mul_I, hz _ (hAb hw) (hA0 hw)]
  have hcirc {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) : ‖e (circleMap 0 s θ)‖ = s := by
    rw [e.norm_map, norm_circleMap_zero, abs_of_nonneg hs]
  refine setIntegral_annulus_fderiv_mul_phaseForm_sub_eq_neg_two_pi_mul_degree hr.le hrb
    (fun w hw ↦ hcomp hw one_le_two hψ.contMDiffAt) (fun w hw ↦ ?_) (fun w hw ↦ ?_)
    (fun θ ↦ hψr _ (by simp [hcirc hr.le])) (fun θ ↦ ?_) d fun ζ ↦ ?_
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w
      (hcomp hw le_rfl (hz₀ _ (hAb hw) (hA0 hw)))).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp w
        (hcomp hw le_rfl (hz₁ _ (hAb hw) (hA0 hw)))).mul contDiffAt_const)
  · intro h
    simpa [h] using hnorm hw
  · -- The outer circle lies outside the support of `ψ`, by injectivity of `g`.
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    obtain ⟨y, hy, hyw⟩ := hψb h
    have hb : e (circleMap 0 b θ) ∈ closedBall 0 b := by simp [hcirc (hr.le.trans hrb)]
    rw [hginj (ball_subset_closedBall hy) hb hyw, mem_ball_zero_iff,
      hcirc (hr.le.trans hrb)] at hy
    exact lt_irrefl b hy
  · have hζ : r ≤ ‖(r : ℂ) * ζ - 0‖ ∧ ‖(r : ℂ) * ζ - 0‖ ≤ b := by
      simp only [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Circle.norm_coe, mul_one]
      exact ⟨le_rfl, hrb⟩
    have h1 : ‖f (r * ζ)‖ = 1 := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, hnorm hζ, Real.sqrt_one]
    rw [zero_add, hd ζ, h1, Complex.ofReal_one, div_one]

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- A function equal to `1` on `g (B(0, r))`, for an open embedding `g` of an open set containing
`B(0, r)`, is locally constant at every point of `g (B(0, r))`. -/
private theorem eventually_eq_of_mem_image_ball {U : Opens (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M}
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2)))) {r : ℝ}
    (hrU : ball (0 : EuclideanSpace ℝ (Fin 2)) r ⊆ U) {ψ : M → ℝ}
    (hψr : ∀ x ∈ ball 0 r, ψ (g x) = 1) {y : M} (hy : y ∈ g '' ball 0 r) :
    ∀ᶠ y' in 𝓝 y, ψ y' = ψ y := by
  have hs : g '' ball 0 r = (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))) ''
      ((↑) ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) r) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hrU hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hopen : IsOpen (g '' ball 0 r) := by
    rw [hs]
    exact hg.isOpenMap _ (isOpen_ball.preimage continuous_subtypeVal)
  obtain ⟨x, hx, rfl⟩ := hy
  filter_upwards [hopen.mem_nhds ⟨x, hx, rfl⟩] with y' ⟨x', hx', hy'⟩
  rw [← hy', hψr x' hx', hψr x hx]

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- A function supported in `g (B(0, b))` and equal to `1` on `g (B̄(0, r))`, for `r > 0` and `g`
injective on a set containing `B̄(0, b)`, forces `r < b`. -/
private theorem lt_of_forall_mem_closedBall_eq_one {U : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} (hginj : InjOn g U) {r b : ℝ} (hr : 0 < r)
    (hbU : closedBall (0 : EuclideanSpace ℝ (Fin 2)) b ⊆ U) {ψ : M → ℝ}
    (hψr : ∀ x ∈ closedBall 0 r, ψ (g x) = 1) (hψb : tsupport ψ ⊆ g '' ball 0 b) : r < b := by
  have hlt {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U) (h : ψ (g x) = 1) : ‖x‖ < b := by
    obtain ⟨y, hy, hyx⟩ := hψb (subset_tsupport _ (show ψ (g x) ≠ 0 by simp [h]))
    rw [← hginj (hbU (ball_subset_closedBall hy)) hx hyx]
    simpa using hy
  have hb : 0 < b := by
    obtain ⟨y, hy, -⟩ := hψb (subset_tsupport _
      (show ψ (g 0) ≠ 0 by simp [hψr 0 (mem_closedBall_self hr.le)]))
    exact (norm_nonneg y).trans_lt (by simpa using hy)
  -- Otherwise the point `b ∈ ℝ²` of norm `b` would lie in `B̄(0, r)`, where `ψ ∘ g = 1`.
  by_contra hbr
  have hx : ‖EuclideanSpace.single (0 : Fin 2) b‖ = b := by
    rw [EuclideanSpace.single, PiLp.norm_single, Real.norm_of_nonneg hb.le]
  exact (hlt (hbU (mem_closedBall_zero_iff.2 hx.le))
    (hψr _ (mem_closedBall_zero_iff.2 (hx.le.trans (not_lt.1 hbr))))).ne hx

/-- Through an oriented parametrization `g` of a neighbourhood of its support, the integral of
`dψ ∧ (z₀ dz₁ - z₁ dz₀)` is the planar integral of its pullback, read on `ℂ`. -/
private theorem integralTopForm_wedge_angleForm_eq_setIntegral
    (o : Manifold.Orientation I M (Fin 2)) {U : Opens (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M}
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) o g x)
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) (hbU : closedBall (0 : EuclideanSpace ℝ (Fin 2)) b ⊆ U)
    (hg₂ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) b,
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I 2 g x)
    {ψ z₀ z₁ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ) 1 ψ) (hψr : ∀ x ∈ ball 0 r, ψ (g x) = 1)
    (hψb : tsupport ψ ⊆ g '' ball 0 b)
    (hz₀ : ∀ x ∈ closedBall 0 b, x ≠ 0 → ContMDiffAt I 𝓘(ℝ) 2 z₀ (g x))
    (hz₁ : ∀ x ∈ closedBall 0 b, x ≠ 0 → ContMDiffAt I 𝓘(ℝ) 2 z₁ (g x)) :
    integralTopForm o ((mextDeriv (RoughForm.ofFunction I ψ)).wedge fun x ↦
        z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
          z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x) =
      ∫ w in closedBall (0 : ℂ) b, mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g
        ((mextDeriv (RoughForm.ofFunction I ψ)).wedge fun x ↦
          z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
            z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x)
        (Complex.orthonormalBasisOneI.repr w) (fun i ↦ EuclideanSpace.single i 1) := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  set β := (mextDeriv (RoughForm.ofFunction I ψ)).wedge fun x ↦
    z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x - z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x
  have hψ₁ {y : M} (hy : y ∈ g '' ball 0 r) := eventually_eq_of_mem_image_ball hg
    ((ball_subset_ball hrb.le).trans (ball_subset_closedBall.trans hbU)) hψr hy
  have hψ₀ {y : M} (hy : y ∉ tsupport ψ) : ∀ᶠ y' in 𝓝 y, ψ y' = ψ y := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with y' hy'
    rw [hy', image_eq_zero_of_notMem_tsupport hy, Pi.zero_apply]
  -- `β` is continuous with compact support in `g (B̄(0, b))`, hence integrable.
  have hβc : IsSmoothForm I 0 β := isSmoothForm_wedge_angleForm hψ fun y ↦ by
    by_cases h₁ : y ∈ g '' ball 0 r
    · exact Or.inl (hψ₁ h₁)
    by_cases h₂ : y ∈ tsupport ψ
    · obtain ⟨x, hxb, rfl⟩ := hψb h₂
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact h₁ ⟨0, mem_ball_self hr, rfl⟩
      exact Or.inr ⟨hz₀ x (ball_subset_closedBall hxb) hx0, hz₁ x (ball_subset_closedBall hxb) hx0⟩
    · exact Or.inl (hψ₀ h₂)
  have htsβ : _root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) β ⊆ tsupport ψ :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ hy (wedge_angleForm_eq_zero z₀ z₁ (hψ₀ h)))
      (isClosed_tsupport ψ)
  have hsupp : _root_.tsupport (α := E [⋀^Fin 2]→L[ℝ] ℝ) β ⊆ g '' closedBall 0 b :=
    htsβ.trans (hψb.trans (image_mono ball_subset_closedBall))
  have hβi : IntegrableTopForm β := hβc.integrableTopForm
    (((isCompact_closedBall 0 b).image_of_continuousOn fun x hx ↦
      (hg₂ x hx).continuousAt.continuousWithinAt).of_isClosed_subset (isClosed_tsupport _) hsupp)
    (Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm))
  -- Move the integral to the plane, and then to `ℂ`.
  rw [integralTopForm_eq_setIntegral_mpullback o isClosed_closedBall hbU hg ho hβi hsupp,
    ← e.measurePreserving.setIntegral_preimage_emb
      (e.coe_toHomeomorph ▸ e.toHomeomorph.measurableEmbedding),
    e.preimage_closedBall, map_zero]

/-- **The cutoff integral of an angle form around a puncture.** Let `o` orient a surface `M`,
and let `g : ℝ² → M` be an open embedding on an open set `U` containing `B̄(0, b)`, which
preserves orientation on `U` and is `C²` on `B̄(0, b)`. Let `z₀, z₁` be functions which are `C²`
with `z₀² + z₁² = 1` on `g (B̄(0, b) \ {0})`, and let `ψ` be a `C¹` function supported in
`g (B(0, b))` and equal to `1` on `g (B̄(0, r))`, for some `r > 0`. Then the integral of
`dψ ∧ (z₀ dz₁ - z₁ dz₀)` is `-2π` times the degree of the loop
`d ζ = z₀ (g (r ζ)) + i z₁ (g (r ζ))` of directions of `z` along the circle of radius `r`, where
`ℂ` is identified with `ℝ²` by `Complex.orthonormalBasisOneI`. -/
theorem integralTopForm_mextDeriv_ofFunction_wedge_eq_neg_two_pi_mul_degree
    (o : Manifold.Orientation I M (Fin 2)) {U : Opens (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M}
    (hg : IsOpenEmbedding (g ∘ ((↑) : U → EuclideanSpace ℝ (Fin 2))))
    (ho : ∀ x ∈ U, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.euclideanSpace 2) o g x)
    {r b : ℝ} (hr : 0 < r) (hbU : closedBall (0 : EuclideanSpace ℝ (Fin 2)) b ⊆ U)
    (hg₂ : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) b,
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I 2 g x)
    {ψ z₀ z₁ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ) 1 ψ) (hψr : ∀ x ∈ closedBall 0 r, ψ (g x) = 1)
    (hψb : tsupport ψ ⊆ g '' ball 0 b)
    (hz₀ : ∀ x ∈ closedBall 0 b, x ≠ 0 → ContMDiffAt I 𝓘(ℝ) 2 z₀ (g x))
    (hz₁ : ∀ x ∈ closedBall 0 b, x ≠ 0 → ContMDiffAt I 𝓘(ℝ) 2 z₁ (g x))
    (hz : ∀ x ∈ closedBall 0 b, x ≠ 0 → z₀ (g x) ^ 2 + z₁ (g x) ^ 2 = 1)
    (d : C(Circle, Circle)) (hd : ∀ ζ : Circle,
      (d ζ : ℂ) = z₀ (g (Complex.orthonormalBasisOneI.repr (r * ζ))) +
        z₁ (g (Complex.orthonormalBasisOneI.repr (r * ζ))) * Complex.I) :
    integralTopForm o ((mextDeriv (RoughForm.ofFunction I ψ)).wedge fun x ↦
        z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
          z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x) =
      -(2 * π * Circle.degree d.toBasedLoop) := by
  set e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hginj {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U) (hy : y ∈ U) (h : g x = g y) :
      x = y :=
    congrArg Subtype.val (hg.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)
  have hbU' : ball (0 : EuclideanSpace ℝ (Fin 2)) b ⊆ U := ball_subset_closedBall.trans hbU
  have hrb : r < b := lt_of_forall_mem_closedBall_eq_one (fun _ hx _ hy h ↦ hginj hx hy h) hr hbU
    hψr hψb
  have hψr' (x) (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) r) :=
    hψr x (ball_subset_closedBall hx)
  rw [integralTopForm_wedge_angleForm_eq_setIntegral o hg ho hr hrb hbU hg₂ hψ hψr' hψb hz₀ hz₁]
  -- Off the annulus `r ≤ ‖w‖ ≤ b` the integrand vanishes, since `ψ` is `1` on `g (B(0, r))`.
  set A : Set ℂ := {w | r ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ b}
  have hvan (w : ℂ) (hw : w ∈ closedBall 0 b \ A) :
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I g
        ((mextDeriv (RoughForm.ofFunction I ψ)).wedge fun x ↦
          z₀ x • mextDeriv (RoughForm.ofFunction I z₁) x -
            z₁ x • mextDeriv (RoughForm.ofFunction I z₀) x) (e w)
        (fun i ↦ EuclideanSpace.single i 1) = 0 := by
    have hwr : ‖w‖ < r := by
      by_contra h
      exact hw.2 ⟨by simpa using not_lt.1 h, by simpa using hw.1⟩
    refine (mpullback_apply _ _ _ _).trans ?_
    rw [wedge_angleForm_eq_zero z₀ z₁ (eventually_eq_of_mem_image_ball hg
      ((ball_subset_ball hrb.le).trans hbU') hψr' ⟨e w, by simpa using hwr, rfl⟩)]
    -- The zero alternating map vanishes on the basis vectors read as tangent vectors.
    rfl
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_closedBall
    (fun w hw ↦ by simpa using hw.2) hvan]
  -- On the annulus it is the integrand of the cutoff integral of the phase form of `z ∘ g`.
  have hAb {w : ℂ} (hw : w ∈ A) : e w ∈ closedBall 0 b := by simpa using hw.2
  have hA0 {w : ℂ} (hw : w ∈ A) : e w ≠ 0 := by
    intro h
    have h1 := hw.1
    rw [sub_zero, ← e.norm_map, h, norm_zero] at h1
    linarith
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const (measurable_id.sub_const 0).norm).inter
      (measurableSet_le (measurable_id.sub_const 0).norm measurable_const)
  have hpt (w : ℂ) (hw : w ∈ A) := mpullback_wedge_angleForm_apply (hg₂ _ (hAb hw))
    hψ.contMDiffAt (hz₀ _ (hAb hw) (hA0 hw)) (hz₁ _ (hAb hw) (hA0 hw)) (hz _ (hAb hw) (hA0 hw))
  refine (setIntegral_congr_fun hAm hpt).trans ?_
  exact setIntegral_annulus_angleForm_eq (fun x hx y hy h ↦ hginj (hbU hx) (hbU hy) h) hg₂ hr
    hrb.le hψ hψr hψb hz₀ hz₁ hz d hd

end TauCeti
