/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.FubiniStudy
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Hopf
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Descent
public import TauCeti.Geometry.Symplectic.Manifold.Rescale
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# The Fubini–Study symplectic form of complex projective space

Complex projective space `CPⁿ` is the quotient of the unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` by the circle
acting by unit scalars, and the Hopf projection `TauCeti.ComplexProjectiveSpace.mk` is a smooth
submersion onto it (`TauCeti.ComplexProjectiveSpace.isSubmersion_mk`). This file constructs the
**Fubini–Study form** `ω_FS` of `CPⁿ` as the symplectic reduction of `ℂⁿ⁺¹` by the diagonal circle:
it is the unique two-form on `CPⁿ` whose pullback to `S²ⁿ⁺¹` is `1 / π` times the restriction of
the symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹` (`TauCeti.imInnerSymplecticForm`),

`mk^* ω_FS = π⁻¹ i^* Im ⟪·, ·⟫_ℂ`,

for the inclusion `i : S²ⁿ⁺¹ → ℂⁿ⁺¹`. So `ω_FS(dmk u, dmk w) = Im ⟪u, w⟫_ℂ / π` for tangent
vectors `u, w` of the sphere read in `ℂⁿ⁺¹`
(`TauCeti.ComplexProjectiveSpace.eval₂_fubiniStudyForm_mfderiv_mk`), and `ω_FS` is symplectic
(`TauCeti.ComplexProjectiveSpace.isSymplectic_fubiniStudyForm`).

* **Basicness.** Unit scalars are unitary, so they preserve `Im ⟪·, ·⟫_ℂ` and its restriction to
  the sphere; their orbits are the fibres of `mk`.
* **Null directions.** At a point `x` of the sphere the tangent space is the real orthogonal
  complement of `x`, and `Im ⟪v, w⟫_ℂ = ⟪i v, w⟫_ℝ`. So a tangent vector `v` is null for the
  restricted form exactly when `i v` is a real multiple of `x`, that is, when `v` is a real multiple
  of `i x` (`TauCeti.ComplexProjectiveSpace.ker_bilinFormAt_mpullback_coe_sphere`). These are
  exactly the vertical vectors of `mk` (`TauCeti.ComplexProjectiveSpace.ker_mfderiv_mk`), so the
  descended form is nondegenerate; it is closed because the restricted form is.

**The Fubini–Study Hermitian form.** On a unit vector `x` and representatives real-orthogonal to
`x`, the imaginary part of the homogeneous Fubini–Study Hermitian form
`TauCeti.fubiniStudyHermitian` is `Im ⟪v, w⟫_ℂ / π`
(`TauCeti.im_fubiniStudyHermitian_of_re_inner_eq_zero`). So `ω_FS` is the imaginary part of the
Fubini–Study Hermitian metric
(`TauCeti.ComplexProjectiveSpace.eval₂_fubiniStudyForm_mfderiv_mk_eq_im_fubiniStudyHermitian`),
with the normalization `ω_FS = (i / 2π) ∂ ∂bar log ‖z‖²` of that form. In the affine chart
`X_k ≠ 0`, pulled back along its parametrization `affineParam k`, it is the imaginary part of the
Hermitian form at the homogeneous coordinate vector `affineVector k z` on the lifts
`insertZeroL k v` of tangent vectors
(`TauCeti.ComplexProjectiveSpace.eval₂_mpullback_affineParam_fubiniStudyForm`), whose coordinate
expression is `TauCeti.ComplexProjectiveSpace.fubiniStudyHermitian_affineVector_insertZeroL`. The
derivative of the unit representative `a(z) / ‖a(z)‖` differs from `‖a(z)‖⁻¹` times the lift by a
real multiple of `a(z)`, which the Hermitian form does not see.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.fubiniStudyForm n`: the Fubini–Study form of `CPⁿ`.

## Main results

* `TauCeti.ComplexProjectiveSpace.ker_bilinFormAt_mpullback_coe_sphere`: the null directions of
  the restriction of `Im ⟪·, ·⟫_ℂ` to `S²ⁿ⁺¹` at `x` are the real multiples of `i x`.
* `TauCeti.ComplexProjectiveSpace.mpullback_smul_mpullback_coe_sphere`: this restriction is
  invariant under the circle acting by unit scalars.
* `TauCeti.ComplexProjectiveSpace.mpullback_mk_fubiniStudyForm`: its pullback to the sphere is
  `π⁻¹` times the restriction of `Im ⟪·, ·⟫_ℂ`.
* `TauCeti.ComplexProjectiveSpace.eq_fubiniStudyForm_iff`: it is the only two-form with this
  pullback.
* `TauCeti.ComplexProjectiveSpace.eval₂_fubiniStudyForm_mfderiv_mk`: its values on images of
  tangent vectors of the sphere.
* `TauCeti.ComplexProjectiveSpace.isSymplectic_fubiniStudyForm`: it is symplectic.
* `TauCeti.ComplexProjectiveSpace.eval₂_fubiniStudyForm_mfderiv_mk_eq_im_fubiniStudyHermitian`:
  it is the imaginary part of the homogeneous Fubini–Study Hermitian form.
* `TauCeti.ComplexProjectiveSpace.eval₂_mpullback_affineParam_fubiniStudyForm`: its expression in
  the affine chart `X_k ≠ 0`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (symplectic reduction, with `CPⁿ` as the reduction of `ℂⁿ⁺¹` by the
  diagonal circle).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 5.4 (symplectic reduction).
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter VI, (4.4) (the
  normalization `ω_FS = (i / 2π) ∂ ∂bar log ‖z‖²`).
-/

public section

noncomputable section

open Complex (I)
open Function Metric Set
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### The restriction of `Im ⟪·, ·⟫_ℂ` to the sphere -/

/-- The restriction to `S²ⁿ⁺¹` of the symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹`. -/
private abbrev sphereForm (n : ℕ) :
    SmoothTwoForm (𝓡 (2 * n + 1)) (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :=
  SmoothForm.mpullback
    ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
    contMDiff_coe_sphere (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth

/-- The restricted form evaluates as `Im ⟪·, ·⟫_ℂ` on the tangent vectors read in `ℂⁿ⁺¹`. -/
private theorem eval₂_sphereForm (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (u w : TangentSpace (𝓡 (2 * n + 1)) x) :
    SmoothBundleForm.eval₂ (sphereForm n) x u w =
      (⟪mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x u,
        mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x w⟫_ℂ).im := by
  rw [SmoothForm.eval₂_mpullback, SymplecticForm.eval₂_constSmooth_mfderiv_eq,
    imInnerSymplecticForm_apply]

/-- **The null directions of the restriction of `Im ⟪·, ·⟫_ℂ` to the sphere** at `x` are the
tangent vectors carried by the inclusion to real multiples of `i x`: the characteristic foliation
of `S²ⁿ⁺¹ ⊂ ℂⁿ⁺¹` is the foliation by the orbits of the circle acting by unit scalars. -/
theorem ker_bilinFormAt_mpullback_coe_sphere
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    LinearMap.ker ((SmoothForm.mpullback
        ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
        contMDiff_coe_sphere
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth).bilinFormAt x) =
      (ℝ ∙ (I • (x : EuclideanSpace ℂ (Fin (n + 1))))).comap
        (mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x).toLinearMap := by
  set D := mvfderiv (𝓡 (2 * n + 1))
    ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1))) x
  -- Tangent vectors are read in `ℂⁿ⁺¹` as vectors real-orthogonal to `x`.
  have horth (w : TangentSpace (𝓡 (2 * n + 1)) x) :
      ⟪(x : EuclideanSpace ℂ (Fin (n + 1))), D w⟫_ℝ = 0 :=
    inner_coe_mvfderiv_subtypeVal_sphere x w
  -- `Im ⟪v, w⟫_ℂ = ⟪i v, w⟫_ℝ`.
  have him (v w : EuclideanSpace ℂ (Fin (n + 1))) : (⟪v, w⟫_ℂ).im = ⟪I • v, w⟫_ℝ := by
    rw [EuclideanSpace.real_inner_eq_re_inner, inner_smul_left]
    simp
  ext u
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_span_singleton,
    ContinuousLinearMap.coe_coe, LinearMap.ext_iff, SmoothForm.bilinFormAt_apply,
    LinearMap.zero_apply, eval₂_sphereForm]
  constructor
  · intro h
    -- The component `y` of `i (D u)` orthogonal to `x` is the image of a tangent vector, and
    -- `0 = Im ⟪D u, y⟫_ℂ = ⟪i (D u), y⟫_ℝ = ‖y‖²`.
    set s : ℝ := ⟪(x : EuclideanSpace ℂ (Fin (n + 1))), I • D u⟫_ℝ
    set y : EuclideanSpace ℂ (Fin (n + 1)) := I • D u - s • (x : EuclideanSpace ℂ (Fin (n + 1)))
    have hx :
        ⟪(x : EuclideanSpace ℂ (Fin (n + 1))), (x : EuclideanSpace ℂ (Fin (n + 1)))⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow]
    have hy : ⟪(x : EuclideanSpace ℂ (Fin (n + 1))), y⟫_ℝ = 0 := by
      rw [inner_sub_right, real_inner_smul_right, hx, mul_one, sub_self]
    obtain ⟨w, hw⟩ := exists_mvfderiv_coe_sphere_eq (n := 2 * n + 1) x hy
    have hyy : ⟪y, y⟫_ℝ = 0 := by
      have h0 := h w
      rw [hw, him] at h0
      have hsplit : I • D u = y + s • (x : EuclideanSpace ℂ (Fin (n + 1))) := by
        rw [sub_add_cancel]
      rw [hsplit, inner_add_left, real_inner_smul_left, real_inner_comm, hy, mul_zero,
        add_zero] at h0
      exact h0
    have hy0 : y = 0 := inner_self_eq_zero.1 hyy
    -- So `i (D u) = s x`, and `D u = (-s) (i x)`.
    refine ⟨-s, ?_⟩
    have hIu : I • D u = s • (x : EuclideanSpace ℂ (Fin (n + 1))) := sub_eq_zero.1 hy0
    calc (-s) • I • (x : EuclideanSpace ℂ (Fin (n + 1)))
        = -(I • (s • (x : EuclideanSpace ℂ (Fin (n + 1))))) := by
          rw [neg_smul, smul_comm]
      _ = D u := by
          rw [← hIu, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  · rintro ⟨t, ht⟩ w
    -- `i (t (i x)) = (-t) x` is real-orthogonal to the tangent vectors.
    have hIt : I • t • I • (x : EuclideanSpace ℂ (Fin (n + 1))) =
        (-t) • (x : EuclideanSpace ℂ (Fin (n + 1))) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t, RCLike.real_smul_eq_coe_smul (K := ℂ) (-t),
        smul_smul, smul_smul]
      congr 1
      push_cast
      linear_combination (t : ℂ) * Complex.I_sq
    rw [← ht, him, hIt, real_inner_smul_left, horth, mul_zero]

/-- **The restriction of `Im ⟪·, ·⟫_ℂ` to the sphere is invariant under the circle** acting by
unit scalars, which acts on `ℂⁿ⁺¹` by unitary maps. -/
theorem mpullback_smul_mpullback_coe_sphere (c : Circle) :
    SmoothForm.mpullback (fun z : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦ c • z)
        (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) c)
        (SmoothForm.mpullback
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          (contMDiff_coe_sphere (n := 2 * n + 1))
          (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth) =
      SmoothForm.mpullback
        ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
        contMDiff_coe_sphere
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth := by
  -- Multiplication by `c` on `ℂⁿ⁺¹`, as a real linear map.
  let L : EuclideanSpace ℂ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℂ (Fin (n + 1)) :=
    ((c : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (n + 1)))).restrictScalars ℝ
  have hL : SmoothForm.mpullback L L.contMDiff
      (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth =
      (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth := by
    refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
    rw [SmoothForm.eval₂_mpullback, SymplecticForm.eval₂_constSmooth_mfderiv_eq,
      SymplecticForm.fromTangentSpace_constSmooth_apply, mvfderiv_eq_fderiv, L.fderiv]
    have hc (a b : EuclideanSpace ℂ (Fin (n + 1))) :
        (⟪(c : ℂ) • a, (c : ℂ) • b⟫_ℂ).im = (⟪a, b⟫_ℂ).im := by
      rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', Circle.norm_coe]
      simp
    simpa [L] using hc _ _
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_coe_sphere L.contMDiff
    (funext fun z ↦ Circle.coe_smul_sphere c z), hL]

/-- The restricted form is basic for the Hopf projection: it is invariant under the circle, whose
orbits are the fibres of `mk`, and the vertical vectors of `mk` are its null directions. -/
private theorem isBasic_sphereForm :
    RoughForm.IsBasic (V := ℝ) 𝓘(ℝ, Fin n → ℂ) (mk n) (sphereForm n).val :=
  SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le (τ := fun (c : Circle) z ↦ c • z)
    ((contMDiff_mk ∞).mdifferentiable (by simp))
    (fun c ↦ (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) c (n := ∞)).mdifferentiable
      (by simp))
    (fun c ↦ funext fun z ↦ mk_circle_smul n c z)
    (fun x y h ↦ .inr ((mk_eq_mk_iff_exists_circle_smul n y x).1 h.symm))
    (fun x ↦ (ker_mfderiv_mk x).trans_le (ker_bilinFormAt_mpullback_coe_sphere x).ge)
    fun c ↦ by
      simpa only [SmoothForm.coe_mpullback] using
        congrArg Subtype.val (mpullback_smul_mpullback_coe_sphere c)

/-! ### The Fubini–Study form -/

variable (n) in
/-- **The Fubini–Study form** of complex projective space `CPⁿ`: the descent along the Hopf
projection `mk : S²ⁿ⁺¹ → CPⁿ` of `1 / π` times the restriction to `S²ⁿ⁺¹` of the symplectic form
`Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹`. It is the unique two-form with this pullback
(`TauCeti.ComplexProjectiveSpace.eq_fubiniStudyForm_iff`), and it is symplectic
(`TauCeti.ComplexProjectiveSpace.isSymplectic_fubiniStudyForm`). -/
def fubiniStudyForm : SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ComplexProjectiveSpace n) :=
  Real.pi⁻¹ • SmoothForm.descendedForm (isSubmersion_mk ∞) (mk_surjective n) (sphereForm n)
    isBasic_sphereForm

/-- **The pullback of the Fubini–Study form to the sphere** is `1 / π` times the restriction to
`S²ⁿ⁺¹` of the symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹`. -/
theorem mpullback_mk_fubiniStudyForm :
    SmoothForm.mpullback (mk n) (contMDiff_mk ∞) (fubiniStudyForm n) =
      Real.pi⁻¹ • SmoothForm.mpullback
        ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
        contMDiff_coe_sphere
        (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth := by
  rw [fubiniStudyForm, SmoothForm.mpullback_smul]
  exact congrArg (Real.pi⁻¹ • ·) SmoothForm.mpullback_descendedForm

/-- **The Fubini–Study form is characterized by its pullback to the sphere**: a two-form on `CPⁿ`
is the Fubini–Study form exactly when its pullback along the Hopf projection is `1 / π` times the
restriction to `S²ⁿ⁺¹` of the symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ⁺¹`. -/
theorem eq_fubiniStudyForm_iff {η : SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ComplexProjectiveSpace n)} :
    η = fubiniStudyForm n ↔
      SmoothForm.mpullback (mk n) (contMDiff_mk ∞) η =
        Real.pi⁻¹ • SmoothForm.mpullback
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          contMDiff_coe_sphere
          (imInnerSymplecticForm (EuclideanSpace ℂ (Fin (n + 1)))).constSmooth := by
  rw [← mpullback_mk_fubiniStudyForm]
  exact (SmoothForm.mpullback_injective_of_surjective (contMDiff_mk ∞) (mk_surjective n)
    surjective_mfderiv_mk).eq_iff.symm

/-- **The Fubini–Study form on the image of the sphere.** For tangent vectors `u, w` of `S²ⁿ⁺¹` at
`x`, read in `ℂⁿ⁺¹`, the Fubini–Study form takes the value `Im ⟪u, w⟫_ℂ / π` on their images under
the derivative of the Hopf projection. As this derivative is onto, this determines the form. -/
theorem eval₂_fubiniStudyForm_mfderiv_mk (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (u w : TangentSpace (𝓡 (2 * n + 1)) x) :
    SmoothBundleForm.eval₂ (fubiniStudyForm n) (mk n x)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (mk n) x u)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (mk n) x w) =
      (⟪mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x u,
        mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x w⟫_ℂ).im / Real.pi := by
  rw [← SmoothForm.eval₂_mpullback (mk n) (contMDiff_mk ∞), mpullback_mk_fubiniStudyForm,
    SmoothForm.eval₂_smul, eval₂_sphereForm, smul_eq_mul, inv_mul_eq_div]

/-- **The Fubini–Study form is symplectic.** It is closed since the restriction of the closed form
`Im ⟪·, ·⟫_ℂ` to the sphere is, and nondegenerate since the null directions of that restriction,
the real multiples of `i x` at `x`, are exactly the vertical directions of the Hopf projection. -/
theorem isSymplectic_fubiniStudyForm : (fubiniStudyForm n).IsSymplectic :=
  (SmoothTwoForm.isSymplectic_descendedForm_iff.2
    ⟨(SymplecticForm.isClosed_constSmooth _).mpullback _ contMDiff_coe_sphere,
      fun x ↦ (ker_bilinFormAt_mpullback_coe_sphere x).trans (ker_mfderiv_mk x).symm⟩).smul _
    (inv_ne_zero Real.pi_ne_zero)

/-! ### The Fubini–Study form and the Fubini–Study Hermitian form -/

/-- **The Fubini–Study form is the imaginary part of the Fubini–Study Hermitian form.** At the
image `[x]` of a point `x` of `S²ⁿ⁺¹`, the Fubini–Study form takes on the images of tangent vectors
`u, w` of the sphere the value `Im H_x(u, w)` of the homogeneous Fubini–Study Hermitian form
`TauCeti.fubiniStudyHermitian`, with `u` and `w` read in `ℂⁿ⁺¹` as representatives of tangent
vectors of `CPⁿ` at `[x]`. -/
theorem eval₂_fubiniStudyForm_mfderiv_mk_eq_im_fubiniStudyHermitian
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (u w : TangentSpace (𝓡 (2 * n + 1)) x) :
    SmoothBundleForm.eval₂ (fubiniStudyForm n) (mk n x)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (mk n) x u)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (mk n) x w) =
      (fubiniStudyHermitian ℂ (x : EuclideanSpace ℂ (Fin (n + 1)))
        (mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x u)
        (mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x w)).im := by
  have horth (v : TangentSpace (𝓡 (2 * n + 1)) x) :
      RCLike.re ⟪(x : EuclideanSpace ℂ (Fin (n + 1))),
        mvfderiv (𝓡 (2 * n + 1))
          ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))
          x v⟫_ℂ = 0 := by
    rw [RCLike.re_to_complex, ← EuclideanSpace.real_inner_eq_re_inner]
    exact inner_coe_mvfderiv_subtypeVal_sphere x v
  rw [eval₂_fubiniStudyForm_mfderiv_mk]
  simpa using (im_fubiniStudyHermitian_of_re_inner_eq_zero (norm_eq_of_mem_sphere x) (horth u)
    (horth w)).symm

/-- The derivative of the unit representative `z ↦ a(z) / ‖a(z)‖` of the affine point `z` of the
chart `X_k ≠ 0`, `a = affineVector k`, is `‖a(z)‖⁻¹` times the lift `insertZeroL k v` plus a real
multiple of `a(z)`. -/
private theorem exists_fderiv_coe_affineUnitVector (k : Fin (n + 1)) (z : Fin n → ℂ) :
    ∃ φ : (Fin n → ℂ) →L[ℝ] ℝ, ∀ v : Fin n → ℂ,
      fderiv ℝ (fun y ↦ (affineUnitVector k y : EuclideanSpace ℂ (Fin (n + 1)))) z v =
        ‖affineVector k z‖⁻¹ • insertZeroL k v + φ v • affineVector k z := by
  have ha : HasFDerivAt (affineVector k) ((insertZeroL k).restrictScalars ℝ) z :=
    (hasFDerivAt_affineVector k z).restrictScalars ℝ
  have hg : DifferentiableAt ℝ (fun y ↦ ‖affineVector k y‖⁻¹) z :=
    (ha.differentiableAt.norm ℝ (affineVector_ne_zero k z)).inv
      (norm_ne_zero_iff.2 (affineVector_ne_zero k z))
  have hN : (fun y ↦ (affineUnitVector k y : EuclideanSpace ℂ (Fin (n + 1)))) =
      fun y ↦ ‖affineVector k y‖⁻¹ • affineVector k y :=
    funext (coe_affineUnitVector_apply k)
  refine ⟨fderiv ℝ (fun y ↦ ‖affineVector k y‖⁻¹) z, fun v ↦ ?_⟩
  rw [hN]
  refine (congrArg (fun L ↦ L v) (hg.hasFDerivAt.smul ha).fderiv).trans ?_
  simp

/-- **The Fubini–Study form in an affine chart.** Pulled back along the parametrization
`affineParam k` of the chart `X_k ≠ 0`, the Fubini–Study form at the affine coordinates `z` is the
imaginary part of the homogeneous Fubini–Study Hermitian form at the homogeneous coordinate vector
`affineVector k z`, evaluated on the lifts `insertZeroL k v`, `insertZeroL k w` of the coordinate
tangent vectors. With `fubiniStudyHermitian_affineVector_insertZeroL` this is the coordinate
expression `ω_FS = (i / 2π) ∑ (δ_ij / r - conj (z_i) z_j / r²) dz_i ∧ dconj (z_j)`,
`r = 1 + ∑ |z_l|²`. -/
theorem eval₂_mpullback_affineParam_fubiniStudyForm (k : Fin (n + 1)) (z : Fin n → ℂ)
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) z) :
    SmoothBundleForm.eval₂
        (SmoothForm.mpullback (affineParam k) (contMDiff_affineParam_real k ∞) (fubiniStudyForm n))
        z v w =
      (fubiniStudyHermitian ℂ (affineVector k z) (insertZeroL k v) (insertZeroL k w)).im := by
  set x := affineUnitVector k z
  have hx : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) (affineUnitVector k) z :=
    (contMDiff_affineUnitVector (r := 1) k z).mdifferentiableAt one_ne_zero
  have hcoe : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1))) x :=
    (contMDiff_coe_sphere (m := 1) x).mdifferentiableAt one_ne_zero
  -- `affineParam k` is the Hopf projection of the unit representative.
  have hpull : SmoothForm.mpullback (affineParam k) (contMDiff_affineParam_real k ∞)
      (fubiniStudyForm n) = SmoothForm.mpullback (affineUnitVector k) (contMDiff_affineUnitVector k)
        (SmoothForm.mpullback (mk n) (contMDiff_mk ∞) (fubiniStudyForm n)) := by
    rw [SmoothForm.mpullback_mpullback]
    exact SmoothForm.mpullback_congr _ _ (funext (affineParam_def k)) _
  -- Read in `ℂⁿ⁺¹`, the tangent vectors of the sphere are derivatives of the unit representative.
  have hD (u : TangentSpace 𝓘(ℝ, Fin n → ℂ) z) : mvfderiv (𝓡 (2 * n + 1))
      ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1))) x
        (mfderiv 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) (affineUnitVector k) z u) =
      fderiv ℝ (fun y ↦ (affineUnitVector k y : EuclideanSpace ℂ (Fin (n + 1)))) z u :=
    ((mvfderiv_comp_apply z hcoe hx u).symm.trans (mvfderiv_eq_fderiv_apply _ z u))
  rw [hpull, SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback]
  refine (eval₂_fubiniStudyForm_mfderiv_mk_eq_im_fubiniStudyHermitian x _ _).trans ?_
  obtain ⟨φ, hφ⟩ := exists_fderiv_coe_affineUnitVector k z
  rw [hD v, hD w, hφ v, hφ w, coe_affineUnitVector_apply]
  -- Remove the real normalization `c = ‖a‖⁻¹` and the multiples of `a = affineVector k z`.
  set a := affineVector k z
  set c : ℂ := ((‖a‖⁻¹ : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    have ha : a ≠ 0 := affineVector_ne_zero k z
    simp [c, ha]
  have hsplit (u : Fin n → ℂ) :
      ‖a‖⁻¹ • insertZeroL k u + φ u • a = c • (insertZeroL k u + (c⁻¹ * φ u) • a) := by
    rw [smul_add, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul,
      RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ) (φ u)]
    -- `c` abbreviates the coefficient `((‖a‖⁻¹ : ℝ) : ℂ)` produced by the last rewrite.
    rfl
  rw [hsplit v, hsplit w, RCLike.real_smul_eq_coe_smul (K := ℂ) ‖a‖⁻¹ a]
  -- The base point is now `c • a`; the lemmas are applied up to the abbreviation `c` and the
  -- reading of tangent vectors of the chart as vectors of `Fin n → ℂ`, so they are closed by
  -- `exact` rather than rewritten.
  exact congrArg Complex.im ((fubiniStudyHermitian_smul_apply_smul_smul hc _ _ _).trans
    (fubiniStudyHermitian_apply_add_smul_add_smul _ _ _ _ _))

end TauCeti.ComplexProjectiveSpace
