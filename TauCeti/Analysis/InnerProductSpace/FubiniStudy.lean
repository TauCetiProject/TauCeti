/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The homogeneous Fubini–Study Hermitian form

For a vector `z` of an inner product space `E` over `𝕜 = ℝ` or `ℂ`, the *homogeneous Fubini–Study
Hermitian form* at `z` is the sesquilinear form

`H_z(v, w) = (‖z‖² ⟪v, w⟫ - ⟪v, z⟫ ⟪z, w⟫) / (π ‖z‖⁴)`,

conjugate-linear in `v` and linear in `w`, as is Mathlib's inner product. For `𝕜 = ℂ` this is the
Fubini–Study Hermitian metric of the projective space of `E`, with the normalization
`ω_FS = (i / 2π) ∂ ∂bar log ‖z‖²`, written on homogeneous representatives: a tangent vector at the
line `[z]` is represented by a vector `v` of `E`, up to adding multiples of `z`. Its value on the
lifts of the coordinate vectors of an affine chart of `CPⁿ` is computed in
`TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.FubiniStudy`.

The results below are the facts that make this a well-defined metric on the projective tangent
space. `H_z` is Hermitian. It is `⟪Pv, Pw⟫ / (π ‖z‖²)`, where `P` is the orthogonal projection onto
`(𝕜 ∙ z)ᗮ`. Hence it is positive semidefinite, for `z ≠ 0` its kernel is the line `𝕜 ∙ z`, and
it is unchanged when multiples of `z` are added to its arguments; so it depends only on the
classes of its arguments in `E ⧸ 𝕜 ∙ z`, on which it is positive definite. It is unchanged when the
base point and both arguments are rescaled by the same nonzero scalar
(`H_{cz}(cv, cw) = H_z(v, w)`), so it does not depend on the representative of the line, and it is
preserved by linear isometries, so unitary maps act by isometries of the projective metric. At
`z = 0` the formula gives the zero form.

## Main definitions

* `TauCeti.fubiniStudyHermitian 𝕜 z`: the sesquilinear form `H_z`.

## Main results

* `TauCeti.fubiniStudyHermitian_apply_eq_inner_starProjection`: `H_z(v, w)` is the inner product
  of the projections of `v` and `w` onto `(𝕜 ∙ z)ᗮ`, divided by `π ‖z‖²`.
* `TauCeti.isSymm_fubiniStudyHermitian`: `H_z` is Hermitian.
* `TauCeti.re_fubiniStudyHermitian_apply_self_pos_iff`, `TauCeti.ker_fubiniStudyHermitian`: for
  `z ≠ 0`, `H_z` is positive away from the line `𝕜 ∙ z`, which is its kernel.
* `TauCeti.fubiniStudyHermitian_apply_add_smul_add_smul`: `H_z` is unchanged when multiples of
  `z` are added to its arguments.
* `TauCeti.fubiniStudyHermitian_smul_apply_smul_smul`: `H_{cz}(cv, cw) = H_z(v, w)` for `c ≠ 0`.
* `LinearIsometry.fubiniStudyHermitian_map_map_map`: linear isometries preserve `H`.
* `TauCeti.im_fubiniStudyHermitian_of_re_inner_eq_zero`: at a unit vector `z`, on representatives
  real-orthogonal to `z`, the imaginary part of `H_z(v, w)` is `Im ⟪v, w⟫ / π`.

## References

* W. Ballmann, *Lectures on Kähler Manifolds*, ESI Lectures in Mathematics and Physics, EMS,
  2006, §4, Example 5, (4.12)–(4.14).
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter VI, (4.4) (for the
  normalization `(i / 2π) ∂ ∂bar log ‖z‖²`).
-/

public section

open RCLike Real
open scoped InnerProductSpace ComplexConjugate

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (𝕜) in
/-- The **homogeneous Fubini–Study Hermitian form** at `z`,
`H_z(v, w) = (‖z‖² ⟪v, w⟫ - ⟪v, z⟫ ⟪z, w⟫) / (π ‖z‖⁴)`, conjugate-linear in `v` and linear in `w`.
For `𝕜 = ℂ` and `z ≠ 0` it is the Fubini–Study Hermitian metric of the projective space of `E` at
the line `[z]`, evaluated on homogeneous representatives `v`, `w` of tangent vectors. -/
noncomputable def fubiniStudyHermitian (z : E) : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _
    (fun v w ↦ (((‖z‖ ^ 2 : ℝ) : 𝕜) * ⟪v, w⟫_𝕜 - ⟪v, z⟫_𝕜 * ⟪z, w⟫_𝕜) / ((π * ‖z‖ ^ 4 : ℝ) : 𝕜))
    (fun _ _ _ ↦ by simp only [inner_add_left]; ring)
    (fun _ _ _ ↦ by simp only [inner_smul_left, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [inner_add_right]; ring)
    (fun _ _ _ ↦ by simp only [inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring)

/-- The defining formula of the homogeneous Fubini–Study Hermitian form. -/
theorem fubiniStudyHermitian_apply (z v w : E) :
    fubiniStudyHermitian 𝕜 z v w =
      (((‖z‖ ^ 2 : ℝ) : 𝕜) * ⟪v, w⟫_𝕜 - ⟪v, z⟫_𝕜 * ⟪z, w⟫_𝕜) / ((π * ‖z‖ ^ 4 : ℝ) : 𝕜) :=
  (rfl)

/-- At the zero vector the homogeneous Fubini–Study form is zero. -/
@[simp]
theorem fubiniStudyHermitian_zero : fubiniStudyHermitian 𝕜 (0 : E) = 0 := by
  ext v w
  simp [fubiniStudyHermitian_apply]

/-- The homogeneous Fubini–Study form `H_z(v, w)` is the inner product of the orthogonal
projections of `v` and `w` onto the hyperplane `(𝕜 ∙ z)ᗮ`, divided by `π ‖z‖²`. -/
theorem fubiniStudyHermitian_apply_eq_inner_starProjection (z v w : E) :
    fubiniStudyHermitian 𝕜 z v w =
      ⟪(𝕜 ∙ z)ᗮ.starProjection v, (𝕜 ∙ z)ᗮ.starProjection w⟫_𝕜 / ((π * ‖z‖ ^ 2 : ℝ) : 𝕜) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hN : (‖z‖ : 𝕜) ≠ 0 := by simpa using hz
  have hπ : ((π : ℝ) : 𝕜) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  simp only [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, map_div₀, conj_ofReal,
    inner_conj_symm, inner_self_eq_norm_sq_to_K, fubiniStudyHermitian_apply]
  push_cast
  field_simp
  ring

/-- The homogeneous Fubini–Study form is Hermitian: `conj (H_z(v, w)) = H_z(w, v)`. -/
theorem isSymm_fubiniStudyHermitian (z : E) : (fubiniStudyHermitian 𝕜 z).IsSymm := by
  refine LinearMap.isSymm_def.2 fun v w ↦ ?_
  simp only [fubiniStudyHermitian_apply_eq_inner_starProjection, map_div₀,
    inner_conj_symm, conj_ofReal]

/-- The value `H_z(v, v)` is the real number `‖Pv‖² / (π ‖z‖²)`, where `P` is the orthogonal
projection onto `(𝕜 ∙ z)ᗮ`. -/
theorem fubiniStudyHermitian_apply_self (z v : E) :
    fubiniStudyHermitian 𝕜 z v v =
      ((‖(𝕜 ∙ z)ᗮ.starProjection v‖ ^ 2 / (π * ‖z‖ ^ 2) : ℝ) : 𝕜) := by
  rw [fubiniStudyHermitian_apply_eq_inner_starProjection, inner_self_eq_norm_sq_to_K,
    ← ofReal_pow, ← ofReal_div]

/-- The homogeneous Fubini–Study form is positive semidefinite. -/
theorem re_fubiniStudyHermitian_apply_self_nonneg (z v : E) :
    0 ≤ re (fubiniStudyHermitian 𝕜 z v v) := by
  rw [fubiniStudyHermitian_apply_self, ofReal_re]
  positivity

/-- The vectors `v` with `H_z(v, v) = 0` are exactly the multiples of `z ≠ 0`. -/
theorem fubiniStudyHermitian_apply_self_eq_zero_iff {z : E} (hz : z ≠ 0) {v : E} :
    fubiniStudyHermitian 𝕜 z v v = 0 ↔ v ∈ 𝕜 ∙ z := by
  have hzpos : 0 < π * ‖z‖ ^ 2 := by positivity
  rw [fubiniStudyHermitian_apply_self, ofReal_eq_zero, div_eq_zero_iff, or_iff_left hzpos.ne',
    sq_eq_zero_iff, norm_eq_zero, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.orthogonal_orthogonal]

/-- The homogeneous Fubini–Study form at `z ≠ 0` is positive exactly away from the line `𝕜 ∙ z`:
it is positive definite on `E ⧸ 𝕜 ∙ z`. -/
theorem re_fubiniStudyHermitian_apply_self_pos_iff {z : E} (hz : z ≠ 0) {v : E} :
    0 < re (fubiniStudyHermitian 𝕜 z v v) ↔ v ∉ 𝕜 ∙ z := by
  rw [← fubiniStudyHermitian_apply_self_eq_zero_iff hz, (re_fubiniStudyHermitian_apply_self_nonneg
    z v).lt_iff_ne', fubiniStudyHermitian_apply_self, ofReal_re, Ne, ofReal_eq_zero]

/-- The radial direction lies in the kernel of the homogeneous Fubini–Study form in its first
argument: `H_z(z, w) = 0`. -/
@[simp]
theorem fubiniStudyHermitian_self_left (z w : E) : fubiniStudyHermitian 𝕜 z z w = 0 := by
  rw [fubiniStudyHermitian_apply, inner_self_eq_norm_sq_to_K, ofReal_pow, sub_self, zero_div]

/-- The radial direction lies in the kernel of the homogeneous Fubini–Study form in its second
argument: `H_z(v, z) = 0`. -/
@[simp]
theorem fubiniStudyHermitian_self_right (z v : E) : fubiniStudyHermitian 𝕜 z v z = 0 := by
  rw [fubiniStudyHermitian_apply, inner_self_eq_norm_sq_to_K, ofReal_pow]
  ring

/-- The homogeneous Fubini–Study form is unchanged when multiples of `z` are added to its
arguments, so it descends to `E ⧸ 𝕜 ∙ z`. -/
theorem fubiniStudyHermitian_apply_add_smul_add_smul (z v w : E) (a b : 𝕜) :
    fubiniStudyHermitian 𝕜 z (v + a • z) (w + b • z) = fubiniStudyHermitian 𝕜 z v w := by
  simp

/-- The kernel of the homogeneous Fubini–Study form at `z ≠ 0` is the line `𝕜 ∙ z`. -/
theorem ker_fubiniStudyHermitian {z : E} (hz : z ≠ 0) :
    LinearMap.ker (fubiniStudyHermitian 𝕜 z) = 𝕜 ∙ z := by
  ext v
  refine ⟨fun hv ↦ (fubiniStudyHermitian_apply_self_eq_zero_iff hz).1 ?_, fun hv ↦ ?_⟩
  · rw [LinearMap.mem_ker.1 hv, LinearMap.zero_apply]
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    ext w
    simp

/-- Rescaling the base point by `c` divides the homogeneous Fubini–Study form by `‖c‖²`. -/
theorem fubiniStudyHermitian_smul_apply (c : 𝕜) (z v w : E) :
    fubiniStudyHermitian 𝕜 (c • z) v w =
      (((‖c‖ ^ 2)⁻¹ : ℝ) : 𝕜) * fubiniStudyHermitian 𝕜 z v w := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hC : (‖c‖ : 𝕜) ≠ 0 := by simpa using hc
  have hN : (‖z‖ : 𝕜) ≠ 0 := by simpa using hz
  have hπ : ((π : ℝ) : 𝕜) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  simp only [fubiniStudyHermitian_apply, inner_smul_right, inner_smul_left, norm_smul]
  push_cast
  field_simp
  linear_combination -(⟪v, z⟫_𝕜 * ⟪z, w⟫_𝕜) * RCLike.conj_mul c

/-- The homogeneous Fubini–Study form does not depend on the representative of the line:
`H_{cz}(cv, cw) = H_z(v, w)` for every nonzero scalar `c`. -/
theorem fubiniStudyHermitian_smul_apply_smul_smul {c : 𝕜} (hc : c ≠ 0) (z v w : E) :
    fubiniStudyHermitian 𝕜 (c • z) (c • v) (c • w) = fubiniStudyHermitian 𝕜 z v w := by
  have hC : (‖c‖ : 𝕜) ≠ 0 := by simpa using hc
  simp only [fubiniStudyHermitian_smul_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul,
    smul_eq_mul]
  push_cast
  rw [← mul_assoc, RCLike.conj_mul]
  field_simp

/-- Linear isometries preserve the homogeneous Fubini–Study form:
`H_{f z}(f v, f w) = H_z(v, w)`. In particular unitary maps act by isometries of the
Fubini–Study metric. -/
@[simp]
theorem _root_.LinearIsometry.fubiniStudyHermitian_map_map_map (f : E →ₗᵢ[𝕜] F)
    (z v w : E) :
    fubiniStudyHermitian 𝕜 (f z) (f v) (f w) = fubiniStudyHermitian 𝕜 z v w := by
  simp only [fubiniStudyHermitian_apply, LinearIsometry.inner_map_map, LinearIsometry.norm_map]

/-- **The imaginary part on representatives tangent to the sphere.** At a unit vector `z`, on
representatives `v`, `w` real-orthogonal to `z`, the imaginary part of the homogeneous
Fubini–Study form is `Im ⟪v, w⟫ / π`: the inner products `⟪v, z⟫` and `⟪z, w⟫` are then purely
imaginary, so their product is real. This is the Fubini–Study symplectic form read on the unit
sphere. -/
theorem im_fubiniStudyHermitian_of_re_inner_eq_zero {z v w : E} (hz : ‖z‖ = 1)
    (hv : re ⟪z, v⟫_𝕜 = 0) (hw : re ⟪z, w⟫_𝕜 = 0) :
    im (fubiniStudyHermitian 𝕜 z v w) = im ⟪v, w⟫_𝕜 / π := by
  have hvz : im (⟪v, z⟫_𝕜 * ⟪z, w⟫_𝕜) = 0 := by
    rw [← inner_conj_symm, mul_im, conj_re, conj_im, hv, hw]
    ring
  simp [fubiniStudyHermitian_apply, hz, hvz, div_im, normSq_apply, mul_div_mul_right, pi_ne_zero]

end TauCeti
