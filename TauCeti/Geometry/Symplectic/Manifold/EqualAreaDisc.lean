/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.StereographicArea
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import TauCeti.Analysis.InnerProductSpace.UnivBall

/-!
# The equal-area embedding of a disc into the round two-sphere

Let `S²(a)` be the unit sphere `S² ⊂ ℝ³` with the area form `(a / 4π) σ`, a rescaling of the
area form `σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`), whose total area is `4π`; so
`S²(a)` has total area `a`. The open disc of the same area `a` in `ℂ`, of radius `√(a / π)`, with
the standard symplectic form `ω(v, w) = Im ⟪v, w⟫_ℂ = dx ∧ dy`, embeds symplectically onto
`S²(a)` minus the south pole (`TauCeti.discToSphere`).

The embedding is the inverse of Lambert's azimuthal equal-area projection, written as a radial
stretching of the disc onto the plane followed by inverse stereographic projection from the south
pole (`TauCeti.stereoSphere`). With `r² = a / π`, the stretching is the inverse
`x ↦ x / √(r² - ‖x‖²)` of Mathlib's radial homeomorphism `OpenPartialHomeomorph.univBall 0 r` of
the plane onto the open disc of radius `r`. Its Jacobian determinant is `r² / (r² - ‖x‖²)²`
(`OpenPartialHomeomorph.fderiv_univBall_zero_symm_apply_mul_sub_mul`), and inverse stereographic
projection pulls `σ` back to `4 / (1 + ‖u‖²)² dx ∧ dy`
(`TauCeti.sphereVolumeForm_mfderiv_stereoSphere_apply`).
Since `1 + ‖u‖² = r² / (r² - ‖x‖²)` at `u = x / √(r² - ‖x‖²)`, the two factors multiply to
`4 / r² = 4π / a`, which `a / 4π` cancels (`TauCeti.eval₂_mfderiv_discToSphere`).

This is the sphere factor of the compactification in the proof of Gromov's nonsqueezing theorem:
a ball embedded symplectically in the cylinder `{z ∈ ℂⁿ | |z₀| < R}` is moved into
`S²(a) × T²ⁿ⁻²` with `a = πR² + ε`, which requires a symplectic embedding of the disc of radius `R`
into `S²(a)`; the disc of radius `√(a / π) > R` contains it.

## Main definitions

* `TauCeti.discToSphere`: the equal-area embedding of the disc of area `a` into `S²(a)`.

## Main results

* `TauCeti.contMDiffAt_discToSphere`: the embedding is smooth on the open disc.
* `TauCeti.eval₂_mfderiv_discToSphere`: it is symplectic, pulling `(a / 4π) σ` back to
  `Im ⟪v, w⟫_ℂ`.
* `TauCeti.isEmbedding_discToSphere`, `TauCeti.image_discToSphere_ball`: it is a topological
  embedding of the open disc onto the sphere minus the south pole.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A (the nonsqueezing theorem).
* J. P. Snyder, *Map Projections: A Working Manual*, U.S. Geological Survey Professional
  Paper 1395, 1987, §24 (Lambert azimuthal equal-area projection).
-/

public section

noncomputable section

open Metric Module Complex
open scoped Manifold ContDiff InnerProductSpace Real

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### The equal-area embedding into the sphere -/

/-- **The equal-area embedding of the disc of area `a` into the round sphere `S²(a)`**: the inverse
of Lambert's azimuthal equal-area projection, rescaled to area `a`. Identifying `ℂ` with `ℝ²` by
`z ↦ (re z, im z)`, it is the radial stretching `z ↦ z / √(a / π - ‖z‖²)` of the open disc of
radius `√(a / π)` onto the plane, the inverse of `OpenPartialHomeomorph.univBall 0 √(a / π)`,
followed by inverse stereographic projection from the south pole. It is a symplectic embedding of
the disc onto the sphere minus the south pole for the form `(a / 4π) σ`
(`TauCeti.eval₂_mfderiv_discToSphere`, `TauCeti.isEmbedding_discToSphere`,
`TauCeti.image_discToSphere_ball`). -/
def discToSphere (a : ℝ) (z : ℂ) : S² :=
  stereoSphere ((OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)).symm
    (orthonormalBasisOneI.repr z))

theorem discToSphere_apply (a : ℝ) (z : ℂ) :
    discToSphere a z = stereoSphere ((OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)).symm
      (orthonormalBasisOneI.repr z)) :=
  (rfl)

private theorem repr_mem_ball {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) :
    orthonormalBasisOneI.repr z ∈ ball (0 : ℝ²) √(a / π) := by
  rwa [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← mem_ball_zero_iff]

private theorem repr_symm_univBall_mem_ball {r : ℝ} (hr : 0 < r) (u : ℝ²) :
    orthonormalBasisOneI.repr.symm (OpenPartialHomeomorph.univBall (0 : ℝ²) r u) ∈
      ball (0 : ℂ) r := by
  rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← mem_ball_zero_iff,
    ← OpenPartialHomeomorph.univBall_target 0 hr]
  exact (OpenPartialHomeomorph.univBall (0 : ℝ²) r).map_source (by simp)

/-- The equal-area embedding is smooth on the open disc of area `a`. -/
theorem contMDiffAt_discToSphere {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 2) ∞ (discToSphere a) z :=
  contMDiff_stereoSphere.contMDiffAt.comp z
    ((OpenPartialHomeomorph.contDiffOn_univBall_symm.contDiffAt
      (isOpen_ball.mem_nhds (repr_mem_ball hz))).comp z
        orthonormalBasisOneI.repr.contDiff.contDiffAt).contMDiffAt

/-- The derivative of the equal-area embedding is the derivative of inverse stereographic
projection after that of the radial stretching. -/
private theorem mfderiv_discToSphere_apply {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π))
    (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (discToSphere a) z v =
      mfderiv 𝓘(ℝ, ℝ²) (𝓡 2) stereoSphere
        ((OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)).symm (orthonormalBasisOneI.repr z))
        (fderiv ℝ (OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)).symm
          (orthonormalBasisOneI.repr z) (orthonormalBasisOneI.repr v)) := by
  have hd : DifferentiableAt ℝ (OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)).symm
      (orthonormalBasisOneI.repr z) :=
    (OpenPartialHomeomorph.contDiffOn_univBall_symm (n := 1)).differentiableOn one_ne_zero
      |>.differentiableAt (isOpen_ball.mem_nhds (repr_mem_ball hz))
  have hcomp : discToSphere a = stereoSphere ∘
      ((OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)).symm ∘ orthonormalBasisOneI.repr) :=
    rfl
  rw [hcomp, mfderiv_comp z ((contMDiff_stereoSphere _).mdifferentiableAt (by simp))
    (hd.comp z orthonormalBasisOneI.repr.differentiableAt).mdifferentiableAt,
    mfderiv_eq_fderiv, fderiv_comp z hd orthonormalBasisOneI.repr.differentiableAt,
    LinearIsometryEquiv.fderiv]
  -- The two sides differ only by applying composites of continuous linear maps and by the
  -- identifications `NormedSpace.fromTangentSpace` of a tangent space of a normed space with the
  -- space itself, which Mathlib defines as the identity; so they agree definitionally.
  rfl

/-- **The equal-area embedding is symplectic**: it pulls the area form `(a / 4π) σ` of `S²(a)`
back to the standard symplectic form `ω(v, w) = Im ⟪v, w⟫_ℂ` on the open disc of area `a`. -/
theorem eval₂_mfderiv_discToSphere {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) (v w : ℂ) :
    ((a / (4 * π)) • sphereAreaForm).eval₂ (discToSphere a z)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (discToSphere a) z v)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (discToSphere a) z w) =
      (⟪v, w⟫_ℂ).im := by
  set r := √(a / π) with hr
  set x := orthonormalBasisOneI.repr z
  have hx : ‖x‖ < r := mem_ball_zero_iff.1 (repr_mem_ball hz)
  have hr0 : 0 < r := (norm_nonneg x).trans_lt hx
  have ha : a / π = r ^ 2 := by
    rw [hr, Real.sq_sqrt (Real.sqrt_pos.1 (hr ▸ hr0)).le]
  have hs : 0 < r ^ 2 - ‖x‖ ^ 2 := sub_pos.2 (pow_lt_pow_left₀ hx (norm_nonneg x) two_ne_zero)
  have hnu : ‖(OpenPartialHomeomorph.univBall (0 : ℝ²) r).symm x‖ ^ 2 =
      ‖x‖ ^ 2 / (r ^ 2 - ‖x‖ ^ 2) := by
    rw [OpenPartialHomeomorph.univBall_zero_symm_apply hr0, norm_smul, mul_pow, norm_inv,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hs.le, inv_mul_eq_div]
  set u := (OpenPartialHomeomorph.univBall (0 : ℝ²) r).symm x
  have hu : 1 + u 0 ^ 2 + u 1 ^ 2 = r ^ 2 / (r ^ 2 - ‖x‖ ^ 2) := by
    rw [add_assoc, ← Fin.sum_univ_two (fun i ↦ u i ^ 2), ← EuclideanSpace.real_norm_sq_eq, hnu]
    field_simp
    ring
  rw [SmoothForm.eval₂_smul, smul_eq_mul, SmoothBundleForm.eval₂_apply,
    sphereAreaForm_eq_sphereVolumeForm, mfderiv_discToSphere_apply hz,
    mfderiv_discToSphere_apply hz, discToSphere_apply, sphereVolumeForm_mfderiv_stereoSphere_apply,
    OpenPartialHomeomorph.fderiv_univBall_zero_symm_apply_mul_sub_mul hx, hu]
  simp only [orthonormalBasisOneI_repr_apply, inner, mul_im, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.star_def, conj_re, conj_im]
  have ha' : a = r ^ 2 * π := by
    rw [← ha]
    field_simp
  rw [ha']
  field_simp
  ring

/-- The equal-area embedding restricted to the open disc of area `a` is a topological embedding. -/
theorem isEmbedding_discToSphere (a : ℝ) :
    Topology.IsEmbedding fun z : ball (0 : ℂ) √(a / π) ↦ discToSphere a z := by
  set r := √(a / π)
  rcases le_or_gt r 0 with hr | hr
  · -- For `r ≤ 0` the disc is empty.
    have : IsEmpty (ball (0 : ℂ) r) := by
      rw [ball_eq_empty.2 hr]
      infer_instance
    exact .of_subsingleton _
  set e := OpenPartialHomeomorph.univBall (0 : ℝ²) r
  have hmem (u : ℝ²) : orthonormalBasisOneI.repr.symm (e u) ∈ ball (0 : ℂ) r :=
    repr_symm_univBall_mem_ball hr u
  -- The radial stretching restricted to the disc has the continuous left inverse `e`.
  have hf : Continuous fun z : ball (0 : ℂ) r ↦ e.symm (orthonormalBasisOneI.repr z) :=
    (OpenPartialHomeomorph.continuousOn_univBall_symm 0 r).comp_continuous
      (orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val)
      fun z ↦ repr_mem_ball z.2
  have hg : Continuous fun u : ℝ² ↦ (⟨_, hmem u⟩ : ball (0 : ℂ) r) :=
    (orthonormalBasisOneI.repr.symm.continuous.comp
      (OpenPartialHomeomorph.continuous_univBall 0 r)).subtype_mk _
  have hleft : Function.LeftInverse (fun u : ℝ² ↦ (⟨_, hmem u⟩ : ball (0 : ℂ) r))
      fun z : ball (0 : ℂ) r ↦ e.symm (orthonormalBasisOneI.repr z) :=
    fun z ↦ Subtype.ext <| by
      dsimp only
      rw [e.right_inv (by rw [OpenPartialHomeomorph.univBall_target 0 hr]; exact repr_mem_ball z.2),
        LinearIsometryEquiv.symm_apply_apply]
  exact isOpenEmbedding_stereoSphere.isEmbedding.comp (hleft.isEmbedding hg hf)

/-- The equal-area embedding is injective on the open disc of area `a`. -/
theorem injOn_discToSphere (a : ℝ) : Set.InjOn (discToSphere a) (ball (0 : ℂ) √(a / π)) :=
  fun z hz w hw h ↦ congrArg Subtype.val
    ((isEmbedding_discToSphere a).injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) h)

/-- The equal-area embedding maps the open disc of area `a > 0` onto the sphere minus the south
pole. -/
theorem image_discToSphere_ball {a : ℝ} (ha : 0 < a) :
    discToSphere a '' ball (0 : ℂ) √(a / π) = {sphereSouthPole}ᶜ := by
  have hr : 0 < √(a / π) := Real.sqrt_pos.2 (by positivity)
  set e := OpenPartialHomeomorph.univBall (0 : ℝ²) √(a / π)
  rw [← range_stereoSphere]
  ext y
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨orthonormalBasisOneI.repr.symm (e u), ?_, ?_⟩
    · exact repr_symm_univBall_mem_ball hr u
    · rw [discToSphere_apply, LinearIsometryEquiv.apply_symm_apply, e.left_inv (by simp [e])]

end TauCeti
