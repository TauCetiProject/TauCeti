/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.SouthPole
public import TauCeti.Geometry.Manifold.Instances.OnePoint.AreaDisc
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import TauCeti.Analysis.InnerProductSpace.Euclidean.CrossProduct

/-!
# The equal-area embedding of a disc into the round two-sphere

Let `S²(a)` be the unit sphere `S² ⊂ ℝ³` with the area form `(a / 4π) σ`, a rescaling of the
area form `σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`), whose total area is `4π`; so
`S²(a)` has total area `a`. The open disc of the same area `a` in `ℂ`, of radius `√(a / π)`, with
the standard symplectic form `ω(v, w) = Im ⟪v, w⟫_ℂ = dx ∧ dy`, embeds symplectically onto
`S²(a)` minus the south pole (`TauCeti.discToSphere`).

The embedding is the inverse of Lambert's azimuthal equal-area projection. It is the composite of
two maps already on hand: the inverse of the disc chart `OnePoint.areaDiscChart a`, which carries
the disc onto the Riemann sphere minus `∞` and pulls `a • ω_FS` back to `dx ∧ dy`
(`OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_areaDiscChart_symm`), followed by the diffeomorphism
`OnePoint.diffeomorphSphere` of the Riemann sphere onto `S²`, sending `∞` to the south pole and
`z` to `(2 Re z, 2 Im z, 1 - |z|²) / (1 + |z|²)`. The latter pulls `σ` back to `4π ω_FS`
(`OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm`; the sign is `+` because the frame
`(0, 0, 1), (1, 0, 0), (0, 1, 0)` is positively oriented), so the composite pulls `(a / 4π) σ` back
to `dx ∧ dy` (`TauCeti.eval₂_mfderiv_discToSphere`). The south pole `TauCeti.sphereSouthPole` and
the equatorial isometry `TauCeti.complexIsometryOrthogonalSphereSouthPole` that set up
`OnePoint.diffeomorphSphere` here come from
`TauCeti.Analysis.InnerProductSpace.Euclidean.SouthPole`.

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
open scoped Manifold ContDiff InnerProductSpace Real TauCeti.ComplexManifold

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### The orientation of the south-pole frame -/

/-- The frame `(-v, ι 1, ι i)`, for the south pole `v` and the isometry `ι` onto the equatorial
plane, is positively oriented: the frame `(v, ι 1, ι i)` has volume `-1`. -/
private theorem volumeForm_sphereSouthPole_frame :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm
        ![(sphereSouthPole : ℝ³), (complexIsometryOrthogonalSphereSouthPole 1 : ℝ³),
          (complexIsometryOrthogonalSphereSouthPole I : ℝ³)] = -1 := by
  rw [EuclideanSpace.volumeForm_basisFun_orientation_three]
  simp [cross_apply, dotProduct, Fin.sum_univ_three]

/-! ### The equal-area embedding into the sphere -/

/-- **The equal-area embedding of the disc of area `a` into the round sphere `S²(a)`**: the inverse
of Lambert's azimuthal equal-area projection, rescaled to area `a`. It is the inverse
`y ↦ y / √(a / π - |y|²)` of the disc chart `OnePoint.areaDiscChart a`, followed by inverse
stereographic projection `z ↦ (2 Re z, 2 Im z, 1 - |z|²) / (1 + |z|²)` from the south pole
(`OnePoint.diffeomorphSphere`). It is a symplectic embedding of the open disc of radius
`√(a / π)` onto the sphere minus the south pole for the form `(a / 4π) σ`
(`TauCeti.eval₂_mfderiv_discToSphere`, `TauCeti.isEmbedding_discToSphere`,
`TauCeti.image_discToSphere_ball`). -/
def discToSphere (a : ℝ) (z : ℂ) : S² :=
  OnePoint.diffeomorphSphere sphereSouthPole complexIsometryOrthogonalSphereSouthPole
    ((OnePoint.areaDiscChart a).symm z)

theorem discToSphere_apply (a : ℝ) (z : ℂ) :
    discToSphere a z =
      OnePoint.diffeomorphSphere sphereSouthPole complexIsometryOrthogonalSphereSouthPole
        ((OnePoint.areaDiscChart a).symm z) :=
  (rfl)

private theorem pos_of_mem_ball {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) : 0 < a := by
  have h : 0 < √(a / π) := (norm_nonneg z).trans_lt (mem_ball_zero_iff.1 hz)
  exact (div_pos_iff_of_pos_right Real.pi_pos).1 (Real.sqrt_pos.1 h)

/-- The equal-area embedding is smooth on the open disc of area `a`. -/
theorem contMDiffAt_discToSphere {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 2) ∞ (discToSphere a) z := by
  have hz' : z ∈ (OnePoint.areaDiscChart a).target := by
    rwa [OnePoint.areaDiscChart_target (pos_of_mem_ball hz)]
  exact ((OnePoint.diffeomorphSphere _ _).contMDiff.of_le le_top).contMDiffAt.comp z
    ((OnePoint.areaDiscChart a).symm.contMDiffOn.contMDiffAt
      ((OnePoint.areaDiscChart a).open_target.mem_nhds hz'))

/-- **The equal-area embedding is symplectic**: it pulls the area form `(a / 4π) σ` of `S²(a)`
back to the standard symplectic form `ω(v, w) = Im ⟪v, w⟫_ℂ` on the open disc of area `a`. -/
theorem eval₂_mfderiv_discToSphere {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) √(a / π)) (v w : ℂ) :
    ((a / (4 * π)) • sphereAreaForm).eval₂ (discToSphere a z)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (discToSphere a) z v)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (discToSphere a) z w) =
      (⟪v, w⟫_ℂ).im := by
  have ha := pos_of_mem_ball hz
  have hz' : z ∈ (OnePoint.areaDiscChart a).target := by
    rwa [OnePoint.areaDiscChart_target ha]
  have hd (u : ℂ) : mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (discToSphere a) z u =
      mfderiv 𝓘(ℝ, ℂ) (𝓡 2)
        (OnePoint.diffeomorphSphere sphereSouthPole complexIsometryOrthogonalSphereSouthPole)
        ((OnePoint.areaDiscChart a).symm z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint.areaDiscChart a).symm z u) :=
    mfderiv_comp_apply z ((OnePoint.diffeomorphSphere _ _).mdifferentiable (by simp) _)
      ((OnePoint.areaDiscChart a).symm.mdifferentiableAt (by simp) hz') u
  -- The round area form pulls back along `diffeomorphSphere` to `4π ω_FS`.
  have hpull := congrArg (fun η ↦ η ((OnePoint.areaDiscChart a).symm z)
    ![mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint.areaDiscChart a).symm z v,
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint.areaDiscChart a).symm z w])
    (OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm sphereSouthPole
      complexIsometryOrthogonalSphereSouthPole
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)
  simp only [mpullback_apply_pair, volumeForm_sphereSouthPole_frame] at hpull
  -- The disc chart pulls `a • ω_FS` back to the standard area form.
  have hφ := OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_areaDiscChart_symm ha
    (mem_ball_zero_iff.1 hz) v w
  rw [SmoothForm.eval₂_smul, SmoothBundleForm.eval₂_apply] at hφ
  rw [SmoothForm.eval₂_smul, SmoothBundleForm.eval₂_apply, hd, hd,
    sphereAreaForm_eq_sphereVolumeForm, discToSphere_apply, hpull]
  simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    stdComplexSymplecticForm_apply] at hφ ⊢
  rw [← mul_assoc, show a / (4 * π) * -(4 * π * -1) = a by field_simp, hφ]
  simp only [inner, mul_im, Complex.star_def, conj_re, conj_im]
  ring

/-- The equal-area embedding restricted to the open disc of area `a` is a topological embedding. -/
theorem isEmbedding_discToSphere (a : ℝ) :
    Topology.IsEmbedding fun z : ball (0 : ℂ) √(a / π) ↦ discToSphere a z := by
  rcases le_or_gt a 0 with ha | ha
  · -- For `a ≤ 0` the disc is empty.
    have : IsEmpty (ball (0 : ℂ) √(a / π)) :=
      ⟨fun z ↦ (pos_of_mem_ball z.property).not_ge ha⟩
    exact .of_subsingleton _
  rw [← OnePoint.areaDiscChart_target ha]
  exact (OnePoint.diffeomorphSphere _ _).toHomeomorph.isEmbedding.comp
    (OnePoint.areaDiscChart a).toOpenPartialHomeomorph.symm.isOpenEmbedding_restrict.isEmbedding

/-- The equal-area embedding maps the open disc of area `a > 0` onto the sphere minus the south
pole. -/
theorem image_discToSphere_ball {a : ℝ} (ha : 0 < a) :
    discToSphere a '' ball (0 : ℂ) √(a / π) = {sphereSouthPole}ᶜ := by
  have h : (OnePoint.areaDiscChart a).symm '' (OnePoint.areaDiscChart a).target =
      (OnePoint.areaDiscChart a).source :=
    (OnePoint.areaDiscChart a).toOpenPartialHomeomorph.symm_image_target_eq_source
  rw [← OnePoint.areaDiscChart_target ha, show discToSphere a =
    OnePoint.diffeomorphSphere _ _ ∘ (OnePoint.areaDiscChart a).symm from rfl, Set.image_comp, h,
    OnePoint.areaDiscChart_source, Set.image_compl_eq
    (f := OnePoint.diffeomorphSphere sphereSouthPole complexIsometryOrthogonalSphereSouthPole)
    (OnePoint.diffeomorphSphere _ _).toEquiv.bijective, Set.image_singleton]
  exact congrArg _ (congrArg _ (OnePoint.diffeomorphSphere_infty _ _))

end TauCeti
