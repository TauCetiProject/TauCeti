/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.RCLike.Lemmas
public import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Maximal-volume ellipsoids

Let `E` be a finite-dimensional inner product space and `F` a normed space of the same dimension.
For a continuous linear equivalence `T : E ≃L[𝕜] F`, the image `T(B)` of the Euclidean unit ball
`B` of `E` is an ellipsoid in `F`, and it lies in the closed unit ball of `F` exactly when
`‖T‖ ≤ 1`. Volumes of such images are compared through determinants on `E`: since
`S = T ∘ (T⁻¹ ∘ S)`, for every Haar measure on `F` the volume of `S(B)` is that of `T(B)` times
`|det (T⁻¹ ∘ S)|` over `ℝ`, and times `|det (T⁻¹ ∘ S)|²` over `ℂ`. Comparing determinants
therefore needs no volume on `F` and no choice of basis.

`ContinuousLinearEquiv.IsMaxVolumeEllipsoid T` says that `T` is a contraction whose ellipsoid has
maximal volume in this sense among the images of the Euclidean ball under all contractions
`S : E →L[𝕜] F`. These are the ellipsoids of John's theorem; when `T` is one, the norm
`x ↦ ‖T x‖` on `E` is in *John's position*: its closed unit ball contains the Euclidean unit ball,
which is the inscribed ellipsoid of maximal volume.

Neither the definition nor the existence theorem uses an inner product: the definition makes sense
over any nontrivially normed field, and the existence theorem holds over any locally compact one.

## Main declarations

* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid`: `T` is a contraction maximizing the determinant.
* `TauCeti.exists_isMaxVolumeEllipsoid`: between finite-dimensional spaces of equal dimension a
  maximal-volume ellipsoid exists, by compactness of the unit ball of `E →L[𝕜] F`.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.isMaxVolumeEllipsoid_iff`: a contraction is maximal
  exactly when its determinant relative to a maximal one has norm one.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.norm_eq_one`: over `ℝ` or `ℂ`, a maximal
  contraction from a nonzero space has norm one.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_norm_eq_one_and_norm_apply_eq_one`: it has a
  contact point, a unit vector `u` with `‖T u‖ = 1`.

At a contact point `u` of John's position, the inequalities
`ContinuousLinearMap.re_inner_le_norm_mul_norm_apply` and
`ContinuousLinearMap.norm_inner_le_norm_mul_norm_apply` of
`TauCeti.Analysis.InnerProductSpace.Contraction` show that `re ⟪·, u⟫` is a support functional of
the unit ball of the norm `x ↦ ‖T x‖`, and that `‖⟪u, x⟫‖ ≤ ‖T x‖`.

## References

* K. Ball, *An Elementary Introduction to Modern Convex Geometry*, Lecture 3.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.1.
-/

public section

open Module Metric

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*}

section NormedField

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear equivalence `T : E ≃L[𝕜] F` from a finite-dimensional space is a
*maximal-volume ellipsoid* if it is a contraction and, for every contraction `S : E →L[𝕜] F`, the
determinant of `T⁻¹ ∘ S` has norm at most one. When `E` is an inner product space, `T` maps the
Euclidean unit ball onto an ellipsoid of maximal volume among the ellipsoids contained in the closed
unit ball of `F`. Finite dimensionality is required because determinants are only meaningful there:
`LinearMap.det` is constantly `1` on infinite-dimensional spaces. -/
structure IsMaxVolumeEllipsoid [FiniteDimensional 𝕜 E] (T : E ≃L[𝕜] F) : Prop where
  /-- The ellipsoid lies in the closed unit ball. -/
  norm_le_one : ‖(T : E →L[𝕜] F)‖ ≤ 1
  /-- No contraction gives an ellipsoid of larger volume. -/
  norm_det_le_one : ∀ S : E →L[𝕜] F, ‖S‖ ≤ 1 → ‖((T.symm : F →L[𝕜] E).comp S).det‖ ≤ 1

namespace IsMaxVolumeEllipsoid

variable [FiniteDimensional 𝕜 E] {T : E ≃L[𝕜] F}

/-- Two maximal-volume ellipsoids have the same volume. -/
theorem norm_det_eq_one (hT : T.IsMaxVolumeEllipsoid) {U : E ≃L[𝕜] F}
    (hU : U.IsMaxVolumeEllipsoid) : ‖((T.symm : F →L[𝕜] E).comp (U : E →L[𝕜] F)).det‖ = 1 := by
  have h := det_symm_comp_mul_det_symm_comp T U T
  rw [T.coe_symm_comp_coe, ContinuousLinearMap.det_id] at h
  have h₁ := hT.norm_det_le_one U hU.norm_le_one
  have h₂ := hU.norm_det_le_one T hT.norm_le_one
  have h₃ := congrArg norm h
  rw [norm_mul, norm_one] at h₃
  nlinarith [norm_nonneg ((T.symm : F →L[𝕜] E).comp (U : E →L[𝕜] F)).det,
    norm_nonneg ((U.symm : F →L[𝕜] E).comp (T : E →L[𝕜] F)).det]

/-- Given a maximal-volume ellipsoid `T`, a contraction `U` is a maximal-volume ellipsoid exactly
when the determinant of `T⁻¹ ∘ U` has norm one. -/
theorem isMaxVolumeEllipsoid_iff (hT : T.IsMaxVolumeEllipsoid) {U : E ≃L[𝕜] F}
    (hU : ‖(U : E →L[𝕜] F)‖ ≤ 1) :
    U.IsMaxVolumeEllipsoid ↔ ‖((T.symm : F →L[𝕜] E).comp (U : E →L[𝕜] F)).det‖ = 1 := by
  refine ⟨hT.norm_det_eq_one, fun h ↦ ⟨hU, fun S hS ↦ ?_⟩⟩
  have hS' := hT.norm_det_le_one S hS
  rw [← det_symm_comp_mul_det_symm_comp T U S, norm_mul, h, one_mul] at hS'
  exact hS'

end IsMaxVolumeEllipsoid

end NormedField

end ContinuousLinearEquiv

namespace TauCeti

open ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Existence of maximal-volume ellipsoids.** Between finite-dimensional normed spaces of equal
dimension over a locally compact field, some continuous linear equivalence is a maximal-volume
ellipsoid. -/
theorem exists_isMaxVolumeEllipsoid [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (h : finrank 𝕜 E = finrank 𝕜 F) : ∃ T : E ≃L[𝕜] F, T.IsMaxVolumeEllipsoid := by
  -- Maximize `S ↦ ‖det (e⁻¹ ∘ S)‖` over the compact unit ball of `E →L[𝕜] F`, for a reference
  -- equivalence `e`. A small multiple of `e` shows that the maximum is positive, so a maximizer
  -- is invertible; the ratio of determinants then shows that it is maximal in the above sense.
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  have : ProperSpace (E →L[𝕜] F) := FiniteDimensional.proper 𝕜 _
  let e : E ≃L[𝕜] F := .ofFinrankEq h
  let φ : (E →L[𝕜] F) → ℝ := fun S ↦ ‖((e.symm : F →L[𝕜] E).comp S).det‖
  have hφ : Continuous φ :=
    (ContinuousLinearMap.continuous_det.comp (continuous_const.clm_comp continuous_id)).norm
  obtain ⟨S₀, hS₀, hmax⟩ := (isCompact_closedBall (0 : E →L[𝕜] F) 1).exists_isMaxOn
    (nonempty_closedBall.2 zero_le_one) hφ.continuousOn
  obtain ⟨c, hc₀, hc⟩ := NormedField.exists_norm_lt 𝕜
    (inv_pos.2 (add_pos_of_nonneg_of_pos (norm_nonneg (e : E →L[𝕜] F)) one_pos))
  have hce : c • (e : E →L[𝕜] F) ∈ closedBall (0 : E →L[𝕜] F) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul]
    have := mul_lt_mul_of_pos_right hc (by positivity : 0 < ‖(e : E →L[𝕜] F)‖ + 1)
    rw [inv_mul_cancel₀ (by positivity)] at this
    nlinarith [norm_nonneg (e : E →L[𝕜] F)]
  have hφce : φ (c • (e : E →L[𝕜] F)) = ‖c‖ ^ finrank 𝕜 E := by
    have : (e.symm : F →L[𝕜] E).comp (c • (e : E →L[𝕜] F)) = c • ContinuousLinearMap.id 𝕜 E := by
      rw [ContinuousLinearMap.comp_smul, e.coe_symm_comp_coe]
    simp only [φ, this, ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one,
      norm_pow]
  have hdet : ((e.symm : F →L[𝕜] E).comp S₀).det ≠ 0 := by
    intro h0
    have := hmax hce
    simp only [Set.mem_ofPred_eq, hφce, φ, h0, norm_zero] at this
    exact (pow_pos hc₀ _).not_ge this
  -- The maximizer `S₀ = e ∘ (e⁻¹ ∘ S₀)` is invertible.
  let T : E ≃L[𝕜] F :=
    (((e.symm : F →L[𝕜] E).comp S₀).toContinuousLinearEquivOfDetNeZero hdet).trans e
  have hT : (T : E →L[𝕜] F) = S₀ := by
    ext x
    simp [T]
  refine ⟨T, ⟨by rwa [hT, ← mem_closedBall_zero_iff], fun S hS ↦ ?_⟩⟩
  have hS' : φ S ≤ φ S₀ := hmax (mem_closedBall_zero_iff.2 hS)
  have hφ₀ : 0 < φ S₀ := norm_pos_iff.2 hdet
  simp only [φ, ← det_symm_comp_mul_det_symm_comp e T S, hT, norm_mul] at hS' hφ₀ ⊢
  nlinarith [norm_nonneg ((T.symm : F →L[𝕜] E).comp S).det]

end TauCeti

namespace ContinuousLinearEquiv.IsMaxVolumeEllipsoid

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] {T : E ≃L[𝕜] F}

/-- Over `ℝ` or `ℂ`, a maximal-volume ellipsoid from a nonzero finite-dimensional space has
norm one: a contraction of norm `a < 1` could be enlarged by the factor `a⁻¹`. -/
theorem norm_eq_one [Nontrivial E] (hT : T.IsMaxVolumeEllipsoid) : ‖(T : E →L[𝕜] F)‖ = 1 := by
  refine le_antisymm hT.norm_le_one (not_lt.1 fun ha ↦ ?_)
  set a := ‖(T : E →L[𝕜] F)‖
  have ha₀ : 0 < a := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact norm_pos_iff.2 fun h ↦ hx (by simpa using congr($h x))
  have hS : ‖((a⁻¹ : ℝ) : 𝕜) • (T : E →L[𝕜] F)‖ ≤ 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 ha₀), inv_mul_cancel₀ ha₀.ne']
  have h := hT.norm_det_le_one _ hS
  have hn : 0 < finrank 𝕜 E := finrank_pos
  simp only [ContinuousLinearMap.comp_smul, T.coe_symm_comp_coe,
    ContinuousLinearMap.det_smul, ContinuousLinearMap.det_id, mul_one, norm_pow,
    RCLike.norm_ofReal, abs_of_pos (inv_pos.2 ha₀)] at h
  exact (one_lt_pow₀ (one_lt_inv₀ ha₀ |>.2 ha) hn.ne').not_ge h

/-- **Contact points.** Over `ℝ` or `ℂ`, a maximal-volume ellipsoid from a nonzero
finite-dimensional space touches the unit sphere of `F`: some unit vector `u` has `‖T u‖ = 1`. -/
theorem exists_norm_eq_one_and_norm_apply_eq_one [Nontrivial E] (hT : T.IsMaxVolumeEllipsoid) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖T u‖ = 1 := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn
    (Set.nonempty_coe_sort.1 (NormedSpace.sphere_nonempty_rclike 𝕜 zero_le_one))
    T.continuous.norm.continuousOn
  rw [mem_sphere_zero_iff_norm] at hu
  refine ⟨u, hu, le_antisymm ?_ ?_⟩
  · simpa [hu] using (T : E →L[𝕜] F).le_of_opNorm_le hT.norm_le_one u
  · rw [← hT.norm_eq_one]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun x hx ↦ ?_
    exact hmax (mem_sphere_zero_iff_norm.2 hx)

end ContinuousLinearEquiv.IsMaxVolumeEllipsoid
