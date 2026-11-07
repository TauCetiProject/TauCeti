/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Normed.Module.BanachMazur
public import TauCeti.Topology.Algebra.Module.Determinant

import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Convex.Caratheodory
import TauCeti.Analysis.InnerProductSpace.Contraction

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

**John's theorem** describes a maximal-volume ellipsoid `T` through its contact points, the unit
vectors `u` with `‖T u‖ = 1`: there are finitely many contact points `uᵢ` and positive weights `cᵢ`
with `∑ cᵢ ⟪uᵢ, x⟫ uᵢ = x` for every `x`, and then `∑ cᵢ = n` where `n` is the dimension. This is
the first-order optimality condition for the volume: if no such decomposition existed, separating
the identity from the convex hull of the rank-one maps `x ↦ ⟪u, x⟫ u` would give an operator `H`
with `re (trace H) ≤ 0` and `re ⟪u, H u⟫ > 0` at every contact point, and a small multiple of
`T ∘ (1 - δ H)` would then be a contraction of larger volume. Pairing the decomposition with `x`
gives `‖x‖² = ∑ cᵢ ‖⟪uᵢ, x⟫‖² ≤ n ‖T x‖²`, so `‖T⁻¹‖ ≤ √n` and every `n`-dimensional normed space
is at Banach–Mazur distance at most `√n` from the Euclidean space of the same dimension.

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
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_contact_re_inner_apply_nonpos`: over an inner
  product space, for every operator `H` with `re (trace H) ≤ 0` some contact point `u` has
  `re ⟪u, H u⟫ ≤ 0`.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.exists_sum_rankOne_eq_id`: **John's theorem**, the
  decomposition `∑ cᵢ • rankOne uᵢ uᵢ = 1` of the identity over contact points `uᵢ` with positive
  weights `cᵢ` summing to the dimension.
* `ContinuousLinearEquiv.IsMaxVolumeEllipsoid.norm_symm_le_sqrt_finrank`: `‖T⁻¹‖ ≤ √n`.
* `TauCeti.banachMazurDist_le_sqrt_finrank` and
  `TauCeti.banachMazurDist_euclideanSpace_le_sqrt_finrank`: an `n`-dimensional normed space is at
  Banach–Mazur distance at most `√n` from an `n`-dimensional inner product space, in particular
  from `EuclideanSpace 𝕜 (Fin n)`.

At a contact point `u` of John's position, the inequalities
`ContinuousLinearMap.re_inner_le_norm_mul_norm_apply` and
`ContinuousLinearMap.norm_inner_le_norm_mul_norm_apply` of
`TauCeti.Analysis.InnerProductSpace.Contraction` show that `re ⟪·, u⟫` is a support functional of
the unit ball of the norm `x ↦ ‖T x‖`, and that `‖⟪u, x⟫‖ ≤ ‖T x‖`.

## References

* K. Ball, *An Elementary Introduction to Modern Convex Geometry*, Lecture 3, Theorem 3.1. The
  proof of John's theorem follows its separation argument, phrased for operators over `ℝ` or `ℂ`.
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

/-! ### John's theorem -/

namespace ContinuousLinearEquiv.IsMaxVolumeEllipsoid

open RCLike InnerProductSpace Filter Topology Set
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] {T : E ≃L[𝕜] F}

/-- A second-order lower bound for `‖det (1 - δ H)‖` on `0 ≤ δ ≤ 1`, from the expansion
`det (1 + r M) = 1 + r trace M + O(r²)` of `Matrix.det_one_add_smul`. -/
private theorem exists_le_norm_det_id_sub_smul (H : E →L[𝕜] E) :
    ∃ P : ℝ, ∀ δ ∈ Icc (0 : ℝ) 1,
      1 - δ * re (LinearMap.trace 𝕜 E H) - P * δ ^ 2 ≤
        ‖(ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det‖ := by
  classical
  let b := Module.finBasis 𝕜 E
  set M := LinearMap.toMatrix b b (H : E →ₗ[𝕜] E)
  set q := (Matrix.det (1 + (Polynomial.X : Polynomial 𝕜) • M.map Polynomial.C)).divX.divX
  obtain ⟨P, hP⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    ((q.continuous.comp RCLike.continuous_ofReal).continuousOn)
  refine ⟨P, fun δ hδ ↦ ?_⟩
  have hM : LinearMap.toMatrix b b
      ((ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H : E →L[𝕜] E) : E →ₗ[𝕜] E) =
        1 + (-(δ : 𝕜)) • M := by
    simp [M, sub_eq_add_neg]
  have hdet : (ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det =
      1 + LinearMap.trace 𝕜 E H * (-(δ : 𝕜)) + q.eval (-(δ : 𝕜)) * ((δ ^ 2 : ℝ) : 𝕜) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hM, Matrix.det_one_add_smul,
      LinearMap.trace_eq_matrix_trace 𝕜 b]
    push_cast
    ring
  have hq : ‖q.eval (-(δ : 𝕜))‖ ≤ P := by
    have := hP (-δ) ⟨neg_le_neg hδ.2, neg_nonpos.2 hδ.1⟩
    simpa only [Function.comp_apply, ofReal_neg] using this
  have hre : -(P * δ ^ 2) ≤ re (q.eval (-(δ : 𝕜)) * ((δ ^ 2 : ℝ) : 𝕜)) := by
    rw [mul_comm (q.eval _), re_ofReal_mul]
    nlinarith [abs_le.1 ((abs_re_le_norm _).trans hq), sq_nonneg δ]
  have htr : re (LinearMap.trace 𝕜 E H * (-(δ : 𝕜))) = -δ * re (LinearMap.trace 𝕜 E H) := by
    rw [mul_comm, ← ofReal_neg, re_ofReal_mul]
  calc 1 - δ * re (LinearMap.trace 𝕜 E H) - P * δ ^ 2
      ≤ re ((ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det) := by
        rw [hdet, AddMonoidHom.map_add re, AddMonoidHom.map_add re, htr, one_re]
        linarith
    _ ≤ ‖(ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H).det‖ := re_le_norm _

omit [FiniteDimensional 𝕜 E] in
/-- The perturbation estimate behind John's theorem: if a contraction `S` has norm at most `1 - r`
on the unit vectors `x` with `re ⟪x, H x⟫ ≤ s`, then `S ∘ (1 - δ H)` has norm at most
`1 - δ s / 2` for small `δ > 0`. Near the remaining unit vectors `1 - δ H` itself shrinks the norm,
since `‖x - δ H x‖² = 1 - 2 δ re ⟪x, H x⟫ + δ² ‖H x‖²`. -/
private theorem norm_comp_id_sub_smul_le {S : E →L[𝕜] F} (hS : ‖S‖ ≤ 1) (H : E →L[𝕜] E)
    {s r δ : ℝ} (hδ : 0 < δ) (hc : 0 < 1 - δ * (s / 2))
    (hr : ∀ x, ‖x‖ = 1 → re ⟪x, H x⟫_𝕜 ≤ s → ‖S x‖ ≤ 1 - r)
    (h₁ : δ * ‖H‖ ^ 2 < s) (h₂ : δ * (‖H‖ + s / 2) < r) :
    ‖S.comp (ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H)‖ ≤ 1 - δ * (s / 2) := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hc.le fun x hx ↦ ?_
  have hHx : ‖H x‖ ≤ ‖H‖ := by simpa [hx] using H.le_opNorm x
  rw [ContinuousLinearMap.comp_apply, _root_.sub_apply, ContinuousLinearMap.id_apply,
    _root_.smul_apply]
  by_cases hxs : re ⟪x, H x⟫_𝕜 ≤ s
  · have hSHx : ‖S (H x)‖ ≤ ‖H‖ := by
      simpa using (S.le_of_opNorm_le hS (H x)).trans (by simpa using hHx)
    calc ‖S (x - (δ : 𝕜) • H x)‖ = ‖S x - (δ : 𝕜) • S (H x)‖ := by simp
      _ ≤ ‖S x‖ + δ * ‖S (H x)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_ofReal, abs_of_pos hδ]
      _ ≤ (1 - r) + δ * ‖H‖ := by gcongr; exact hr x hx hxs
      _ ≤ 1 - δ * (s / 2) := by nlinarith
  · rw [not_le] at hxs
    have hsq : ‖x - (δ : 𝕜) • H x‖ ^ 2 ≤ (1 - δ * (s / 2)) ^ 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, re_ofReal_mul, norm_smul, norm_ofReal,
        abs_of_pos hδ, hx, mul_pow]
      have : δ ^ 2 * ‖H x‖ ^ 2 ≤ δ ^ 2 * ‖H‖ ^ 2 := by gcongr
      have h₃ : δ * s < δ * re ⟪x, H x⟫_𝕜 := mul_lt_mul_of_pos_left hxs hδ
      have h₄ : δ * (δ * ‖H‖ ^ 2) < δ * s := mul_lt_mul_of_pos_left h₁ hδ
      nlinarith [sq_nonneg (δ * (s / 2))]
    calc ‖S (x - (δ : 𝕜) • H x)‖ ≤ ‖x - (δ : 𝕜) • H x‖ := by
          simpa using S.le_of_opNorm_le hS (x - (δ : 𝕜) • H x)
      _ ≤ 1 - δ * (s / 2) := (pow_le_pow_iff_left₀ (norm_nonneg _) hc.le two_ne_zero).1 hsq

/-- If a continuous function `φ` exceeds `s` at every contact point, then away from the contact
points, where `φ ≤ s`, the norm `‖T x‖` of a unit vector is bounded by `1 - r` for some `r > 0`. -/
private theorem exists_norm_apply_le_one_sub (hT : T.IsMaxVolumeEllipsoid) {φ : E → ℝ}
    (hφ : Continuous φ) {s : ℝ} (hs : ∀ x, ‖x‖ = 1 → ‖T x‖ = 1 → s < φ x) :
    ∃ r, 0 < r ∧ ∀ x, ‖x‖ = 1 → φ x ≤ s → ‖T x‖ ≤ 1 - r := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  set K := sphere (0 : E) 1 ∩ {x | φ x ≤ s}
  have hK : IsCompact K := (isCompact_sphere (0 : E) 1).inter_right
    (isClosed_le hφ continuous_const)
  rcases K.eq_empty_or_nonempty with hK₀ | hKne
  · refine ⟨1, one_pos, fun x hx hxs ↦ ?_⟩
    have : x ∈ K := ⟨mem_sphere_zero_iff_norm.2 hx, hxs⟩
    simp [hK₀] at this
  obtain ⟨y, ⟨hy, hys⟩, hymax⟩ := hK.exists_isMaxOn hKne
    (by fun_prop : Continuous fun x ↦ ‖T x‖).continuousOn
  rw [mem_sphere_zero_iff_norm] at hy
  have hTy : ‖T y‖ < 1 := by
    refine lt_of_le_of_ne ?_ fun h ↦ (hs y hy h).not_ge hys
    simpa [hy] using (T : E →L[𝕜] F).le_of_opNorm_le hT.norm_le_one y
  refine ⟨1 - ‖T y‖, by linarith, fun x hx hxs ↦ ?_⟩
  have : ‖T x‖ ≤ ‖T y‖ := hymax ⟨mem_sphere_zero_iff_norm.2 hx, hxs⟩
  linarith

/-- **First-order optimality of a maximal-volume ellipsoid.** For every operator `H` on `E` with
`re (trace H) ≤ 0`, some contact point `u`, a unit vector with `‖T u‖ = 1`, has
`re ⟪u, H u⟫ ≤ 0`. Otherwise, for small `δ > 0`, a multiple of `T ∘ (1 - δ H)` would be a
contraction of larger volume. This is the dual form of John's theorem
`exists_sum_rankOne_eq_id`. -/
theorem exists_contact_re_inner_apply_nonpos [Nontrivial E] (hT : T.IsMaxVolumeEllipsoid)
    (H : E →L[𝕜] E) (hH : re (LinearMap.trace 𝕜 E H) ≤ 0) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖T u‖ = 1 ∧ re ⟪u, H u⟫_𝕜 ≤ 0 := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  by_contra! hpos
  -- `φ x = re ⟪x, H x⟫` is at least `2 s > 0` on the compact set of contact points.
  set φ : E → ℝ := fun x ↦ re ⟪x, H x⟫_𝕜
  have hφ : Continuous φ := by fun_prop
  obtain ⟨u₀, hu₀, hTu₀⟩ := hT.exists_norm_eq_one_and_norm_apply_eq_one
  obtain ⟨v, hvC, hvmin⟩ := ((isCompact_sphere (0 : E) 1).inter_right
      (isClosed_eq (by fun_prop : Continuous fun x ↦ ‖T x‖) continuous_const)).exists_isMinOn
    ⟨u₀, mem_sphere_zero_iff_norm.2 hu₀, hTu₀⟩ hφ.continuousOn
  have hv : 0 < φ v := hpos v (mem_sphere_zero_iff_norm.1 hvC.1) hvC.2
  set s := φ v / 2 with hs_def
  have hs : 0 < s := half_pos hv
  obtain ⟨r, hr, hrK⟩ := hT.exists_norm_apply_le_one_sub hφ (s := s) fun x hx hTx ↦ by
    have : φ v ≤ φ x := hvmin ⟨mem_sphere_zero_iff_norm.2 hx, hTx⟩
    linarith
  obtain ⟨P, hP⟩ := exists_le_norm_det_id_sub_smul H
  -- Choose `δ > 0` small enough for all the estimates below.
  have hsmall (K L : ℝ) (hL : 0 < L) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * K < L :=
    nhdsWithin_le_nhds (((continuous_id.mul continuous_const).tendsto' 0 0
      (zero_mul K)).eventually (gt_mem_nhds hL))
  obtain ⟨δ, ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, hδ⟩ := ((((hsmall (‖H‖ ^ 2) s hs).and
    (hsmall (‖H‖ + s / 2) r hr)).and (hsmall P (s / 2) (half_pos hs))).and
    (hsmall 1 1 one_pos)).and (hsmall (s / 2) 1 one_pos) |>.and self_mem_nhdsWithin |>.exists
  replace h₄ : δ < 1 := by simpa using h₄
  set c := 1 - δ * (s / 2) with hc_def
  have hc : 0 < c := by linarith
  have hTA := norm_comp_id_sub_smul_le hT.norm_le_one H hδ hc hrK h₁ h₂
  -- Rescaling `T ∘ (1 - δ H)` by `c⁻¹` gives a contraction, whose volume ratio is
  -- `c⁻ⁿ ‖det (1 - δ H)‖ ≥ c⁻ⁿ (1 - P δ²) > c⁻ⁿ c ≥ 1`.
  have hS : ‖((c⁻¹ : ℝ) : 𝕜) •
      (T : E →L[𝕜] F).comp (ContinuousLinearMap.id 𝕜 E - (δ : 𝕜) • H)‖ ≤ 1 := by
    rw [norm_smul, norm_ofReal, abs_of_pos (inv_pos.2 hc)]
    exact (inv_mul_le_one₀ hc).2 hTA
  have hdet := hT.norm_det_le_one _ hS
  rw [ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_assoc, T.coe_symm_comp_coe,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.det_smul, norm_mul, norm_pow, norm_ofReal,
    abs_of_pos (inv_pos.2 hc), inv_pow, inv_mul_le_one₀ (pow_pos hc _)] at hdet
  have hA := hP δ ⟨hδ.le, h₄.le⟩
  have hcn : c ^ finrank 𝕜 E ≤ c := pow_le_of_le_one hc.le (by nlinarith) finrank_pos.ne'
  have h₆ : δ * (δ * P) < δ * (s / 2) := mul_lt_mul_of_pos_left h₃ hδ
  have h₇ : 0 ≤ δ * -re (LinearMap.trace 𝕜 E H) := mul_nonneg hδ.le (neg_nonneg.2 hH)
  nlinarith

/-- In the coordinates of an orthonormal basis `b`, the identity divided by the dimension is a
convex combination of the matrices `(⟪bⱼ, u⟫ ⟪u, bₖ⟫)ⱼₖ` of the maps `x ↦ ⟪u, x⟫ u` at contact
points `u`. Otherwise a functional separating it from their convex hull, which is compact, would
give an operator contradicting `exists_contact_re_inner_apply_nonpos`. -/
private theorem inv_finrank_smul_mem_convexHull [Nontrivial E] (hT : T.IsMaxVolumeEllipsoid)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    (finrank 𝕜 E : ℝ)⁻¹ • (fun p : ι × ι ↦ ⟪b p.1, b p.2⟫_𝕜) ∈
      convexHull ℝ ((fun u (p : ι × ι) ↦ ⟪b p.1, u⟫_𝕜 * ⟪u, b p.2⟫_𝕜) ''
        (sphere (0 : E) 1 ∩ {u | ‖T u‖ = 1})) := by
  classical
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  set n := finrank 𝕜 E
  set M : E → ι × ι → 𝕜 := fun u p ↦ ⟪b p.1, u⟫_𝕜 * ⟪u, b p.2⟫_𝕜
  set I₀ : ι × ι → 𝕜 := fun p ↦ ⟪b p.1, b p.2⟫_𝕜
  have hQ : IsCompact (convexHull ℝ (M '' (sphere (0 : E) 1 ∩ {u | ‖T u‖ = 1}))) :=
    (((isCompact_sphere (0 : E) 1).inter_right (isClosed_eq
      (by fun_prop : Continuous fun x ↦ ‖T x‖) continuous_const)).image
      (by fun_prop : Continuous M)).convexHull
  by_contra hx
  obtain ⟨f, t, hft, hfQ⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := 𝕜)
    (convex_convexHull ℝ _) hQ.isClosed hx
  -- Write `f` against the standard basis of `ι × ι → 𝕜`, and transport it to an operator `H`.
  set e : ι × ι → ι × ι → 𝕜 := fun p q ↦ if p = q then 1 else 0
  have hf (v : ι × ι → 𝕜) : f v = ∑ p, v p * f (e p) := by
    simpa [smul_eq_mul] using (f : (ι × ι → 𝕜) →ₗ[𝕜] 𝕜).pi_apply_eq_sum_univ v
  let H : E →L[𝕜] E :=
    ∑ p, f (e p) • rankOne 𝕜 (b p.2) (b p.1) - (t : 𝕜) • ContinuousLinearMap.id 𝕜 E
  have hHu (u : E) (hu : ‖u‖ = 1) : re ⟪u, H u⟫_𝕜 = re (f (M u)) - t := by
    rw [hf (M u)]
    simp only [H, _root_.sub_apply, _root_.sum_apply, _root_.smul_apply, rankOne_apply,
      ContinuousLinearMap.id_apply, inner_sub_right, inner_sum, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hu, M]
    simp [mul_comm]
  have htr : re (LinearMap.trace 𝕜 E H) = re (f I₀) - t * n := by
    have hθ : LinearMap.trace 𝕜 E H =
        ((LinearMap.trace 𝕜 E).comp (ContinuousLinearMap.coeLM 𝕜)) H := rfl
    rw [hf I₀, hθ]
    simp [H, trace_rankOne, I₀, n, mul_comm]
  have hfI : re (f ((n : ℝ)⁻¹ • I₀)) = (n : ℝ)⁻¹ * re (f I₀) := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), ContinuousLinearMap.map_smul, smul_eq_mul,
      re_ofReal_mul]
  rw [hfI, inv_mul_lt_iff₀ (Nat.cast_pos.2 finrank_pos)] at hft
  obtain ⟨u, hu, hTu, hle⟩ := hT.exists_contact_re_inner_apply_nonpos H (by linarith)
  have := hfQ (M u) (subset_convexHull ℝ _ ⟨u, ⟨mem_sphere_zero_iff_norm.2 hu, hTu⟩, rfl⟩)
  linarith [hHu u hu]

/-- **John's theorem.** A maximal-volume ellipsoid `T : E ≃L[𝕜] F` decomposes the identity of the
inner product space `E` over its contact points: there are unit vectors `uᵢ` with `‖T uᵢ‖ = 1` and
positive weights `cᵢ` summing to the dimension of `E` such that `∑ cᵢ ⟪uᵢ, x⟫ uᵢ = x` for every
`x`.

In terms of the norm `x ↦ ‖T x‖` on `E`, whose closed unit ball is then in John's position, the
`uᵢ` are points of the Euclidean unit sphere on the boundary of that ball, and `re ⟪·, uᵢ⟫` is a
support functional of the ball at `uᵢ` (`ContinuousLinearMap.re_inner_le_norm_mul_norm_apply`). -/
theorem exists_sum_rankOne_eq_id (hT : T.IsMaxVolumeEllipsoid) :
    ∃ (m : ℕ) (u : Fin m → E) (c : Fin m → ℝ), (∀ i, ‖u i‖ = 1 ∧ ‖T (u i)‖ = 1) ∧
      (∀ i, 0 < c i) ∧ ∑ i, c i = finrank 𝕜 E ∧
      ∑ i, (c i : 𝕜) • rankOne 𝕜 (u i) (u i) = ContinuousLinearMap.id 𝕜 E := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_, ?_⟩
    · simp [finrank_zero_of_subsingleton]
    · ext x
      exact Subsingleton.elim _ _
  set n := finrank 𝕜 E
  have hn : 0 < n := finrank_pos
  let b := stdOrthonormalBasis 𝕜 E
  -- Read off the decomposition from a convex combination given by Carathéodory's theorem.
  obtain ⟨ι, _, z, w, hzs, -, hw₀, hw₁, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull (hT.inv_finrank_smul_mem_convexHull b)
  choose u hu hMu using fun i ↦ hzs (mem_range_self i)
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, u ∘ σ.symm, fun j ↦ n * w (σ.symm j), fun j ↦ ?_, fun j ↦ ?_, ?_, ?_⟩
  · exact ⟨mem_sphere_zero_iff_norm.1 (hu _).1, (hu _).2⟩
  · exact mul_pos (Nat.cast_pos.2 hn) (hw₀ _)
  · rw [σ.symm.sum_comp (fun i ↦ (n : ℝ) * w i), ← Finset.mul_sum, hw₁, mul_one]
  simp only [Function.comp_apply]
  rw [σ.symm.sum_comp (fun i ↦ (((n : ℝ) * w i : ℝ) : 𝕜) • rankOne 𝕜 (u i) (u i))]
  -- Compare the matrix coefficients `⟪bⱼ, · bₖ⟫` of both sides.
  apply ContinuousLinearMap.coe_injective
  refine b.toBasis.ext fun k ↦ ext_inner_left_basis b.toBasis fun j ↦ ?_
  have hjk := congrFun hwz (j, k)
  simp only [Finset.sum_apply, Pi.smul_apply, ← hMu, RCLike.real_smul_eq_coe_mul] at hjk
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, _root_.sum_apply,
    _root_.smul_apply, rankOne_apply, ContinuousLinearMap.id_apply, inner_sum, inner_smul_right]
  have hn' : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  calc ∑ i, ((n * w i : ℝ) : 𝕜) * (⟪u i, b k⟫_𝕜 * ⟪b j, u i⟫_𝕜)
      = n * ∑ i, (w i : 𝕜) * (⟪b j, u i⟫_𝕜 * ⟪u i, b k⟫_𝕜) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        push_cast
        ring
    _ = ⟪b j, b k⟫_𝕜 := by
        rw [hjk]
        push_cast
        exact mul_inv_cancel_left₀ hn' _

/-- Pairing John's decomposition with `x` gives `‖x‖² = ∑ cᵢ ‖⟪uᵢ, x⟫‖² ≤ n ‖T x‖²`: a
maximal-volume ellipsoid `T` satisfies `‖x‖ ≤ √n ‖T x‖`, where `n` is the dimension. -/
theorem norm_le_sqrt_finrank_mul_norm_apply (hT : T.IsMaxVolumeEllipsoid) (x : E) :
    ‖x‖ ≤ √(finrank 𝕜 E) * ‖T x‖ := by
  obtain ⟨m, u, c, hu, hc, hcsum, hid⟩ := hT.exists_sum_rankOne_eq_id
  have hx : ‖x‖ ^ 2 = ∑ i, c i * ‖⟪u i, x⟫_𝕜‖ ^ 2 := by
    have := congrArg (fun A : E →L[𝕜] E ↦ re ⟪x, A x⟫_𝕜) hid
    simp only [_root_.sum_apply, _root_.smul_apply, rankOne_apply, ContinuousLinearMap.id_apply,
      inner_sum, inner_smul_right, map_sum, re_ofReal_mul, inner_self_eq_norm_sq] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← inner_conj_symm x (u i), RCLike.mul_conj, ← ofReal_pow, ofReal_re]
  have hle : ∑ i, c i * ‖⟪u i, x⟫_𝕜‖ ^ 2 ≤ ∑ i, c i * ‖T x‖ ^ 2 := by
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hc i).le
    have := (T : E →L[𝕜] F).norm_inner_le_norm_mul_norm_apply hT.norm_le_one
      (u := u i) (by simp [(hu i).1, (hu i).2]) x
    rw [(hu i).1, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [← Finset.sum_mul, hcsum, ← hx] at hle
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (norm_nonneg (T x)),
    ← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt hle

/-- The inverse of a maximal-volume ellipsoid has norm at most `√n`, where `n` is the
dimension. -/
theorem norm_symm_le_sqrt_finrank (hT : T.IsMaxVolumeEllipsoid) :
    ‖(T.symm : F →L[𝕜] E)‖ ≤ √(finrank 𝕜 E) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y ↦ by
    simpa using hT.norm_le_sqrt_finrank_mul_norm_apply (T.symm y)

end ContinuousLinearEquiv.IsMaxVolumeEllipsoid

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- **John's distance bound.** A finite-dimensional normed space `F` is at Banach–Mazur distance at
most `√n` from any inner product space `E` of the same dimension `n`. -/
theorem banachMazurDist_le_sqrt_finrank (h : finrank 𝕜 E = finrank 𝕜 F) :
    banachMazurDist 𝕜 E F ≤ √(finrank 𝕜 E) := by
  obtain ⟨T, hT⟩ := exists_isMaxVolumeEllipsoid h
  calc banachMazurDist 𝕜 E F ≤ ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ :=
        banachMazurDist_le T
    _ ≤ 1 * √(finrank 𝕜 E) :=
        mul_le_mul hT.norm_le_one hT.norm_symm_le_sqrt_finrank (norm_nonneg _) zero_le_one
    _ = √(finrank 𝕜 E) := one_mul _

/-- An `n`-dimensional normed space is at Banach–Mazur distance at most `√n` from
`EuclideanSpace 𝕜 (Fin n)`. -/
theorem banachMazurDist_euclideanSpace_le_sqrt_finrank :
    banachMazurDist 𝕜 F (EuclideanSpace 𝕜 (Fin (finrank 𝕜 F))) ≤ √(finrank 𝕜 F) := by
  rw [banachMazurDist_comm]
  simpa using banachMazurDist_le_sqrt_finrank (𝕜 := 𝕜)
    (E := EuclideanSpace 𝕜 (Fin (finrank 𝕜 F))) (F := F) (by simp)

end TauCeti
