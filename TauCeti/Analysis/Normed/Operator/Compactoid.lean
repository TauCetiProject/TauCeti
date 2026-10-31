/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Module.Compactoid
public import TauCeti.Analysis.Normed.Operator.CompletelyContinuous

/-!
# Operators with compactoid image

A continuous linear map `u : E →L[K] F` between normed spaces over a normed field `K` *has
compactoid image* (`ContinuousLinearMap.HasCompactoidImage`) if it maps the closed unit ball of
`E` to a compactoid subset of `F`. These are the compact operators of nonarchimedean Banach space
theory in the sense of Schikhof: over a field such as `ℂ_p`, which is not locally compact, the
topological notion `IsCompactOperator` is too restrictive (the identity of a line has finite rank
but is not a compact operator), and compactoidness of the image of the unit ball replaces relative
compactness.

Over a nontrivially normed field, an operator has compactoid image exactly when it maps every
bounded set to a compactoid set (`ContinuousLinearMap.hasCompactoidImage_iff_forall_isBounded`).
Operators with compactoid image form a closed two-sided operator ideal: they are stable under
sums, scalar multiples and composition on either side with continuous linear maps, and under
limits in operator norm (`ContinuousLinearMap.isClosed_setOf_hasCompactoidImage`). Topologically
compact operators have compactoid image (`IsCompactOperator.hasCompactoidImage`). Over a complete
nontrivially normed field, so do completely continuous operators, the operator-norm limits of maps
of finite rank (`ContinuousLinearMap.IsCompletelyContinuous.hasCompactoidImage`). Between the
model spaces `C₀(I, K)` over a complete ultrametric field the converse holds too, combining the
comparison with row compactness (`ContinuousLinearMap.isRowCompact_iff_hasCompactoidImage`) with
Serre's criterion (`ContinuousLinearMap.isRowCompact_iff_isCompletelyContinuous`).

## Main definitions

* `ContinuousLinearMap.HasCompactoidImage`: the image of the closed unit ball is compactoid.

## Main results

* `ContinuousLinearMap.hasCompactoidImage_iff_forall_isBounded`: compactoid image of every
  bounded set.
* `ContinuousLinearMap.HasCompactoidImage.add`, `ContinuousLinearMap.HasCompactoidImage.smul`,
  `ContinuousLinearMap.HasCompactoidImage.clm_comp`,
  `ContinuousLinearMap.HasCompactoidImage.comp_clm`,
  `ContinuousLinearMap.isClosed_setOf_hasCompactoidImage`: the closed operator ideal.
* `IsCompactOperator.hasCompactoidImage`: compact operators have compactoid image.
* `LinearMap.IsFiniteRank.hasCompactoidImage`,
  `ContinuousLinearMap.IsCompletelyContinuous.hasCompactoidImage`: over a complete field, maps of
  finite rank and completely continuous maps have compactoid image.

## References

* W. H. Schikhof, *Banach spaces over nonarchimedean valued fields*, Topology Proceedings **24**
  (1999), 547–581, §2.15.
* N. De Grande-De Kimpe, *Non-archimedean nuclearity*, Groupe de travail d'analyse
  ultramétrique **9**, no. 3 (1981–1982), exp. J4, §2.1.
-/

public section

open Metric Bornology Pointwise TauCeti

namespace ContinuousLinearMap

variable {K E F G : Type*}

section NormedField

variable [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [SeminormedAddCommGroup G] [NormedSpace K G]

/-- A continuous linear map **has compactoid image** if it maps the closed unit ball to a
compactoid set. -/
def HasCompactoidImage (u : E →L[K] F) : Prop :=
  IsCompactoidSet K (u '' closedBall 0 1)

theorem hasCompactoidImage_iff {u : E →L[K] F} :
    u.HasCompactoidImage ↔ IsCompactoidSet K (u '' closedBall 0 1) :=
  Iff.rfl

@[simp]
theorem hasCompactoidImage_zero : (0 : E →L[K] F).HasCompactoidImage :=
  (Set.finite_singleton 0).isCompactoidSet.mono (Set.image_subset_iff.2 fun _ _ ↦ rfl)

/-- The sum of two maps with compactoid image has compactoid image. -/
theorem HasCompactoidImage.add {u v : E →L[K] F} (hu : u.HasCompactoidImage)
    (hv : v.HasCompactoidImage) : (u + v).HasCompactoidImage :=
  (IsCompactoidSet.add hu hv).mono <| Set.image_subset_iff.2 fun _ hx ↦
    Set.add_mem_add (Set.mem_image_of_mem u hx) (Set.mem_image_of_mem v hx)

/-- A scalar multiple of a map with compactoid image has compactoid image. -/
theorem HasCompactoidImage.smul {u : E →L[K] F} (hu : u.HasCompactoidImage) (c : K) :
    (c • u).HasCompactoidImage :=
  (IsCompactoidSet.smul hu c).mono <| Set.image_subset_iff.2 fun _ hx ↦
    Set.smul_mem_smul_set (Set.mem_image_of_mem u hx)

/-- The negation of a map with compactoid image has compactoid image. -/
theorem HasCompactoidImage.neg {u : E →L[K] F} (hu : u.HasCompactoidImage) :
    (-u).HasCompactoidImage := by
  simpa using hu.smul (-1)

/-- A map has compactoid image exactly when its negation does. -/
@[simp]
theorem hasCompactoidImage_neg_iff {u : E →L[K] F} :
    (-u).HasCompactoidImage ↔ u.HasCompactoidImage :=
  ⟨fun h ↦ by simpa using h.neg, HasCompactoidImage.neg⟩

/-- The difference of two maps with compactoid image has compactoid image. -/
theorem HasCompactoidImage.sub {u v : E →L[K] F} (hu : u.HasCompactoidImage)
    (hv : v.HasCompactoidImage) : (u - v).HasCompactoidImage := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- Postcomposing a map with compactoid image with a continuous linear map gives a map with
compactoid image. -/
theorem HasCompactoidImage.clm_comp {u : E →L[K] F} (hu : u.HasCompactoidImage)
    (v : F →L[K] G) : (v.comp u).HasCompactoidImage := by
  rw [HasCompactoidImage, coe_comp, Set.image_comp]
  exact IsCompactoidSet.image hu v

/-- **Compactoid image is closed under uniform approximation.** A continuous linear map that is,
for every `ε > 0`, uniformly `ε`-close to a map with compactoid image has compactoid image. -/
theorem hasCompactoidImage_of_forall_approx {u : E →L[K] F}
    (h : ∀ ε : ℝ, 0 < ε → ∃ v : E →L[K] F, v.HasCompactoidImage ∧
      ∀ x, ‖u x - v x‖ ≤ ε * ‖x‖) :
    u.HasCompactoidImage := by
  refine isCompactoidSet_of_forall_exists_norm_sub_lt fun ε hε ↦ ?_
  obtain ⟨v, hv, huv⟩ := h (ε / 2) (half_pos hε)
  refine ⟨_, hv, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨v x, Set.mem_image_of_mem v hx, (huv x).trans_lt ?_⟩
  calc ε / 2 * ‖x‖ ≤ ε / 2 * 1 := by gcongr; simpa using hx
    _ < ε := by linarith

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [SeminormedAddCommGroup G] [NormedSpace K G]

/-- Over a nontrivially normed field, a continuous linear map has compactoid image exactly when it
maps every bounded set to a compactoid set. -/
theorem hasCompactoidImage_iff_forall_isBounded {u : E →L[K] F} :
    u.HasCompactoidImage ↔ ∀ S : Set E, IsBounded S → IsCompactoidSet K (u '' S) := by
  refine ⟨fun hu S hS ↦ ?_, fun h ↦ h _ isBounded_closedBall⟩
  obtain ⟨a, ha⟩ := (NormedSpace.isBounded_iff_subset_smul_closedBall K).1 hS
  exact (IsCompactoidSet.smul hu a).mono ((Set.image_mono ha).trans (image_smul_set u a _).subset)

/-- Precomposing a map with compactoid image with a continuous linear map gives a map with
compactoid image. -/
theorem HasCompactoidImage.comp_clm {u : F →L[K] G} (hu : u.HasCompactoidImage)
    (v : E →L[K] F) : (u.comp v).HasCompactoidImage := by
  rw [HasCompactoidImage, coe_comp, Set.image_comp]
  exact hasCompactoidImage_iff_forall_isBounded.1 hu _ (isBounded_closedBall.image v)

/-- **Compactoid image is closed in operator norm.** -/
theorem isClosed_setOf_hasCompactoidImage : IsClosed {u : E →L[K] F | u.HasCompactoidImage} := by
  refine isClosed_of_closure_subset fun u hu ↦ hasCompactoidImage_of_forall_approx fun ε hε ↦ ?_
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu ε hε
  rw [dist_eq_norm] at huv
  exact ⟨v, hv, fun x ↦ by simpa using (u - v).le_of_opNorm_le huv.le x⟩

end NontriviallyNormedField

end ContinuousLinearMap

/-- **Compact operators have compactoid image.** A continuous linear map that is a compact
operator in the topological sense maps the closed unit ball into a compact set, which is
compactoid. -/
theorem IsCompactOperator.hasCompactoidImage {K E F : Type*} [NontriviallyNormedField K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [SeminormedAddCommGroup F] [NormedSpace K F]
    {u : E →L[K] F} (hu : IsCompactOperator u) : u.HasCompactoidImage := by
  obtain ⟨C, hC, hsub⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := (u : E →ₗ[K] F)) hu 1
  exact hC.isCompactoidSet.mono hsub

section Complete

variable {K E F : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [SeminormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]

open ContinuousLinearMap

/-- Over a complete nontrivially normed field, **a map of finite rank has compactoid image**: the
image of the closed unit ball is a bounded subset of a finite-dimensional subspace. -/
theorem LinearMap.IsFiniteRank.hasCompactoidImage {u : E →L[K] F}
    (hu : (u : E →ₗ[K] F).IsFiniteRank) : u.HasCompactoidImage := by
  obtain ⟨Q, hQ, hQu⟩ := LinearMap.isFiniteRank_iff_forall_mem.1 hu
  have : FiniteDimensional K Q := Module.Finite.iff_fg.2 hQ
  -- The image of the closed unit ball, viewed inside `Q`, is bounded.
  have hb : IsBounded {y : Q | (y : F) ∈ u '' closedBall 0 1} := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 ((isBounded_closedBall (x := (0 : E))
      (r := 1)).image u)
    exact isBounded_iff_forall_norm_le.2 ⟨C, fun y hy ↦ by rw [← Submodule.norm_coe]; exact hC _ hy⟩
  refine (IsCompactoidSet.image hb.isCompactoidSet Q.subtypeL).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨u x, hQu x⟩, ⟨x, hx, rfl⟩, rfl⟩

/-- Over a complete nontrivially normed field, **completely continuous maps have compactoid
image**. -/
theorem ContinuousLinearMap.IsCompletelyContinuous.hasCompactoidImage {u : E →L[K] F}
    (hu : u.IsCompletelyContinuous) : u.HasCompactoidImage :=
  hasCompactoidImage_of_forall_approx fun ε hε ↦
    have ⟨v, hv, huv⟩ := isCompletelyContinuous_iff.1 hu ε hε
    ⟨v, hv.hasCompactoidImage, huv⟩

end Complete
