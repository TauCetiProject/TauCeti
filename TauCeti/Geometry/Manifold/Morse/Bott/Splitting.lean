/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
public import TauCeti.Geometry.Manifold.Morse.Bott.Index
public import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# The positive and negative normal spaces of a Morse–Bott critical submanifold

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold, with its
normal Hessian `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`, a symmetric bilinear
form on each normal space `TangentSpace I (i s) ⧸ range (mfderiv J I i s)`. A fibre metric `g` on
the normal spaces, given as a Mathlib `Bundle.RiemannianMetric` (for instance the metric
`TauCeti.SmoothEmbedding.normalRiemannianMetric` induced by a Riemannian metric on `M`), splits
the normal Hessian into its negative and positive parts: the **negative normal space** at `s` is
the span of the normal vectors `v` with `Hess v = μ g v` for some `μ < 0`, and the **positive
normal space** is the span of those with `μ > 0`
(`LinearMap.BilinForm.relativeSpectralSubspace`).

The normal Hessian is negative definite on the negative normal space and positive definite on the
positive one, and the two spaces are orthogonal both for `g` and for the normal Hessian. For a
Morse–Bott submanifold the normal Hessian is nondegenerate, so the two spaces are complementary,
and their dimensions are the Morse indices of `f` and of `-f` at `i s`. In particular these
dimensions do not depend on the metric `g`, although the subspaces themselves do, and they are
locally constant along `S`. These are the fibres of the negative and positive normal bundles
`ν⁻` and `ν⁺`, whose disc bundles are attached when a Morse–Bott critical level is crossed.

The complementarity holds across metrics: the negative normal space for one fibre metric `g` and
the positive normal space for another metric `g'` are complementary as well, because the normal
Hessian is negative definite on the first and positive definite on the second. Hence projecting
along the positive normal space for `g'` identifies the negative normal spaces for `g` and `g'`
(`IsNondegenerateCriticalSubmanifold.negativeNormalSpaceEquiv`), and projecting along the
negative normal space for `g'` identifies the positive ones
(`IsNondegenerateCriticalSubmanifold.positiveNormalSpaceEquiv`). These identifications vary
smoothly when the metrics do, so the isomorphism classes of `ν⁻` and `ν⁺` do not depend on the
metric (`TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle`).

## Main declarations

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.negativeNormalSpace` and `IsCriticalSubmanifold.positiveNormalSpace`:
  the negative and positive normal spaces of a critical submanifold relative to a fibre metric.
* `IsCriticalSubmanifold.normalHessian_apply_self_neg_of_mem_negativeNormalSpace` and
  `IsCriticalSubmanifold.normalHessian_apply_self_pos_of_mem_positiveNormalSpace`: the normal
  Hessian is negative definite on the negative normal space and positive definite on the positive
  normal space.
* `IsCriticalSubmanifold.inner_eq_zero_of_mem_negativeNormalSpace` and
  `IsCriticalSubmanifold.normalHessian_eq_zero_of_mem_negativeNormalSpace`: the two spaces are
  orthogonal for the metric and for the normal Hessian.
* `IsNondegenerateCriticalSubmanifold.isCompl_negativeNormalSpace_positiveNormalSpace`: for a
  Morse–Bott submanifold the normal space is the direct sum of the negative normal space for one
  fibre metric and the positive normal space for any other.
* `IsNondegenerateCriticalSubmanifold.negativeNormalProjection`: the projection onto the negative
  normal space along the positive one, and
  `IsNondegenerateCriticalSubmanifold.normalHessian_apply_eq_add`: the normal Hessian splits along
  it.
* `IsNondegenerateCriticalSubmanifold.finrank_negativeNormalSpace` and
  `IsNondegenerateCriticalSubmanifold.finrank_positiveNormalSpace`: their dimensions are the
  Morse indices of `f` and of `-f`.
* `IsNondegenerateCriticalSubmanifold.negativeNormalSpaceEquiv` and
  `IsNondegenerateCriticalSubmanifold.positiveNormalSpaceEquiv`: the negative, respectively
  positive, normal spaces for two fibre metrics are identified by projection along the positive,
  respectively negative, normal space for the second metric.
* `IsNondegenerateCriticalSubmanifold.isLocallyConstant_finrank_negativeNormalSpace` and
  `IsNondegenerateCriticalSubmanifold.isLocallyConstant_finrank_positiveNormalSpace`: these
  dimensions are locally constant along the submanifold.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331–358.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)

namespace IsCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
  (g : RiemannianMetric fun s ↦ i.NormalSpace s hn) {s : S} {v w : i.NormalSpace s hn}

/-- The **negative normal space** of a critical submanifold at `s`, relative to a fibre metric
`g` on the normal spaces: the span of the normal vectors `v` with `Hess v = μ g v` for some
`μ < 0`, where `Hess` is the normal Hessian. -/
def negativeNormalSpace (s : S) : Submodule ℝ (i.NormalSpace s hn) :=
  (g.inner s).toBilinForm.relativeSpectralSubspace (h.normalHessian hn s) (Iio 0)

/-- The **positive normal space** of a critical submanifold at `s`, relative to a fibre metric
`g` on the normal spaces: the span of the normal vectors `v` with `Hess v = μ g v` for some
`μ > 0`, where `Hess` is the normal Hessian. -/
def positiveNormalSpace (s : S) : Submodule ℝ (i.NormalSpace s hn) :=
  (g.inner s).toBilinForm.relativeSpectralSubspace (h.normalHessian hn s) (Ioi 0)

/-- The negative normal space is the relative spectral subspace of the normal Hessian selected by
the negative reals. -/
theorem negativeNormalSpace_def :
    h.negativeNormalSpace hn g s =
      (g.inner s).toBilinForm.relativeSpectralSubspace (h.normalHessian hn s) (Iio 0) :=
  (rfl)

/-- The positive normal space is the relative spectral subspace of the normal Hessian selected by
the positive reals. -/
theorem positiveNormalSpace_def :
    h.positiveNormalSpace hn g s =
      (g.inner s).toBilinForm.relativeSpectralSubspace (h.normalHessian hn s) (Ioi 0) :=
  (rfl)

/-- **The negative and positive normal spaces are orthogonal for the metric `g`.** -/
theorem inner_eq_zero_of_mem_negativeNormalSpace (hv : v ∈ h.negativeNormalSpace hn g s)
    (hw : w ∈ h.positiveNormalSpace hn g s) : g.inner s v w = 0 :=
  (LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace
    (g.isSymm_toBilinForm_inner s) (h.isSymm_normalHessian hn s) Iio_disjoint_Ioi_same hv hw).1

/-- **The negative and positive normal spaces are orthogonal for the normal Hessian.** -/
theorem normalHessian_eq_zero_of_mem_negativeNormalSpace (hv : v ∈ h.negativeNormalSpace hn g s)
    (hw : w ∈ h.positiveNormalSpace hn g s) : h.normalHessian hn s v w = 0 :=
  (LinearMap.BilinForm.apply_eq_zero_of_mem_relativeSpectralSubspace
    (g.isSymm_toBilinForm_inner s) (h.isSymm_normalHessian hn s) Iio_disjoint_Ioi_same hv hw).2

/-- The negative and positive normal spaces meet only in `0`. -/
theorem disjoint_negativeNormalSpace_positiveNormalSpace :
    Disjoint (h.negativeNormalSpace hn g s) (h.positiveNormalSpace hn g s) :=
  LinearMap.BilinForm.disjoint_relativeSpectralSubspace_of_pos (g.isSymm_toBilinForm_inner s)
    (g.pos s) (h.isSymm_normalHessian hn s) Iio_disjoint_Ioi_same

variable [FiniteDimensional ℝ E]

/-- **The normal Hessian is negative definite on the negative normal space.** -/
theorem normalHessian_apply_self_neg_of_mem_negativeNormalSpace
    (hv : v ∈ h.negativeNormalSpace hn g s) (hv0 : v ≠ 0) : h.normalHessian hn s v v < 0 :=
  LinearMap.BilinForm.apply_self_neg_of_mem_relativeSpectralSubspace_Iio
    (g.isSymm_toBilinForm_inner s) (g.pos s) (h.isSymm_normalHessian hn s) hv hv0

/-- **The normal Hessian is positive definite on the positive normal space.** -/
theorem normalHessian_apply_self_pos_of_mem_positiveNormalSpace
    (hv : v ∈ h.positiveNormalSpace hn g s) (hv0 : v ≠ 0) : 0 < h.normalHessian hn s v v :=
  LinearMap.BilinForm.apply_self_pos_of_mem_relativeSpectralSubspace_Ioi
    (g.isSymm_toBilinForm_inner s) (g.pos s) (h.isSymm_normalHessian hn s) hv hv0

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] [FiniteDimensional ℝ E]
  (h : i.IsNondegenerateCriticalSubmanifold f) (g g' : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- **The negative normal space has the dimension of the Morse index**, for every fibre metric. -/
theorem finrank_negativeNormalSpace (s : S) :
    Module.finrank ℝ (h.negativeNormalSpace hn g s) = manifoldMorseIndex I f (i s) := by
  rw [IsCriticalSubmanifold.negativeNormalSpace_def,
    LinearMap.BilinForm.finrank_relativeSpectralSubspace_Iio
      (g.isSymm_toBilinForm_inner s) (g.pos s)
      (h.isSymm_normalHessian hn s),
    h.sigNeg_normalHessian hn s]

/-- **The positive normal space has the dimension of the Morse index of `-f`**, for every fibre
metric. -/
theorem finrank_positiveNormalSpace (s : S) :
    Module.finrank ℝ (h.positiveNormalSpace hn g s) = manifoldMorseIndex I (-f) (i s) := by
  rw [IsCriticalSubmanifold.positiveNormalSpace_def,
    LinearMap.BilinForm.finrank_relativeSpectralSubspace_Ioi
      (g.isSymm_toBilinForm_inner s) (g.pos s)
      (h.isSymm_normalHessian hn s),
    h.sigPos_normalHessian hn s]

/-- **The normal space of a Morse–Bott submanifold splits into its negative and positive parts.**
Since the normal Hessian is nondegenerate, the negative normal space relative to a fibre metric `g`
and the positive normal space relative to a fibre metric `g'` are complementary. The two metrics
may differ: the normal Hessian is negative definite on the first space and positive definite on
the second, so they meet only in `0`, and their dimensions are the Morse indices of `f` and `-f`,
which add up to the rank of the normal bundle. -/
theorem isCompl_negativeNormalSpace_positiveNormalSpace (s : S) :
    IsCompl (h.negativeNormalSpace hn g s) (h.positiveNormalSpace hn g' s) := by
  have hsplit : IsCompl (h.negativeNormalSpace hn g' s) (h.positiveNormalSpace hn g' s) :=
    LinearMap.BilinForm.isCompl_relativeSpectralSubspace_Iio_Ioi
      (g'.isSymm_toBilinForm_inner s) (g'.pos s)
      (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s)
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 (Submodule.disjoint_def.2 fun v hv hv' ↦ ?_)
  · rw [← Submodule.finrank_add_eq_of_isCompl hsplit, h.finrank_negativeNormalSpace hn g,
      h.finrank_negativeNormalSpace hn g']
  · by_contra hv0
    exact (h.normalHessian_apply_self_neg_of_mem_negativeNormalSpace hn g hv hv0).not_gt
      (h.normalHessian_apply_self_pos_of_mem_positiveNormalSpace hn g' hv' hv0)

/-- The projection of the normal space of a Morse–Bott submanifold onto its negative normal space
along its positive normal space, relative to the fibre metric `g`. -/
def negativeNormalProjection (s : S) : Module.End ℝ (i.NormalSpace s hn) :=
  (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
    (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s)

/-- The projection onto the negative normal space is the projection along the positive one. -/
theorem negativeNormalProjection_def (s : S) :
    h.negativeNormalProjection hn g s =
      (h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s) :=
  (rfl)

/-- The range of the projection is the negative normal space. -/
@[simp]
theorem range_negativeNormalProjection (s : S) :
    LinearMap.range (h.negativeNormalProjection hn g s) = h.negativeNormalSpace hn g s :=
  Submodule.range_projection _

/-- The kernel of the projection is the positive normal space. -/
@[simp]
theorem ker_negativeNormalProjection (s : S) :
    LinearMap.ker (h.negativeNormalProjection hn g s) = h.positiveNormalSpace hn g s :=
  Submodule.ker_projection _

/-- The component of a normal vector along the negative normal space lies in it. -/
@[simp]
theorem negativeNormalProjection_apply_mem {s : S} (v : i.NormalSpace s hn) :
    h.negativeNormalProjection hn g s v ∈ h.negativeNormalSpace hn g s :=
  Submodule.projection_apply_mem _ v

/-- The component of a normal vector along the positive normal space lies in it. -/
@[simp]
theorem sub_negativeNormalProjection_apply_mem {s : S} (v : i.NormalSpace s hn) :
    v - h.negativeNormalProjection hn g s v ∈ h.positiveNormalSpace hn g s :=
  Submodule.sub_projection_mem _ v

/-- The projection fixes the negative normal space. -/
@[simp]
theorem negativeNormalProjection_apply_of_mem {s : S} {v : i.NormalSpace s hn}
    (hv : v ∈ h.negativeNormalSpace hn g s) : h.negativeNormalProjection hn g s v = v :=
  Submodule.projection_apply_of_mem_left _ hv

/-- The projection vanishes exactly on the positive normal space. -/
@[simp]
theorem negativeNormalProjection_apply_eq_zero_iff {s : S} {v : i.NormalSpace s hn} :
    h.negativeNormalProjection hn g s v = 0 ↔ v ∈ h.positiveNormalSpace hn g s :=
  Submodule.projection_apply_eq_zero_iff _

/-- The projection kills the positive normal space. -/
@[simp]
theorem negativeNormalProjection_apply_eq_zero_of_mem {s : S} {v : i.NormalSpace s hn}
    (hv : v ∈ h.positiveNormalSpace hn g s) : h.negativeNormalProjection hn g s v = 0 :=
  Submodule.projection_apply_of_mem_right _ hv

/-- The projection fixes exactly the negative normal space. -/
@[simp]
theorem negativeNormalProjection_apply_eq_self_iff {s : S} {v : i.NormalSpace s hn} :
    h.negativeNormalProjection hn g s v = v ↔ v ∈ h.negativeNormalSpace hn g s :=
  Submodule.projection_eq_self_iff _ _

/-- The projection onto the negative normal space is idempotent. -/
@[simp]
theorem isIdempotentElem_negativeNormalProjection (s : S) :
    IsIdempotentElem (h.negativeNormalProjection hn g s) :=
  Submodule.isIdempotentElem_projection _

/-- The projection of `v` is the unique `x` in the negative normal space with `v - x` in the
positive normal space. -/
theorem negativeNormalProjection_apply_eq_of_mem {s : S} {v x : i.NormalSpace s hn}
    (hx : x ∈ h.negativeNormalSpace hn g s) (hvx : v - x ∈ h.positiveNormalSpace hn g s) :
    h.negativeNormalProjection hn g s v = x := by
  conv_lhs => rw [← add_sub_cancel x v]
  rw [map_add, h.negativeNormalProjection_apply_of_mem hn g hx,
    h.negativeNormalProjection_apply_eq_zero_of_mem hn g hvx, add_zero]

/-- **The normal Hessian splits along the negative and positive normal spaces**: it is the sum of
its values on the negative components and on the positive components, the cross terms vanishing
by `IsCriticalSubmanifold.normalHessian_eq_zero_of_mem_negativeNormalSpace`. -/
theorem normalHessian_apply_eq_add {s : S} (v w : i.NormalSpace s hn) :
    h.normalHessian hn s v w =
      h.normalHessian hn s (h.negativeNormalProjection hn g s v)
          (h.negativeNormalProjection hn g s w) +
        h.normalHessian hn s (v - h.negativeNormalProjection hn g s v)
          (w - h.negativeNormalProjection hn g s w) := by
  have h₁ := h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn g
    (h.negativeNormalProjection_apply_mem hn g v) (h.sub_negativeNormalProjection_apply_mem hn g w)
  have h₂ := h.normalHessian_eq_zero_of_mem_negativeNormalSpace hn g
    (h.negativeNormalProjection_apply_mem hn g w) (h.sub_negativeNormalProjection_apply_mem hn g v)
  rw [(h.isSymm_normalHessian hn s).eq] at h₂
  set P := h.negativeNormalProjection hn g s
  conv_lhs => rw [← add_sub_cancel (P v) v, ← add_sub_cancel (P w) w]
  simp only [map_add, LinearMap.add_apply, h₁, h₂]
  ring

/-- **The negative normal spaces for two fibre metrics are isomorphic.** The negative normal
space relative to `g` is identified with the negative normal space relative to `g'` by projecting
along the positive normal space relative to `g'`: both are complements of that space
(`isCompl_negativeNormalSpace_positiveNormalSpace`). -/
def negativeNormalSpaceEquiv (s : S) :
    h.negativeNormalSpace hn g s ≃ₗ[ℝ] h.negativeNormalSpace hn g' s :=
  (Submodule.quotientEquivOfIsCompl _ _
      (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g' s).symm).symm.trans
    (Submodule.quotientEquivOfIsCompl _ _
      (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s).symm)

/-- The identification of the negative normal spaces for two fibre metrics is the projection onto
the negative normal space for `g'` along the positive normal space for `g'`. -/
@[simp]
theorem coe_negativeNormalSpaceEquiv_apply {s : S} (v : h.negativeNormalSpace hn g s) :
    (h.negativeNormalSpaceEquiv hn g g' s v : i.NormalSpace s hn) =
      h.negativeNormalProjection hn g' s v := by
  rw [negativeNormalProjection_def, negativeNormalSpaceEquiv, LinearEquiv.trans_apply,
    ← LinearEquiv.coe_toLinearMap (Submodule.quotientEquivOfIsCompl _ _ _).symm,
    Submodule.toLinearMap_symm_quotientEquivOfIsCompl, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.coe_projectionOnto_apply,
    Submodule.subtype_apply]

/-- For a single metric the identification of the negative normal spaces is the identity. -/
@[simp]
theorem negativeNormalSpaceEquiv_self (s : S) :
    h.negativeNormalSpaceEquiv hn g g s = LinearEquiv.refl ℝ _ := by
  ext v
  simp [h.negativeNormalProjection_apply_of_mem hn g v.2]

/-- **The positive normal spaces for two fibre metrics are isomorphic.** The positive normal
space relative to `g` is identified with the positive normal space relative to `g'` by projecting
along the negative normal space relative to `g'`: both are complements of that space
(`isCompl_negativeNormalSpace_positiveNormalSpace`). -/
def positiveNormalSpaceEquiv (s : S) :
    h.positiveNormalSpace hn g s ≃ₗ[ℝ] h.positiveNormalSpace hn g' s :=
  (Submodule.quotientEquivOfIsCompl _ _
      (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g s)).symm.trans
    (Submodule.quotientEquivOfIsCompl _ _
      (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s))

/-- The identification of the positive normal spaces for two fibre metrics is the projection onto
the positive normal space for `g'` along the negative normal space for `g'`. -/
@[simp]
theorem coe_positiveNormalSpaceEquiv_apply {s : S} (v : h.positiveNormalSpace hn g s) :
    (h.positiveNormalSpaceEquiv hn g g' s v : i.NormalSpace s hn) =
      (h.positiveNormalSpace hn g' s).projection (h.negativeNormalSpace hn g' s)
        (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g' g' s).symm v := by
  rw [positiveNormalSpaceEquiv, LinearEquiv.trans_apply,
    ← LinearEquiv.coe_toLinearMap (Submodule.quotientEquivOfIsCompl _ _ _).symm,
    Submodule.toLinearMap_symm_quotientEquivOfIsCompl, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.coe_projectionOnto_apply,
    Submodule.subtype_apply]

/-- For a single metric the identification of the positive normal spaces is the identity. -/
@[simp]
theorem positiveNormalSpaceEquiv_self (s : S) :
    h.positiveNormalSpaceEquiv hn g g s = LinearEquiv.refl ℝ _ := by
  ext v
  simp [Submodule.projection_apply_of_mem_left _ v.2]

/-- **The rank of the negative normal space is locally constant** along a Morse–Bott
submanifold. -/
theorem isLocallyConstant_finrank_negativeNormalSpace :
    IsLocallyConstant fun s ↦ Module.finrank ℝ (h.negativeNormalSpace hn g s) := by
  simpa only [h.finrank_negativeNormalSpace hn g] using h.isLocallyConstant_manifoldMorseIndex hn

/-- **The rank of the positive normal space is locally constant** along a Morse–Bott
submanifold. -/
theorem isLocallyConstant_finrank_positiveNormalSpace :
    IsLocallyConstant fun s ↦ Module.finrank ℝ (h.positiveNormalSpace hn g s) := by
  simpa only [h.finrank_positiveNormalSpace hn g] using
    h.neg.isLocallyConstant_manifoldMorseIndex hn

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
