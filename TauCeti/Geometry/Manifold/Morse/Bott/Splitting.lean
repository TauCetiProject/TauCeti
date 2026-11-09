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
  Morse–Bott submanifold the normal space is their direct sum.
* `IsNondegenerateCriticalSubmanifold.finrank_negativeNormalSpace` and
  `IsNondegenerateCriticalSubmanifold.finrank_positiveNormalSpace`: their dimensions are the
  Morse indices of `f` and of `-f`.
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
  LinearMap.BilinForm.disjoint_relativeSpectralSubspace (g.isSymm_toBilinForm_inner s)
    (fun v h ↦ by_contra fun hv ↦ (g.pos s v hv).ne' h) (h.isSymm_normalHessian hn s)
    Iio_disjoint_Ioi_same

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
  (h : i.IsNondegenerateCriticalSubmanifold f) (g : RiemannianMetric fun s ↦ i.NormalSpace s hn)

/-- **The normal space of a Morse–Bott submanifold splits into its negative and positive parts.**
Since the normal Hessian is nondegenerate, the negative and positive normal spaces relative to any
fibre metric are complementary. -/
theorem isCompl_negativeNormalSpace_positiveNormalSpace (s : S) :
    IsCompl (h.negativeNormalSpace hn g s) (h.positiveNormalSpace hn g s) :=
  LinearMap.BilinForm.isCompl_relativeSpectralSubspace_Iio_Ioi
    (g.isSymm_toBilinForm_inner s) (g.pos s)
    (h.isSymm_normalHessian hn s) (h.ker_normalHessian hn s)

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
