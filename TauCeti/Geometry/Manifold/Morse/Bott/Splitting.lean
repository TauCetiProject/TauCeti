/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
import TauCeti.Analysis.InnerProductSpace.Spectral.Inertia
import TauCeti.Geometry.Manifold.Morse.Bott.Index

/-!
# The negative and positive normal spaces of a Morse–Bott critical submanifold

Let `i : S → M` be a critical submanifold of a function `f` on a boundaryless manifold whose
tangent spaces carry a Riemannian metric. At a point `i s` the metric turns the critical Hessian
into a symmetric operator, its Riesz operator `Hess♯`, characterized by
`⟪Hess♯ v, w⟫ = Hess f (i s) (v, w)`. Its eigenvectors with negative, respectively positive,
eigenvalues span subspaces of the tangent space of `M` at `i s`, and their images in the normal
space `TangentSpace I (i s) ⧸ range (di)` are the **negative normal space**
(`TauCeti.SmoothEmbedding.negativeNormalSpace`) and the **positive normal space**
(`TauCeti.SmoothEmbedding.positiveNormalSpace`) of `f` along `i` at `s`. They are the fibres of the
negative and positive normal bundles of Bott's theory, along which a Morse–Bott function decreases,
respectively increases, away from its critical submanifold. Exchanging `f` with `-f` exchanges them
(`TauCeti.SmoothEmbedding.negativeNormalSpace_neg`).

The tangent space of the submanifold lies in the kernel of the Hessian, so both eigenvector spans
are orthogonal to it and the quotient map to the normal space is injective on them. Hence, for every
critical submanifold:

* the normal Hessian is negative definite on the negative normal space and positive definite on
  the positive normal space, and the two are orthogonal both for the normal Hessian and for the
  metric induced on the normal space;
* the negative normal space has dimension the Morse index of `f` at `i s`, and the positive normal
  space has dimension the Morse index of `-f`.

When the submanifold is nondegenerate, the kernel of the Hessian is exactly the tangent space of
the submanifold, so the tangent space of `M` at `i s` is the orthogonal sum of the two eigenvector
spans and of the tangent space of `S`, and the normal space is the direct sum of its negative and
positive parts; see the results in the namespace `IsNondegenerateCriticalSubmanifold` below. The
dimensions of these parts are then locally constant along `S`. The subspaces themselves depend
on the metric; their dimensions do not.

## Main definitions

* `TauCeti.SmoothEmbedding.negativeNormalSpace`: the negative normal space.
* `TauCeti.SmoothEmbedding.positiveNormalSpace`: the positive normal space.

## Main results

In the namespace `TauCeti.SmoothEmbedding`:

* `IsCriticalSubmanifold.normalHessian_apply_self_neg` and
  `IsCriticalSubmanifold.normalHessian_apply_self_pos`: definiteness of the normal Hessian.
* `normalHessian_eq_zero_of_mem_negativeNormalSpace_of_mem_positiveNormalSpace` and
  `normalRiemannianMetric_inner_eq_zero_of_mem_negativeNormalSpace_of_mem_positiveNormalSpace`, in
  the namespace `IsCriticalSubmanifold`: the negative and positive normal spaces are orthogonal for
  the normal Hessian and for the normal metric.
* `IsCriticalSubmanifold.pointSpectralSubspace_le_orthogonal`: the eigenvectors of `Hess♯` with
  nonzero eigenvalues are orthogonal to the tangent space of a critical submanifold.
* `IsCriticalSubmanifold.finrank_negativeNormalSpace` and
  `IsCriticalSubmanifold.finrank_positiveNormalSpace`: the dimensions are the Morse indices of `f`
  and of `-f`.
* `IsNondegenerateCriticalSubmanifold.pointSpectralSubspace_singleton_zero`: for a Morse–Bott
  submanifold the zero eigenspace of `Hess♯` is its tangent space.
* `IsNondegenerateCriticalSubmanifold.sup_pointSpectralSubspace_eq_orthogonal`: for a Morse–Bott
  submanifold the two eigenvector spans together span the orthogonal complement of its tangent
  space.
* `IsNondegenerateCriticalSubmanifold.isCompl_negativeNormalSpace_positiveNormalSpace`: for a
  Morse–Bott submanifold the normal space splits into its negative and positive parts.
* `IsNondegenerateCriticalSubmanifold.isLocallyConstant_finrank_negativeNormalSpace` and
  `IsNondegenerateCriticalSubmanifold.isLocallyConstant_finrank_positiveNormalSpace`: their ranks
  are locally constant along the submanifold.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

open Bundle Function InnerProductSpace Module Module.End Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {f : M → ℝ} {n : ℕ∞ω}

variable (i : SmoothEmbedding J I n S M) (f) in
/-- The **negative normal space** of `f` along the embedding `i` at `s`, for the Riemannian metric
on `M`: the image in the normal space of the span of the eigenvectors of the Riesz operator of the
critical Hessian of `f` at `i s` with negative eigenvalues. For a critical submanifold, the normal
Hessian is negative definite on it and its dimension is the Morse index. -/
def negativeNormalSpace (s : S) (hn : n ≠ 0) : Submodule ℝ (i.NormalSpace s hn) :=
  (pointSpectralSubspace
    (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
      TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Iio 0)).map (i.normalClass s hn)

variable (i : SmoothEmbedding J I n S M) (f) in
/-- The **positive normal space** of `f` along the embedding `i` at `s`, for the Riemannian metric
on `M`: the image in the normal space of the span of the eigenvectors of the Riesz operator of the
critical Hessian of `f` at `i s` with positive eigenvalues. For a critical submanifold, the normal
Hessian is positive definite on it and its dimension is the Morse index of `-f`. -/
def positiveNormalSpace (s : S) (hn : n ≠ 0) : Submodule ℝ (i.NormalSpace s hn) :=
  (pointSpectralSubspace
    (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
      TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Ioi 0)).map (i.normalClass s hn)

variable {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)

/-- The negative normal space is the image in the normal space of the span of the eigenvectors of
the Riesz operator of the critical Hessian with negative eigenvalues. -/
theorem negativeNormalSpace_def (s : S) :
    i.negativeNormalSpace f s hn =
      (pointSpectralSubspace
        (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
          TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Iio 0)).map (i.normalClass s hn) :=
  (rfl)

/-- The positive normal space is the image in the normal space of the span of the eigenvectors of
the Riesz operator of the critical Hessian with positive eigenvalues. -/
theorem positiveNormalSpace_def (s : S) :
    i.positiveNormalSpace f s hn =
      (pointSpectralSubspace
        (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
          TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Ioi 0)).map (i.normalClass s hn) :=
  (rfl)

/-- A normal class lies in the negative normal space exactly when it is the class of an
eigenvector combination of the Riesz operator of the critical Hessian with negative eigenvalues. -/
theorem mem_negativeNormalSpace_iff {s : S} {p : i.NormalSpace s hn} :
    p ∈ i.negativeNormalSpace f s hn ↔
      ∃ v ∈ pointSpectralSubspace
        (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
          TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Iio 0), i.normalClass s hn v = p := by
  rw [negativeNormalSpace_def, Submodule.mem_map]

/-- A normal class lies in the positive normal space exactly when it is the class of an
eigenvector combination of the Riesz operator of the critical Hessian with positive eigenvalues. -/
theorem mem_positiveNormalSpace_iff {s : S} {p : i.NormalSpace s hn} :
    p ∈ i.positiveNormalSpace f s hn ↔
      ∃ v ∈ pointSpectralSubspace
        (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
          TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Ioi 0), i.normalClass s hn v = p := by
  rw [positiveNormalSpace_def, Submodule.mem_map]

/-- The negative normal space of `-f` is the positive normal space of `f`. -/
@[simp]
theorem negativeNormalSpace_neg (s : S) :
    i.negativeNormalSpace (-f) s hn = i.positiveNormalSpace f s hn := by
  rw [negativeNormalSpace_def, positiveNormalSpace_def, criticalHessian_neg,
    pointSpectralSubspace_continuousLinearMapOfBilin_neg_Iio_zero]

/-- The positive normal space of `-f` is the negative normal space of `f`. -/
@[simp]
theorem positiveNormalSpace_neg (s : S) :
    i.positiveNormalSpace (-f) s hn = i.negativeNormalSpace f s hn := by
  rw [← negativeNormalSpace_neg, neg_neg]

namespace IsCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
include h

/-- The tangent space of a critical submanifold lies in the zero eigenspace of the Riesz operator
of the critical Hessian. -/
private theorem tangentRange_le_pointSpectralSubspace_zero (s : S) :
    i.tangentRange s hn ≤ pointSpectralSubspace
      (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
        TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) {0} := by
  intro v hv
  have hker : v ∈ (criticalHessian I f (i s)).ker :=
    h.tangentRange_le_ker_criticalHessian hn s hv
  rw [← ker_continuousLinearMapOfBilin] at hker
  refine eigenspace_le_pointSpectralSubspace (mem_singleton 0) ?_
  rw [mem_eigenspace_iff, RCLike.ofReal_zero, zero_smul]
  exact hker

/-- The eigenvectors of the Riesz operator of the critical Hessian with nonzero eigenvalues are
orthogonal to the tangent space of a critical submanifold. -/
theorem pointSpectralSubspace_le_orthogonal {Ω : Set ℝ} (hΩ : 0 ∉ Ω) (s : S) :
    pointSpectralSubspace
      (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
        TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) Ω ≤ (i.tangentRange s hn)ᗮ :=
  ((isSymmetric_continuousLinearMapOfBilin (criticalHessian_apply_swap (h.contMDiffAt s))
    |>.isOrtho_pointSpectralSubspace (disjoint_singleton_right.mpr hΩ)).mono_right
      (h.tangentRange_le_pointSpectralSubspace_zero hn s)).le

/-- The quotient map to the normal space is injective on the eigenvectors of the Riesz operator
of the critical Hessian with nonzero eigenvalues. -/
private theorem injOn_normalClass {Ω : Set ℝ} (hΩ : 0 ∉ Ω) (s : S) :
    InjOn (i.normalClass s hn) (pointSpectralSubspace
      (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
        TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) Ω) := by
  intro u hu w hw huw
  have hle := h.pointSpectralSubspace_le_orthogonal hn hΩ s
  -- Both vectors are orthogonal to the tangent space, so they are the normal representative of
  -- their common class.
  rw [← (i.normalRepresentative_eq_iff s hn _ u).mpr ⟨hle hu, rfl⟩,
    ← (i.normalRepresentative_eq_iff s hn _ w).mpr ⟨hle hw, huw.symm⟩]

/-- **The normal Hessian is negative definite on the negative normal space.** -/
theorem normalHessian_apply_self_neg {s : S} {p : i.NormalSpace s hn}
    (hp : p ∈ i.negativeNormalSpace f s hn) (hp0 : p ≠ 0) : h.normalHessian hn s p p < 0 := by
  obtain ⟨v, hv, rfl⟩ := mem_negativeNormalSpace_iff hn |>.mp hp
  rw [normalHessian_normalClass]
  exact apply_self_neg_of_mem_pointSpectralSubspace_Iio
    (criticalHessian_apply_swap (h.contMDiffAt s)) hv (by rintro rfl; exact hp0 (map_zero _))

/-- **The normal Hessian is positive definite on the positive normal space.** -/
theorem normalHessian_apply_self_pos {s : S} {p : i.NormalSpace s hn}
    (hp : p ∈ i.positiveNormalSpace f s hn) (hp0 : p ≠ 0) : 0 < h.normalHessian hn s p p := by
  obtain ⟨v, hv, rfl⟩ := mem_positiveNormalSpace_iff hn |>.mp hp
  rw [normalHessian_normalClass]
  exact apply_self_pos_of_mem_pointSpectralSubspace_Ioi
    (criticalHessian_apply_swap (h.contMDiffAt s)) hv (by rintro rfl; exact hp0 (map_zero _))

/-- The negative and positive normal spaces are orthogonal for the normal Hessian. -/
theorem normalHessian_eq_zero_of_mem_negativeNormalSpace_of_mem_positiveNormalSpace
    {s : S} {p q : i.NormalSpace s hn}
    (hp : p ∈ i.negativeNormalSpace f s hn) (hq : q ∈ i.positiveNormalSpace f s hn) :
    h.normalHessian hn s p q = 0 := by
  obtain ⟨v, hv, rfl⟩ := mem_negativeNormalSpace_iff hn |>.mp hp
  obtain ⟨w, hw, rfl⟩ := mem_positiveNormalSpace_iff hn |>.mp hq
  rw [normalHessian_normalClass]
  exact apply_eq_zero_of_mem_pointSpectralSubspace (criticalHessian_apply_swap (h.contMDiffAt s))
    Ioi_disjoint_Iio_same.symm hv hw

/-- The negative and positive normal spaces are orthogonal for the metric induced on the normal
space, which pairs the orthogonal representatives of normal classes. -/
theorem normalRiemannianMetric_inner_eq_zero_of_mem_negativeNormalSpace_of_mem_positiveNormalSpace
    {s : S} {p q : i.NormalSpace s hn}
    (hp : p ∈ i.negativeNormalSpace f s hn) (hq : q ∈ i.positiveNormalSpace f s hn) :
    (i.normalRiemannianMetric hn).inner s p q = 0 := by
  obtain ⟨v, hv, rfl⟩ := mem_negativeNormalSpace_iff hn |>.mp hp
  obtain ⟨w, hw, rfl⟩ := mem_positiveNormalSpace_iff hn |>.mp hq
  -- Both vectors are orthogonal to the tangent space, so they are their own representatives.
  have hv' : i.normalRepresentative s hn (i.normalClass s hn v) = v :=
    (i.normalRepresentative_eq_iff s hn _ v).mpr
      ⟨h.pointSpectralSubspace_le_orthogonal hn (lt_irrefl 0) s hv, rfl⟩
  have hw' : i.normalRepresentative s hn (i.normalClass s hn w) = w :=
    (i.normalRepresentative_eq_iff s hn _ w).mpr
      ⟨h.pointSpectralSubspace_le_orthogonal hn (lt_irrefl 0) s hw, rfl⟩
  rw [normalRiemannianMetric_inner, hv', hw']
  exact ((isSymmetric_continuousLinearMapOfBilin (criticalHessian_apply_swap (h.contMDiffAt s))
    ).isOrtho_pointSpectralSubspace Ioi_disjoint_Iio_same.symm).inner_eq hv hw

/-- **The dimension of the negative normal space is the Morse index.** -/
theorem finrank_negativeNormalSpace (s : S) :
    finrank ℝ (i.negativeNormalSpace f s hn) = manifoldMorseIndex I f (i s) := by
  set U := pointSpectralSubspace
    (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
      TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Iio 0)
  have hinj : Injective ((i.normalClass s hn).domRestrict U) := fun u w huw ↦
    Subtype.ext (h.injOn_normalClass hn (lt_irrefl 0) s u.2 w.2 huw)
  rw [negativeNormalSpace_def, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj,
    finrank_pointSpectralSubspace_Iio_zero (criticalHessian_apply_swap (h.contMDiffAt s)),
    manifoldMorseIndex_eq_sigNeg_criticalHessian]

/-- **The dimension of the positive normal space is the Morse index of `-f`.** -/
theorem finrank_positiveNormalSpace (s : S) :
    finrank ℝ (i.positiveNormalSpace f s hn) = manifoldMorseIndex I (-f) (i s) := by
  rw [← negativeNormalSpace_neg, h.neg.finrank_negativeNormalSpace]

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] (h : i.IsNondegenerateCriticalSubmanifold f)
include h

/-- At a point of a Morse–Bott critical submanifold, the tangent space of the submanifold is the
zero eigenspace of the Riesz operator of the critical Hessian. -/
theorem pointSpectralSubspace_singleton_zero (s : S) :
    pointSpectralSubspace
      (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
        TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) {0} = i.tangentRange s hn := by
  refine le_antisymm ?_ (h.toIsCriticalSubmanifold.tangentRange_le_pointSpectralSubspace_zero hn s)
  rw [pointSpectralSubspace_le_iff]
  rintro μ rfl v hv
  rw [mem_eigenspace_iff, RCLike.ofReal_zero, zero_smul] at hv
  rw [← h.ker_criticalHessian hn s, ← ker_continuousLinearMapOfBilin]
  exact hv

/-- **The Morse–Bott splitting of the tangent space.** At a point of a Morse–Bott critical
submanifold, the eigenvectors of the Riesz operator of the critical Hessian with negative and
with positive eigenvalues together span the orthogonal complement of the tangent space of the
submanifold. -/
theorem sup_pointSpectralSubspace_eq_orthogonal (s : S) :
    pointSpectralSubspace
        (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
          TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Iio 0) ⊔
      pointSpectralSubspace
        (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
          TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s)) (Ioi 0) =
      (i.tangentRange s hn)ᗮ := by
  rw [← h.pointSpectralSubspace_singleton_zero hn s,
    (isSymmetric_continuousLinearMapOfBilin (criticalHessian_apply_swap (h.contMDiffAt s))
      ).orthogonal_pointSpectralSubspace, ← pointSpectralSubspace_union, Iio_union_Ioi]

/-- **The normal space of a Morse–Bott critical submanifold is the direct sum of its negative and
positive normal spaces.** -/
theorem isCompl_negativeNormalSpace_positiveNormalSpace (s : S) :
    IsCompl (i.negativeNormalSpace f s hn) (i.positiveNormalSpace f s hn) := by
  set A : Module.End ℝ (TangentSpace I (i s)) :=
    (continuousLinearMapOfBilin (criticalHessian I f (i s)) :
      TangentSpace I (i s) →ₗ[ℝ] TangentSpace I (i s))
  have hc := h.toIsCriticalSubmanifold
  refine ⟨?_, ?_⟩
  · -- A common normal class has representatives in both spans, which are equal by injectivity of
    -- the quotient map on the nonzero eigenvalues; the two spans meet only in `0`.
    rw [Submodule.disjoint_def]
    intro p hp hq
    obtain ⟨v, hv, rfl⟩ := mem_negativeNormalSpace_iff hn |>.mp hp
    obtain ⟨w, hw, hwv⟩ := mem_positiveNormalSpace_iff hn |>.mp hq
    have hΩ : (0 : ℝ) ∉ Iio 0 ∪ Ioi 0 := by simp
    have hvw : w = v := hc.injOn_normalClass hn hΩ s
      (pointSpectralSubspace_mono subset_union_right hw)
      (pointSpectralSubspace_mono subset_union_left hv) hwv
    subst hvw
    have hbot : w ∈ pointSpectralSubspace A (Iio 0) ⊓ pointSpectralSubspace A (Ioi 0) := ⟨hv, hw⟩
    rw [(disjoint_pointSpectralSubspace Ioi_disjoint_Iio_same.symm).eq_bot, Submodule.mem_bot]
      at hbot
    rw [hbot, map_zero]
  · -- The two spans together span the orthogonal complement of the tangent space, which
    -- contains the normal representative of every normal class.
    rw [codisjoint_iff, negativeNormalSpace_def, positiveNormalSpace_def, ← Submodule.map_sup,
      h.sup_pointSpectralSubspace_eq_orthogonal hn s, eq_top_iff]
    rintro p -
    exact Submodule.mem_map.mpr ⟨i.normalRepresentative s hn p,
      i.normalRepresentative_mem_orthogonal s hn p, i.normalClass_normalRepresentative s hn p⟩

/-- The rank of the negative normal space is locally constant along a Morse–Bott critical
submanifold, hence constant on each connected component. -/
theorem isLocallyConstant_finrank_negativeNormalSpace :
    IsLocallyConstant fun s ↦ finrank ℝ (i.negativeNormalSpace f s hn) := by
  simpa only [h.toIsCriticalSubmanifold.finrank_negativeNormalSpace hn] using
    h.isLocallyConstant_manifoldMorseIndex hn

/-- The rank of the positive normal space is locally constant along a Morse–Bott critical
submanifold, hence constant on each connected component. -/
theorem isLocallyConstant_finrank_positiveNormalSpace :
    IsLocallyConstant fun s ↦ finrank ℝ (i.positiveNormalSpace f s hn) := by
  have hfun : (fun s ↦ finrank ℝ (i.positiveNormalSpace f s hn)) =
      fun s ↦ finrank ℝ (i.negativeNormalSpace (-f) s hn) :=
    funext fun s ↦ by rw [negativeNormalSpace_neg]
  rw [hfun]
  exact h.neg.isLocallyConstant_finrank_negativeNormalSpace hn

end IsNondegenerateCriticalSubmanifold

end TauCeti.SmoothEmbedding
