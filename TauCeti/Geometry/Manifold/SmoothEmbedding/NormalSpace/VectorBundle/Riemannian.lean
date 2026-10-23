/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Riemannian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.Riemannian.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Smooth orthogonal representatives in intrinsic normal bundles

Orthogonal representatives of intrinsic normal classes vary smoothly with both the base point
and the normal vector. The metric is the ambient Riemannian metric; no normal framing or
compactness assumption is needed. This supplies the map from the normal bundle to the ambient
tangent bundle used by the normal exponential.

The construction uses the pullback metric on the embedded manifold. Inverting its flat map
recovers the tangential component of an ambient vector from its pairings with tangent vectors.
Subtracting this component gives the orthogonal representative, which descends through the
smooth normal quotient.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I ∞ M] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- Orthogonal normal projection is smooth on the pulled-back ambient tangent bundle.
Both the base point and the ambient tangent vector may vary. -/
theorem contMDiff_normalRepresentative_normalClass
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : ∞ ≤ n) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) ∞
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨f p.proj, f.normalRepresentative p.proj hn (f.normalClass p.proj hn p.2)⟩ :
          TangentBundle J N)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- The induced metric identifies tangent vectors with covectors on the source.
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := J) (n := ∞) (F := V) (V := fun y : N => TangentSpace J y)
  let a := g.pullback f (f.contMDiff.of_le (by simpa using hm)) (f.isImmersion.mfderiv_injective hn)
  have ha (x : M) : (a.inner x).IsInvertible := by
    apply ContinuousLinearMap.isInvertible_of_separatingLeft (E := E)
    intro v hv
    by_contra hv0
    exact (a.pos x v hv0).ne' (hv v)
  let fc : C^∞⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le hm⟩
  let : ContMDiffVectorBundle ∞ V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  have : ContMDiffVectorBundle 1 V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.of_le (n := ∞) (by simp)
  let : IsManifold (I.prod 𝓘(ℝ, V)) 1
      (TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))) :=
    Bundle.TotalSpace.isManifold V ((f : M → N) *ᵖ (TangentSpace J))
  have hbase : ContMDiff (I.prod 𝓘(ℝ, V)) I ∞
      (π V ((f : M → N) *ᵖ (TangentSpace J))) := contMDiff_proj _
  have hlift : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) ∞
      (Pullback.lift (f : M → N)) :=
    ((Pullback.contMDiff_iff fc fc.contMDiff
      (E := fun y : N => TangentSpace J y)).mp contMDiff_id).2
  -- Pair the ambient vector with the differential, then pull the covector back.
  let φ := fun (x : M) (v : TangentSpace J (f x)) =>
    (g.inner (f x) v).comp (mfderiv I J f x)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨p.proj, φ p.proj p.2⟩ : CotangentBundle I M)) := by
    exact CotangentBundle.contMDiff_mk_comp_mfderiv (IX := I.prod 𝓘(ℝ, V))
      (X := TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))) (f := (f : M → N))
      (g := π V ((f : M → N) *ᵖ (TangentSpace J))) (fun _ => rfl)
      ((g.contMDiff.comp (fc.contMDiff.comp hbase)).clm_bundle_apply hlift)
      hbase f.contMDiff (by simpa using hm)
  -- Invert the induced metric and push the resulting tangential component forward.
  let u := fun (x : M) (v : TangentSpace J (f x)) =>
    (a.inner x).inverse (φ x v)
  have hu : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨p.proj, u p.proj p.2⟩ : TangentBundle I M)) :=
    ((a.contMDiff.clm_bundle_inverse ha).comp hbase).clm_bundle_apply hφ
  have ht := (f.contMDiff.contMDiff_tangentMap (by simpa using hm)).comp hu
  have hneg := (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace ht
  have hsub := hlift.add_sectionAlong hneg
  -- The remainder is perpendicular to the tangent range and has the prescribed normal class.
  have hformula (x : M) (v : TangentSpace J (f x)) :
      f.normalRepresentative x hn (f.normalClass x hn v) =
        v + (-1 : ℝ) • mfderiv I J f x (u x v) := by
    apply (f.normalRepresentative_eq_iff x hn _ _).mpr
    constructor
    · apply (Submodule.mem_orthogonal' _ _).mpr
      intro w hw
      obtain ⟨z, rfl⟩ := (f.mem_tangentRange_iff x hn w).mp hw
      have hpair := DFunLike.congr_fun ((ha x).self_apply_inverse (φ x v)) z
      rw [ContMDiffRiemannianMetric.pullback_inner] at hpair
      simp only [φ, ContinuousLinearMap.comp_apply, g,
        ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner] at hpair
      have hpair' : inner ℝ (mfderiv I J f x (u x v)) (mfderiv I J f x z) =
          inner ℝ v (mfderiv I J f x z) := hpair
      simpa only [neg_one_smul, ← sub_eq_add_neg, inner_sub_left, sub_eq_zero] using hpair'.symm
    · simp only [map_add, map_smul, normalClass_mfderiv, smul_zero, add_zero]
  exact hsub.congr fun p => congrArg (TotalSpace.mk (f p.proj)) (hformula p.proj p.2)

/-- The map taking an intrinsic normal vector to its orthogonal representative in the ambient
tangent bundle is smooth for a smooth embedding and a smooth ambient Riemannian metric. -/
theorem contMDiff_normalRepresentative
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : ∞ ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, V)) ∞
      (fun p : TotalSpace P (fun x => f.NormalSpace x hn) =>
        (⟨f p.proj, f.normalRepresentative p.proj hn p.2⟩ : TangentBundle J N)) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  convert f.contMDiff_normalRepresentative_normalClass hn hm using 1
  funext p
  rw [Function.comp_apply, normalQuotientMap_apply]

end TauCeti.SmoothEmbedding
