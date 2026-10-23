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
  {n : ℕ∞ω}
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable {m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

/-- Orthogonal normal projection is `C^m` on the pulled-back ambient tangent bundle for a
`C^n` embedding with `m + 1 ≤ n` and a `C^m` ambient metric. Both the base point and the
ambient tangent vector may vary. -/
theorem contMDiff_normalRepresentative_normalClass
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨f p.proj, f.normalRepresentative p.proj hn (f.normalClass p.proj hn p.2)⟩ :
          TangentBundle J N)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- The induced metric identifies tangent vectors with covectors on the source.
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := J) (n := m) (F := V) (V := fun y : N => TangentSpace J y)
  let a := g.pullback f (f.contMDiff.of_le (by simpa using hm)) (f.isImmersion.mfderiv_injective hn)
  have ha (x : M) : (a.inner x).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_pos (E := E) (a.pos x)
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  have hbase : ContMDiff (I.prod 𝓘(ℝ, V)) I m
      (π V ((f : M → N) *ᵖ (TangentSpace J))) := contMDiff_proj _
  have hlift : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (Pullback.lift (f : M → N)) :=
    ((Pullback.contMDiff_iff fc fc.contMDiff
      (E := fun y : N => TangentSpace J y)).mp contMDiff_id).2
  -- Pair the ambient vector with the differential, then pull the covector back.
  let φ := fun (x : M) (v : TangentSpace J (f x)) =>
    (g.inner (f x) v).comp (mfderiv I J f x)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨p.proj, φ p.proj p.2⟩ : CotangentBundle I M)) :=
    CotangentBundle.contMDiff_mk_comp_mfderiv
      (Ψ := fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨f q.proj, g.inner (f q.proj) q.2⟩ : CotangentBundle J N))
      (fun _ => rfl) ((g.contMDiff.comp (fc.contMDiff.comp hbase)).clm_bundle_apply hlift)
      hbase f.contMDiff hm
  -- Invert the induced metric and push the resulting tangential component forward.
  let u := fun (x : M) (v : TangentSpace J (f x)) =>
    (a.inner x).inverse (φ x v)
  have hu : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) =>
        (⟨p.proj, u p.proj p.2⟩ : TangentBundle I M)) :=
    ((a.contMDiff.clm_bundle_inverse ha).comp hbase).clm_bundle_apply hφ
  have ht := (f.contMDiff.contMDiff_tangentMap (by simpa using hm)).comp hu
  have hneg := (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace ht
  have hsub := hlift.add_sectionAlong hneg
  have hformula (x : M) (v : TangentSpace J (f x)) :
      f.normalRepresentative x hn (f.normalClass x hn v) =
        v + (-1 : ℝ) • mfderiv I J f x (u x v) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    have hg : g.inner (f x) = RiemannianBundle.g.inner (f x) := by
      ext w z
      exact ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner _ _ _
    have hflat : a.inner x = (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
        ((g.inner (f x)).comp (mfderiv I J f x)) := by
      ext w z
      exact ContMDiffRiemannianMetric.pullback_inner _ _ _ _ _ _ _
    simpa only [u, φ, hflat, hg] using
      f.normalRepresentative_normalClass_eq_sub_mfderiv_inverse x hn v
  exact hsub.congr fun p => congrArg (TotalSpace.mk (f p.proj)) (hformula p.proj p.2)

/-- The map taking an intrinsic normal vector to its orthogonal representative in the ambient
tangent bundle is `C^m` for a `C^n` embedding with `m + 1 ≤ n` and a `C^m` ambient metric. -/
theorem contMDiff_normalRepresentative
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace P (fun x => f.NormalSpace x hn) =>
        (⟨f p.proj, f.normalRepresentative p.proj hn p.2⟩ : TangentBundle J N)) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  convert f.contMDiff_normalRepresentative_normalClass hn hm using 1
  funext p
  rw [Function.comp_apply, normalQuotientMap_apply]

end TauCeti.SmoothEmbedding
