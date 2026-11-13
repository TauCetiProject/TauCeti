/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Smooth tangential corrections along a map

Let `f : M → N` be a `C^n` map, `b` a smooth family of bilinear forms on the ambient tangent
spaces and `a` a smooth family of invertible bilinear forms on the tangent spaces of `M`. For an
ambient tangent vector `v` at `f x`, the tangent vector `u = (a x)⁻¹ (b(v, df_x ·))` of `M` is
the one whose `a`-pairings reproduce the `b`-pairings of `v` with the image of `df_x`, and
`v - df_x u` is the corresponding correction of `v` by a tangent vector. This file shows that
the correction is a `C^m` self-map of the pulled-back ambient tangent bundle `f *ᵖ TN` when
`m + 1 ≤ n` (`TauCeti.contMDiff_of_eq_sub_mfderiv_inverse`).

With `b` the ambient Riemannian metric and `a` the induced metric of an immersion, `v - df_x u`
is the orthogonal projection of `v` onto the normal space; with `b` a nondegenerate two-form and
`a` its pullback to a symplectic submanifold, it is the symplectic representative of the normal
class of `v`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E V H G M N K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [FunLike K M N] [ContinuousMapClass K M N]
  {n m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]

/-- **Smooth tangential correction.** For a `C^m` family `b` of bilinear forms on the ambient
tangent spaces and a `C^m` family `a` of invertible bilinear forms on the tangent spaces of `M`,
a map `r` on ambient tangent vectors given by `r x v = v - df_x ((a x)⁻¹ (b(v, df_x ·)))` is a
`C^m` self-map of the pulled-back ambient tangent bundle `f *ᵖ TN` of a `C^n` map `f` with
`m + 1 ≤ n`. Both the base point and the ambient tangent vector may vary. -/
theorem contMDiff_of_eq_sub_mfderiv_inverse (f : K) (hf : ContMDiff I J n f) (hm : m + 1 ≤ n)
    {a : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜}
    (ha : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] 𝕜)) m
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] 𝕜)
        (E := fun x : M ↦ TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) x (a x)))
    (hainv : ∀ x, (a x).IsInvertible)
    {b : (y : N) → TangentSpace J y →L[𝕜] TangentSpace J y →L[𝕜] 𝕜}
    (hb : ContMDiff J (J.prod 𝓘(𝕜, V →L[𝕜] V →L[𝕜] 𝕜)) m
      (fun y ↦ TotalSpace.mk' (V →L[𝕜] V →L[𝕜] 𝕜)
        (E := fun y : N ↦ TangentSpace J y →L[𝕜] TangentSpace J y →L[𝕜] 𝕜) y (b y)))
    (r : (x : M) → TangentSpace J (f x) → TangentSpace J (f x))
    (hr : ∀ x v, r x v = v - mfderiv I J f x ((a x).inverse ((b (f x) v).comp (mfderiv I J f x)))) :
    ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, r p.proj p.2⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) := by
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  have hbase : ContMDiff (I.prod 𝓘(𝕜, V)) I m
      (π V ((f : M → N) *ᵖ (TangentSpace J))) := contMDiff_proj _
  have hlift : ContMDiff (I.prod 𝓘(𝕜, V)) (J.prod 𝓘(𝕜, V)) m
      (Pullback.lift (f : M → N)) :=
    Pullback.contMDiff_lift fc fc.contMDiff (E := fun y : N ↦ TangentSpace J y)
  -- Pair the ambient vector with the differential under `b`, then pull the covector back.
  let φ := fun (x : M) (v : TangentSpace J (f x)) ↦ (b (f x) v).comp (mfderiv I J f x)
  have hφ : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, φ p.proj p.2⟩ : CotangentBundle I M)) :=
    CotangentBundle.contMDiff_mk_comp_mfderiv
      (Ψ := fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f q.proj, b (f q.proj) q.2⟩ : CotangentBundle J N))
      (fun _ ↦ rfl) ((hb.comp (fc.contMDiff.comp hbase)).clm_bundle_apply hlift)
      hbase hf hm
  -- Invert `a` and push the resulting tangential component forward.
  let u := fun (x : M) (v : TangentSpace J (f x)) ↦ (a x).inverse (φ x v)
  have hu : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, E)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, u p.proj p.2⟩ : TangentBundle I M)) :=
    ((ha.clm_bundle_inverse hainv).comp hbase).clm_bundle_apply hφ
  have ht := (hf.contMDiff_tangentMap (by simpa using hm)).comp hu
  have hneg := (contMDiff_const (c := (-1 : 𝕜))).smul_totalSpace ht
  have hformula (x : M) (v : TangentSpace J (f x)) :
      r x v = v + (-1 : 𝕜) • mfderiv I J f x (u x v) := by
    rw [hr, neg_one_smul, ← sub_eq_add_neg]
  refine (Pullback.contMDiff_iff fc fc.contMDiff).mpr ⟨hbase, ?_⟩
  exact (hlift.add_sectionAlong hneg).congr fun p ↦
    congrArg (TotalSpace.mk (f p.proj)) (hformula p.proj p.2)

end TauCeti
