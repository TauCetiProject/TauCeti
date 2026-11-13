/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Smooth tangential corrections along an embedding

Let `f : M → N` be an embedding, `b` a smooth family of bilinear forms on the ambient tangent
spaces and `a` a smooth family of invertible bilinear forms on the tangent spaces of `M`. For an
ambient tangent vector `v` at `f x`, the tangent vector `u = (a x)⁻¹ (b(v, df_x ·))` of `M` is
the one whose `a`-pairings reproduce the `b`-pairings of `v` with the tangent space, and
`v - df_x u` is the corresponding correction of `v` by a tangent vector. This file shows that
the correction is `C^m` on the pulled-back ambient tangent bundle for a `C^n` embedding with
`m + 1 ≤ n` (`TauCeti.SmoothEmbedding.contMDiff_of_eq_sub_mfderiv_inverse`).

With `b` the ambient Riemannian metric and `a` the induced metric, `v - df_x u` is the orthogonal
representative of the normal class of `v`; with `b` a nondegenerate two-form and `a` its pullback
to a symplectic submanifold, it is the symplectic representative. A family of representatives
that is smooth on ambient tangent vectors descends to the intrinsic normal bundle
(`TauCeti.SmoothEmbedding.contMDiff_normalBundle_of_contMDiff_normalClass`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
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
  {n m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

variable [IsManifold I 1 M] [IsManifold J 1 N]

omit [FiniteDimensional ℝ V] in
/-- **Smooth tangential correction.** For a `C^m` family `b` of bilinear forms on the ambient
tangent spaces and a `C^m` family `a` of invertible bilinear forms on the tangent spaces of `M`,
a map `r` on ambient tangent vectors given by `r x v = v - df_x ((a x)⁻¹ (b(v, df_x ·)))` is
`C^m` on the pulled-back ambient tangent bundle of a `C^n` embedding with `m + 1 ≤ n`. Both the
base point and the ambient tangent vector may vary. -/
theorem contMDiff_of_eq_sub_mfderiv_inverse (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n)
    {a : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (ha : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (a x)))
    (hainv : ∀ x, (a x).IsInvertible)
    {b : (y : N) → TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ}
    (hb : ContMDiff J (J.prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) m
      (fun y ↦ TotalSpace.mk' (V →L[ℝ] V →L[ℝ] ℝ)
        (E := fun y : N ↦ TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ) y (b y)))
    (r : (x : M) → TangentSpace J (f x) → TangentSpace J (f x))
    (hr : ∀ x v, r x v = v - mfderiv I J f x ((a x).inverse ((b (f x) v).comp (mfderiv I J f x)))) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f p.proj, r p.proj p.2⟩ : TangentBundle J N)) := by
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
      (E := fun y : N ↦ TangentSpace J y)).mp contMDiff_id).2
  -- Pair the ambient vector with the differential under `b`, then pull the covector back.
  let φ := fun (x : M) (v : TangentSpace J (f x)) ↦ (b (f x) v).comp (mfderiv I J f x)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, φ p.proj p.2⟩ : CotangentBundle I M)) :=
    CotangentBundle.contMDiff_mk_comp_mfderiv
      (Ψ := fun q : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f q.proj, b (f q.proj) q.2⟩ : CotangentBundle J N))
      (fun _ ↦ rfl) ((hb.comp (fc.contMDiff.comp hbase)).clm_bundle_apply hlift)
      hbase f.contMDiff hm
  -- Invert `a` and push the resulting tangential component forward.
  let u := fun (x : M) (v : TangentSpace J (f x)) ↦ (a x).inverse (φ x v)
  have hu : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, u p.proj p.2⟩ : TangentBundle I M)) :=
    ((ha.clm_bundle_inverse hainv).comp hbase).clm_bundle_apply hφ
  have ht := (f.contMDiff.contMDiff_tangentMap (by simpa using hm)).comp hu
  have hneg := (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace ht
  have hformula (x : M) (v : TangentSpace J (f x)) :
      r x v = v + (-1 : ℝ) • mfderiv I J f x (u x v) := by
    rw [hr, neg_one_smul, ← sub_eq_add_neg]
  exact (hlift.add_sectionAlong hneg).congr fun p ↦
    congrArg (TotalSpace.mk (f p.proj)) (hformula p.proj p.2)

/-- **Smooth descent of representatives.** A family of maps `r x` from the normal spaces to the
ambient tangent spaces is `C^m` on the intrinsic normal bundle as soon as its values on normal
classes of ambient tangent vectors are `C^m` on the pulled-back ambient tangent bundle. -/
theorem contMDiff_normalBundle_of_contMDiff_normalClass (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    (r : (x : M) → f.NormalSpace x hn → TangentSpace J (f x))
    (hr : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨f p.proj, r p.proj (f.normalClass p.proj hn p.2)⟩ : TangentBundle J N))) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨f p.proj, r p.proj p.2⟩ : TangentBundle J N)) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  convert hr using 1
  funext p
  rw [Function.comp_apply, normalQuotientMap_apply]

end TauCeti.SmoothEmbedding
