/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The orthogonal normal bundle of an immersion

Let `f : M → N` be an immersion into a manifold whose tangent spaces carry a Riemannian metric.
Its normal space at `x : M` is the orthogonal complement of the range of `mfderiv I J f x` in
`T_{f x} N` (`TauCeti.orthogonalNormalSpace`). These spaces are indexed by the source point, so
two sheets of an immersion through one image point keep separate normal spaces.

The orthogonal projection onto the normal space removes the tangential component of an ambient
vector. That component is recovered by inverting the pullback metric on `M`, which gives the
formula `v ↦ v - df ((df* df)⁻¹ (df* v))`
(`TauCeti.starProjection_orthogonalNormalSpace_eq_sub_mfderiv_inverse`). Consequently the
normal projection is a `C^m` self-map of the pulled-back tangent bundle `f *ᵖ TN` for a `C^n`
immersion with `m + 1 ≤ n` and a `C^m` metric
(`TauCeti.contMDiff_starProjection_orthogonalNormalSpace`). Projecting a local frame of
`f *ᵖ TN` and keeping a subfamily that is linearly independent at the base point gives `C^m`
local frames of the normal spaces
(`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace`). By the smooth local frame
criterion `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` the normal spaces,
with the subspace topology of `f *ᵖ TN`, therefore form a `C^m` subbundle `ν_f` of `f *ᵖ TN` of
rank `dim N - dim M`. No compactness, injectivity of `f`, boundarylessness or choice of normal
frame is assumed. The identity map has zero normal spaces and a constant map has the whole
ambient tangent space as normal space (`TauCeti.orthogonalNormalSpace_id`,
`TauCeti.orthogonalNormalSpace_const`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8, the normal bundle
  of an immersed submanifold.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Lemma 10.32.
-/

public section

noncomputable section

open Bundle Manifold Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable (I J) in
/-- The normal space of a map `f : M → N` at `x : M`: the orthogonal complement of the range of
the differential `mfderiv I J f x` in `T_{f x} N`. For an immersion these are the fibres of its
normal bundle `ν_f`. -/
def orthogonalNormalSpace (f : M → N) (x : M) : Submodule ℝ (TangentSpace J (f x)) :=
  (LinearMap.range (mfderiv I J f x).toLinearMap)ᗮ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The normal space is the orthogonal complement of the range of the differential. -/
theorem orthogonalNormalSpace_def (f : M → N) (x : M) :
    orthogonalNormalSpace I J f x = (LinearMap.range (mfderiv I J f x).toLinearMap)ᗮ :=
  (rfl)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- A vector is normal exactly when it is orthogonal to the differential of every tangent
vector. -/
theorem mem_orthogonalNormalSpace_iff {f : M → N} {x : M} {w : TangentSpace J (f x)} :
    w ∈ orthogonalNormalSpace I J f x ↔
      ∀ u : TangentSpace I x, inner ℝ (mfderiv I J f x u) w = 0 := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.mem_orthogonal' _ _ |>.trans
    ⟨fun h u ↦ by rw [real_inner_comm]; exact h _ ⟨u, rfl⟩,
      fun h _ ⟨u, hu⟩ ↦ by rw [← hu, real_inner_comm]; exact h u⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The identity map has zero normal spaces. -/
@[simp]
theorem orthogonalNormalSpace_id (y : N) : orthogonalNormalSpace J J id y = ⊥ := by
  rw [orthogonalNormalSpace_def, mfderiv_id]
  simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- A constant map has the whole ambient tangent space as normal space; in particular so does
a point immersed in `N`. -/
@[simp]
theorem orthogonalNormalSpace_const (y : N) (x : M) :
    orthogonalNormalSpace I J (fun _ : M ↦ y) x = ⊤ := by
  rw [orthogonalNormalSpace_def, mfderiv_const]
  simp

omit [FiniteDimensional ℝ E] in
/-- The normal space of an immersion at `x` is a complement of `T_x M`: its dimension is
`dim N - dim M`. -/
theorem finrank_orthogonalNormalSpace_add_finrank {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) :
    finrank ℝ (orthogonalNormalSpace I J f x) + finrank ℝ E = finrank ℝ V := by
  have h := Submodule.finrank_add_finrank_orthogonal
    (LinearMap.range (mfderiv I J f x).toLinearMap)
  rw [LinearMap.finrank_range_of_inj hinj] at h
  rw [orthogonalNormalSpace_def, add_comm]
  exact h

/-- The orthogonal projection onto the normal space subtracts the tangential component of an
ambient vector `v`. Inverting the pullback metric `df* df` on `T_x M` recovers that component from
the covector `df* v`. Only injectivity of the differential at `x` is used; the ambient metric need
not be regular. -/
theorem starProjection_orthogonalNormalSpace_eq_sub_mfderiv_inverse {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) (v : TangentSpace J (f x)) :
    let d := mfderiv I J f x
    let φ := (RiemannianBundle.g.inner (f x) v).comp d
    let a := (ContinuousLinearMap.precomp ℝ d).comp ((RiemannianBundle.g.inner (f x)).comp d)
    (orthogonalNormalSpace I J f x).starProjection v = v - d (a.inverse φ) := by
  intro d φ a
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have ha : a.IsInvertible := ContinuousLinearMap.isInvertible_of_pos (E := E) fun w hw0 ↦
    RiemannianBundle.g.pos (f x) (d w) ((map_ne_zero_iff d hinj).mpr hw0)
  refine Submodule.eq_starProjection_of_mem_orthogonal' (z := d (a.inverse φ)) ?_ ?_
    (sub_add_cancel _ _).symm
  · refine mem_orthogonalNormalSpace_iff.mpr fun z ↦ ?_
    have hpair := DFunLike.congr_fun (ha.self_apply_inverse φ) z
    simp only [a, φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply] at hpair
    -- The `RiemannianBundle` inner product is defined by its stored metric pairing.
    have hpair' : inner ℝ (d (a.inverse φ)) (d z) = inner ℝ v (d z) := hpair
    rw [inner_sub_right, real_inner_comm v (d z), real_inner_comm (d (a.inverse φ)) (d z), hpair',
      sub_self]
  · rw [orthogonalNormalSpace_def]
    exact Submodule.le_orthogonal_orthogonal _ ⟨_, rfl⟩

variable {n m : ℕ∞ω} [IsManifold J 1 N] [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

/-- **The normal projection is smooth.** For a `C^n` immersion `f` with `m + 1 ≤ n` and a `C^m`
ambient metric, orthogonal projection onto the normal spaces is a `C^m` self-map of the
pulled-back tangent bundle `f *ᵖ TN`. Both the base point and the ambient vector may vary. -/
theorem contMDiff_starProjection_orthogonalNormalSpace {f : C^n⟮I, M; J, N⟯}
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V (f *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).starProjection p.2⟩ :
          TotalSpace V (f *ᵖ (TangentSpace J)))) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hf₁ : ContMDiff I J (m + 1) f := f.contMDiff.of_le hm
  -- The induced metric identifies tangent vectors with covectors on the source.
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := J) (n := m) (F := V) (V := fun y : N ↦ TangentSpace J y)
  let a := g.pullback f hf₁ hinj
  have ha (x : M) : (a.inner x).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_pos (E := E) (a.pos x)
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := m)
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have hbase : ContMDiff (I.prod 𝓘(ℝ, V)) I m (π V (f *ᵖ (TangentSpace J))) := contMDiff_proj _
  have hlift : ContMDiff (I.prod 𝓘(ℝ, V)) (J.prod 𝓘(ℝ, V)) m (Pullback.lift f) :=
    ((Pullback.contMDiff_iff fc fc.contMDiff
      (E := fun y : N ↦ TangentSpace J y)).mp contMDiff_id).2
  -- Pair the ambient vector with the differential, then pull the covector back.
  let φ := fun (x : M) (v : TangentSpace J (f x)) ↦ (g.inner (f x) v).comp (mfderiv I J f x)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun p : TotalSpace V (f *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, φ p.proj p.2⟩ : CotangentBundle I M)) :=
    CotangentBundle.contMDiff_mk_comp_mfderiv
      (Ψ := fun q : TotalSpace V (f *ᵖ (TangentSpace J)) ↦
        (⟨f q.proj, g.inner (f q.proj) q.2⟩ : CotangentBundle J N))
      (fun _ ↦ rfl) ((g.contMDiff.comp (fc.contMDiff.comp hbase)).clm_bundle_apply hlift)
      hbase f.contMDiff hm
  -- Invert the induced metric and push the resulting tangential component forward.
  let u := fun (x : M) (v : TangentSpace J (f x)) ↦ (a.inner x).inverse (φ x v)
  have hu : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) m
      (fun p : TotalSpace V (f *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, u p.proj p.2⟩ : TangentBundle I M)) :=
    ((a.contMDiff.clm_bundle_inverse ha).comp hbase).clm_bundle_apply hφ
  have ht := (hf₁.contMDiff_tangentMap le_rfl).comp hu
  have hneg := (contMDiff_const (c := (-1 : ℝ))).smul_totalSpace ht
  have hsub := hlift.add_sectionAlong hneg
  have hformula (x : M) (v : TangentSpace J (f x)) :
      (orthogonalNormalSpace I J f x).starProjection v =
        v + (-1 : ℝ) • mfderiv I J f x (u x v) := by
    rw [neg_one_smul, ← sub_eq_add_neg,
      starProjection_orthogonalNormalSpace_eq_sub_mfderiv_inverse (hinj x)]
    have hg : g.inner (f x) = RiemannianBundle.g.inner (f x) := by
      ext w z
      exact ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner _ _ _
    have hflat : a.inner x = (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
        ((g.inner (f x)).comp (mfderiv I J f x)) := by
      ext w z
      exact ContMDiffRiemannianMetric.pullback_inner _ _ _ _ _ _ _
    simp only [u, φ, hflat, hg]
  refine (Pullback.contMDiff_iff fc fc.contMDiff).mpr ⟨hbase, ?_⟩
  exact hsub.congr fun p ↦ congrArg (TotalSpace.mk (f p.proj)) (hformula p.proj p.2)

/-- **Local frames of the normal bundle.** For a `C^n` immersion `f` with `m + 1 ≤ n`, a `C^m`
ambient metric and `dim N = dim M + r`, the normal spaces have `C^m` local frames of size `r` in
the pulled-back tangent bundle `f *ᵖ TN`. By
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` they form a `C^m` subbundle
`ν_f` of `f *ᵖ TN`. The frames are normal projections of a local frame of `f *ᵖ TN`. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace {r : ℕ} {f : C^n⟮I, M; J, N⟯}
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    HasLocalContMDiffSubbundleFrames I m V (Fin r) (E := f *ᵖ (TangentSpace J))
      (orthogonalNormalSpace I J f) := by
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, f.contMDiff.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V (f *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  -- Elaborate in the fibres `TangentSpace J (f x)`, not in the pullback fibres.
  have hrange (x : M) : LinearMap.range ((orthogonalNormalSpace I J f x).starProjection :
      TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x)) = orthogonalNormalSpace I J f x :=
    Submodule.range_starProjection _
  have hfin (x : M) : finrank ℝ (orthogonalNormalSpace I J f x) = r := by
    have := finrank_orthogonalNormalSpace_add_finrank (hinj x)
    omega
  exact hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range _
    (contMDiff_starProjection_orthogonalNormalSpace hinj hm) hrange hfin

end TauCeti
