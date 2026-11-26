/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.VectorBundle.Riemannian.Hermitian

/-!
# The orthogonal normal bundle of an immersion

Let `f : M → N` be an immersion into a manifold whose tangent spaces carry a Riemannian metric.
Its normal space at `x : M` is the orthogonal complement of the range of `mfderiv I J f x` in
`T_{f x} N` (`TauCeti.orthogonalNormalSpace`). These spaces are indexed by the source point, so
two sheets of an immersion through one image point keep separate normal spaces. This file makes
them a smooth vector bundle `ν_f`, a subbundle of the pulled-back tangent bundle `f *ᵖ TN`,
together with the smooth orthogonal projection of `f *ᵖ TN` onto `ν_f`. This is the bundle in which
the second fundamental form and the normal connection of an immersion take values.

The normal spaces are closed (`TauCeti.isClosed_orthogonalNormalSpace`). When the range of the
differential admits an orthogonal projection, for instance for a finite-dimensional source, so do
the normal spaces, and their orthogonal complements are the tangent ranges
(`TauCeti.orthogonal_orthogonalNormalSpace`). The normal space is then isometric to the quotient
`T_{f x} N ⧸ range df_x` by `w ↦ [w]` (`TauCeti.orthogonalNormalSpaceEquivQuotient`, the inverse of
Mathlib's `Submodule.quotientEquivOrthogonal`). For a finite-dimensional source, the orthogonal
projection onto the normal space is `v ↦ v - df ((df* df)⁻¹ (df* v))`, where `df* df` is the
pullback metric on `T_x M` (`TauCeti.starProjection_orthogonalNormalSpace_eq_sub_mfderiv_inverse`).
It is a `C^m` self-map of `f *ᵖ TN` near every point where `f` is `C^n` with injective
differential, for `m + 1 ≤ n` and a `C^m` metric
(`TauCeti.contMDiffAt_starProjection_orthogonalNormalSpace`,
`TauCeti.contMDiff_starProjection_orthogonalNormalSpace`). The smoothness is that of the projection
onto `(range df)ᗮ`, `ContMDiffAt.starProjection_orthogonal_range_mfderiv` in
`TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection`.

For a `C^n` immersion with `m + 1 ≤ n` into a finite-dimensional manifold, the normal spaces have
`C^m` local frames (`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace`), the ranges
of the normal projection, a `C^m` constant-rank fibrewise map, by the criterion
`TauCeti.hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range`. With the
subspace topology of `f *ᵖ TN` they form a `C^m` vector bundle `ν_f` of rank `dim N - dim M`
(`TauCeti.orthogonalNormalFiberBundle`, `TauCeti.orthogonalNormalVectorBundle`,
`TauCeti.orthogonalNormalContMDiffVectorBundle`). The fibre bundle structure is a definition,
not a global instance, since it depends on the regularity hypotheses: install it with `letI`, as
the statements below do. Its atlas consists of the `C^m` local frames, so it depends on `m`, but
not on `n` or on the proofs of the hypotheses (`TauCeti.orthogonalNormalFiberBundle_congr`). The
inclusions of `ν_f` into `f *ᵖ TN` and `TN` are `C^m`
(`TauCeti.contMDiff_orthogonalNormalSpace_inclusion`,
`TauCeti.contMDiff_orthogonalNormalSpace_inclusion_tangentBundle`). For `k ≤ m`, a map into `ν_f`
is `C^k` (within a set) exactly when it is `C^k` into `f *ᵖ TN`
(`TauCeti.contMDiffWithinAt_orthogonalNormalSpace_mk_iff`), or when its base point is `C^k` and it
is `C^k` into `TN` (`TauCeti.contMDiffWithinAt_orthogonalNormalSpace_mk_iff_tangentBundle`). The
orthogonal projection of `f *ᵖ TN` onto `ν_f` is `C^m`
(`TauCeti.contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace`). For a continuous metric, the
fibre norm of `ν_f` is continuous on its total space
(`TauCeti.continuous_norm_orthogonalNormalSpace`, an instance of `TauCeti.continuous_norm_subbundle`
for any family of subspaces of the fibres). No compactness, injectivity
of `f`, boundarylessness or choice of normal frame is assumed. The identity map has zero normal
spaces and a constant map has the whole ambient tangent space as normal space
(`TauCeti.orthogonalNormalSpace_id`, `TauCeti.orthogonalNormalSpace_const`).

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

variable {E V H G M N K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [FunLike K M N] [ContinuousMapClass K M N]

variable (I J) in
/-- The normal space of a map `f : M → N` at `x : M`: the orthogonal complement of the range of
the differential `mfderiv I J f x` in `T_{f x} N`. For an immersion these are the fibres of its
normal bundle `ν_f`. -/
def orthogonalNormalSpace (f : M → N) (x : M) : Submodule ℝ (TangentSpace J (f x)) :=
  (LinearMap.range (mfderiv I J f x).toLinearMap)ᗮ

/-- The normal space is the orthogonal complement of the range of the differential. -/
theorem orthogonalNormalSpace_def (f : M → N) (x : M) :
    orthogonalNormalSpace I J f x = (LinearMap.range (mfderiv I J f x).toLinearMap)ᗮ :=
  (rfl)

/-- A vector is normal exactly when it is orthogonal to the differential of every tangent
vector. -/
theorem mem_orthogonalNormalSpace_iff {f : M → N} {x : M} {w : TangentSpace J (f x)} :
    w ∈ orthogonalNormalSpace I J f x ↔
      ∀ u : TangentSpace I x, inner ℝ (mfderiv I J f x u) w = 0 := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.mem_orthogonal' _ _ |>.trans
    ⟨fun h u ↦ by rw [real_inner_comm]; exact h _ ⟨u, rfl⟩,
      fun h _ ⟨u, hu⟩ ↦ by rw [← hu, real_inner_comm]; exact h u⟩

/-- The normal spaces are closed. -/
theorem isClosed_orthogonalNormalSpace (f : M → N) (x : M) :
    IsClosed (orthogonalNormalSpace I J f x : Set (TangentSpace J (f x))) := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.isClosed_orthogonal _

/-- The differential of a tangent vector is orthogonal to every normal vector. -/
@[simp]
theorem inner_mfderiv_coe_orthogonalNormalSpace {f : M → N} {x : M} (u : TangentSpace I x)
    (w : orthogonalNormalSpace I J f x) :
    inner ℝ (mfderiv I J f x u) (w : TangentSpace J (f x)) = 0 :=
  mem_orthogonalNormalSpace_iff.mp w.property u

/-- A normal vector is orthogonal to the differential of every tangent vector. -/
@[simp]
theorem inner_coe_orthogonalNormalSpace_mfderiv {f : M → N} {x : M}
    (w : orthogonalNormalSpace I J f x) (u : TangentSpace I x) :
    inner ℝ (w : TangentSpace J (f x)) (mfderiv I J f x u) = 0 := by
  rw [real_inner_comm]
  exact inner_mfderiv_coe_orthogonalNormalSpace u w

/-- The differential of a tangent vector is orthogonal to the normal space. -/
@[simp]
theorem mfderiv_mem_orthogonal_orthogonalNormalSpace (f : M → N) (x : M) (u : TangentSpace I x) :
    mfderiv I J f x u ∈ (orthogonalNormalSpace I J f x)ᗮ := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.le_orthogonal_orthogonal _ ⟨u, rfl⟩

/-- The normal projection kills the differentials of tangent vectors. -/
@[simp]
theorem starProjection_orthogonalNormalSpace_mfderiv (f : M → N) (x : M)
    [(orthogonalNormalSpace I J f x).HasOrthogonalProjection] (u : TangentSpace I x) :
    (orthogonalNormalSpace I J f x).starProjection (mfderiv I J f x u) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr
    (mfderiv_mem_orthogonal_orthogonalNormalSpace f x u)

/-- The orthogonal projection onto the normal space kills the differentials of tangent
vectors. -/
@[simp]
theorem orthogonalProjectionOnto_orthogonalNormalSpace_mfderiv (f : M → N) (x : M)
    [(orthogonalNormalSpace I J f x).HasOrthogonalProjection] (u : TangentSpace I x) :
    (orthogonalNormalSpace I J f x).orthogonalProjectionOnto (mfderiv I J f x u) = 0 :=
  Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    (mfderiv_mem_orthogonal_orthogonalNormalSpace f x u)

/-- The identity map has zero normal spaces. -/
@[simp]
theorem orthogonalNormalSpace_id (y : N) : orthogonalNormalSpace J J id y = ⊥ := by
  rw [orthogonalNormalSpace_def, mfderiv_id]
  simp

/-- A constant map has the whole ambient tangent space as normal space; in particular so does
a point immersed in `N`. -/
@[simp]
theorem orthogonalNormalSpace_const (y : N) (x : M) :
    orthogonalNormalSpace I J (fun _ : M ↦ y) x = ⊤ := by
  rw [orthogonalNormalSpace_def, mfderiv_const]
  simp

/-- The normal space of an immersion at `x` is a complement of `T_x M`: its dimension is
`dim N - dim M`. -/
theorem finrank_orthogonalNormalSpace_add_finrank [FiniteDimensional ℝ V] {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) :
    finrank ℝ (orthogonalNormalSpace I J f x) + finrank ℝ E = finrank ℝ V := by
  have h := Submodule.finrank_add_finrank_orthogonal
    (LinearMap.range (mfderiv I J f x).toLinearMap)
  rw [LinearMap.finrank_range_of_inj hinj, finrank_tangentSpace, finrank_tangentSpace] at h
  rw [orthogonalNormalSpace_def, add_comm]
  exact h

/-- The normal spaces of an immersion of codimension one are lines. -/
theorem finrank_orthogonalNormalSpace_eq_one [FiniteDimensional ℝ V] {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) (hr : finrank ℝ V = finrank ℝ E + 1) :
    finrank ℝ (orthogonalNormalSpace I J f x) = 1 := by
  have := finrank_orthogonalNormalSpace_add_finrank hinj
  omega

section OrthogonalProjection

variable {f : M → N} {x : M}
  [(LinearMap.range (mfderiv I J f x).toLinearMap).HasOrthogonalProjection]

/-- If the range of the differential admits an orthogonal projection, so does the normal space.
This applies in particular to a finite-dimensional source, where the range is finite-dimensional
and hence complete. -/
instance instHasOrthogonalProjectionOrthogonalNormalSpace :
    (orthogonalNormalSpace I J f x).HasOrthogonalProjection :=
  inferInstanceAs (LinearMap.range (mfderiv I J f x).toLinearMap)ᗮ.HasOrthogonalProjection

/-- If the range of the differential admits an orthogonal projection, for instance for a
finite-dimensional source, the orthogonal complement of the normal space is that range. -/
@[simp]
theorem orthogonal_orthogonalNormalSpace :
    (orthogonalNormalSpace I J f x)ᗮ = LinearMap.range (mfderiv I J f x).toLinearMap := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.orthogonal_orthogonal _

/-- The orthogonal projection onto the normal space is the orthogonal projection onto the
orthogonal complement of the range of the differential. Both sides are the same map:
`orthogonalNormalSpace I J f x` is this orthogonal complement by definition
(`TauCeti.orthogonalNormalSpace_def`), and `Submodule.HasOrthogonalProjection` is a `Prop`. -/
theorem starProjection_orthogonalNormalSpace :
    (orthogonalNormalSpace I J f x).starProjection =
      (LinearMap.range (mfderiv I J f x).toLinearMap)ᗮ.starProjection :=
  (rfl)

end OrthogonalProjection

section QuotientComparison

variable (f : M → N) (x : M)
  [(LinearMap.range (mfderiv I J f x).toLinearMap).HasOrthogonalProjection]

/-- The normal space `(range df_x)ᗮ` of a map at `x` is isometric to the quotient
`T_{f x} N ⧸ range df_x` by `w ↦ [w]`, whenever the range of the differential admits an orthogonal
projection, for instance for a finite-dimensional source. It is the inverse of Mathlib's isometry
`Submodule.quotientEquivOrthogonal` between a quotient and the orthogonal complement of the
subspace. The inverse is the orthogonal projection onto the normal space
(`TauCeti.orthogonalNormalSpaceEquivQuotient_symm_mk`). -/
def orthogonalNormalSpaceEquivQuotient :
    orthogonalNormalSpace I J f x ≃ₗᵢ[ℝ]
      TangentSpace J (f x) ⧸ LinearMap.range (mfderiv I J f x).toLinearMap :=
  (LinearMap.range (mfderiv I J f x).toLinearMap).quotientEquivOrthogonal.symm

/-- The comparison takes a normal vector to its class. -/
@[simp]
theorem orthogonalNormalSpaceEquivQuotient_apply (w : orthogonalNormalSpace I J f x) :
    orthogonalNormalSpaceEquivQuotient f x w =
      Submodule.Quotient.mk (w : TangentSpace J (f x)) := by
  rw [orthogonalNormalSpaceEquivQuotient]
  exact (LinearMap.range (mfderiv I J f x).toLinearMap).quotientEquivOrthogonal_symm_eq_mk _
    w.property

/-- The inverse comparison takes the class of an ambient vector to its orthogonal projection onto
the normal space; in particular this projection depends only on the class. -/
@[simp]
theorem orthogonalNormalSpaceEquivQuotient_symm_mk (v : TangentSpace J (f x)) :
    (orthogonalNormalSpaceEquivQuotient f x).symm (Submodule.Quotient.mk v) =
      (orthogonalNormalSpace I J f x).orthogonalProjectionOnto v := by
  rw [LinearIsometryEquiv.symm_apply_eq, orthogonalNormalSpaceEquivQuotient_apply,
    Submodule.Quotient.eq, Submodule.coe_orthogonalProjectionOnto_apply]
  have h := (orthogonalNormalSpace I J f x).sub_starProjection_mem_orthogonal v
  rwa [orthogonal_orthogonalNormalSpace] at h

end QuotientComparison

section FiniteDimensionalSource

variable [FiniteDimensional ℝ E]

/-- The orthogonal projection onto the normal space subtracts the tangential component of an
ambient vector `v`, which is `df ((df* df)⁻¹ (df* v))` for the pullback metric `df* df` on `T_x M`.
For a finite-dimensional source, only injectivity of the differential at `x` is assumed; neither
`f` nor the ambient metric need be regular. -/
theorem starProjection_orthogonalNormalSpace_eq_sub_mfderiv_inverse {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) (v : TangentSpace J (f x)) :
    let d := mfderiv I J f x
    let φ := (RiemannianBundle.g.inner (f x) v).comp d
    let a := (ContinuousLinearMap.precomp ℝ d).comp ((RiemannianBundle.g.inner (f x)).comp d)
    (orthogonalNormalSpace I J f x).starProjection v = v - d (a.inverse φ) := by
  intro d φ a
  have ha : a.IsInvertible := ContinuousLinearMap.isInvertible_of_pos fun w hw0 ↦
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
  · rw [orthogonal_orthogonalNormalSpace]
    exact ⟨_, rfl⟩

variable {n m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

/-- **The normal projection is smooth.** If `f` is `C^n` at `p.proj` with injective
differential there, `m + 1 ≤ n` and the ambient metric is `C^m`, then orthogonal projection onto
the normal spaces is a `C^m` self-map of the pulled-back tangent bundle `f *ᵖ TN` at `p`. Both
the base point and the ambient vector may vary. This is
`ContMDiffAt.starProjection_orthogonal_range_mfderiv`, since the normal projection is the projection
onto `(range df)ᗮ`. -/
theorem contMDiffAt_starProjection_orthogonalNormalSpace {f : K}
    {p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))} (hf : ContMDiffAt I J n f p.proj)
    (hinj : Function.Injective (mfderiv I J f p.proj)) (hm : m + 1 ≤ n) :
    ContMDiffAt (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).starProjection p.snd⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) p := by
  have hfm : ContMDiffAt I J m f p.proj := hf.of_le (le_self_add.trans hm)
  have hbase : ContMDiffAt (I.prod 𝓘(ℝ, V)) I m
      (π V ((f : M → N) *ᵖ (TangentSpace J))) p := contMDiffAt_proj _
  simp only [starProjection_orthogonalNormalSpace]
  refine (Pullback.contMDiffAt_iff f hfm).mpr ⟨hbase, ?_⟩
  exact ((hf.starProjection_orthogonal_range_mfderiv hm hinj).comp p hbase).clm_bundle_apply
    (Pullback.contMDiffAt_lift f hfm (E := fun y : N ↦ TangentSpace J y))

/-- **The normal projection is smooth.** For a `C^n` immersion `f` with `m + 1 ≤ n` and a `C^m`
ambient metric, orthogonal projection onto the normal spaces is a `C^m` self-map of the
pulled-back tangent bundle `f *ᵖ TN`. Both the base point and the ambient vector may vary. -/
theorem contMDiff_starProjection_orthogonalNormalSpace {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).starProjection p.snd⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) := fun p ↦
  contMDiffAt_starProjection_orthogonalNormalSpace (hf p.proj) (hinj p.proj) hm

end FiniteDimensionalSource

/-! ### The normal bundle `ν_f` -/

variable [FiniteDimensional ℝ V] {n m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)] [IsManifold J (m + 1) N]

/-- **Local frames of the normal bundle.** For a `C^n` immersion `f` with `m + 1 ≤ n`, a `C^m`
ambient metric and `dim N = dim M + r`, the normal spaces have `C^m` local frames of size `r` in
the pulled-back tangent bundle `f *ᵖ TN`: they are the ranges of the normal projection, a `C^m`
fibrewise map of constant rank `r`, so this is
`TauCeti.hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range`. By
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` they form a `C^m` subbundle
`ν_f` of `f *ᵖ TN`. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    HasLocalContMDiffSubbundleFrames I m V (Fin r) (E := (f : M → N) *ᵖ (TangentSpace J))
      (orthogonalNormalSpace I J f) := by
  have := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (hf.of_le (le_self_add.trans hm))
  -- Elaborate in the fibres `TangentSpace J (f x)`, not in the pullback fibres.
  have hrange (x : M) : LinearMap.range ((orthogonalNormalSpace I J f x).starProjection :
      TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x)) = orthogonalNormalSpace I J f x :=
    Submodule.range_starProjection _
  have hfin (x : M) : finrank ℝ (orthogonalNormalSpace I J f x) = r := by
    have := finrank_orthogonalNormalSpace_add_finrank (hinj x)
    omega
  have hP : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).starProjection p.snd⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) := fun p ↦ by
    have := finiteDimensional_of_injective_mfderiv (hinj p.proj)
    exact contMDiffAt_starProjection_orthogonalNormalSpace (hf p.proj) (hinj p.proj) hm
  exact hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range
    (E₁ := (f : M → N) *ᵖ (TangentSpace J)) (E₂ := (f : M → N) *ᵖ (TangentSpace J)) _
    hP hrange hfin

variable (I J) in
/-- The total space of the normal spaces of `f : M → N` carries the subspace topology
(`TauCeti.subbundleTopology`) of the pulled-back tangent bundle `f *ᵖ TN`. The model-fibre
parameter `P` of `Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceOrthogonalNormalSpace (P : Type*) (f : M → N) :
    TopologicalSpace (TotalSpace P fun x ↦ orthogonalNormalSpace I J f x) :=
  subbundleTopology V (E := f *ᵖ (TangentSpace J)) (orthogonalNormalSpace I J f)

/-- **The normal bundle `ν_f` of an immersion.** For a `C^n` immersion `f` with `m + 1 ≤ n`, a
`C^m` ambient metric and `dim N = dim M + r`, the normal spaces `orthogonalNormalSpace I J f`
form a fibre bundle over `M` with model fibre `Fin r → ℝ`, carrying the subspace topology from
`f *ᵖ TN` (`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Install this definition
locally with `letI`. Its trivializations are those of the `C^m` local frames of the normal
spaces, so the structure depends on `m`; it does not depend on `n` or on the proofs `hf`, `hinj`,
`hm` and `hr` (`TauCeti.orthogonalNormalFiberBundle_congr`). -/
@[instance_reducible]
def orthogonalNormalFiberBundle {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    FiberBundle (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x :=
  (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).fiberBundle

/-- The fibre bundle structure of `ν_f` is the one given by its `C^m` local frames
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`); its trivializations are described by
`TauCeti.HasLocalContMDiffSubbundleFrames.mem_trivializationAtlas_fiberBundle_iff`. -/
theorem orthogonalNormalFiberBundle_def {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    orthogonalNormalFiberBundle hf hinj hm hr =
      (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).fiberBundle :=
  (rfl)

/-- The fibre bundle structure of `ν_f` depends only on the regularity `m` of its local frames:
two `C^n` and `C^n'` immersion hypotheses with the same `m` give the same structure. -/
theorem orthogonalNormalFiberBundle_congr {r : ℕ} {n' : ℕ∞ω} {f : K} (hf : ContMDiff I J n f)
    (hf' : ContMDiff I J n' f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hm' : m + 1 ≤ n') (hr : finrank ℝ V = finrank ℝ E + r) :
    orthogonalNormalFiberBundle hf hinj hm hr = orthogonalNormalFiberBundle hf' hinj hm' hr :=
  (rfl)

/-- **The normal bundle `ν_f` is a topological vector bundle**, with the fibre bundle structure
`TauCeti.orthogonalNormalFiberBundle` installed by `letI`. -/
theorem orthogonalNormalVectorBundle {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    VectorBundle ℝ (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x :=
  (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).vectorBundle

/-- **The normal bundle `ν_f` is a `C^m` vector bundle**, a `C^m` subbundle of `f *ᵖ TN` of rank
`r = dim N - dim M`, with the structures `TauCeti.orthogonalNormalFiberBundle` and
`TauCeti.orthogonalNormalVectorBundle` installed by `letI`. -/
theorem orthogonalNormalContMDiffVectorBundle {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffVectorBundle m (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) I := by
  have := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (hf.of_le (le_self_add.trans hm))
  exact (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).contMDiffVectorBundle

/-- The canonical inclusion `ν_f → f *ᵖ TN` of the normal bundle of an immersion is `C^m`. -/
theorem contMDiff_orthogonalNormalSpace_inclusion {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, V)) m
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
        (⟨v.proj, (v.snd : TangentSpace J (f v.proj))⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) := by
  have := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (hf.of_le (le_self_add.trans hm))
  exact (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr
    ).contMDiff_totalSpace_inclusion

/-- The map `ν_f → TN` sending a normal vector at `x` to the same vector at `f x` is `C^m`. -/
theorem contMDiff_orthogonalNormalSpace_inclusion_tangentBundle {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (J.prod 𝓘(ℝ, V)) m
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
        (⟨f v.proj, (v.snd : TangentSpace J (f v.proj))⟩ : TangentBundle J N)) := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  exact (Pullback.contMDiff_lift fc fc.contMDiff (E := fun y : N ↦ TangentSpace J y)).comp
    (contMDiff_orthogonalNormalSpace_inclusion hf hinj hm hr)

section UniversalProperty

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X] {k : ℕ∞ω}

/-- **Maps into the normal bundle.** For `k ≤ m`, a map into `f *ᵖ TN` whose values are normal
vectors and which is `C^k` within `s` at `z₀` is `C^k` within `s` at `z₀` as a map into `ν_f`. -/
theorem contMDiffWithinAt_orthogonalNormalSpace_mk {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {s : Set X} {z₀ : X}
    (hw : ContMDiffWithinAt IX (I.prod 𝓘(ℝ, V)) k
      (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) s z₀)
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffWithinAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
      (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
        TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) s z₀ := by
  have := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  have := Pullback.contMDiffVectorBundle (F := V) (E := TangentSpace J)
    (hf.of_le (le_self_add.trans hm))
  exact (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr
    ).contMDiffWithinAt_totalSpace_mk hk hw hmem

/-- **Maps into the normal bundle.** For `k ≤ m`, a map into `f *ᵖ TN` whose values are normal
vectors and which is `C^k` at `z₀` is `C^k` at `z₀` as a map into `ν_f`. -/
theorem contMDiffAt_orthogonalNormalSpace_mk {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {z₀ : X}
    (hw : ContMDiffAt IX (I.prod 𝓘(ℝ, V)) k
      (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) z₀)
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
      (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
        TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) z₀ :=
  contMDiffWithinAt_orthogonalNormalSpace_mk hf hinj hm hr hk hw hmem

/-- **Universal property of `ν_f` in `f *ᵖ TN`.** For `k ≤ m`, a map with normal values is `C^k`
within `s` at `z₀` into `ν_f` exactly when it is `C^k` within `s` at `z₀` into `f *ᵖ TN`. -/
theorem contMDiffWithinAt_orthogonalNormalSpace_mk_iff {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {s : Set X} {z₀ : X}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffWithinAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) s z₀ ↔
      ContMDiffWithinAt IX (I.prod 𝓘(ℝ, V)) k
        (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) s z₀ :=
  letI := orthogonalNormalFiberBundle hf hinj hm hr
  letI := orthogonalNormalVectorBundle hf hinj hm hr
  ⟨fun h ↦ ((contMDiff_orthogonalNormalSpace_inclusion hf hinj hm hr).of_le hk _
      ).comp_contMDiffWithinAt z₀ h,
    fun h ↦ contMDiffWithinAt_orthogonalNormalSpace_mk hf hinj hm hr hk h hmem⟩

/-- **Universal property of `ν_f` in `f *ᵖ TN`.** For `k ≤ m`, a map with normal values is `C^k`
at `z₀` into `ν_f` exactly when it is `C^k` at `z₀` into `f *ᵖ TN`. -/
theorem contMDiffAt_orthogonalNormalSpace_mk_iff {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {z₀ : X}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) z₀ ↔
      ContMDiffAt IX (I.prod 𝓘(ℝ, V)) k
        (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) z₀ :=
  contMDiffWithinAt_orthogonalNormalSpace_mk_iff hf hinj hm hr hk hmem

/-- **Universal property of `ν_f` in `f *ᵖ TN`.** For `k ≤ m`, a map with normal values is `C^k`
on `s` into `ν_f` exactly when it is `C^k` on `s` into `f *ᵖ TN`. -/
theorem contMDiffOn_orthogonalNormalSpace_mk_iff {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {s : Set X}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffOn IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) s ↔
      ContMDiffOn IX (I.prod 𝓘(ℝ, V)) k
        (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) s :=
  forall₂_congr fun _ _ ↦ contMDiffWithinAt_orthogonalNormalSpace_mk_iff hf hinj hm hr hk hmem

/-- **Universal property of `ν_f` in `f *ᵖ TN`.** For `k ≤ m`, a map with normal values is `C^k`
into `ν_f` exactly when it is `C^k` into `f *ᵖ TN`. -/
theorem contMDiff_orthogonalNormalSpace_mk_iff {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) ↔
      ContMDiff IX (I.prod 𝓘(ℝ, V)) k
        (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) :=
  forall_congr' fun _ ↦ contMDiffAt_orthogonalNormalSpace_mk_iff hf hinj hm hr hk hmem

/-- **Universal property of `ν_f` in `TN`.** For `k ≤ m`, a map with normal values is `C^k` within
`s` at `z₀` into `ν_f` exactly when its base point is `C^k` within `s` at `z₀` and the
corresponding map into the ambient tangent bundle `TN` is `C^k` within `s` at `z₀`. -/
theorem contMDiffWithinAt_orthogonalNormalSpace_mk_iff_tangentBundle {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {s : Set X} {z₀ : X}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffWithinAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) s z₀ ↔
      ContMDiffWithinAt IX I k b s z₀ ∧
        ContMDiffWithinAt IX (J.prod 𝓘(ℝ, V)) k
          (fun z ↦ (⟨f (b z), w z⟩ : TangentBundle J N)) s z₀ :=
  (contMDiffWithinAt_orthogonalNormalSpace_mk_iff hf hinj hm hr hk hmem).trans
    (Pullback.contMDiffWithinAt_iff f ((hf (b z₀)).of_le ((hk.trans le_self_add).trans hm)))

/-- **Universal property of `ν_f` in `TN`.** For `k ≤ m`, a map with normal values is `C^k` at
`z₀` into `ν_f` exactly when its base point is `C^k` at `z₀` and the corresponding map into the
ambient tangent bundle `TN` is `C^k` at `z₀`. -/
theorem contMDiffAt_orthogonalNormalSpace_mk_iff_tangentBundle {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {z₀ : X}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) z₀ ↔
      ContMDiffAt IX I k b z₀ ∧
        ContMDiffAt IX (J.prod 𝓘(ℝ, V)) k
          (fun z ↦ (⟨f (b z), w z⟩ : TangentBundle J N)) z₀ :=
  contMDiffWithinAt_orthogonalNormalSpace_mk_iff_tangentBundle hf hinj hm hr hk hmem

/-- **Universal property of `ν_f` in `TN`.** For `k ≤ m`, a map with normal values is `C^k` on `s`
into `ν_f` exactly when its base point is `C^k` on `s` and the corresponding map into the ambient
tangent bundle `TN` is `C^k` on `s`. -/
theorem contMDiffOn_orthogonalNormalSpace_mk_iff_tangentBundle {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {s : Set X}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffOn IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) s ↔
      ContMDiffOn IX I k b s ∧
        ContMDiffOn IX (J.prod 𝓘(ℝ, V)) k (fun z ↦ (⟨f (b z), w z⟩ : TangentBundle J N)) s :=
  (forall₂_congr fun _ _ ↦
    contMDiffWithinAt_orthogonalNormalSpace_mk_iff_tangentBundle hf hinj hm hr hk hmem).trans
    forall₂_and

/-- **Universal property of `ν_f` in `TN`.** For `k ≤ m`, a map with normal values is `C^k` into
`ν_f` exactly when its base point is `C^k` and the corresponding map into the ambient tangent
bundle `TN` is `C^k`. -/
theorem contMDiff_orthogonalNormalSpace_mk_iff_tangentBundle {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) (hk : k ≤ m) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))}
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff IX (I.prod 𝓘(ℝ, Fin r → ℝ)) k
        (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) ↔
      ContMDiff IX I k b ∧
        ContMDiff IX (J.prod 𝓘(ℝ, V)) k (fun z ↦ (⟨f (b z), w z⟩ : TangentBundle J N)) :=
  (forall_congr' fun _ ↦
    contMDiffAt_orthogonalNormalSpace_mk_iff_tangentBundle hf hinj hm hr hk hmem).trans
    forall_and

end UniversalProperty

/-- **The normal projection into `ν_f` is smooth.** Orthogonal projection of the pulled-back
tangent bundle `f *ᵖ TN` onto the normal bundle `ν_f` is `C^m`. -/
theorem contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, Fin r → ℝ)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).orthogonalProjectionOnto p.snd⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) := fun p ↦ by
  have := finiteDimensional_of_injective_mfderiv (hinj p.proj)
  -- The values in `f *ᵖ TN` are the normal projections (`Submodule.starProjection_apply`).
  have hw := (contMDiffAt_starProjection_orthogonalNormalSpace (hf p.proj) (hinj p.proj) hm
    ).congr_of_eventuallyEq <| .of_forall fun q ↦ congrArg (TotalSpace.mk q.proj)
      ((orthogonalNormalSpace I J f q.proj).starProjection_apply (q.snd : TangentSpace J _)).symm
  exact contMDiffAt_orthogonalNormalSpace_mk hf hinj hm hr le_rfl hw
    fun q ↦ ((orthogonalNormalSpace I J f q.proj).orthogonalProjectionOnto q.snd).property

omit [FiniteDimensional ℝ V] [IsManifold I 1 M] in
/-- The fibre norm of the normal spaces of a map `f`, the norm of the ambient metric, is
continuous on their total space with the subspace topology of `f *ᵖ TN`, for any model fibre. -/
theorem continuous_norm_orthogonalNormalSpace
    [IsContinuousRiemannianBundle V (fun y : N ↦ TangentSpace J y)] (P : Type*) (f : M → N) :
    Continuous fun v : TotalSpace P (fun x ↦ orthogonalNormalSpace I J f x) ↦ ‖v.snd‖ :=
  continuous_norm_subbundle (F := V) (E := (f : M → N) *ᵖ (TangentSpace J))
    (ContinuousFiberNorm.continuous_norm (F := V) (E := (f : M → N) *ᵖ (TangentSpace J))) P
    (orthogonalNormalSpace I J f)

end TauCeti
