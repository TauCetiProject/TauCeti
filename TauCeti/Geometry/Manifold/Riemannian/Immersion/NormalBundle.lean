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
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Pullback.TangentialCorrection
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
(`TauCeti.contMDiff_starProjection_orthogonalNormalSpace`), an instance of the smooth
tangential correction `TauCeti.contMDiff_of_eq_sub_mfderiv_inverse`. Projecting local sections
of `f *ᵖ TN` through preimages of a basis of one normal space gives `C^m` local frames of the
normal spaces
(`TauCeti.hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace`). By the smooth local frame
criterion `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` the normal spaces,
with the subspace topology of `f *ᵖ TN`, therefore form a `C^m` subbundle `ν_f` of `f *ᵖ TN` of
rank `dim N - dim M` (`TauCeti.orthogonalNormalFiberBundle`,
`TauCeti.orthogonalNormalVectorBundle`, `TauCeti.orthogonalNormalContMDiffVectorBundle`). Its
inclusion into `f *ᵖ TN` is `C^m` (`TauCeti.contMDiff_orthogonalNormalSpace_inclusion`), a `C^m`
map into `f *ᵖ TN` with normal values is `C^m` into `ν_f`
(`TauCeti.contMDiffAt_orthogonalNormalSpace_mk`), and so is the orthogonal projection onto `ν_f`
(`TauCeti.contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace`). No
compactness, injectivity of `f`, boundarylessness or choice of normal frame is assumed. The
identity map has zero normal spaces and a constant map has the whole ambient tangent space as
normal space (`TauCeti.orthogonalNormalSpace_id`, `TauCeti.orthogonalNormalSpace_const`).

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

section FiniteDimensional

variable {𝕜 E V H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

/-- A map into a finite-dimensional manifold whose differential is injective at some point has a
finite-dimensional model space. -/
theorem finiteDimensional_of_injective_mfderiv {f : M → N} {x : M}
    (hinj : Function.Injective (mfderiv I J f x)) : FiniteDimensional 𝕜 E := by
  have : FiniteDimensional 𝕜 (TangentSpace I x) :=
    Module.Finite.of_injective (mfderiv I J f x).toLinearMap hinj
  exact (tangentSpaceCastModel I x).toLinearEquiv.finiteDimensional

end FiniteDimensional

variable {E V H G M N K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
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
/-- The differential of a tangent vector is orthogonal to the normal space. -/
@[simp]
theorem mfderiv_mem_orthogonal_orthogonalNormalSpace (f : M → N) (x : M) (u : TangentSpace I x) :
    mfderiv I J f x u ∈ (orthogonalNormalSpace I J f x)ᗮ := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.le_orthogonal_orthogonal _ ⟨u, rfl⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The normal projection kills the differentials of tangent vectors. -/
@[simp]
theorem starProjection_orthogonalNormalSpace_mfderiv (f : M → N) (x : M)
    [(orthogonalNormalSpace I J f x).HasOrthogonalProjection] (u : TangentSpace I x) :
    (orthogonalNormalSpace I J f x).starProjection (mfderiv I J f x u) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr
    (mfderiv_mem_orthogonal_orthogonalNormalSpace f x u)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- The orthogonal projection onto the normal space kills the differentials of tangent
vectors. -/
@[simp]
theorem orthogonalProjectionOnto_orthogonalNormalSpace_mfderiv (f : M → N) (x : M)
    [(orthogonalNormalSpace I J f x).HasOrthogonalProjection] (u : TangentSpace I x) :
    (orthogonalNormalSpace I J f x).orthogonalProjectionOnto (mfderiv I J f x u) = 0 :=
  Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    (mfderiv_mem_orthogonal_orthogonalNormalSpace f x u)

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
  rw [LinearMap.finrank_range_of_inj hinj, finrank_tangentSpace, finrank_tangentSpace] at h
  rw [orthogonalNormalSpace_def, add_comm]
  exact h

omit [FiniteDimensional ℝ E] in
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
  have := finiteDimensional_of_injective_mfderiv hinj
  intro d φ a
  let : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
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

variable {n m : ℕ∞ω} [IsManifold I 1 M] [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]

omit [FiniteDimensional ℝ E] in
/-- **The normal projection is smooth.** For a `C^n` immersion `f` with `m + 1 ≤ n` and a `C^m`
ambient metric, orthogonal projection onto the normal spaces is a `C^m` self-map of the
pulled-back tangent bundle `f *ᵖ TN`. Both the base point and the ambient vector may vary. It is
the tangential correction `TauCeti.contMDiff_of_eq_sub_mfderiv_inverse` for the ambient metric
and the induced metric on `M`. -/
theorem contMDiff_starProjection_orthogonalNormalSpace {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (hm : m + 1 ≤ n) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).starProjection p.2⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact fun p ↦ isEmptyElim p.proj
  have := finiteDimensional_of_injective_mfderiv (hinj x₀)
  let : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- The induced metric identifies tangent vectors with covectors on the source.
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := J) (n := m) (F := V) (V := fun y : N ↦ TangentSpace J y)
  let a := g.pullback f (hf.of_le hm) hinj
  refine contMDiff_of_eq_sub_mfderiv_inverse f hf hm a.contMDiff
    (fun x ↦ ContinuousLinearMap.isInvertible_of_pos (E := E) (a.pos x)) g.contMDiff
    (fun x v ↦ (orthogonalNormalSpace I J f x).starProjection v) fun x v ↦ ?_
  rw [starProjection_orthogonalNormalSpace_eq_sub_mfderiv_inverse (hinj x)]
  have hg : g.inner (f x) = RiemannianBundle.g.inner (f x) := by
    ext w z
    exact ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner _ _ _
  have hflat : a.inner x = (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
      ((g.inner (f x)).comp (mfderiv I J f x)) := by
    ext w z
    exact ContMDiffRiemannianMetric.pullback_inner _ _ _ _ _ _ _
  simp only [hflat, hg]

variable [IsManifold J (m + 1) N]

omit [FiniteDimensional ℝ E] in
/-- **Local frames of the normal bundle.** For a `C^n` immersion `f` with `m + 1 ≤ n`, a `C^m`
ambient metric and `dim N = dim M + r`, the normal spaces have `C^m` local frames of size `r` in
the pulled-back tangent bundle `f *ᵖ TN`. By
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` they form a `C^m` subbundle
`ν_f` of `f *ᵖ TN`. The frames are normal projections of local sections of `f *ᵖ TN`. -/
theorem hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    HasLocalContMDiffSubbundleFrames I m V (Fin r) (E := (f : M → N) *ᵖ (TangentSpace J))
      (orthogonalNormalSpace I J f) := by
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  -- Elaborate in the fibres `TangentSpace J (f x)`, not in the pullback fibres.
  have hrange (x : M) : LinearMap.range ((orthogonalNormalSpace I J f x).starProjection :
      TangentSpace J (f x) →ₗ[ℝ] TangentSpace J (f x)) = orthogonalNormalSpace I J f x :=
    Submodule.range_starProjection _
  have hfin (x : M) : finrank ℝ (orthogonalNormalSpace I J f x) = r := by
    have := finrank_orthogonalNormalSpace_add_finrank (hinj x)
    omega
  exact hasLocalContMDiffSubbundleFrames_of_contMDiff_totalSpace_range
    (E₁ := (f : M → N) *ᵖ (TangentSpace J)) (E₂ := (f : M → N) *ᵖ (TangentSpace J)) _
    (contMDiff_starProjection_orthogonalNormalSpace hf hinj hm) hrange hfin

/-! ### The normal bundle `ν_f` -/

variable (I J) in
/-- The total space of the normal spaces of `f : M → N` carries the subspace topology
(`TauCeti.subbundleTopology`) of the pulled-back tangent bundle `f *ᵖ TN`. The model-fibre
parameter `P` of `Bundle.TotalSpace` plays no role. -/
instance instTopologicalSpaceTotalSpaceOrthogonalNormalSpace (P : Type*) (f : M → N) :
    TopologicalSpace (TotalSpace P fun x ↦ orthogonalNormalSpace I J f x) :=
  subbundleTopology V (E := f *ᵖ (TangentSpace J)) (orthogonalNormalSpace I J f)

omit [FiniteDimensional ℝ E] in
/-- **The normal bundle `ν_f` of an immersion.** For a `C^n` immersion `f` with `m + 1 ≤ n`, a
`C^m` ambient metric and `dim N = dim M + r`, the normal spaces `orthogonalNormalSpace I J f`
form a fibre bundle over `M` with model fibre `Fin r → ℝ`, carrying the subspace topology from
`f *ᵖ TN` (`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). Install this definition
locally with `letI`. -/
@[instance_reducible]
def orthogonalNormalFiberBundle {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    FiberBundle (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x :=
  (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).fiberBundle

omit [FiniteDimensional ℝ E] in
/-- The fibre bundle structure of `ν_f` is the one given by its `C^m` local frames
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`); its trivializations are described by
`TauCeti.HasLocalContMDiffSubbundleFrames.mem_trivializationAtlas_fiberBundle_iff`. -/
theorem orthogonalNormalFiberBundle_def {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    orthogonalNormalFiberBundle hf hinj hm hr =
      (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).fiberBundle :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- **The normal bundle `ν_f` is a topological vector bundle.** Its local frame trivializations
are linear with continuous coordinate changes. -/
theorem orthogonalNormalVectorBundle {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    VectorBundle ℝ (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x :=
  (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).vectorBundle

omit [FiniteDimensional ℝ E] in
/-- **The normal bundle `ν_f` is a `C^m` vector bundle**, a `C^m` subbundle of `f *ᵖ TN` of rank
`r = dim N - dim M`, by the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`. -/
theorem orthogonalNormalContMDiffVectorBundle {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffVectorBundle m (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) I := by
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  exact (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr).contMDiffVectorBundle

omit [FiniteDimensional ℝ E] in
/-- The canonical inclusion `ν_f → f *ᵖ TN` of the normal bundle of an immersion is `C^m`. -/
theorem contMDiff_orthogonalNormalSpace_inclusion {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, V)) m
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
        (⟨v.proj, (v.2 : TangentSpace J (f v.proj))⟩ :
          TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) := by
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  exact (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr
    ).contMDiff_totalSpace_inclusion

omit [FiniteDimensional ℝ E] in
/-- The map `ν_f → TN` sending a normal vector at `x` to the same vector at `f x` is `C^m`. -/
theorem contMDiff_orthogonalNormalSpace_inclusion_tangentBundle {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (J.prod 𝓘(ℝ, V)) m
      (fun v : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
        (⟨f v.proj, (v.2 : TangentSpace J (f v.proj))⟩ : TangentBundle J N)) := by
  let := orthogonalNormalFiberBundle hf hinj hm hr
  let := orthogonalNormalVectorBundle hf hinj hm hr
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  exact (Pullback.contMDiff_lift fc fc.contMDiff (E := fun y : N ↦ TangentSpace J y)).comp
    (contMDiff_orthogonalNormalSpace_inclusion hf hinj hm hr)

section UniversalProperty

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]

omit [FiniteDimensional ℝ E] in
/-- **Maps into the normal bundle.** A `C^m` map into `f *ᵖ TN` whose values are normal vectors
is `C^m` as a map into `ν_f`. -/
theorem contMDiffAt_orthogonalNormalSpace_mk {r : ℕ} {f : K} (hf : ContMDiff I J n f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) {b : X → M}
    {w : ∀ z, TangentSpace J (f (b z))} {z₀ : X}
    (hw : ContMDiffAt IX (I.prod 𝓘(ℝ, V)) m
      (fun z ↦ (⟨b z, w z⟩ : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)))) z₀)
    (hmem : ∀ z, w z ∈ orthogonalNormalSpace I J f (b z)) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiffAt IX (I.prod 𝓘(ℝ, Fin r → ℝ)) m
      (fun z ↦ (⟨b z, ⟨w z, hmem z⟩⟩ :
        TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) z₀ := by
  let fc : C^m⟮I, M; J, N⟯ := ⟨f, hf.of_le (le_self_add.trans hm)⟩
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := m)
  let : ContMDiffVectorBundle m V ((f : M → N) *ᵖ (TangentSpace J)) I :=
    ContMDiffVectorBundle.pullback V (TangentSpace J) I fc
  exact (hasLocalContMDiffSubbundleFrames_orthogonalNormalSpace hf hinj hm hr
    ).contMDiffAt_totalSpace_mk hw hmem

end UniversalProperty

omit [FiniteDimensional ℝ E] in
/-- **The normal projection into `ν_f` is smooth.** Orthogonal projection of the pulled-back
tangent bundle `f *ᵖ TN` onto the normal bundle `ν_f` is `C^m`. -/
theorem contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace {r : ℕ} {f : K}
    (hf : ContMDiff I J n f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r) :
    letI := orthogonalNormalFiberBundle hf hinj hm hr
    letI := orthogonalNormalVectorBundle hf hinj hm hr
    ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, Fin r → ℝ)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, (orthogonalNormalSpace I J f p.proj).orthogonalProjectionOnto p.2⟩ :
          TotalSpace (Fin r → ℝ) fun x ↦ orthogonalNormalSpace I J f x)) := fun p ↦
  contMDiffAt_orthogonalNormalSpace_mk hf hinj hm hr
    (contMDiff_starProjection_orthogonalNormalSpace hf hinj hm p)
    fun q ↦ (orthogonalNormalSpace I J f q.proj).starProjection_apply_mem
      (q.2 : TangentSpace J (f q.proj))

end TauCeti
