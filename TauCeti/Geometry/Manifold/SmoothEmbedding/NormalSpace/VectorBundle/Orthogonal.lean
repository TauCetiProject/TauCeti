/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The orthogonal normal bundle as a quotient bundle

Let `f : M → N` be an immersion into a manifold whose tangent spaces carry a Riemannian metric.
At `x : M` the orthogonal normal space `ν_f,x = (range df_x)ᗮ` (`TauCeti.orthogonalNormalSpace`)
maps isomorphically onto the quotient `T_{f x} N ⧸ range df_x` by `w ↦ [w]`
(`TauCeti.orthogonalNormalSpaceEquivQuotient`). The inverse sends `[v]` to the orthogonal
projection of `v` onto `ν_f,x`, which does not depend on the representative, since adding `df u`
leaves the projection unchanged. The quotient norm of `[w]` is the norm of `w`
(`TauCeti.norm_orthogonalNormalSpaceEquivQuotient`). The fibres are indexed by the source point,
so two sheets of an immersion through one image point keep separate fibres.

For a `C^n` embedding with `m + 1 ≤ n` and a `C^m` metric, these fibre isomorphisms assemble into
a `C^m` diffeomorphism over the identity of `M` from the orthogonal normal bundle `ν_f`
(`TauCeti.orthogonalNormalFiberBundle`) to the intrinsic normal bundle `f*TN / df(TM)` of the
embedding (`TauCeti.SmoothEmbedding.normalSpaceFiberBundle`), fibrewise linear
(`TauCeti.SmoothEmbedding.orthogonalNormalBundleDiffeomorph`). Smoothness of the forward map is
smoothness of the inclusion `ν_f → f*TN` followed by the normal quotient; smoothness of the inverse
descends, through the smooth normal quotient, from smoothness of the orthogonal projection
`f*TN → ν_f`, given in local frames by `v ↦ v - df((df* df)⁻¹ df* v)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8, the normal bundle
  of an immersed submanifold.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Manifold Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

section Fibre

variable (f : M → N) (x : M)
  [(LinearMap.range (mfderiv I J f x).toLinearMap).HasOrthogonalProjection]

/-- The range of the differential and the normal space are topological complements. -/
theorem isTopCompl_range_mfderiv_orthogonalNormalSpace :
    (LinearMap.range (mfderiv I J f x).toLinearMap).IsTopCompl (orthogonalNormalSpace I J f x) := by
  rw [orthogonalNormalSpace_def]
  exact Submodule.isTopCompl_orthogonal _

/-- The normal space `(range df_x)ᗮ` of a map at `x` is isomorphic to the quotient
`T_{f x} N ⧸ range df_x` by `w ↦ [w]`, whenever the range of the differential admits an orthogonal
projection, for instance for a finite-dimensional source. The inverse is the orthogonal projection
onto the normal space (`TauCeti.orthogonalNormalSpaceEquivQuotient_symm_mk`). -/
def orthogonalNormalSpaceEquivQuotient :
    orthogonalNormalSpace I J f x ≃L[ℝ]
      TangentSpace J (f x) ⧸ LinearMap.range (mfderiv I J f x).toLinearMap :=
  (Submodule.quotientEquivOfIsTopCompl _ _
    (isTopCompl_range_mfderiv_orthogonalNormalSpace f x)).symm

/-- The comparison takes a normal vector to its class. -/
@[simp]
theorem orthogonalNormalSpaceEquivQuotient_apply (w : orthogonalNormalSpace I J f x) :
    orthogonalNormalSpaceEquivQuotient f x w = Submodule.Quotient.mk (w : TangentSpace J (f x)) :=
  (rfl)

/-- The inverse comparison takes the class of an ambient vector to its orthogonal projection onto
the normal space; in particular this projection depends only on the class. -/
@[simp]
theorem orthogonalNormalSpaceEquivQuotient_symm_mk (v : TangentSpace J (f x)) :
    (orthogonalNormalSpaceEquivQuotient f x).symm (Submodule.Quotient.mk v) =
      (orthogonalNormalSpace I J f x).orthogonalProjectionOnto v := by
  rw [ContinuousLinearEquiv.symm_apply_eq, orthogonalNormalSpaceEquivQuotient_apply,
    Submodule.Quotient.eq, Submodule.coe_orthogonalProjectionOnto_apply]
  have h := (orthogonalNormalSpace I J f x).sub_starProjection_mem_orthogonal v
  rwa [orthogonal_orthogonalNormalSpace] at h

/-- **The quotient norm equals the normal norm.** For a normal vector `w`, the quotient norm of its
class `[w]` in `T_{f x} N ⧸ range df_x` is the norm of `w`. -/
theorem norm_orthogonalNormalSpaceEquivQuotient (w : orthogonalNormalSpace I J f x) :
    ‖orthogonalNormalSpaceEquivQuotient f x w‖ = ‖(w : TangentSpace J (f x))‖ := by
  rw [orthogonalNormalSpaceEquivQuotient_apply]
  refine (QuotientAddGroup.norm_mk (S := (LinearMap.range (mfderiv I J f x).toLinearMap
    ).toAddSubgroup) (w : TangentSpace J (f x))).trans ?_
  rw [Submodule.coe_toAddSubgroup, ← Submodule.dist_starProjection_eq_infDist,
    (Submodule.starProjection_apply_eq_zero_iff _).mpr, dist_zero_right]
  rw [← orthogonalNormalSpace_def]
  exact w.2

end Fibre

namespace SmoothEmbedding

variable {n : ℕ∞ω} [FiniteDimensional ℝ V]

/-- For a smooth embedding, the orthogonal normal space at `x` is isomorphic to the intrinsic normal
space `T_{f x} N ⧸ range df_x` by `w ↦ [w]`; the inverse takes orthogonal representatives
(`TauCeti.SmoothEmbedding.orthogonalNormalSpaceEquiv_symm_apply`). -/
def orthogonalNormalSpaceEquiv (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    orthogonalNormalSpace I J f x ≃L[ℝ] f.NormalSpace x hn :=
  orthogonalNormalSpaceEquivQuotient f x

/-- The comparison takes a normal vector to its normal class. -/
@[simp]
theorem orthogonalNormalSpaceEquiv_apply (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (w : orthogonalNormalSpace I J f x) :
    f.orthogonalNormalSpaceEquiv x hn w = f.normalClass x hn w := by
  rw [normalClass_def]
  rfl

/-- The inverse comparison takes the normal class of an ambient vector to its orthogonal projection
onto the normal space. -/
@[simp]
theorem orthogonalNormalSpaceEquiv_symm_normalClass (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) (v : TangentSpace J (f x)) :
    (f.orthogonalNormalSpaceEquiv x hn).symm (f.normalClass x hn v) =
      (orthogonalNormalSpace I J f x).orthogonalProjectionOnto v := by
  rw [normalClass_def]
  exact orthogonalNormalSpaceEquivQuotient_symm_mk (I := I) (f : M → N) x v

/-- The inverse comparison takes a normal class to its orthogonal representative. -/
theorem orthogonalNormalSpaceEquiv_symm_apply (f : SmoothEmbedding I J n M N) (x : M)
    (hn : n ≠ 0) (v : f.NormalSpace x hn) :
    ((f.orthogonalNormalSpaceEquiv x hn).symm v : TangentSpace J (f x)) =
      f.normalRepresentative x hn v := by
  obtain ⟨v, rfl⟩ := f.normalClass_surjective x hn v
  rw [normalRepresentative_normalClass_eq_starProjection_orthogonalNormalSpace,
    orthogonalNormalSpaceEquiv_symm_normalClass, Submodule.coe_orthogonalProjectionOnto_apply]

/-- The quotient norm (`TauCeti.SmoothEmbedding.normalSpaceNormedAddCommGroup`) of the normal class
of a normal vector is its norm. -/
theorem norm_orthogonalNormalSpaceEquiv (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0)
    (w : orthogonalNormalSpace I J f x) :
    letI := f.normalSpaceNormedAddCommGroup x hn
    ‖f.orthogonalNormalSpaceEquiv x hn w‖ = ‖(w : TangentSpace J (f x))‖ :=
  norm_orthogonalNormalSpaceEquivQuotient (f : M → N) x w

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] {m : ℕ∞ω} [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]
  [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

/-- The map `w ↦ [w]` from the orthogonal normal bundle `ν_f` of a `C^n` embedding to its intrinsic
normal bundle `f*TN / df(TM)` is `C^m`, for `m + 1 ≤ n` and a `C^m` ambient metric. -/
theorem contMDiff_orthogonalNormalSpaceEquiv {r : ℕ} (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, P)) m
      (fun p : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
        (⟨p.proj, f.orthogonalNormalSpaceEquiv p.proj hn p.2⟩ :
          TotalSpace P (fun x ↦ f.NormalSpace x hn))) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := f.normalSpaceFiberBundle hn hdim
  refine ((f.contMDiff_normalQuotientMap hn hm hdim).comp
    (contMDiff_orthogonalNormalSpace_inclusion f.contMDiff
      (f.isImmersion.mfderiv_injective hn) hm hr)).congr fun p ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk p.proj) (f.orthogonalNormalSpaceEquiv_apply p.proj hn p.2)

/-- The map taking a class of the intrinsic normal bundle `f*TN / df(TM)` of a `C^n` embedding to
its orthogonal representative in `ν_f` is `C^m`, for `m + 1 ≤ n` and a `C^m` ambient metric. -/
theorem contMDiff_orthogonalNormalSpaceEquiv_symm {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, Fin r → ℝ)) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨p.proj, (f.orthogonalNormalSpaceEquiv p.proj hn).symm p.2⟩ :
          TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x))) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := f.normalSpaceFiberBundle hn hdim
  refine (f.contMDiff_normalBundle_iff hn hm hdim _).mpr ?_
  refine (contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace f.contMDiff
    (f.isImmersion.mfderiv_injective hn) hm hr).congr fun p ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk p.proj)
    (f.orthogonalNormalSpaceEquiv_symm_normalClass p.proj hn p.2)

/-- **The orthogonal normal bundle is the intrinsic normal bundle.** For a `C^n` embedding `f` with
`m + 1 ≤ n` and a `C^m` ambient metric, the map `w ↦ [w]` from the orthogonal normal bundle `ν_f`
to the intrinsic normal bundle `f*TN / df(TM)` is a `C^m` diffeomorphism of total spaces, over the
identity of `M` and linear on fibres (`TauCeti.SmoothEmbedding.orthogonalNormalSpaceEquiv`). Its
inverse takes orthogonal representatives. The model fibres are `Fin r → ℝ` for `ν_f` and any `P`
of dimension `dim N - dim M` for the intrinsic bundle. -/
def orthogonalNormalBundleDiffeomorph {r : ℕ} (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ≃ₘ^m⟮I.prod 𝓘(ℝ, Fin r → ℝ),
      I.prod 𝓘(ℝ, P)⟯ TotalSpace P (fun x ↦ f.NormalSpace x hn) :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  letI := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  letI := f.normalSpaceFiberBundle hn hdim
  { toFun p := ⟨p.proj, f.orthogonalNormalSpaceEquiv p.proj hn p.2⟩
    invFun p := ⟨p.proj, (f.orthogonalNormalSpaceEquiv p.proj hn).symm p.2⟩
    left_inv p := congrArg (TotalSpace.mk p.proj)
      ((f.orthogonalNormalSpaceEquiv p.proj hn).symm_apply_apply p.2)
    right_inv p := congrArg (TotalSpace.mk p.proj)
      ((f.orthogonalNormalSpaceEquiv p.proj hn).apply_symm_apply p.2)
    contMDiff_toFun := f.contMDiff_orthogonalNormalSpaceEquiv hn hm hr hdim
    contMDiff_invFun := f.contMDiff_orthogonalNormalSpaceEquiv_symm hn hm hr hdim }

/-- The comparison diffeomorphism takes a normal vector to its normal class, over the same base
point. -/
@[simp]
theorem orthogonalNormalBundleDiffeomorph_apply {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (p : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    f.orthogonalNormalBundleDiffeomorph hn hm hr hdim p =
      ⟨p.proj, f.normalClass p.proj hn p.2⟩ :=
  congrArg (TotalSpace.mk p.proj) (f.orthogonalNormalSpaceEquiv_apply p.proj hn p.2)

/-- The inverse comparison diffeomorphism takes a normal class to its orthogonal representative,
over the same base point. -/
theorem orthogonalNormalBundleDiffeomorph_symm_apply {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    (f.orthogonalNormalBundleDiffeomorph hn hm hr hdim).symm p =
      ⟨p.proj, ⟨f.normalRepresentative p.proj hn p.2, by
        rw [← orthogonalNormalSpaceEquiv_symm_apply]; exact Subtype.coe_prop _⟩⟩ :=
  congrArg (TotalSpace.mk p.proj)
    (Subtype.ext (f.orthogonalNormalSpaceEquiv_symm_apply p.proj hn p.2))

end SmoothEmbedding

end TauCeti
