/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Riemannian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Equiv

/-!
# The orthogonal normal bundle as a quotient bundle

Let `f : M → N` be an immersion into a manifold whose tangent spaces carry a Riemannian metric.
At `x : M` the orthogonal normal space `ν_f,x = (range df_x)ᗮ` (`TauCeti.orthogonalNormalSpace`)
maps isomorphically and isometrically onto the quotient `T_{f x} N ⧸ range df_x` by `w ↦ [w]`
(`TauCeti.orthogonalNormalSpaceEquivQuotient`, the inverse of Mathlib's
`Submodule.quotientEquivOrthogonal`); for an embedding this quotient is its intrinsic normal space.
The inverse sends `[v]` to the orthogonal projection of `v` onto `ν_f,x`, which is the normal
representative of `[v]`. The fibres are indexed by the source point, so two sheets of an
immersion through one image point keep separate fibres.

For a `C^n` embedding with `m + 1 ≤ n` and a `C^m` metric, these fibre isomorphisms assemble into
a `C^m` diffeomorphism over the identity of `M` from the orthogonal normal bundle `ν_f`
(`TauCeti.orthogonalNormalFiberBundle`) to the intrinsic normal bundle `f*TN / df(TM)` of the
embedding (`TauCeti.SmoothEmbedding.normalSpaceFiberBundle`), fibrewise linear
(`TauCeti.SmoothEmbedding.orthogonalNormalBundleDiffeomorph`). It is the inverse of the
identification of the intrinsic normal bundle by the orthogonal projections onto `ν_f`
(`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfKer`): these projections kill exactly the
tangent ranges and are smooth on `f*TN`
(`TauCeti.contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace`).

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

namespace SmoothEmbedding

variable {n : ℕ∞ω} [FiniteDimensional ℝ V]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] {m : ℕ∞ω} [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]
  [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

omit [IsManifold J 1 N] in
/-- The orthogonal projection onto the orthogonal normal space `ν_f,x` of an embedding kills
exactly the tangent range. -/
private theorem orthogonalProjectionOnto_orthogonalNormalSpace_eq_zero_iff
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) (v : TangentSpace J (f x)) :
    (orthogonalNormalSpace I J f x).orthogonalProjectionOnto v = 0 ↔
      v ∈ f.tangentRange x hn := by
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff,
    ← orthogonal_tangentRange_eq_orthogonalNormalSpace f x hn, Submodule.orthogonal_orthogonal]

/-- **The orthogonal normal bundle is the intrinsic normal bundle.** For a `C^n` embedding `f` with
`m + 1 ≤ n` and a `C^m` ambient metric, the map `w ↦ [w]` from the orthogonal normal bundle `ν_f`
to the intrinsic normal bundle `f*TN / df(TM)` is a `C^m` diffeomorphism of total spaces, over the
identity of `M` and linear on fibres. Its inverse takes orthogonal representatives. The model
fibres are `Fin r → ℝ` for `ν_f` and any `P` of dimension `r = dim N - dim M` for the intrinsic
bundle. It is the inverse of the identification
`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfKer` given by the orthogonal projections onto
`ν_f`, whose kernels are the tangent ranges. -/
def orthogonalNormalBundleDiffeomorph {r : ℕ} (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hP : finrank ℝ P = r) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle (P := P) hn (by omega)
    TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ≃ₘ^m⟮I.prod 𝓘(ℝ, Fin r → ℝ),
      I.prod 𝓘(ℝ, P)⟯ TotalSpace P (fun x ↦ f.NormalSpace x hn) :=
  haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  letI := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  letI := f.normalSpaceFiberBundle (P := P) hn (by omega)
  (f.normalBundleDiffeomorphOfKer (P := P) hn hm (by omega)
    (fun x ↦ (orthogonalNormalSpace I J f x).orthogonalProjectionOnto)
    (orthogonalProjectionOnto_orthogonalNormalSpace_eq_zero_iff f · hn)
    (fun x ↦ by
      rw [(f.normalSpaceOrthogonalComplementEquiv x hn).toLinearEquiv.finrank_eq,
        orthogonal_tangentRange_eq_orthogonalNormalSpace])
    (contMDiff_orthogonalProjectionOnto_orthogonalNormalSpace f.contMDiff
      (f.isImmersion.mfderiv_injective hn) hm hr)).symm

/-- The comparison diffeomorphism takes a normal vector to its normal class, over the same base
point. -/
@[simp]
theorem orthogonalNormalBundleDiffeomorph_apply {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hP : finrank ℝ P = r)
    (p : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle (P := P) hn (by omega)
    f.orthogonalNormalBundleDiffeomorph hn hm hr hP p =
      ⟨p.proj, f.normalClass p.proj hn p.snd⟩ := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  rw [orthogonalNormalBundleDiffeomorph, normalBundleDiffeomorphOfKer_symm_apply]
  refine congrArg (TotalSpace.mk p.proj) ?_
  conv_lhs => rw [← Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p.snd]
  exact normalSpaceEquivOfKer_symm_apply ..

/-- The inverse comparison diffeomorphism takes a normal class to its orthogonal representative,
over the same base point. -/
@[simp]
theorem orthogonalNormalBundleDiffeomorph_symm_apply {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hP : finrank ℝ P = r)
    (p : TotalSpace P (fun x ↦ f.NormalSpace x hn)) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle (P := P) hn (by omega)
    (f.orthogonalNormalBundleDiffeomorph hn hm hr hP).symm p =
      ⟨p.proj, ⟨f.normalRepresentative p.proj hn p.snd, by
        rw [← orthogonal_tangentRange_eq_orthogonalNormalSpace f p.proj hn]
        exact f.normalRepresentative_mem_orthogonal p.proj hn p.snd⟩⟩ := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  obtain ⟨x, w⟩ := p
  obtain ⟨v, rfl⟩ := f.normalClass_surjective x hn w
  rw [orthogonalNormalBundleDiffeomorph]
  -- The double inverse of a diffeomorphism is the diffeomorphism itself, by structure eta.
  refine (normalBundleDiffeomorphOfKer_apply ..).trans (congrArg (TotalSpace.mk x) (Subtype.ext ?_))
  rw [normalSpaceEquivOfKer_normalClass, Submodule.coe_orthogonalProjectionOnto_apply]
  exact (normalRepresentative_normalClass_eq_starProjection_orthogonalNormalSpace f x hn v).symm

end SmoothEmbedding

end TauCeti
