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

namespace SmoothEmbedding

variable {n : ℕ∞ω} [FiniteDimensional ℝ V]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] {m : ℕ∞ω} [IsManifold J 1 N]
  [IsContMDiffRiemannianBundle J m V (fun y : N ↦ TangentSpace J y)]
  [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]

omit [FiniteDimensional ℝ V] [IsManifold J 1 N] in
/-- For an embedding, the quotient comparison takes a normal vector to its normal class. -/
private theorem orthogonalNormalSpaceEquivQuotient_eq_normalClass (f : SmoothEmbedding I J n M N)
    (x : M) (hn : n ≠ 0) (w : orthogonalNormalSpace I J f x) :
    (orthogonalNormalSpaceEquivQuotient (f : M → N) x w : f.NormalSpace x hn) =
      f.normalClass x hn w := by
  rw [normalClass_def]
  exact orthogonalNormalSpaceEquivQuotient_apply (I := I) (f : M → N) x w

omit [FiniteDimensional ℝ V] [IsManifold J 1 N] in
/-- For an embedding, the inverse quotient comparison takes the normal class of an ambient vector to
its orthogonal projection onto the normal space. -/
private theorem orthogonalNormalSpaceEquivQuotient_symm_normalClass
    (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) (v : TangentSpace J (f x)) :
    (orthogonalNormalSpaceEquivQuotient (f : M → N) x).symm (f.normalClass x hn v) =
      (orthogonalNormalSpace I J f x).orthogonalProjectionOnto v := by
  rw [normalClass_def]
  exact orthogonalNormalSpaceEquivQuotient_symm_mk (I := I) (f : M → N) x v

omit [IsManifold J 1 N] in
/-- For an embedding, the inverse quotient comparison takes a normal class to its normal
representative. -/
private theorem coe_orthogonalNormalSpaceEquivQuotient_symm (f : SmoothEmbedding I J n M N)
    (x : M) (hn : n ≠ 0) (v : f.NormalSpace x hn) :
    ((orthogonalNormalSpaceEquivQuotient (f : M → N) x).symm v : TangentSpace J (f x)) =
      f.normalRepresentative x hn v := by
  obtain ⟨v, rfl⟩ := f.normalClass_surjective x hn v
  rw [normalRepresentative_normalClass_eq_starProjection_orthogonalNormalSpace,
    orthogonalNormalSpaceEquivQuotient_symm_normalClass,
    Submodule.coe_orthogonalProjectionOnto_apply]

/-- The map `w ↦ [w]` from the orthogonal normal bundle `ν_f` of a `C^n` embedding to its intrinsic
normal bundle `f*TN / df(TM)` is `C^m`, for `m + 1 ≤ n` and a `C^m` ambient metric. -/
theorem contMDiff_orthogonalNormalSpaceEquivQuotient {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0)
    (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, Fin r → ℝ)) (I.prod 𝓘(ℝ, P)) m
      (fun p : TotalSpace (Fin r → ℝ) (fun x ↦ orthogonalNormalSpace I J f x) ↦
        (⟨p.proj, orthogonalNormalSpaceEquivQuotient (f : M → N) p.proj p.snd⟩ :
          TotalSpace P (fun x ↦ f.NormalSpace x hn))) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  let := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
  let := f.normalSpaceFiberBundle hn hdim
  refine ((f.contMDiff_normalQuotientMap hn hm hdim).comp
    (contMDiff_orthogonalNormalSpace_inclusion f.contMDiff
      (f.isImmersion.mfderiv_injective hn) hm hr)).congr fun p ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk p.proj)
    (orthogonalNormalSpaceEquivQuotient_eq_normalClass f p.proj hn p.snd)

/-- The map taking a class of the intrinsic normal bundle `f*TN / df(TM)` of a `C^n` embedding to
its orthogonal representative in `ν_f` is `C^m`, for `m + 1 ≤ n` and a `C^m` ambient metric. -/
theorem contMDiff_orthogonalNormalSpaceEquivQuotient_symm {r : ℕ} (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) (hm : m + 1 ≤ n) (hr : finrank ℝ V = finrank ℝ E + r)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    letI := orthogonalNormalFiberBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := orthogonalNormalVectorBundle f.contMDiff (f.isImmersion.mfderiv_injective hn) hm hr
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, Fin r → ℝ)) m
      (fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨p.proj, (orthogonalNormalSpaceEquivQuotient (f : M → N) p.proj).symm p.snd⟩ :
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
    (orthogonalNormalSpaceEquivQuotient_symm_normalClass f p.proj hn p.snd)

/-- **The orthogonal normal bundle is the intrinsic normal bundle.** For a `C^n` embedding `f` with
`m + 1 ≤ n` and a `C^m` ambient metric, the map `w ↦ [w]` from the orthogonal normal bundle `ν_f`
to the intrinsic normal bundle `f*TN / df(TM)` is a `C^m` diffeomorphism of total spaces, over the
identity of `M` and linear on fibres (`TauCeti.orthogonalNormalSpaceEquivQuotient`). Its
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
  { toFun p := ⟨p.proj, orthogonalNormalSpaceEquivQuotient (f : M → N) p.proj p.snd⟩
    invFun p := ⟨p.proj, (orthogonalNormalSpaceEquivQuotient (f : M → N) p.proj).symm p.snd⟩
    left_inv p := congrArg (TotalSpace.mk p.proj)
      ((orthogonalNormalSpaceEquivQuotient (f : M → N) p.proj).symm_apply_apply p.snd)
    right_inv p := congrArg (TotalSpace.mk p.proj)
      ((orthogonalNormalSpaceEquivQuotient (f : M → N) p.proj).apply_symm_apply p.snd)
    contMDiff_toFun := f.contMDiff_orthogonalNormalSpaceEquivQuotient hn hm hr hdim
    contMDiff_invFun := f.contMDiff_orthogonalNormalSpaceEquivQuotient_symm hn hm hr hdim }

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
      ⟨p.proj, f.normalClass p.proj hn p.snd⟩ :=
  congrArg (TotalSpace.mk p.proj)
    (orthogonalNormalSpaceEquivQuotient_eq_normalClass f p.proj hn p.snd)

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
      ⟨p.proj, ⟨f.normalRepresentative p.proj hn p.snd, by
        rw [← coe_orthogonalNormalSpaceEquivQuotient_symm]; exact Subtype.coe_prop _⟩⟩ :=
  congrArg (TotalSpace.mk p.proj)
    (Subtype.ext (coe_orthogonalNormalSpaceEquivQuotient_symm f p.proj hn p.snd))

end SmoothEmbedding

end TauCeti
