/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.PrescribedDerivative
public import TauCeti.Geometry.Symplectic.Lagrangian.Presymplectic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Symplectic.Normal
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence
import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Representative
import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDifferential
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# The coisotropic embedding theorem

Let `θ` and `σ` be symplectic forms on manifolds `M` and `N`, and let `i : Q → M` and
`j : Q → N` be embeddings of a compact manifold `Q` with coisotropic tangent images, inducing the
same presymplectic form `i^* θ = j^* σ` on `Q`. The **coisotropic embedding theorem**
(`TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_isCoisotropicMap`) says that the germs of
`θ` along `i(Q)` and of `σ` along `j(Q)` are symplectomorphic: there are open neighbourhoods `U₀`
of `i(Q)` and `U₁` of `j(Q)` and a diffeomorphism `φ : U₀ → U₁` pulling `σ` back to `θ`, with
`φ (i q) = j q` for every `q`. So a neighbourhood of a compact coisotropic submanifold is
determined, up to symplectomorphism, by the presymplectic form it inherits. For a Lagrangian
submanifold this form is zero, and the theorem compares any two Lagrangian embeddings of `Q`.

Unlike the symplectic and Lagrangian neighbourhood theorems, no bundle isomorphism along `Q`
carrying `θ` to `σ` has to be constructed. It suffices to extend the differential of `j ∘ i⁻¹` to
linear maps `A q : T_(i q) M → T_(j q) N` with

`A q ∘ di_q = dj_q` and `σ(A q v, dj_q w) = θ(v, di_q w)` for all `v` and `w`,

which need not be symplectic. Fix auxiliary Riemannian metrics `g_M` and `g_N`, and write `P v`
for the tangent vector of `Q` whose image under `di_q` is the `g_M`-orthogonal projection of `v`
onto the tangent image. Then

`A q v = dj_q (P v) + (σ♭)⁻¹ (g_N(dj_q x, ·))`,

where `x ∈ T_q Q` is the vector with `g_N(dj_q x, dj_q ·) = θ(v - di_q (P v), di_q ·)`. Each step
inverts a smooth family of invertible bilinear forms, so `A` is smooth, and its two defining
identities follow from `i^* θ = j^* σ`. It is injective because a vector `v` with
`θ(v, di_q ·) = 0` lies in the coisotropic tangent image, and it is invertible because both
embeddings have the same codimension, the kernel rank of the common presymplectic form.

The two identities say that `A q^* σ` and `θ` agree on every pair of vectors one of which is
tangent to `i(Q)`. On the remaining pairs they may differ, but every form
`θ + s (A q^* σ - θ)`, `s ∈ [0, 1]`, is still nondegenerate: a vector annihilating it pairs to
zero with the coisotropic tangent image, so lies in it, and is then annihilated by `θ`. A partial
diffeomorphism `Ψ` with `Ψ ∘ i = j` and differential `A` along `i(Q)`
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`) therefore pulls `σ` back to a
form with the same pullback to `Q` as `θ`, joined to `θ` by a path nondegenerate along `i(Q)`. The
relative Moser theorem for such forms
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_eq_of_eval₂_mfderiv_eq`) corrects `Ψ` to the
required symplectomorphism. Neither closedness of the forms nor compactness of `Q` is used before
this last step.

## Main results

* `TauCeti.SmoothEmbedding.exists_diffeomorph_opens_of_isCoisotropicMap`: two compact coisotropic
  embeddings inducing the same presymplectic form have symplectomorphic neighbourhoods.

## References

* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114 (the local uniqueness theorem).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 8.6.
* A. Weinstein, *Lectures on Symplectic Manifolds*, CBMS Regional Conference Series in
  Mathematics 29, American Mathematical Society, 1977, Lecture 5.
-/

public section

noncomputable section

open Bundle Manifold Function Set TopologicalSpace Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

open SmoothTwoForm

variable {E V F H G G' Q M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G} {K : ModelWithCorners ℝ F G'}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
  [TopologicalSpace N] [ChartedSpace G' N] [IsManifold K ∞ N]

/-! ### The ambient extension of `dj ∘ di⁻¹` -/

section Extension

/-- The Riemannian metric induced on `Q` by a metric on `M` along an embedding `i`. -/
private abbrev inducedMetric (g : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
    (i : SmoothEmbedding I J ∞ Q M) :
    ContMDiffRiemannianMetric I ∞ E (fun q : Q ↦ TangentSpace I q) :=
  g.pullback i (i.contMDiff.of_le (by simp)) fun q ↦ i.isImmersion.mfderiv_injective (by simp) q

omit [FiniteDimensional ℝ V] in
private theorem inducedMetric_inner_apply
    (g : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
    (i : SmoothEmbedding I J ∞ Q M) (q : Q) (u w : TangentSpace I q) :
    (inducedMetric g i).inner q u w = g.inner (i q) (mfderiv I J i q u) (mfderiv I J i q w) :=
  ContMDiffRiemannianMetric.pullback_inner _ _ _ _ q u w

omit [FiniteDimensional ℝ V] in
private theorem isInvertible_inducedMetric_inner
    (g : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
    (i : SmoothEmbedding I J ∞ Q M) (q : Q) : ((inducedMetric g i).inner q).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_pos ((inducedMetric g i).pos q)

/-- The tangential part `P v` of an ambient tangent vector `v` along `i`: the tangent vector of
`Q` whose image under `di_q` is the `g`-orthogonal projection of `v` onto the tangent image. -/
private def tangentialPart (g : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
    (i : SmoothEmbedding I J ∞ Q M) (q : Q) : TangentSpace J (i q) →L[ℝ] TangentSpace I q :=
  ((inducedMetric g i).inner q).inverse.comp
    (((ContinuousLinearMap.compL ℝ E V ℝ).flip (mfderiv I J i q)).comp (g.inner (i q)))

omit [FiniteDimensional ℝ V] in
private theorem tangentialPart_apply
    (g : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
    (i : SmoothEmbedding I J ∞ Q M) (q : Q) (v : TangentSpace J (i q)) :
    tangentialPart g i q v =
      ((inducedMetric g i).inner q).inverse ((g.inner (i q) v).comp (mfderiv I J i q)) :=
  -- `comp_apply`, `flip_apply` and `compL_apply` hold by `rfl` but cannot be applied here: the
  -- tangent-space instances do not unify with the model-space instances they expect.
  rfl

omit [FiniteDimensional ℝ V] in
private theorem tangentialPart_mfderiv
    (g : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
    (i : SmoothEmbedding I J ∞ Q M) (q : Q) (u : TangentSpace I q) :
    tangentialPart g i q (mfderiv I J i q u) = u := by
  rw [tangentialPart_apply]
  -- The `g`-pairings of `di_q u` with the tangent image are the induced pairings of `u`.
  have h : (g.inner (i q) (mfderiv I J i q u)).comp (mfderiv I J i q) =
      (inducedMetric g i).inner q u :=
    ContinuousLinearMap.ext fun w ↦ (inducedMetric_inner_apply g i q u w).symm
  rw [h, (isInvertible_inducedMetric_inner g i q).inverse_apply_self]

variable (θ : SmoothTwoForm J M) (σ : SmoothTwoForm K N)
  (gM : ContMDiffRiemannianMetric J ∞ V (fun x : M ↦ TangentSpace J x))
  (gN : ContMDiffRiemannianMetric K ∞ F (fun y : N ↦ TangentSpace K y))
  (i : SmoothEmbedding I J ∞ Q M) (j : SmoothEmbedding I K ∞ Q N)

/-- The ambient extension `A q : T_(i q) M → T_(j q) N` of `dj_q ∘ di_q⁻¹`, given by
`A q v = dj_q (P v) + (σ♭)⁻¹ (g_N(dj_q x, ·))`, where `P v` is the tangential part of `v` and
`x` is the tangent vector of `Q` with `g_N(dj_q x, dj_q ·) = θ(v - di_q (P v), di_q ·)`. -/
private def coisotropicExtension (q : Q) : TangentSpace J (i q) →L[ℝ] TangentSpace K (j q) :=
  (mfderiv I K j q).comp (tangentialPart gM i q) +
    (σ.flat (j q)).inverse.comp ((gN.inner (j q)).comp ((mfderiv I K j q).comp
      (((inducedMetric gN j).inner q).inverse.comp ((i.tangentPairing θ q).comp
        (ContinuousLinearMap.id ℝ (TangentSpace J (i q)) -
          (mfderiv I J i q).comp (tangentialPart gM i q))))))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
private theorem coisotropicExtension_apply (q : Q) (v : TangentSpace J (i q)) :
    coisotropicExtension θ σ gM gN i j q v =
      mfderiv I K j q (tangentialPart gM i q v) + (σ.flat (j q)).inverse (gN.inner (j q)
        (mfderiv I K j q (((inducedMetric gN j).inner q).inverse
          ((θ.flat (i q) (v - mfderiv I J i q (tangentialPart gM i q v))).comp
            (mfderiv I J i q))))) := by
  rw [coisotropicExtension, add_apply, ← tangentPairing_apply]
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] in
/-- The ambient extension extends `dj_q ∘ di_q⁻¹`. -/
private theorem coisotropicExtension_mfderiv (q : Q) (u : TangentSpace I q) :
    coisotropicExtension θ σ gM gN i j q (mfderiv I J i q u) = mfderiv I K j q u := by
  simp only [coisotropicExtension_apply, tangentialPart_mfderiv, sub_self, map_zero,
    ContinuousLinearMap.zero_comp, add_zero]

omit [FiniteDimensional ℝ V] in
/-- The ambient extension carries the pairings of `θ` with the tangent image of `i` to those of
`σ` with the tangent image of `j`. -/
private theorem eval₂_coisotropicExtension_mfderiv {σ : SmoothTwoForm K N}
    (hσ : σ.IsNondegenerate) (q : Q)
    (hpull : ∀ u w : TangentSpace I q,
      SmoothBundleForm.eval₂ σ (j q) (mfderiv I K j q u) (mfderiv I K j q w) =
        SmoothBundleForm.eval₂ θ (i q) (mfderiv I J i q u) (mfderiv I J i q w))
    (v : TangentSpace J (i q)) (w : TangentSpace I q) :
    SmoothBundleForm.eval₂ σ (j q) (coisotropicExtension θ σ gM gN i j q v) (mfderiv I K j q w) =
      SmoothBundleForm.eval₂ θ (i q) v (mfderiv I J i q w) := by
  rw [coisotropicExtension_apply, SmoothBundleForm.eval₂_add_left, hpull, ← flat_apply σ,
    (hσ.isInvertible_flat (j q)).self_apply_inverse]
  -- `g_N(dj_q x, dj_q w)` is the induced metric on `x` and `w`.
  rw [← inducedMetric_inner_apply gN j,
    (isInvertible_inducedMetric_inner gN j q).self_apply_inverse, ContinuousLinearMap.comp_apply,
    flat_apply, SmoothBundleForm.eval₂_sub_left, add_sub_cancel]

variable {θ σ} {hθ : θ.IsNondegenerate}

omit [FiniteDimensional ℝ V] in
/-- **The ambient extension is invertible** when `i` is coisotropic and the ambient manifolds
have the same dimension. -/
private theorem isInvertible_coisotropicExtension (hσ : σ.IsNondegenerate)
    (hi : hθ.IsCoisotropicMap I i) (q : Q)
    (hpull : ∀ u w : TangentSpace I q,
      SmoothBundleForm.eval₂ σ (j q) (mfderiv I K j q u) (mfderiv I K j q w) =
        SmoothBundleForm.eval₂ θ (i q) (mfderiv I J i q u) (mfderiv I J i q w))
    (hdim : finrank ℝ V = finrank ℝ F) :
    (coisotropicExtension θ σ gM gN i j q).IsInvertible := by
  set A := coisotropicExtension θ σ gM gN i j q
  -- If `A v = 0`, then `θ(v, di_q ·) = σ(A v, dj_q ·) = 0`, so `v = di_q u` and `dj_q u = 0`.
  have hinj : Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv ↦ ?_
    obtain ⟨u, rfl⟩ := hi.exists_mfderiv_eq_of_forall_eval₂_mfderiv_eq_zero q (v := v) fun u ↦ by
      rw [← eval₂_coisotropicExtension_mfderiv θ gM gN i j hσ q hpull, hv,
        SmoothBundleForm.eval₂_zero_left]
    have h0 : mfderiv I K j q u = 0 := by
      rw [← coisotropicExtension_mfderiv θ σ gM gN i j]
      exact hv
    rw [(injective_iff_map_eq_zero _).1 (j.isImmersion.mfderiv_injective (by simp) q) u h0,
      map_zero]
  exact (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim).2 hinj

omit [FiniteDimensional ℝ V] in
/-- **The path from `θ` to `A^* σ` is nondegenerate along `i(Q)`.** For every `s`, a vector `v`
annihilated by `θ + s (A^* σ - θ)` vanishes: it pairs with the tangent image of `i` as under `θ`,
so it lies in the coisotropic tangent image, where the form is `θ` again. -/
private theorem eq_zero_of_forall_eval₂_add_mul_sub (hσ : σ.IsNondegenerate)
    (hi : hθ.IsCoisotropicMap I i) (q : Q)
    (hpull : ∀ u w : TangentSpace I q,
      SmoothBundleForm.eval₂ σ (j q) (mfderiv I K j q u) (mfderiv I K j q w) =
        SmoothBundleForm.eval₂ θ (i q) (mfderiv I J i q u) (mfderiv I J i q w))
    (s : ℝ) (v : TangentSpace J (i q))
    (hv : ∀ w, SmoothBundleForm.eval₂ θ (i q) v w + s *
      (SmoothBundleForm.eval₂ σ (j q) (coisotropicExtension θ σ gM gN i j q v)
        (coisotropicExtension θ σ gM gN i j q w) - SmoothBundleForm.eval₂ θ (i q) v w) = 0) :
    v = 0 := by
  have hA := eval₂_coisotropicExtension_mfderiv θ gM gN i j hσ q hpull
  have hAi := coisotropicExtension_mfderiv θ σ gM gN i j q
  -- Against the tangent image, the path is `θ`, so `v` lies in the tangent image.
  obtain ⟨u, rfl⟩ := hi.exists_mfderiv_eq_of_forall_eval₂_mfderiv_eq_zero q (v := v) fun u ↦ by
    simpa only [hAi, hA, sub_self, mul_zero, add_zero] using hv (mfderiv I J i q u)
  -- There, by antisymmetry, the path is `θ` again, which is nondegenerate.
  rw [isNondegenerate_iff_separatingLeft.1 hθ (i q) (mfderiv I J i q u) fun w ↦ by
    simpa only [hAi, SmoothBundleForm.eval₂_swap σ (j q) (mfderiv I K j q u), hA,
      ← SmoothBundleForm.eval₂_swap θ (i q), sub_self, mul_zero, add_zero] using hv w]

omit [FiniteDimensional ℝ V] in
/-- **Smoothness of the ambient extension** on the pulled-back ambient tangent bundle. -/
private theorem contMDiff_coisotropicExtension (hσ : σ.IsNondegenerate) :
    ContMDiff (I.prod 𝓘(ℝ, V)) (K.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨j p.proj, coisotropicExtension θ σ gM gN i j p.proj p.snd⟩ : TangentBundle K N)) := by
  have hbase : ContMDiff (I.prod 𝓘(ℝ, V)) I ∞ (π V ((i : Q → M) *ᵖ (TangentSpace J))) :=
    contMDiff_proj _
  have hjb : ContMDiff (I.prod 𝓘(ℝ, V)) K ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦ j p.proj) :=
    j.contMDiff.comp hbase
  -- The tangential part `P v`, in `T Q`.
  have hP : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, tangentialPart gM i p.proj p.snd⟩ : TangentBundle I Q)) :=
    i.contMDiff_inverse_comp_mfderiv (m := ∞) (by simp) (inducedMetric gM i).contMDiff
      (isInvertible_inducedMetric_inner gM i) gM.contMDiff
  -- The normal part `v - di_q (P v)`, as a vector of the pulled-back bundle.
  let c (q : Q) (v : TangentSpace J (i q)) : TangentSpace J (i q) :=
    v - mfderiv I J i q (tangentialPart gM i q v)
  have hc : ContMDiff (I.prod 𝓘(ℝ, V)) (I.prod 𝓘(ℝ, V)) ∞
      (fun p : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)) ↦
        (⟨p.proj, c p.proj p.snd⟩ : TotalSpace V ((i : Q → M) *ᵖ (TangentSpace J)))) :=
    (Bundle.Pullback.contMDiff_iff i i.contMDiff).2 ⟨hbase,
      i.contMDiff_of_eq_sub_mfderiv_inverse (m := ∞) (by simp) (inducedMetric gM i).contMDiff
        (isInvertible_inducedMetric_inner gM i) gM.contMDiff _ fun _ _ ↦ rfl⟩
  -- The vector `x` of `Q` with `g_N(dj_q x, dj_q ·) = θ(v - di_q (P v), di_q ·)`.
  have hx := (i.contMDiff_inverse_comp_mfderiv (m := ∞) (by simp) (inducedMetric gN j).contMDiff
    (isInvertible_inducedMetric_inner gN j) (contMDiff_flat θ)).comp hc
  -- Push `x` forward by `dj`, take its `g_N`-dual and invert `σ♭`.
  have hη := (gN.contMDiff.comp hjb).clm_bundle_apply (F₂ := F →L[ℝ] ℝ)
    (E₂ := fun y : N ↦ TangentSpace K y →L[ℝ] ℝ)
    ((j.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hx)
  have hR :=
    (((contMDiff_flat σ).clm_bundle_inverse hσ.isInvertible_flat).comp hjb).clm_bundle_apply hη
  exact (((j.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hP).add_sectionAlong
    hR).congr fun p ↦ congrArg (TotalSpace.mk (j p.proj))
      (coisotropicExtension_apply θ σ gM gN i j p.proj p.snd)

end Extension

/-! ### The coisotropic embedding theorem -/

omit [FiniteDimensional ℝ E] in
/-- Two coisotropic embeddings of a nonempty manifold `Q` inducing the same form on `Q` have
ambient manifolds of the same dimension: both codimensions are the kernel rank of that form. -/
private theorem finrank_eq_of_isCoisotropicMap [Nonempty Q] {θ : SmoothTwoForm J M}
    {hθ : θ.IsNondegenerate} {σ : SmoothTwoForm K N} {hσ : σ.IsNondegenerate}
    (i : SmoothEmbedding I J ∞ Q M) (hi : hθ.IsCoisotropicMap I i)
    (j : SmoothEmbedding I K ∞ Q N) (hj : hσ.IsCoisotropicMap I j)
    (h : SmoothForm.mpullback j j.contMDiff σ = SmoothForm.mpullback i i.contMDiff θ) :
    finrank ℝ V = finrank ℝ F := by
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  have hM := hi.finrank_ker_bilinFormAt_mpullback_add i.contMDiff
    (i.isImmersion.mfderiv_injective (by simp) q₀)
  have hN := hj.finrank_ker_bilinFormAt_mpullback_add j.contMDiff
    (j.isImmersion.mfderiv_injective (by simp) q₀)
  rw [h] at hN
  omega

/-- **The coisotropic embedding theorem.** Let `θ` and `σ` be symplectic forms on boundaryless,
Hausdorff, second-countable manifolds `M` and `N`, and let `i : Q → M` and `j : Q → N` be
embeddings of a compact boundaryless manifold `Q` with coisotropic tangent images, inducing the
same form on `Q`: `j^* σ = i^* θ`. Then there are open neighbourhoods `U₀` of `i(Q)` and `U₁` of
`j(Q)` and a diffeomorphism `φ : U₀ → U₁` pulling `σ` back to `θ`, with `φ (i q) = j q` for every
`q`. -/
theorem exists_diffeomorph_opens_of_isCoisotropicMap [I.Boundaryless] [J.Boundaryless]
    [K.Boundaryless] [CompactSpace Q] [T2Space M] [SecondCountableTopology M] [T2Space N]
    [SecondCountableTopology N] {θ : SmoothTwoForm J M} {hθ : θ.IsNondegenerate}
    {σ : SmoothTwoForm K N} {hσ : σ.IsNondegenerate} (hθc : θ.IsClosed) (hσc : σ.IsClosed)
    (i : SmoothEmbedding I J ∞ Q M) (hi : hθ.IsCoisotropicMap I i)
    (j : SmoothEmbedding I K ∞ Q N) (hj : hσ.IsCoisotropicMap I j)
    (h : SmoothForm.mpullback j j.contMDiff σ = SmoothForm.mpullback i i.contMDiff θ) :
    ∃ (U₀ : Opens M) (U₁ : Opens N) (φ : U₀ ≃ₘ⟮J, K⟯ U₁),
      (∀ q, ∃ h : i q ∈ U₀, (φ ⟨i q, h⟩ : N) = j q) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal θ := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · -- For empty `Q` every condition along `Q` is vacuous, and the neighbourhood theorem with a
    -- prescribed derivative applies to the empty family of linear maps.
    obtain ⟨U₀, U₁, φ, -, hφ⟩ := SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq i j.contMDiff
      j.isEmbedding.isInducing hθc (fun q ↦ isEmptyElim q) hσc (A := fun q ↦ isEmptyElim q)
      (fun q ↦ isEmptyElim q) (fun q ↦ isEmptyElim q) (fun q ↦ isEmptyElim q)
      fun q ↦ isEmptyElim q
    exact ⟨U₀, U₁, φ, fun q ↦ isEmptyElim q, hφ⟩
  -- Auxiliary smooth Riemannian metrics on `M` and `N`.
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace G' := K.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace G M
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G' N
  obtain ⟨gM⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := V)
    (E := fun x : M ↦ TangentSpace J x)
  obtain ⟨gN⟩ := nonempty_contMDiffRiemannianMetric (IB := K) (n := ⊤) (F := F)
    (E := fun y : N ↦ TangentSpace K y)
  set A := coisotropicExtension θ σ gM gN i j
  have hpull (q : Q) (u w : TangentSpace I q) :
      SmoothBundleForm.eval₂ σ (j q) (mfderiv I K j q u) (mfderiv I K j q w) =
        SmoothBundleForm.eval₂ θ (i q) (mfderiv I J i q u) (mfderiv I J i q w) := by
    simpa only [SmoothForm.eval₂_mpullback] using
      congrArg (fun φ ↦ SmoothBundleForm.eval₂ φ q u w) h
  -- `A` is smooth in tangent coordinates, invertible and extends `dj ∘ di⁻¹`.
  have hA (q : Q) : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] F) ∞ (inTangentCoordinates J K i j A q) q :=
    Bundle.Pullback.contMDiffAt_inCoordinates_of_contMDiffAt i
      (⟨j, j.contMDiff.continuous⟩ : C(Q, N)) (j.contMDiff q) A
      fun _ ↦ contMDiff_coisotropicExtension gM gN i j hσ _
  have hdim := finrank_eq_of_isCoisotropicMap i hi j hj h
  have hAi (q : Q) : (A q).comp (mfderiv I J i q) = mfderiv I K j q :=
    ContinuousLinearMap.ext (coisotropicExtension_mfderiv θ σ gM gN i j q)
  -- Realize `A` as the differential of a partial diffeomorphism, then correct it by Moser.
  obtain ⟨Ψ, hsrc, -, -, hval, hd⟩ := i.exists_partialDiffeomorph_mfderiv_eq j.contMDiff
    j.isEmbedding.isInducing hA
    (fun q ↦ isInvertible_coisotropicExtension gM gN i j hσ hi q (hpull q) hdim) hAi
    isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
  obtain ⟨U₀, U₁, φ, hφ, hφσ⟩ := SmoothTwoForm.exists_diffeomorph_opens_eq_of_eval₂_mfderiv_eq
    i hθc hσc Ψ (fun q ↦ hsrc (mem_range_self q))
    (fun q u w ↦ by
      rw [hd q, hval q, coisotropicExtension_mfderiv, coisotropicExtension_mfderiv]
      exact hpull q u w)
    fun q s _ v hv ↦ eq_zero_of_forall_eval₂_add_mul_sub gM gN i j hσ hi q (hpull q) s v
      fun w ↦ by
        rw [← hv w, hd q, hval q]
  exact ⟨U₀, U₁, φ, fun q ↦ (hφ q).imp fun _ h ↦ h.1.trans (hval q), hφσ⟩

end TauCeti.SmoothEmbedding
