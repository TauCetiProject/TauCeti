/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Symplectomorphisms of neighbourhoods with prescribed derivative

Let `θ` and `σ` be closed two-forms on boundaryless manifolds `M` and `N`, let `f : Q → M` be a
compact embedded submanifold along which `θ` is nondegenerate, and let `Ψ` be a partial
diffeomorphism from `M` to `N`, defined near `f(Q)`, whose differential at every point of `f(Q)`
is a linear symplectic map: `σ(dΨ v, dΨ w) = θ(v, w)` for all tangent vectors `v`, `w` of `M` at
that point. Then `Ψ` can be corrected to a symplectomorphism of neighbourhoods without changing
it to first order along `f(Q)`: there are open neighbourhoods `U₀` of `f(Q)` and `U₁` of `Ψ(f(Q))`
and a diffeomorphism `φ : U₀ → U₁` pulling `σ` back to `θ` which agrees with `Ψ` at every point of
`f(Q)` and has the same differential there
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq`).

The hypothesis says that `Ψ^* σ` and `θ` agree as bilinear forms on the full ambient tangent spaces
along `f(Q)`. The relative Moser theorem in this form
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`) gives a
diffeomorphism `Θ` of the source of `Ψ` which fixes `f(Q)`, has the identity as differential along
it, and pulls `Ψ^* σ` back to `θ` near `f(Q)`. The correction is `φ = Ψ ∘ Θ`, and the chain rule
gives `dφ = dΨ ∘ dΘ = dΨ` along `f(Q)`.

This is the last step in the construction of a symplectomorphism of neighbourhoods of two compact
submanifolds with a prescribed symplectic bundle isomorphism `A` between the ambient tangent
bundles along them: once `A` is realized as the differential along the submanifold of some
diffeomorphism of neighbourhoods, this theorem makes that diffeomorphism symplectic without
changing its differential.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq`: a partial
  diffeomorphism which is symplectic to first order along a compact embedded submanifold is, to
  first order along it, a symplectomorphism of neighbourhoods.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 7.4 (the relative Moser theorem).
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothTwoForm

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {K : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

/-- The correction of a partial diffeomorphism `Ψ` by a diffeomorphism `Θ` of its source,
restricted to an open subset `U₀` of the source, is a diffeomorphism onto an open subset of `N`. -/
private theorem exists_diffeomorph_opens_comp_eq (Ψ : PartialDiffeomorph I K M N ∞)
    (Θ : (⟨Ψ.source, Ψ.open_source⟩ : Opens M) ≃ₘ⟮I, I⟯
      (⟨Ψ.source, Ψ.open_source⟩ : Opens M))
    {U₀ : Opens M} (hU₀ : U₀ ≤ (⟨Ψ.source, Ψ.open_source⟩ : Opens M)) :
    ∃ (U₁ : Opens N) (φ : U₀ ≃ₘ⟮I, K⟯ U₁),
      Subtype.val ∘ ⇑φ = (Ψ ∘ Subtype.val) ∘ Θ ∘ Opens.inclusion hU₀ := by
  let ι := Opens.inclusion hU₀
  have hιval : Subtype.val ∘ ι = Subtype.val := Set.val_comp_inclusion hU₀
  have hι : ContMDiff I I ∞ ι := contMDiff_inclusion hU₀
  let Φ : U₀ → N := (Ψ ∘ Subtype.val) ∘ Θ ∘ ι
  have hinj : Function.Injective Φ := fun z z' h ↦ by
    have h' := Ψ.toPartialEquiv.injOn (Θ (ι z)).2 (Θ (ι z')).2 h
    have hv := congrArg Subtype.val (Θ.injective (Subtype.ext h') : ι z = ι z')
    exact Subtype.ext hv
  -- `Φ` is a composite of local diffeomorphisms.
  have hloc : IsLocalDiffeomorph I K ∞ Φ := fun z ↦
    (IsLocalDiffeomorphAt.of_comp_left (hιval ▸ isLocalDiffeomorph_subtype_val z)
        (isLocalDiffeomorph_subtype_val _) hι.continuous.continuousAt).comp
      (hg := (Θ.isLocalDiffeomorph _).comp (hg := (isLocalDiffeomorph_subtype_val _).comp
        (hg := Ψ.isLocalDiffeomorphAt I K ∞ (Θ (ι z)).2)))
  exact ⟨hloc.image, hloc.diffeomorphOfInjective hinj,
    funext (IsLocalDiffeomorph.coe_diffeomorphOfInjective_apply hloc hinj)⟩

variable {E' H' Q : Type*} [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [IsManifold K ∞ N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]

/-- The Moser step: on the source `U` of `Ψ`, a diffeomorphism of `U` which fixes `f(Q)` with the
identity as differential pulls `Ψ^* σ` back to `θ` near `f(Q)`. -/
private theorem exists_diffeomorph_source_eventually_mpullback_eq (f : SmoothEmbedding J I ∞ Q M)
    {θ : SmoothTwoForm I M} (hθ : θ.IsClosed) (hnd : ∀ q, (θ.bilinFormAt (f q)).Nondegenerate)
    {σ : SmoothTwoForm K N} (hσ : σ.IsClosed) (Ψ : PartialDiffeomorph I K M N ∞)
    (hsrc : ∀ q, f q ∈ Ψ.source)
    (heq : ∀ q (v w : TangentSpace I (f q)),
      SmoothBundleForm.eval₂ σ (Ψ (f q)) (mfderiv I K Ψ (f q) v) (mfderiv I K Ψ (f q) w) =
        SmoothBundleForm.eval₂ θ (f q) v w)
    (hΨU : ContMDiff I K ∞ (Ψ ∘ (Subtype.val : (⟨Ψ.source, Ψ.open_source⟩ : Opens M) → M))) :
    ∃ Θ : (⟨Ψ.source, Ψ.open_source⟩ : Opens M) ≃ₘ⟮I, I⟯
        (⟨Ψ.source, Ψ.open_source⟩ : Opens M),
      (∀ q, Θ ⟨f q, hsrc q⟩ = ⟨f q, hsrc q⟩) ∧
      (∀ q, mfderiv I I Θ ⟨f q, hsrc q⟩ = ContinuousLinearMap.id ℝ
        (TangentSpace I (⟨f q, hsrc q⟩ : (⟨Ψ.source, Ψ.open_source⟩ : Opens M)))) ∧
      ∀ᶠ z in 𝓝ˢ (range fun q ↦ (⟨f q, hsrc q⟩ : (⟨Ψ.source, Ψ.open_source⟩ : Opens M))),
        (SmoothForm.mpullback Θ Θ.contMDiff (SmoothForm.mpullback _ hΨU σ)).1 z =
          (SmoothForm.mpullback Subtype.val contMDiff_subtype_val θ).1 z := by
  let U : Opens M := ⟨Ψ.source, Ψ.open_source⟩
  let fU : SmoothEmbedding J I ∞ Q U := f.codRestrict U hsrc
  have hfU : ⇑fU = fun q ↦ ⟨f q, hsrc q⟩ := funext fun q ↦ Subtype.ext (by simp [fU])
  -- Along `f(Q)` the forms `Ψ^* σ` and `θ` agree on `U`, so the relative Moser theorem applies.
  obtain ⟨Θ, hΘf, -, hΘ, hΘ1⟩ := exists_diffeomorph_fix_embedding_eventually_mpullback_eq fU
    (σ₀ := SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val θ)
    (σ₁ := SmoothForm.mpullback _ hΨU σ) (hθ.mpullback _ _) (hσ.mpullback _ _)
    (fun q ↦ by
      rw [nondegenerate_bilinFormAt_mpullback_subtype_val_iff, hfU]
      exact hnd q)
    fun q ↦ by
      rw [congrFun hfU q]
      refine SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ ?_
      rw [SmoothForm.eval₂_mpullback, Manifold.mfderiv_comp_subtype_val_apply,
        Manifold.mfderiv_comp_subtype_val_apply, Function.comp_apply]
      -- `v` and `w` are tangent vectors of `U`, so `θ` and its restriction are compared through
      -- `eval₂_apply` rather than by rewriting.
      have h := congrArg (fun φ ↦ φ ![v, w])
        (SmoothForm.coe_mpullback_subtype_val_apply θ ⟨f q, hsrc q⟩)
      exact (heq q v w).trans ((SmoothBundleForm.eval₂_apply θ (f q) _ _).trans
        (h.symm.trans (SmoothBundleForm.eval₂_apply _ _ _ _).symm))
  rw [hfU] at hΘf hΘ hΘ1
  exact ⟨Θ, hΘf, hΘ1, hΘ⟩

/-- **A symplectomorphism of neighbourhoods with prescribed derivative.** Let `θ` and `σ` be
closed two-forms on `M` and `N`, with `M` boundaryless, Hausdorff and second countable, let
`f : Q → M` be a compact embedded submanifold along which `θ` is nondegenerate, and let `Ψ` be a
partial diffeomorphism from `M` to `N` whose source contains `f(Q)` and whose differential at each
point of `f(Q)` carries `σ` to `θ` on the full ambient tangent space. Then there are open
neighbourhoods `U₀` of `f(Q)` and `U₁` of `Ψ(f(Q))` and a diffeomorphism `φ : U₀ → U₁` pulling the
restriction of `σ` back to the restriction of `θ`, which agrees with `Ψ` at every point of `f(Q)`
and has the same differential as `Ψ` there. -/
theorem exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq (f : SmoothEmbedding J I ∞ Q M)
    {θ : SmoothTwoForm I M} (hθ : θ.IsClosed) (hnd : ∀ q, (θ.bilinFormAt (f q)).Nondegenerate)
    {σ : SmoothTwoForm K N} (hσ : σ.IsClosed) (Ψ : PartialDiffeomorph I K M N ∞)
    (hsrc : ∀ q, f q ∈ Ψ.source)
    (heq : ∀ q (v w : TangentSpace I (f q)),
      SmoothBundleForm.eval₂ σ (Ψ (f q)) (mfderiv I K Ψ (f q) v) (mfderiv I K Ψ (f q) w) =
        SmoothBundleForm.eval₂ θ (f q) v w) :
    ∃ (U₀ : Opens M) (U₁ : Opens N) (φ : U₀ ≃ₘ⟮I, K⟯ U₁),
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : N) = Ψ (f q) ∧
        ∀ v, mfderiv I K φ ⟨f q, h⟩ v = mfderiv I K Ψ (f q) v) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtype_val σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtype_val θ := by
  let U : Opens M := ⟨Ψ.source, Ψ.open_source⟩
  have hΨU : ContMDiff I K ∞ (Ψ ∘ (Subtype.val : U → M)) :=
    Ψ.contMDiffOn.comp_contMDiff contMDiff_subtype_val fun z ↦ z.2
  obtain ⟨Θ, hΘf, hΘ1, hΘ⟩ :=
    exists_diffeomorph_source_eventually_mpullback_eq f hθ hnd hσ Ψ hsrc heq hΨU
  -- Restrict to an open neighbourhood `U₀ ⊆ U` of `f(Q)` on which `Θ` pulls `Ψ^* σ` back to `θ`,
  -- and correct `Ψ` there to `φ = Ψ ∘ Θ`.
  obtain ⟨A, ⟨hA, hfA⟩, hAΘ⟩ := (hasBasis_nhdsSet _).mem_iff.1 hΘ
  let U₀ : Opens M := ⟨Subtype.val '' A, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap A hA⟩
  have hU₀ : U₀ ≤ U := Subtype.coe_image_subset (U : Set M) A
  have hιval : Subtype.val ∘ Opens.inclusion hU₀ = Subtype.val := Set.val_comp_inclusion hU₀
  have hι : ContMDiff I I ∞ (Opens.inclusion hU₀) := contMDiff_inclusion hU₀
  have hq (q : Q) : f q ∈ U₀ := ⟨⟨f q, hsrc q⟩, hfA (mem_range_self q), rfl⟩
  have hιq (q : Q) : Opens.inclusion hU₀ ⟨f q, hq q⟩ = ⟨f q, hsrc q⟩ :=
    Subtype.ext (congrFun hιval _)
  obtain ⟨U₁, φ, hφ⟩ := exists_diffeomorph_opens_comp_eq Ψ Θ hU₀
  refine ⟨U₀, U₁, φ, fun q ↦ ⟨hq q, ?_, fun v ↦ ?_⟩, ?_⟩
  · rw [← Function.comp_apply (f := Subtype.val), hφ]
    simp only [Function.comp_apply]
    rw [hιq, hΘf]
  · -- By the chain rule, `dφ = dΨ ∘ dΘ ∘ dι`, where `dΘ` and `dι` are identities along `f(Q)`.
    rw [← Manifold.mfderiv_subtype_val_comp_apply, hφ,
      mfderiv_comp_apply _ (hΨU.mdifferentiableAt (by simp))
        ((Θ.contMDiff.comp hι).mdifferentiableAt (by simp)),
      mfderiv_comp_apply _ (Θ.contMDiff.mdifferentiableAt (by simp))
        (hι.mdifferentiableAt (by simp)),
      Manifold.mfderiv_comp_subtype_val_apply, Manifold.mfderiv_inclusion_apply, hιq, hΘ1]
    -- The base point `Θ (ι ⟨f q, _⟩)` is `f q` only propositionally; `mfderiv_congr_point`
    -- compares the differentials of `Ψ` at the two points as maps of model spaces.
    have hpt : (((Θ ∘ Opens.inclusion hU₀) ⟨f q, hq q⟩ : U) : M) = f q := by
      rw [Function.comp_apply, hιq, hΘf]
    exact DFunLike.congr_fun (mfderiv_congr_point (I := I) (I' := K) (f := Ψ) hpt) v
  · -- On `U₀`, the pullback by `φ` is the pullback along `ι` of the pullback by `Θ` of `Ψ^* σ`.
    simp only [SmoothForm.mpullback_mpullback, hφ]
    rw [show SmoothForm.mpullback ((Ψ ∘ Subtype.val) ∘ Θ ∘ Opens.inclusion hU₀)
          (hΨU.comp (Θ.contMDiff.comp hι)) σ =
        SmoothForm.mpullback _ hι (SmoothForm.mpullback Θ Θ.contMDiff
          (SmoothForm.mpullback _ hΨU σ)) by
      rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback],
      show SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtype_val θ =
        SmoothForm.mpullback _ hι (SmoothForm.mpullback _ contMDiff_subtype_val θ) by
      simp only [SmoothForm.mpullback_mpullback, hιval]]
    refine Subtype.ext (funext fun z ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
    have hzA : Opens.inclusion hU₀ z ∈ A := by
      obtain ⟨a, ha, h⟩ := z.2
      rwa [show Opens.inclusion hU₀ z = a from Subtype.ext ((congrFun hιval z).trans h.symm)]
    rw [SmoothForm.mpullback_apply _ hι, SmoothForm.mpullback_apply _ hι, hAΘ hzA]

end TauCeti.SmoothTwoForm
