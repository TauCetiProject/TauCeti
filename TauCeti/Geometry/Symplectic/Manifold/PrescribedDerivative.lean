/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import TauCeti.Geometry.Manifold.TubularNeighborhood.PrescribedDifferential
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# Symplectic neighbourhood germs with a prescribed ambient derivative

Let `θ` and `σ` be closed two-forms on manifolds `M` and `N`, with `M` boundaryless, let
`i : Q → M` be a compact embedded submanifold along which `θ` is nondegenerate, and let `Ψ` be a
partial diffeomorphism from `M` to `N`, defined near `i(Q)`, whose differential at every point of
`i(Q)` is a linear symplectic map: `σ(dΨ v, dΨ w) = θ(v, w)` for all tangent vectors `v`, `w` of
`M` at that point. Then `Ψ` can be corrected to a diffeomorphism of neighbourhoods pulling `σ`
back to `θ` without changing it to first order along `i(Q)`: there are open neighbourhoods `U₀`
of `i(Q)` and `U₁` of `Ψ(i(Q))` and a diffeomorphism `φ : U₀ → U₁` pulling `σ` back to `θ` which
agrees with `Ψ` at every point of `i(Q)` and has the same differential there
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq`).

The hypothesis says that `Ψ^* σ` and `θ` agree as bilinear forms on the full ambient tangent spaces
along `i(Q)`. The relative Moser theorem in this form
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`) gives a
diffeomorphism `Θ` of the source of `Ψ` which fixes `i(Q)`, has the identity as differential along
it, and pulls `Ψ^* σ` back to `θ` near `i(Q)`. The correction is `φ = Ψ ∘ Θ`, and the chain rule
gives `dφ = dΨ ∘ dΘ = dΨ` along `i(Q)`.

Together with the realization of a bundle isomorphism along `i(Q)` as the differential of a
partial diffeomorphism (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`), this gives
symplectic neighbourhood germs with a prescribed ambient derivative
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq`). With `θ`, `σ` and `i` as above,
let `g : Q → N` be a smooth map inducing the topology of `Q`, and let
`A q : T_{i q} M → T_{g q} N` be linear isomorphisms, smooth in tangent coordinates, with
`A q ∘ d i_q = d g_q` and `σ(A q v, A q w) = θ(v, w)`. Then there is a
diffeomorphism `φ` between open neighbourhoods of `i(Q)` and `g(Q)` pulling `σ` back to `θ`, with
`φ (i q) = g q` and `d φ_{i q} = A q`. For a diffeomorphism `e : Q → Q'` and a second compact
embedded submanifold `j : Q' → N`, the case `g = j ∘ e` realizes a symplectic bundle isomorphism
`A : i^* TM → j^* TN` over `e`. No constant-rank hypothesis on the pullback of `θ` to `Q` is
needed. Conversely, the restriction and the differentials along `i(Q)` of any such `φ` are data of
this kind, so these conditions characterize them
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_iff`).

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq`: a partial
  diffeomorphism whose differential carries `σ` to `θ` along a compact embedded submanifold
  `i(Q)` agrees to first order along `i(Q)` with a diffeomorphism of neighbourhoods pulling `σ`
  back to `θ`.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq`: a symplectic bundle isomorphism
  along a compact embedded submanifold is the differential of a diffeomorphism of neighbourhoods
  pulling one form back to the other.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_mfderiv_eq_iff`: the data realized by such
  diffeomorphisms are characterized.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 7.4 (the relative Moser theorem) and Theorem 8.4 (the Lagrangian
  neighbourhood theorem, whose prescribed-derivative refinement is proved here).
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

variable {E' H' Q : Type*} [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M] [IsManifold K ∞ N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]

/-- The Moser step: on the source `U` of `Ψ`, there is a diffeomorphism `Θ` of `U` which fixes
`f(Q)`, has the identity as differential there, and pulls `Ψ^* σ` back to `θ` near `f(Q)`. -/
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
        (SmoothForm.mpullback Θ Θ.contMDiff (SmoothForm.mpullback _ hΨU σ)).val z =
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal θ).val z := by
  let U : Opens M := ⟨Ψ.source, Ψ.open_source⟩
  let fU : SmoothEmbedding J I ∞ Q U := f.codRestrict U hsrc
  have hfU : ⇑fU = fun q ↦ ⟨f q, hsrc q⟩ := funext fun q ↦ Subtype.ext (by simp [fU])
  -- Along `f(Q)` the forms `Ψ^* σ` and `θ` agree on `U`, so the relative Moser theorem applies.
  obtain ⟨Θ, hΘf, -, hΘ, hΘ1⟩ := exists_diffeomorph_fix_embedding_eventually_mpullback_eq fU
    (σ₀ := SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtypeVal θ)
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

/-- **Correcting a partial diffeomorphism to pull `σ` back to `θ` near `f(Q)`, keeping its
differential along `f(Q)`.** Let `θ` and `σ` be
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
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal θ := by
  let U : Opens M := ⟨Ψ.source, Ψ.open_source⟩
  have hΨU : ContMDiff I K ∞ (Ψ ∘ (Subtype.val : U → M)) :=
    Ψ.contMDiffOn.comp_contMDiff contMDiff_subtypeVal fun z ↦ z.property
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
  obtain ⟨U₁, φ, hφ⟩ := Ψ.exists_diffeomorph_opens_comp_eq Θ hU₀
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
    rw [SmoothForm.mpullback_mpullback_of_comp_eq φ.contMDiff contMDiff_subtypeVal
      (Θ.contMDiff.comp hι) hΨU hφ, ← SmoothForm.mpullback_mpullback _ _ hι Θ.contMDiff]
    refine Subtype.ext (funext fun z ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
    have hzA : Opens.inclusion hU₀ z ∈ A := by
      obtain ⟨a, ha, h⟩ := z.property
      rwa [show Opens.inclusion hU₀ z = a from Subtype.ext ((congrFun hιval z).trans h.symm)]
    rw [SmoothForm.mpullback_apply _ hι, hAΘ hzA, SmoothForm.coe_mpullback_subtype_val_apply,
      SmoothForm.coe_mpullback_subtype_val_apply]
    simp only [Manifold.mfderiv_inclusion_apply]
    -- The base point `ι z` of `U` is `z` in `M`, by `hιval`.
    exact congrArg (fun x : M ↦ θ.val x v) (congrFun hιval z)

section PrescribedDerivative

variable [FiniteDimensional ℝ F] [K.Boundaryless] [T2Space N] [SecondCountableTopology N]

/-- **Symplectic neighbourhood germs with a prescribed ambient derivative.** Let `θ` and `σ` be
closed two-forms on finite-dimensional boundaryless manifolds `M` and `N`, Hausdorff and second
countable, let `i : Q → M` be a compact embedded submanifold along which `θ` is nondegenerate, and
let `g : Q → N` be a smooth map inducing the topology of `Q`. Let `A q : T_{i q} M → T_{g q} N` be
linear isomorphisms, smooth in tangent coordinates, which extend the differential of `g` along `i`,
`A q ∘ d i_q = d g_q`, and carry `σ` to `θ`. Then there are open neighbourhoods `U₀` of `i(Q)` and
`U₁` of `g(Q)` and a diffeomorphism `φ : U₀ → U₁` pulling `σ` back to `θ`, with `φ (i q) = g q`
and `d φ_{i q} = A q` for every `q`.

For a diffeomorphism `e : Q → Q'` onto a second compact embedded submanifold `j : Q' → N`, the
case `g = j ∘ e` is a symplectomorphism of neighbourhoods with `φ ∘ i = j ∘ e` realizing a
symplectic bundle isomorphism `A : i^* TM → j^* TN` over `e`. -/
theorem exists_diffeomorph_opens_mfderiv_eq (i : SmoothEmbedding J I ∞ Q M) {g : Q → N}
    (hg : ContMDiff J K ∞ g) (hgi : Topology.IsInducing g)
    {θ : SmoothTwoForm I M} (hθ : θ.IsClosed) (hnd : ∀ q, (θ.bilinFormAt (i q)).Nondegenerate)
    {σ : SmoothTwoForm K N} (hσ : σ.IsClosed)
    {A : ∀ q, TangentSpace I (i q) →L[ℝ] TangentSpace K (g q)}
    (hA : ∀ q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] F) ∞ (inTangentCoordinates I K i g A q) q)
    (hAinv : ∀ q, (A q).IsInvertible)
    (hAi : ∀ q, (A q).comp (mfderiv J I i q) = mfderiv J K g q)
    (hAσ : ∀ q (v w : TangentSpace I (i q)),
      SmoothBundleForm.eval₂ σ (g q) (A q v) (A q w) = SmoothBundleForm.eval₂ θ (i q) v w) :
    ∃ (U₀ : Opens M) (U₁ : Opens N) (φ : U₀ ≃ₘ⟮I, K⟯ U₁),
      (∀ q, ∃ h : i q ∈ U₀, (φ ⟨i q, h⟩ : N) = g q ∧ ∀ v, mfderiv I K φ ⟨i q, h⟩ v = A q v) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal θ := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · -- For empty `Q`, the empty open sets will do.
    have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ Set.notMem_empty (x : M) <| by
      simpa only [← SetLike.mem_coe, Opens.coe_bot] using x.property⟩
    have : IsEmpty (⊥ : Opens N) := ⟨fun y ↦ Set.notMem_empty (y : N) <| by
      simpa only [← SetLike.mem_coe, Opens.coe_bot] using y.property⟩
    let φ : (⊥ : Opens M) ≃ₘ⟮I, K⟯ (⊥ : Opens N) :=
      { toEquiv := Equiv.equivOfIsEmpty _ _
        contMDiff_toFun := fun x ↦ isEmptyElim x
        contMDiff_invFun := fun y ↦ isEmptyElim y }
    exact ⟨⊥, ⊥, φ, fun q ↦ isEmptyElim q, Subtype.ext (funext fun x ↦ isEmptyElim x)⟩
  -- Realize `A` as the differential of a partial diffeomorphism `Ψ`, then correct `Ψ` by the
  -- relative Moser theorem without changing its differential along `i(Q)`.
  obtain ⟨Ψ, hsrc, -, -, hval, hd⟩ := i.exists_partialDiffeomorph_mfderiv_eq hg hgi hA hAinv hAi
    isOpen_univ (subset_univ _) isOpen_univ (subset_univ _)
  obtain rfl : g = Ψ ∘ i := funext fun q ↦ (hval q).symm
  obtain rfl : A = fun q ↦ mfderiv I K Ψ (i q) := funext fun q ↦ (hd q).symm
  exact exists_diffeomorph_opens_mfderiv_eq_of_eval₂_eq i hθ hnd hσ Ψ
    (fun q ↦ hsrc (mem_range_self q)) hAσ

/-- **Symplectic neighbourhood germs with a prescribed ambient derivative, characterized.** Along a
compact embedded submanifold `i : Q → M` with `θ` nondegenerate along it, a map `g : Q → N` and
linear maps `A q : T_{i q} M → T_{g q} N` are the restriction and the differentials along `i(Q)`
of a diffeomorphism of open neighbourhoods pulling `σ` back to `θ` exactly when `g` is smooth and
induces the topology of `Q`, `A` is smooth in tangent coordinates, each `A q` is invertible,
`A q ∘ d i_q = d g_q`, and each `A q` carries `σ` to `θ`. -/
theorem exists_diffeomorph_opens_mfderiv_eq_iff (i : SmoothEmbedding J I ∞ Q M) {g : Q → N}
    {θ : SmoothTwoForm I M} (hθ : θ.IsClosed) (hnd : ∀ q, (θ.bilinFormAt (i q)).Nondegenerate)
    {σ : SmoothTwoForm K N} (hσ : σ.IsClosed)
    {A : ∀ q, TangentSpace I (i q) →L[ℝ] TangentSpace K (g q)} :
    (∃ (U₀ : Opens M) (U₁ : Opens N) (φ : U₀ ≃ₘ⟮I, K⟯ U₁),
      (∀ q, ∃ h : i q ∈ U₀, (φ ⟨i q, h⟩ : N) = g q ∧ ∀ v, mfderiv I K φ ⟨i q, h⟩ v = A q v) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtypeVal σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal θ) ↔
      ContMDiff J K ∞ g ∧ Topology.IsInducing g ∧
        (∀ q, ContMDiffAt J 𝓘(ℝ, E →L[ℝ] F) ∞ (inTangentCoordinates I K i g A q) q) ∧
        (∀ q, (A q).IsInvertible) ∧ (∀ q, (A q).comp (mfderiv J I i q) = mfderiv J K g q) ∧
        ∀ q (v w : TangentSpace I (i q)),
          SmoothBundleForm.eval₂ σ (g q) (A q v) (A q w) = SmoothBundleForm.eval₂ θ (i q) v w := by
  refine ⟨fun ⟨U₀, U₁, φ, hφ, hpull⟩ ↦ ?_, fun ⟨hg, hgi, hA, hAinv, hAi, hAσ⟩ ↦
    exists_diffeomorph_opens_mfderiv_eq i hg hgi hθ hnd hσ hA hAinv hAi hAσ⟩
  -- `φ` carries `σ` to `θ` on every tangent space of `U₀`, in particular along `i(Q)`.
  have hφσ (z : U₀) (v w : TangentSpace I z) :
      SmoothBundleForm.eval₂ σ (φ z : N) (mfderiv I K φ z v) (mfderiv I K φ z w) =
        SmoothBundleForm.eval₂ θ (z : M) v w := by
    simpa only [SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val_apply] using
      congrArg (fun α : SmoothTwoForm I U₀ ↦ SmoothBundleForm.eval₂ α z v w) hpull
  have hAσ (q : Q) (v w : TangentSpace I (i q)) :
      SmoothBundleForm.eval₂ σ (g q) (A q v) (A q w) = SmoothBundleForm.eval₂ θ (i q) v w := by
    obtain ⟨h, hφq, hdφ⟩ := hφ q
    have hz := hφσ ⟨i q, h⟩ v w
    rwa [hdφ v, hdφ w, hφq] at hz
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · exact ⟨fun q ↦ isEmptyElim q, (Topology.IsEmbedding.of_subsingleton g).isInducing,
      fun q ↦ isEmptyElim q, fun q ↦ isEmptyElim q, fun q ↦ isEmptyElim q, hAσ⟩
  -- Read `φ` as a partial diffeomorphism `Ψ` from `M` to `N`, whose restriction and differentials
  -- along `i(Q)` are `g` and `A`.
  obtain ⟨q₀⟩ := id hQ
  have hU₀ : Nonempty U₀ := ⟨⟨i q₀, (hφ q₀).1⟩⟩
  have hU₁ : Nonempty U₁ := ⟨φ ⟨i q₀, (hφ q₀).1⟩⟩
  let Ψ := φ.toPartialDiffeomorph.liftOpens hU₀ hU₁
  have hΨ : Ψ ∘ Subtype.val = Subtype.val ∘ φ := funext fun x ↦ by
    simp [Ψ, PartialDiffeomorph.liftOpens_apply_coe]
  have hsrc : range i ⊆ Ψ.source := by
    rintro _ ⟨q, rfl⟩
    rw [PartialDiffeomorph.liftOpens_source]
    exact ⟨⟨i q, (hφ q).1⟩, by simp, rfl⟩
  have hval (q : Q) : Ψ (i q) = g q := by
    obtain ⟨h, hφq, -⟩ := hφ q
    rw [← hφq]
    exact congrFun hΨ ⟨i q, h⟩
  have hd (q : Q) : mfderiv I K Ψ (i q) = A q := by
    obtain ⟨h, -, hdφ⟩ := hφ q
    ext v
    -- `v` is ascribed to the tangent space of `U₀` at `⟨i q, h⟩`, which is only definitionally the
    -- tangent space of `M` at `i q`, so that the rewrites below find their patterns.
    have h1 := Manifold.mfderiv_comp_subtype_val_apply (J := I) (I := K) (f := (Ψ : M → N))
      (x := (⟨i q, h⟩ : U₀)) (show TangentSpace I (⟨i q, h⟩ : U₀) from v)
    rw [hΨ, Manifold.mfderiv_subtype_val_comp_apply, hdφ] at h1
    exact h1.symm
  obtain ⟨hg, hgi, hA, hAinv, hAi⟩ :=
    (i.exists_partialDiffeomorph_mfderiv_eq_iff (g := g) (A := A)).1 ⟨Ψ, hsrc, hval, hd⟩
  exact ⟨hg, hgi, hA, hAinv, hAi, hAσ⟩

end PrescribedDerivative

end TauCeti.SmoothTwoForm
