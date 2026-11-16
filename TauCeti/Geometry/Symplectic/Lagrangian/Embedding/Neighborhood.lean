/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Normal
public import TauCeti.Geometry.Symplectic.Manifold.RelativeMoser

/-!
# Weinstein's Lagrangian neighbourhood theorem

Let `f : M → N` be a Lagrangian embedding of a compact boundaryless manifold `M` into a symplectic
manifold `(N, σ)`. **Weinstein's Lagrangian neighbourhood theorem**
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding`)
says that a neighbourhood of `f(M)` in `N` is symplectomorphic to a neighbourhood of the zero
section in the cotangent bundle `T*M`, with its canonical symplectic form `ω = -dλ`, by a map
sending the zero covector over each point `x` of `M` to `f x`. So near a compact Lagrangian
submanifold, every symplectic manifold looks like the cotangent bundle near its zero section.

The proof follows Weinstein and Cannas da Silva.

* **Tubular coordinates.** For an auxiliary Riemannian metric on `N`, the normal exponential of
  `f` identifies a neighbourhood of the zero section of the normal bundle of `f` with a
  neighbourhood of `f(M)` (`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`).
  Since `f` is Lagrangian, `σ` identifies the normal space at `x` with the cotangent space
  `T*_x M` by `[v] ↦ σ(df_x ·, v)`
  (`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLagrangianMap`). Together they give a
  partial diffeomorphism `Ψ` from `T*M` to `N`, defined near the zero section and sending the zero
  covector over `x` to `f x`.
* **Agreement along the zero section.** In the splitting `T_x M × T*_x M` of the tangent space of
  `T*M` at the zero covector over `x`, the differential of `Ψ` sends `(u, α)` to `df_x u + n`,
  where `n` is the normal representative whose normal class corresponds to `α`. Hence
  `(Ψ^* σ)((u, 0), (u', α')) = σ(df_x u, n') = α'(u)`, which is the value of `ω` on the same pair
  (`TauCeti.CotangentBundle.eval₂_symplecticForm_zeroSection`). So `Ψ^* σ` and `ω` agree whenever
  one argument is tangent to the zero section. They need not agree on pairs of vertical vectors,
  since the normal representatives need not span a Lagrangian complement.
* **Moser's argument.** Agreement on the tangent spaces of the zero section, which is Lagrangian
  for `ω`, is enough for the linear path from `ω` to `Ψ^* σ` to stay nondegenerate along the zero
  section (`TauCeti.SymplecticForm.IsCoisotropic.nondegenerate_of_apply_eq`). The relative Moser
  theorem then corrects `Ψ` near the zero section to a symplectomorphism
  (`TauCeti.SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_of_isCoisotropicMap_of_eval₂_eq`).

## References

* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorems 8.4 and 9.3.
-/

public section

noncomputable section

open Bundle Set Module TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {σ : SmoothTwoForm J N}

/-- **Lagrangian tubular coordinates.** For a Lagrangian embedding `f`, a partial diffeomorphism
`Ψ` from `T*M` to `N`, defined near the zero section and sending the zero covector over `x` to
`f x`, whose differential at that zero covector is `(u, α) ↦ df_x u + A α` in the splitting
`T_x M × T*_x M`, for a linear map `A` with `σ(df_x ·, A α) = α`. It is the normal exponential of
`f` for a Riemannian metric on `N`, composed with the identification of the normal bundle of `f`
with `T*M` by `σ`, and `A α` is the normal representative of the normal class corresponding to
`α`. -/
private theorem SmoothEmbedding.exists_partialDiffeomorph_cotangent_mfderiv [Nonempty M]
    [SecondCountableTopology N] [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
    {hσ : σ.IsNondegenerate} (f : SmoothEmbedding I J ∞ M N) (hf : hσ.IsLagrangianMap I f) :
    ∃ Ψ : PartialDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) J (CotangentBundle I M) N ∞,
      (∀ x, zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x ∈ Ψ.source) ∧
      (∀ x, Ψ (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x) = f x) ∧
      ∀ x, ∃ A : (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace J (f x),
        (∀ α, f.pairingCovector σ x (A α) = α) ∧ ∀ v α,
          mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) J Ψ
              (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x)
              ((Bundle.zeroSectionTangentEquiv (I := I) x).symm (v, α)) =
            mfderiv I J f x v + A α := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hdim := f.finrank_continuousLinearMap_eq_sub_of_isLagrangianMap hf hn
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  obtain ⟨Φ, hzero, -, -, -, hΦ⟩ := f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn
    (by simp) (by simp) hdim isOpen_univ (subset_univ _)
  -- `D⁻¹` identifies `T*M` with the normal bundle, fibrewise linearly.
  let D := f.normalBundleDiffeomorphOfIsLagrangianMap hf hn (m := ∞) (by simp) (by simp) hdim
  let ι := f.normalSpaceEquivOfIsLagrangianMap hf hn
  have hD (x : M) (α : TangentSpace I x →L[ℝ] ℝ) :
      D.symm ⟨x, α⟩ = ⟨x, ((ι x).symm : _ →L[ℝ] _).toLinearMap α⟩ :=
    normalBundleDiffeomorphOfIsLagrangianMap_symm_apply f hf hn (m := ∞) _ _ hdim _
  have hDz (x : M) : D.symm (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x) =
      zeroSection (E →L[ℝ] ℝ) (fun x ↦ f.NormalSpace x hn) x := by
    simpa [zeroSection] using hD x 0
  let Ψ := D.symm.toPartialDiffeomorph.trans Φ
  have hΨe : Ψ.toPartialEquiv = D.symm.toEquiv.toPartialEquiv.trans Φ.toPartialEquiv := by
    rw [PartialDiffeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv]
    exact congrArg₂ PartialEquiv.trans (Diffeomorph.toPartialDiffeomorph_toPartialEquiv _) rfl
  have hΨ : ⇑Ψ = f.normalExp hn ∘ D.symm := by
    rw [← hΦ, hΨe, PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, Diffeomorph.coe_toEquiv]
  refine ⟨Ψ, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ⟨(f.normalRepresentative x hn).toLinearMap ∘ₗ
    ((ι x).symm : _ →L[ℝ] _).toLinearMap, fun α ↦ ?_, fun v α ↦ ?_⟩⟩
  · rw [hΨe, PartialEquiv.trans_source, mem_inter_iff, mem_preimage, Equiv.toPartialEquiv_apply,
      Diffeomorph.coe_toEquiv, hDz]
    exact ⟨mem_univ _, hzero x⟩
  · rw [hΨ, Function.comp_apply, hDz, normalExp_zeroSection]
  · -- The normal class of the representative of `ι⁻¹ α` is `ι⁻¹ α`, which `ι` sends to `α`.
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      ← f.normalSpaceEquivOfIsLagrangianMap_normalClass hf hn, f.normalClass_normalRepresentative]
    exact (ι x).apply_symm_apply α
  · -- The differential is that of the normal exponential after the fibrewise linear `D⁻¹`.
    have hexp : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) J (f.normalExp hn)
        (zeroSection (E →L[ℝ] ℝ) (fun x ↦ f.NormalSpace x hn) x) :=
      hΦ ▸ Φ.mdifferentiableAt (by simp) (hzero x)
    have : IsManifold I (1 + 1) M := .of_le (n := ∞) (by norm_cast)
    rw [hΨ, mfderiv_comp_apply_of_eq _ hexp (D.symm.contMDiff.mdifferentiableAt (by simp)) (hDz x),
      Bundle.mfderiv_zeroSection_zeroSectionTangentEquiv_symm _ hD x
        (D.symm.contMDiff.mdifferentiableAt (by simp)), mfderiv_normalExp_zeroSection_apply f hn
        (by simp) hdim, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe]

/-- Along the zero section, the tubular coordinates of
`SmoothEmbedding.exists_partialDiffeomorph_cotangent_mfderiv` pull `σ` back to a form agreeing
with the canonical form `ω` of `T*M` whenever the first argument is tangent to the zero section:
`σ(df u, df u' + A α') = α'(u) = ω((u, 0), (u', α'))`, since `df` has isotropic image. -/
private theorem SmoothEmbedding.exists_partialDiffeomorph_cotangent [Nonempty M]
    [SecondCountableTopology N] [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
    {hσ : σ.IsNondegenerate} (f : SmoothEmbedding I J ∞ M N) (hf : hσ.IsLagrangianMap I f) :
    ∃ Ψ : PartialDiffeomorph (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) J (CotangentBundle I M) N ∞,
      (∀ x, zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x ∈ Ψ.source) ∧
      (∀ x, Ψ (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x) = f x) ∧
      ∀ x (u : TangentSpace I x) w,
        SmoothBundleForm.eval₂ σ
            (Ψ (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x))
            (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) J Ψ
              (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x)
              (mfderiv I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
                (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) x u))
            (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) J Ψ
              (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x) w) =
          SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm I M)
            (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x)
            (mfderiv I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
              (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) x u) w := by
  obtain ⟨Ψ, hsrc, hval, hA⟩ := f.exists_partialDiffeomorph_cotangent_mfderiv hf
  refine ⟨Ψ, hsrc, hval, fun x u w ↦ ?_⟩
  obtain ⟨A, hAα, hdΨ⟩ := hA x
  let e := Bundle.zeroSectionTangentEquiv (I := I) (F := E →L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x
  have hz0 : mfderiv I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) x u = e.symm (u, 0) :=
    (ContinuousLinearEquiv.eq_symm_apply _).2
      (Bundle.zeroSectionTangentEquiv_mfderiv_zeroSection x u)
  rw [← e.symm_apply_apply w]
  generalize e w = p
  obtain ⟨u', α'⟩ := p
  rw [hz0, CotangentBundle.eval₂_symplecticForm_zeroSection, zero_apply, sub_zero, hdΨ, hdΨ,
    map_zero, add_zero, hval]
  refine (SmoothBundleForm.eval₂_add_right σ (f x) _ _ _).trans ?_
  rw [(SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff.1 hf.isIsotropicMap) x u u', zero_add,
    ← f.pairingCovector_apply_apply, hAα]

/-- **Weinstein's Lagrangian neighbourhood theorem.** Let `f : M → N` be a Lagrangian embedding of
a compact boundaryless manifold `M` into a symplectic manifold `(N, σ)`, boundaryless, Hausdorff
and second countable. Then there are an open neighbourhood `U₀` of the zero section of the
cotangent bundle `T*M` and an open neighbourhood `U₁` of `f(M)`, with a diffeomorphism
`φ : U₀ → U₁` sending the zero covector over each `x` to `f x` and pulling `σ` back to the
canonical symplectic form `ω = -dλ` of `T*M`. -/
theorem SmoothTwoForm.IsSymplectic.exists_diffeomorph_opens_cotangent_of_isLagrangianEmbedding
    [CompactSpace M] [SecondCountableTopology N] (hσ : σ.IsSymplectic) {f : M → N}
    (hf : hσ.isNondegenerate.IsLagrangianEmbedding I f) :
    ∃ (U₀ : Opens (CotangentBundle I M)) (U₁ : Opens N)
      (φ : U₀ ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J⟯ U₁),
      (∀ x, ∃ h : zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x ∈ U₀,
        (φ ⟨_, h⟩ : N) = f x) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → N) contMDiff_subtype_val σ) =
        SmoothForm.mpullback (Subtype.val : U₀ → CotangentBundle I M) contMDiff_subtype_val
          (CotangentBundle.symplecticForm I M) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · -- Over an empty manifold the cotangent bundle is empty, and empty neighbourhoods suffice.
    have : IsEmpty (⊥ : Opens (CotangentBundle I M)) := ⟨fun z ↦ z.2⟩
    have : IsEmpty (⊥ : Opens N) := ⟨fun z ↦ z.2⟩
    refine ⟨⊥, ⊥, { Equiv.equivOfIsEmpty _ _ with
        contMDiff_toFun := fun z ↦ isEmptyElim z
        contMDiff_invFun := fun z ↦ isEmptyElim z },
      fun x ↦ isEmptyElim x, Subtype.ext (funext fun z ↦ isEmptyElim z)⟩
  have : T2Space M := hf.isEmbedding.t2Space
  have : SecondCountableTopology M := hf.isEmbedding.isInducing.secondCountableTopology
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  -- An auxiliary Riemannian metric on `N` provides the tubular coordinates.
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := F)
    (E := fun y : N ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle g
  let fe := SmoothEmbedding.ofIsSmoothEmbedding f hf.isSmoothEmbedding
  have hfe : ⇑fe = f := SmoothEmbedding.coe_ofIsSmoothEmbedding f _
  obtain ⟨Ψ, hsrc, hval, hder⟩ :=
    fe.exists_partialDiffeomorph_cotangent (hσ := hσ.isNondegenerate) (hfe ▸ hf.isLagrangianMap)
  -- The zero section is Lagrangian for `ω`, so the relative Moser theorem corrects `Ψ`.
  obtain ⟨U₀, U₁, φ, hφ, hφσ⟩ :=
    (CotangentBundle.isSymplectic_symplecticForm (I := I) (M := M)
      ).exists_diffeomorph_opens_of_isCoisotropicMap_of_eval₂_eq
      (Bundle.isSmoothEmbedding_zeroSection (n := ∞) (by simp))
      CotangentBundle.isLagrangianMap_zeroSection.isCoisotropicMap hσ.isClosed Ψ hsrc hder
  refine ⟨U₀, U₁, φ, fun x ↦ ?_, hφσ⟩
  obtain ⟨h, hx⟩ := hφ x
  exact ⟨h, hx.trans ((hval x).trans (congrFun hfe x))⟩

end TauCeti
