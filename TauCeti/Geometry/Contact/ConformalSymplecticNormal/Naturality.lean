/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ConformalSymplecticNormal.Bundle
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Algebra.Module.Submodule.Map

/-!
# Contactomorphisms induce isomorphisms of conformal symplectic normal bundles

Let `D` and `D₁` be smooth contact structures on Hausdorff manifolds `M` and `M₁`, and let
`F : M → M₁` be a smooth map. Let `f : N → M` be a smooth isotropic immersion of a nonempty
manifold, and assume that `F` carries `D` onto `D₁` along `f`: at each `f y` the differential `dF`
is invertible and maps `D (f y)` into `D₁ (F (f y))`, and near `f y` its inverse maps `D₁ (F z)`
into `D z`. A contactomorphism between open subsets is the main example. Then `F ∘ f` is again
an isotropic immersion (`TauCeti.IsHorizontalMap.comp_left`, `TauCeti.injective_mfderiv_comp`),
and the differential of `F` induces at each `y : N` the conformally symplectic isomorphism
`[u] ↦ [dF u]` of conformal symplectic normal spaces (`TauCeti.conformalSymplecticNormalEquiv`).
This file shows that these isomorphisms form a smooth isomorphism of the conformal symplectic
normal bundles of `f` and of `F ∘ f` (`TauCeti.conformalSymplecticNormalPrebundle`).

* **Smoothness.** The map of total spaces `(y, [u]) ↦ (y, [dF u])` is smooth
  (`TauCeti.contMDiff_totalSpace_conformalSymplecticNormalEquiv`). Both bundles are quotients of
  bundles of Levi orthogonals, smooth subbundles of `f^* D` and `(F ∘ f)^* D₁`; the differential of
  `F` maps the first Levi orthogonals onto the second
  (`TauCeti.map_orthogonalBilin_comap_range_mfderiv`), and
  read along `f` and `F ∘ f` it is the tangent map of `F`, which is smooth. The induced map of
  quotient bundles is then smooth
  (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mapQ`).
* **The bundle isomorphism.** Since each fibre map is a linear isomorphism, the map of total spaces
  is a diffeomorphism, an isomorphism of smooth vector bundles over `N`
  (`TauCeti.exists_bundleDiffeomorph_conformalSymplecticNormalEquiv`).

On each fibre the isomorphism is conformally symplectic: it carries the line-valued form of `D₁` to
the image of the form of `D` under the isomorphism of contact lines induced by `dF`
(`TauCeti.conformalSymplecticNormalForm_conformalSymplecticNormalEquiv`), and it is compatible
with composition (`TauCeti.conformalSymplecticNormalEquiv_trans`). No contact form or
coorientation is chosen. These are the bundle isomorphisms `Ψ : CSN(N) → CSN(N')` of the isotropic
neighbourhood theorem.

## Main results

* `TauCeti.contMDiff_totalSpace_conformalSymplecticNormalEquiv`: the map of conformal symplectic
  normal bundles induced by `F` is smooth on total spaces.
* `TauCeti.exists_bundleDiffeomorph_conformalSymplecticNormalEquiv`: it is a smooth isomorphism of
  vector bundles.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle and the isotropic neighbourhood
  theorem).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ 2 M₁]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {D₁ : Π x : M₁, Submodule ℝ (TangentSpace I₁ x)}
  {f : N → M} {F : M → M₁} {y : N}

section Bundle

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- `C^(∞ + 1)` charts on `M`, needed by the smooth vector bundle structure of a smooth
distribution at smoothness `∞`. -/
local instance instIsManifoldConformalSymplecticNormalNaturalitySource [IsManifold I ∞ M] :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

omit [CompleteSpace E₁] [IsManifold I₁ 2 M₁] in
/-- `C^(∞ + 1)` charts on `M₁`, as for `M`. -/
local instance instIsManifoldConformalSymplecticNormalNaturalityTarget [IsManifold I₁ ∞ M₁] :
    IsManifold I₁ ((∞ : WithTop ℕ∞) + 1) M₁ :=
  IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts on `N`, as for `M`. -/
local instance instIsManifoldConformalSymplecticNormalNaturalityBase [IsManifold J ∞ N] :
    IsManifold J ((∞ : WithTop ℕ∞) + 1) N :=
  IsManifold.of_le (n := ∞) (by simp)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₁]

/-- The map of Levi orthogonals `u ↦ dF u` from `f` to `F ∘ f`: the restriction to Levi
orthogonals of the isomorphism `D (f y) ≃ D₁ (F (f y))` induced by `dF`
(`TauCeti.map_orthogonalBilin_comap_range_mfderiv`). Its map of quotients is
`TauCeti.conformalSymplecticNormalEquiv`. -/
private def leviOrthogonalPullbackMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hf : ContMDiff J I ∞ f)
    (y : N) : leviOrthogonalPullback J D f y →ₗ[ℝ] leviOrthogonalPullback J D₁ (F ∘ f) y :=
  (((LinearEquiv.ofBijective (mfderiv I I₁ F (f y)).toLinearMap
    (hFx y).bijective).ofSubmodules _ _
      (map_ofBijective_mfderiv_eq (hFx y) (hFD y) (hFD' y).self_of_nhds)).ofSubmodules _ _
    (map_orthogonalBilin_comap_range_mfderiv (hD.isContMDiffDistribution.of_le (m := 1) (by simp))
      (hD₁.isContMDiffDistribution.of_le (m := 1) (by simp)) hF.contMDiffAt (n := ∞) (by simp)
      (hFx y) (hFD y) (hFD' y) _ (hf.mdifferentiableAt (by simp)))).toLinearMap

/-- The map of Levi orthogonals acts as `dF` on the underlying tangent vectors. -/
private theorem leviOrthogonalPullbackMap_apply (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hf : ContMDiff J I ∞ f)
    (y : N) (u : leviOrthogonalPullback J D f y) :
    (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf y u).val.val =
      mfderiv I I₁ F (f y) u.val.val :=
  (congrArg Subtype.val (LinearEquiv.ofSubmodules_apply _ _ _)).trans
    ((LinearEquiv.ofSubmodules_apply _ _ _).trans (LinearEquiv.ofBijective_apply _ _))

/-- The map of Levi orthogonals carries the tangent images of `f` into those of `F ∘ f`. -/
private theorem le_comap_leviOrthogonalPullbackMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z)
    (hf : ContMDiff J I ∞ f)
    (y : N) :
    ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype ≤
      (((LinearMap.range (mfderiv J I₁ (F ∘ f) y).toLinearMap).comap
        (D₁ ((F ∘ f) y)).subtype).comap (leviOrthogonalPullback J D₁ (F ∘ f) y).subtype).comap
          (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf y) :=
  Submodule.map_le_iff_le_comap.1 (LinearEquiv.map_comap_subtype_ofSubmodules _ _
    (map_comap_range_mfderiv (hFx y) (map_ofBijective_mfderiv_eq (hFx y) (hFD y)
      (hFD' y).self_of_nhds)
      (hF.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)))).le

omit [CompleteSpace E] [IsManifold I 2 M] [CompleteSpace E₁] [IsManifold I₁ 2 M₁]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E₁] in
/-- `F ∘ f` is again horizontal, with injective differentials. -/
private theorem isHorizontalMap_comp_and_injective_mfderiv_comp (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y))) (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y)) :
    IsHorizontalMap J D₁ (F ∘ f) ∧ ∀ y, Injective (mfderiv J I₁ (F ∘ f) y) :=
  ⟨hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp)) (fun _ ↦ hf.mdifferentiableAt (by simp))
    hFD, fun y ↦ injective_mfderiv_comp (hFx y).injective (hinj y)⟩

variable [FiniteDimensional ℝ E'] [IsManifold I ∞ M] [IsManifold I₁ ∞ M₁] [IsManifold J ∞ N]
  [T2Space M] [T2Space M₁] {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

/-- The map of Levi orthogonals is smooth on total spaces: it is the tangent map of `F`, read
along `f` and `F ∘ f`. -/
private theorem contMDiff_totalSpace_leviOrthogonalPullbackMap
    (hD : IsContactDistribution I ∞ D) (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : K}
    (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    letI := hD₁.isContMDiffDistribution.fiberBundle
    letI := hD₁.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ)
      (E := ((ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous : C(N, M₁)) : N → M₁) *ᵖ
        fun x ↦ D₁ x)
      (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ (F ∘ f))
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁
      (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf)
      (hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (g := F) (hFx y).injective (hinj y)).fiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
          (fun y ↦ leviOrthogonalPullback J D f y) ↦
        (⟨p.proj, leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf p.proj p.snd⟩ :
          TotalSpace (Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ)
            fun y ↦ leviOrthogonalPullback J D₁ (F ∘ f) y)) := by
  obtain ⟨hgD, hginj⟩ := isHorizontalMap_comp_and_injective_mfderiv_comp hF hFx hFD hf hfD hinj
  set g := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous
  have hg : ContMDiff J I₁ ∞ g := hF.comp hf
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  let := hD₁.isContMDiffDistribution.fiberBundle
  let := hD₁.isContMDiffDistribution.vectorBundle
  have := hD₁.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E₁ - 1) → ℝ)
    (E := fun x ↦ D₁ x) (IB := I₁) (IB' := J) hg
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
    (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).fiberBundle
  intro p₀
  have hproj := (Bundle.contMDiff_proj (IB := J) (n := ∞)
    (F := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
    (fun y ↦ leviOrthogonalPullback J D f y)).contMDiffAt (x := p₀)
  -- The vectors of the Levi orthogonals, read in the tangent bundle of `M` along `f`.
  have h₁ : ContMDiffAt (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (I.prod 𝓘(ℝ, E)) ∞ (fun p ↦ (⟨f p.proj, p.snd.val.val⟩ : TangentBundle I M)) p₀ :=
    hD.isContMDiffDistribution.contMDiff_totalSpace_inclusion.contMDiffAt.comp p₀
      ((Bundle.Pullback.contMDiffAt_iff f hf.contMDiffAt).1
        (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj
          ).contMDiff_totalSpace_inclusion.contMDiffAt).2
  -- Their images under the tangent map of `F`, read in `D₁` along `g` and then in `g^* D₁`.
  have h₂ : ContMDiffAt (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (I₁.prod 𝓘(ℝ, E₁)) ∞
      (fun p ↦ (⟨g p.proj, (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf p.proj
        p.snd).val.val⟩ : TangentBundle I₁ M₁)) p₀ :=
    ((hF.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp p₀ h₁).congr_of_eventuallyEq
      (.of_forall fun p ↦ congrArg (TotalSpace.mk (F (f p.proj)))
        (leviOrthogonalPullbackMap_apply hD hD₁ hF hFx hFD hFD' hf p.proj p.snd))
  have h₃ := hD₁.isContMDiffDistribution.contMDiffAt_totalSpace_mk h₂
    fun p ↦ (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf p.proj p.snd).val.property
  have h₄ : ContMDiffAt (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - 1) → ℝ)) ∞ (fun p ↦ TotalSpace.mk'
        (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x) p.proj
        (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf p.proj p.snd).val) p₀ :=
    (Bundle.Pullback.contMDiffAt_iff g hg.contMDiffAt).2 ⟨hproj, h₃⟩
  exact (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj
    ).contMDiffAt_totalSpace_mk le_rfl h₄
      fun p ↦ (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf p.proj p.snd).property

/-- **Contactomorphisms induce smooth maps of conformal symplectic normal bundles.** Let
`f` be a smooth isotropic immersion of a nonempty manifold into `(M, D)`, and let `F : M → M₁` be
a smooth map carrying the smooth contact structure `D` onto `D₁` along `f`: its differential at
each `f y` is invertible and maps `D (f y)` into `D₁ (F (f y))`, and near `f y` the inverse
differentials map `D₁ (F z)` into `D z`. Then `F ∘ f` is again an isotropic immersion
(`TauCeti.IsHorizontalMap.comp_left`, `TauCeti.injective_mfderiv_comp`), and the map
`(y, [u]) ↦ (y, [dF u])` from the conformal symplectic normal bundle of `f` to that of `F ∘ f`
(`TauCeti.conformalSymplecticNormalPrebundle`), which is the isomorphism
`TauCeti.conformalSymplecticNormalEquiv` on each fibre, is smooth on total spaces. -/
theorem contMDiff_totalSpace_conformalSymplecticNormalEquiv [Nonempty N]
    (hD : IsContactDistribution I ∞ D) (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : K}
    (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf)
      (hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (g := F) (hFx y).injective (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf)
      (hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (g := F) (hFx y).injective (hinj y)).toFiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
          (fun y ↦ ConformalSymplecticNormal J D f y) ↦
        TotalSpace.mk' (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
          (E := fun y ↦ ConformalSymplecticNormal J D₁
            (ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) y) p.proj
          (conformalSymplecticNormalEquiv J D f p.proj
            (hD.isContMDiffDistribution.of_le (by simp))
            (hD₁.isContMDiffDistribution.of_le (by simp)) hF.contMDiffAt
            (n := ∞) (by simp) (hFx _) (hFD _) (hFD' _)
            (hf.mdifferentiableAt (by simp)) p.snd)) := by
  obtain ⟨hgD, hginj⟩ := isHorizontalMap_comp_and_injective_mfderiv_comp hF hFx hFD hf hfD hinj
  set g := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous
  have hg : ContMDiff J I₁ ∞ g := hF.comp hf
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
  let := hD₁.isContMDiffDistribution.fiberBundle
  let := hD₁.isContMDiffDistribution.vectorBundle
  have := hD₁.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E₁ - 1) → ℝ)
    (E := fun x ↦ D₁ x) (IB := I₁) (IB' := J) hg
  let := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
    (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD₁ hg hgD hginj
  rw [conformalSymplecticNormalPrebundle_eq hD hf hfD hinj,
    conformalSymplecticNormalPrebundle_eq hD₁ hg hgD hginj]
  -- The map of conformal symplectic normal spaces is induced by the map of Levi orthogonals.
  have hT := hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj
  have hT₁ := hasLocalContMDiffSubbundleFrames_comap_range hD₁ hg hgD hginj
  have hκ := hfD.card_add_card_eq_finrank hD hf hinj
  have hκ₁ := hgD.card_add_card_eq_finrank hD₁ hg hginj
  let := (hT.quotientPrebundle hκ).totalSpaceTopology
  let := (hT.quotientPrebundle hκ).toFiberBundle
  let := (hT₁.quotientPrebundle hκ₁).totalSpaceTopology
  let := (hT₁.quotientPrebundle hκ₁).toFiberBundle
  refine (hT.contMDiff_totalSpace_mapQ hκ hT₁ hκ₁ (f := id)
    (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf)
    (le_comap_leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf)
    (contMDiff_totalSpace_leviOrthogonalPullbackMap hD hD₁ hf hfD hinj hF hFx hFD
      hFD')).congr fun p ↦ ?_
  obtain ⟨y, a⟩ := p
  induction a using Submodule.Quotient.induction_on with
  | H u =>
    refine congrArg (TotalSpace.mk y) ((conformalSymplecticNormalEquiv_mk _ _ _ _ _ _ _ _ u
      (leviOrthogonalPullbackMap hD hD₁ hF hFx hFD hFD' hf y u)
      (leviOrthogonalPullbackMap_apply hD hD₁ hF hFx hFD hFD' hf y u)).trans ?_)
    -- After `mapQ_apply`, the two sides differ only by the projection `⟨y, [u]⟩.proj = y`.
    rw [Submodule.mapQ_apply]
    rfl

/-- **Contactomorphisms induce isomorphisms of conformal symplectic normal bundles.** Under the
hypotheses of `TauCeti.contMDiff_totalSpace_conformalSymplecticNormalEquiv`, the map
`(y, [u]) ↦ (y, [dF u])` from the conformal symplectic normal bundle of `f` to that of `F ∘ f` is a
smooth diffeomorphism of total spaces, linear on each fibre: a smooth isomorphism of vector bundles
over `N`, conformally symplectic on each fibre
(`TauCeti.conformalSymplecticNormalForm_conformalSymplecticNormalEquiv`). -/
theorem exists_bundleDiffeomorph_conformalSymplecticNormalEquiv [Nonempty N]
    (hD : IsContactDistribution I ∞ D) (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : K}
    (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) (hF : ContMDiff I I₁ ∞ F)
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toVectorBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf)
      (hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (g := F) (hFx y).injective (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf)
      (hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (g := F) (hFx y).injective (hinj y)).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf)
      (hfD.comp_left (fun _ ↦ hF.mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (g := F) (hFx y).injective (hinj y)).toVectorBundle
    ∃ Φ : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
        (fun y ↦ ConformalSymplecticNormal J D f y) ≃ₘ^∞⟮
          J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ),
          J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)⟯
        TotalSpace (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
          (fun y ↦ ConformalSymplecticNormal J D₁
            (ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) y),
      ∀ p, Φ p = TotalSpace.mk' (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
          (E := fun y ↦ ConformalSymplecticNormal J D₁
            (ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) y) p.proj
          (conformalSymplecticNormalEquiv J D f p.proj
            (hD.isContMDiffDistribution.of_le (by simp))
            (hD₁.isContMDiffDistribution.of_le (by simp)) hF.contMDiffAt
            (n := ∞) (by simp) (hFx _) (hFD _) (hFD' _)
            (hf.mdifferentiableAt (by simp)) p.snd) := by
  obtain ⟨hgD, hginj⟩ := isHorizontalMap_comp_and_injective_mfderiv_comp hF hFx hFD hf hfD hinj
  let := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
  let := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
  let := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toVectorBundle
  let := (conformalSymplecticNormalPrebundle hD₁
    (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf) hgD
      hginj).totalSpaceTopology
  let := (conformalSymplecticNormalPrebundle hD₁
    (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf) hgD
      hginj).toFiberBundle
  let := (conformalSymplecticNormalPrebundle hD₁
    (f := ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) (hF.comp hf) hgD
      hginj).toVectorBundle
  -- The fibres are finite-dimensional Hausdorff topological vector spaces, so the linear
  -- isomorphisms of fibres are continuous.
  let e (y : N) := by
    have := VectorBundle.isTopologicalAddGroup ℝ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) y
    have := VectorBundle.continuousSMul ℝ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) y
    have := FiberBundle.t2Space (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) y
    have := VectorBundle.finiteDimensional ℝ (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) y
    have := VectorBundle.isTopologicalAddGroup ℝ
      (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D₁
        (ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) y) y
    have := VectorBundle.continuousSMul ℝ (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D₁
        (ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) y) y
    have := FiberBundle.t2Space (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D₁
        (ContinuousMap.mk (F ∘ f) (hF.comp hf).continuous) y) y
    exact (conformalSymplecticNormalEquiv J D f y (hD.isContMDiffDistribution.of_le (by simp))
      (hD₁.isContMDiffDistribution.of_le (by simp)) hF.contMDiffAt (n := ∞) (by simp) (hFx _)
      (hFD _) (hFD' _) (hf.mdifferentiableAt (by simp))).toContinuousLinearEquiv
  -- `e y` is the fibre isomorphism made continuous by `LinearEquiv.toContinuousLinearEquiv`, the
  -- same function by definition (`LinearEquiv.coe_toContinuousLinearEquiv'`). That lemma needs the
  -- fibre instances installed only inside `e`, so the last step is closed by `rfl`.
  exact ⟨bundleDiffeomorph e (contMDiff_totalSpace_conformalSymplecticNormalEquiv hD hD₁ hf hfD
    hinj hF hFx hFD hFD'), fun p ↦ (bundleDiffeomorph_apply _ _ p).trans rfl⟩

end Bundle

end TauCeti
