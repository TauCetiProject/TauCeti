/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ConformalSymplecticNormal.Bundle
public import TauCeti.Geometry.Manifold.Distribution.Levi.Bundle
public import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# The smooth structure maps of the conformal symplectic normal bundle

Let `f : N → M` be a smooth isotropic immersion of a nonempty manifold into a smooth contact
manifold `(M, D)`, with conformal symplectic normal bundle `CSN(f)`, the smooth vector bundle of
the spaces `(T_y N)^⊥ ⧸ T_y N` (`TauCeti.conformalSymplecticNormalPrebundle`). Its fibres carry
the nondegenerate form induced by the Levi form, with values in the contact line `L = TM ⧸ D`
(`TauCeti.conformalSymplecticNormalForm`), and a map `F` carrying `D` to a second contact
structure `D₁` induces isomorphisms of the fibres onto those of `CSN(F ∘ f)`
(`TauCeti.conformalSymplecticNormalEquiv`). This file shows that both are smooth bundle maps, so
that `CSN(f)` is a smooth conformal symplectic vector bundle with values in the pullback of `L`,
natural under contactomorphisms. These are the normal data of the isotropic neighbourhood theorem.

* **The form.** The form of two smooth local sections of `CSN(f)` is a smooth section of the
  contact line along `f` (`TauCeti.contMDiffOn_conformalSymplecticNormalForm`). Near each point
  the sections are classes of smooth sections of the bundle of Levi orthogonals
  (`TauCeti.HasLocalContMDiffSubbundleFrames.exists_contMDiffOn_mk_eq`), which are sections of
  `D` along `f`, and the Levi form of `D` is a smooth section of `Hom(D, Hom(D, L))`
  (`TauCeti.contMDiff_distributionLeviFormL`).
* **The induced maps.** Let `F : M → M₁` be smooth at the points of `f(N)`, with invertible
  differentials along `f`, mapping `D` into `D₁` along `f` and with inverse differentials mapping
  `D₁` into `D` near `f(N)`, as a contactomorphism between neighbourhoods of `f(N)` and `F(f(N))`
  does. Then the map of total spaces `CSN(f) → CSN(F ∘ f)`, `(y, [u]) ↦ (y, [dF u])`, is smooth
  (`TauCeti.contMDiff_totalSpace_conformalSymplecticNormalEquiv`). It is the map of quotient
  bundles induced by the restriction of the tangent map of `F` to the bundles of Levi orthogonals
  (`TauCeti.restrict_mfderiv_mem_orthogonalBilin`,
  `TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mapQ`).

## Main results

* `TauCeti.contMDiffOn_conformalSymplecticNormalForm`: the line-valued form of two smooth sections
  of the conformal symplectic normal bundle is a smooth section of the contact line along `f`.
* `TauCeti.contMDiff_totalSpace_conformalSymplecticNormalEquiv`: the isomorphisms of conformal
  symplectic normal spaces induced by a map carrying one contact structure to another form a
  smooth map of total spaces.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the conformal symplectic normal bundle and the isotropic neighbourhood
  theorem).
* S. Courte and S. Guillermou, *Introduction to symplectic and contact geometry*, course notes,
  Université Grenoble Alpes (2018), Proposition 3.5, p. 35 (the conformal symplectic normal bundle
  with values in the contact line).
-/

public section

noncomputable section

open Set Filter Function Module Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {K : Type*} [FunLike K N M]
  [ContinuousMapClass K N M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M] in
/-- `C^(∞ + 1)` charts on the target manifold, needed by the smooth vector bundle structure of a
smooth distribution (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`) at smoothness `∞`. -/
local instance instIsManifoldConformalSymplecticNormalSmoothTarget :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space M] in
/-- `C^(∞ + 1 + 1)` charts on the target manifold, the smoothness at which the Levi form of a smooth
distribution is a smooth section (`TauCeti.contMDiff_distributionLeviFormL`) at smoothness `∞`. -/
local instance instIsManifoldConformalSymplecticNormalSmoothTarget' :
    IsManifold I ((∞ : WithTop ℕ∞) + 1 + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

omit [FiniteDimensional ℝ E'] in
/-- `C^(∞ + 1)` charts on the source manifold, as for the target. -/
local instance instIsManifoldConformalSymplecticNormalSmoothSource :
    IsManifold J ((∞ : WithTop ℕ∞) + 1) N :=
  IsManifold.of_le (n := ∞) (by simp)

/-- A point of the bundle of Levi orthogonals of `f` is a vector of `D` over its image under `f`:
the map of total spaces `(y, u) ↦ (f y, u)` into `D` is smooth. -/
private theorem contMDiff_totalSpace_leviOrthogonalPullback (hD : IsContactDistribution I ∞ D)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (I.prod 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
          (fun y ↦ leviOrthogonalPullback J D f y) ↦
        TotalSpace.mk' (Fin (finrank ℝ E - 1) → ℝ) (E := fun x ↦ D x) (f p.proj)
          (p.snd : (f *ᵖ fun x ↦ D x) p.proj)) := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  have hW := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj
  let := hW.fiberBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  exact (Bundle.Pullback.contMDiff_lift f hf).comp hW.contMDiff_totalSpace_inclusion

/-- **The form on the conformal symplectic normal bundle is smooth.** Let `f : N → M` be a smooth
isotropic immersion of a nonempty manifold into a smooth contact manifold `(M, D)`, and let `s`,
`t` be smooth sections of its conformal symplectic normal bundle on an open set `U`. Then their
line-valued form `y ↦ ω_y (s y, t y)` (`TauCeti.conformalSymplecticNormalForm`) is a smooth
section of the contact line `TM ⧸ D` along `f` on `U`, the contact line carrying its bundle
structure as a quotient of `TM` (of rank `r = 1`). -/
theorem contMDiffOn_conformalSymplecticNormalForm [Nonempty N]
    (hD : IsContactDistribution I ∞ D) {r : ℕ} (hr : finrank ℝ E - 1 + r = finrank ℝ E)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) {U : Set N} (hU : IsOpen U)
    {s t : Π y, ConformalSymplecticNormal J D f y}
    (hs : letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
      letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
      ContMDiffOn J (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
          (E := fun y ↦ ConformalSymplecticNormal J D f y) y (s y)) U)
    (ht : letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
      letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
      ContMDiffOn J (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)) ∞
        (fun y ↦ TotalSpace.mk' (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
          (E := fun y ↦ ConformalSymplecticNormal J D f y) y (t y)) U) :
    letI := (hD.isContMDiffDistribution.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.isContMDiffDistribution.quotientPrebundle hr).toFiberBundle
    ContMDiffOn J (I.prod 𝓘(ℝ, Fin r → ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (Fin r → ℝ) (E := fun x ↦ TangentSpace I x ⧸ D x) (f y)
        (conformalSymplecticNormalForm J D f y (s y) (t y))) U := by
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  let := (hD.isContMDiffDistribution.quotientPrebundle hr).totalSpaceTopology
  let := (hD.isContMDiffDistribution.quotientPrebundle hr).toFiberBundle
  let := (hD.isContMDiffDistribution.quotientPrebundle hr).toVectorBundle
  -- The Levi forms along `f`.
  have hL := (contMDiff_distributionLeviFormL (n := ∞) hD.isContMDiffDistribution hr).comp hf
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  have hW := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj
  let := hW.fiberBundle
  let := hW.vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
  have hV := hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj
  have hκ := hfD.card_add_card_eq_finrank hD hf hinj
  rw [conformalSymplecticNormalPrebundle_eq hD hf hfD hinj] at hs ht
  -- Near each point, `s` and `t` are classes of smooth sections `σ` and `τ` of the bundle of
  -- Levi orthogonals, which are sections of `D` along `f`.
  have hlift := contMDiff_totalSpace_leviOrthogonalPullback hD hf hfD hinj
  intro y₀ hy₀
  obtain ⟨U₁, hU₁, hy₁, -, σ, hσ, hσs⟩ := hV.exists_contMDiffOn_mk_eq hκ hU hs hy₀
  obtain ⟨U₂, hU₂, hy₂, -, τ, hτ, hτt⟩ := hV.exists_contMDiffOn_mk_eq hκ hU ht hy₀
  -- The Levi form of the lifts is smooth.
  have hLf : ContMDiffOn J
      (I.prod 𝓘(ℝ, (Fin (finrank ℝ E - 1) → ℝ) →L[ℝ] (Fin (finrank ℝ E - 1) → ℝ) →L[ℝ]
        (Fin r → ℝ))) ∞
      (fun y ↦ TotalSpace.mk' ((Fin (finrank ℝ E - 1) → ℝ) →L[ℝ] (Fin (finrank ℝ E - 1) → ℝ) →L[ℝ]
        (Fin r → ℝ)) (E := fun x ↦ D x →L[ℝ] D x →L[ℝ] TangentSpace I x ⧸ D x) (f y)
        (distributionLeviFormL D (f y))) (U₁ ∩ U₂) :=
    hL.contMDiffOn
  have hστ := hLf.clm_bundle_apply₂ (F₁ := Fin (finrank ℝ E - 1) → ℝ)
    (F₂ := Fin (finrank ℝ E - 1) → ℝ) (F₃ := Fin r → ℝ) (E₁ := fun x ↦ D x)
    (E₂ := fun x ↦ D x) (E₃ := fun x ↦ TangentSpace I x ⧸ D x)
    ((hlift.comp_contMDiffOn hσ).mono inter_subset_left)
    ((hlift.comp_contMDiffOn hτ).mono inter_subset_right)
  -- On `U₁ ∩ U₂` the form is the Levi form of the lifts.
  have hval {y : N} (hy : y ∈ U₁ ∩ U₂) :
      conformalSymplecticNormalForm J D f y (s y) (t y) =
        distributionLeviFormL D (f y) (σ y : (f *ᵖ fun x ↦ D x) y)
          (τ y : (f *ᵖ fun x ↦ D x) y) := by
    rw [← hσs y hy.1, ← hτt y hy.2]
    exact (conformalSymplecticNormalForm_mk (σ y) (τ y)).trans
      (distributionLeviFormL_apply _ _ _).symm
  refine (hστ.contMDiffAt ((hU₁.inter hU₂).mem_nhds ⟨hy₁, hy₂⟩)
    ).contMDiffWithinAt.congr_of_eventuallyEq ?_ (by rw [hval ⟨hy₁, hy₂⟩])
  filter_upwards [nhdsWithin_le_nhds ((hU₁.inter hU₂).mem_nhds ⟨hy₁, hy₂⟩)] with y hy
  rw [hval hy]

section Map

variable {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [FiniteDimensional ℝ E₁] [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁] [T2Space M₁]
  {D₁ : Π x : M₁, Submodule ℝ (TangentSpace I₁ x)} {F : M → M₁}

omit [CompleteSpace E₁] [FiniteDimensional ℝ E₁] [T2Space M₁] in
/-- `C^(∞ + 1)` charts on the second target manifold, as for the first. -/
local instance instIsManifoldConformalSymplecticNormalSmoothTarget₁ :
    IsManifold I₁ ((∞ : WithTop ℕ∞) + 1) M₁ :=
  IsManifold.of_le (n := ∞) (by simp)

/-- The restriction of `dF` to the Levi orthogonals of the tangent images of `f` and `F ∘ f`
(`TauCeti.restrict_mfderiv_mem_orthogonalBilin`). -/
private def leviOrthogonalMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : N → M} (hf : ContMDiff J I ∞ f)
    (hF : ∀ y, ContMDiffAt I I₁ ∞ F (f y)) (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) (y : N) :
    leviOrthogonalPullback J D f y →ₗ[ℝ] leviOrthogonalPullback J D₁ (F ∘ f) y :=
  ((mfderiv I I₁ F (f y)).toLinearMap.restrict (hFD y)).restrict fun _ hu ↦
    restrict_mfderiv_mem_orthogonalBilin (hD.isContMDiffDistribution.of_le (by simp))
      (hD₁.isContMDiffDistribution.of_le (by simp)) (hF y) (by simp) (hFx y) (hFD y)
      (hFD' y) (hf.mdifferentiableAt (by simp)) hu

omit [T2Space M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space M₁] in
/-- The restriction of `dF` to the Levi orthogonals is `dF` on the underlying tangent vectors. -/
private theorem leviOrthogonalMap_coe_apply (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : N → M} (hf : ContMDiff J I ∞ f)
    (hF : ∀ y, ContMDiffAt I I₁ ∞ F (f y)) (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) (y : N)
    (u : leviOrthogonalPullback J D f y) :
    ((Subtype.val (leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' y u) : D₁ ((F ∘ f) y)) :
      TangentSpace I₁ ((F ∘ f) y)) =
      mfderiv I I₁ F (f y) ((Subtype.val u : D (f y)) : TangentSpace I (f y)) := by
  -- `LinearMap.coe_restrict_apply` does not match syntactically: the coercions pass through the
  -- pullback fibres `(f *ᵖ D) y` and `((F ∘ f) *ᵖ D₁) y`, which are `D (f y)` and
  -- `D₁ (F (f y))` only up to unfolding the pullback.
  rfl

omit [T2Space M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space M₁] in
/-- The restriction of `dF` to the Levi orthogonals maps tangent images to tangent images. -/
private theorem le_comap_leviOrthogonalMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : N → M} (hf : ContMDiff J I ∞ f)
    (hF : ∀ y, ContMDiffAt I I₁ ∞ F (f y)) (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) (y : N) :
    ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype ≤
      (((LinearMap.range (mfderiv J I₁ (F ∘ f) y).toLinearMap).comap
        (D₁ ((F ∘ f) y)).subtype).comap (leviOrthogonalPullback J D₁ (F ∘ f) y).subtype).comap
          (leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' y) := by
  rintro u ⟨w, hw⟩
  refine ⟨w, ?_⟩
  simp only [ContinuousLinearMap.coe_coe] at hw ⊢
  rw [mfderiv_comp y ((hF y).mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)),
    ContinuousLinearMap.comp_apply, hw]
  exact (leviOrthogonalMap_coe_apply hD hD₁ hf hF hFx hFD hFD' y u).symm

/-- The restriction of `dF` to the Levi orthogonals is a smooth map of total spaces: it is the
tangent map of `F`, read on the bundles of Levi orthogonals. -/
private theorem contMDiff_totalSpace_leviOrthogonalMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : K} (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y))
    (hF : ∀ y, ContMDiffAt I I₁ ∞ F (f y)) (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) :
    letI g : C(N, M₁) := ⟨F ∘ f, (ContMDiff.continuous fun y ↦ (hF y).comp y (hf y))⟩
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := hD₁.isContMDiffDistribution.fiberBundle
    letI := hD₁.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    letI := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
      (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin (f := g) hD₁
      (fun y ↦ (hF y).comp y (hf y))
      (hfD.comp_left (fun y ↦ (hF y).mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      (fun y ↦ injective_mfderiv_comp (f := f) (g := F) ((hF y).mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp)) (hFx y).injective (hinj y))).fiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
          (fun y ↦ leviOrthogonalPullback J D f y) ↦
        (⟨p.proj, leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' p.proj p.snd⟩ :
          TotalSpace (Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ)
            (fun y ↦ leviOrthogonalPullback J D₁ g y))) := by
  let g : C(N, M₁) := ⟨F ∘ f, (ContMDiff.continuous fun y ↦ (hF y).comp y (hf y))⟩
  have hg : ContMDiff J I₁ ∞ g := fun y ↦ (hF y).comp y (hf y)
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  let := hD₁.isContMDiffDistribution.fiberBundle
  let := hD₁.isContMDiffDistribution.vectorBundle
  have := hD₁.isContMDiffDistribution.contMDiffVectorBundle
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
    (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
  have hW₁ := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg
    (hfD.comp_left (fun y ↦ (hF y).mdifferentiableAt (by simp))
      (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD) fun y ↦ injective_mfderiv_comp (f := f) (g := F)
        ((hF y).mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)) (hFx y).injective
        (hinj y)
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E₁ - 1) → ℝ)
    (E := fun x ↦ D₁ x) (IB := I₁) (IB' := J) hg
  -- The tangent map of `F` on the vectors of the Levi orthogonals of `f`.
  have hinc := hD.isContMDiffDistribution.contMDiff_totalSpace_inclusion.comp
    (contMDiff_totalSpace_leviOrthogonalPullback hD hf hfD hinj)
  -- Its values lie in `D₁`, then in the Levi orthogonals of `F ∘ f`.
  refine hW₁.contMDiff_totalSpace_mk le_rfl ?_ fun p ↦
    (leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' p.proj p.snd).property
  refine (Bundle.Pullback.contMDiff_iff g hg).2 ⟨Bundle.contMDiff_proj _, fun p ↦ ?_⟩
  exact hD₁.isContMDiffDistribution.contMDiffAt_totalSpace_mk
    (((hF p.proj).contMDiffAt_tangentMap (m := ∞) (by simp)).comp p (hinc p)) fun p ↦
    ((leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' p.proj p.snd :
      (g *ᵖ fun x ↦ D₁ x) p.proj) : D₁ (g p.proj)).property

omit [T2Space M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space M₁] in
/-- The isomorphism of conformal symplectic normal spaces induced by `F` is the map of quotients
induced by the restriction of `dF` to the Levi orthogonals. -/
private theorem conformalSymplecticNormalEquiv_eq_mapQ (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) {f : N → M} (hf : ContMDiff J I ∞ f)
    (hF : ∀ y, ContMDiffAt I I₁ ∞ F (f y)) (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) (y : N)
    (a : ConformalSymplecticNormal J D f y) :
    conformalSymplecticNormalEquiv J D f y (hD.isContMDiffDistribution.of_le (by simp))
        (hD₁.isContMDiffDistribution.of_le (by simp)) (hF y) (by simp) (hFx y) (hFD y)
        (hFD' y) (hf.mdifferentiableAt (by simp)) a =
      Submodule.mapQ _ _ (leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' y)
        (le_comap_leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' y) a := by
  induction a using Submodule.Quotient.induction_on with
  | H u =>
    exact (conformalSymplecticNormalEquiv_mk _ _ _ _ _ _ _ _ u
      (leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD' y u)
      (leviOrthogonalMap_coe_apply hD hD₁ hf hF hFx hFD hFD' y u)).trans
        (Submodule.mapQ_apply _ _ _ _).symm

/-- **Contactomorphisms induce smooth maps of conformal symplectic normal bundles.** Let
`f : N → M` be a smooth isotropic immersion of a nonempty manifold into a smooth contact manifold
`(M, D)`, and let `F : M → M₁` be a map into a second smooth contact manifold `(M₁, D₁)`, smooth
at every `f y`, with invertible differentials along `f`, mapping `D (f y)` into `D₁ (F (f y))`, and
whose inverse differentials map `D₁` into `D` near every `f y`; a contactomorphism between open
neighbourhoods of `f(N)` and `F(f(N))` is the main example. Then `F ∘ f` (written `g`, as a
continuous map) is again a smooth isotropic immersion, and the isomorphisms `[u] ↦ [dF u]` of
conformal symplectic normal spaces (`TauCeti.conformalSymplecticNormalEquiv`) form a smooth map of
total spaces `CSN(f) → CSN(F ∘ f)` over the identity of `N`. -/
theorem contMDiff_totalSpace_conformalSymplecticNormalEquiv [Nonempty N]
    (hD : IsContactDistribution I ∞ D) (hD₁ : IsContactDistribution I₁ ∞ D₁)
    {f : K} (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f)
    (hinj : ∀ y, Injective (mfderiv J I f y)) (hF : ∀ y, ContMDiffAt I I₁ ∞ F (f y))
    (hFx : ∀ y, (mfderiv I I₁ F (f y)).IsInvertible)
    (hFD : ∀ y, ∀ u ∈ D (f y), mfderiv I I₁ F (f y) u ∈ D₁ (F (f y)))
    (hFD' : ∀ y, ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (F z), (mfderiv I I₁ F z).inverse v ∈ D z) :
    letI g : C(N, M₁) := ⟨F ∘ f, (ContMDiff.continuous fun y ↦ (hF y).comp y (hf y))⟩
    letI P := conformalSymplecticNormalPrebundle hD hf hfD hinj
    letI P₁ := conformalSymplecticNormalPrebundle (f := g) hD₁ (fun y ↦ (hF y).comp y (hf y))
      (hfD.comp_left (fun y ↦ (hF y).mdifferentiableAt (by simp))
        (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD)
      fun y ↦ injective_mfderiv_comp (f := f) (g := F) ((hF y).mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp)) (hFx y).injective (hinj y)
    letI := P.totalSpaceTopology
    letI := P.toFiberBundle
    letI := P₁.totalSpaceTopology
    letI := P₁.toFiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
          (fun y ↦ ConformalSymplecticNormal J D f y) ↦
        (⟨p.proj, conformalSymplecticNormalEquiv J D f p.proj
          (hD.isContMDiffDistribution.of_le (by simp))
          (hD₁.isContMDiffDistribution.of_le (by simp)) (hF p.proj) (by simp) (hFx p.proj)
          (hFD p.proj) (hFD' p.proj) (hf.mdifferentiableAt (by simp)) p.snd⟩ :
        TotalSpace (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
          (fun y ↦ ConformalSymplecticNormal J D₁ g y))) := by
  let g : C(N, M₁) := ⟨F ∘ f, (ContMDiff.continuous fun y ↦ (hF y).comp y (hf y))⟩
  have hg : ContMDiff J I₁ ∞ g := fun y ↦ (hF y).comp y (hf y)
  have hgD : IsHorizontalMap J D₁ g := hfD.comp_left (fun y ↦ (hF y).mdifferentiableAt (by simp))
    (fun _ ↦ hf.mdifferentiableAt (by simp)) hFD
  have hginj : ∀ y, Injective (mfderiv J I₁ g y) := fun y ↦ injective_mfderiv_comp (g := F)
    ((hF y).mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)) (hFx y).injective (hinj y)
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  let := hD₁.isContMDiffDistribution.fiberBundle
  let := hD₁.isContMDiffDistribution.vectorBundle
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
  let := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
    (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD₁ hg hgD hginj
  have hV := hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj
  have hV₁ := hasLocalContMDiffSubbundleFrames_comap_range hD₁ hg hgD hginj
  have hκ := hfD.card_add_card_eq_finrank hD hf hinj
  have hκ₁ := hgD.card_add_card_eq_finrank hD₁ hg hginj
  -- Both bundles are quotients of bundles of Levi orthogonals, and the map is induced by the
  -- smooth restriction of `dF` to them.
  have hmapQ := hV.contMDiff_totalSpace_mapQ hκ hV₁ hκ₁ (f := id)
    (leviOrthogonalMap hD hD₁ hf hF hFx hFD hFD') (le_comap_leviOrthogonalMap hD hD₁ hf hF hFx
      hFD hFD') (contMDiff_totalSpace_leviOrthogonalMap hD hD₁ hf hfD hinj hF hFx hFD hFD')
  let := (hV.quotientPrebundle hκ).totalSpaceTopology
  let := (hV.quotientPrebundle hκ).toFiberBundle
  let := (hV₁.quotientPrebundle hκ₁).totalSpaceTopology
  let := (hV₁.quotientPrebundle hκ₁).toFiberBundle
  have h := hmapQ.congr (f₁ := fun p : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ leviOrthogonalPullback J D f y ⧸
        ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
          (leviOrthogonalPullback J D f y).subtype) ↦
    (⟨p.proj, conformalSymplecticNormalEquiv J D f p.proj
      (hD.isContMDiffDistribution.of_le (by simp))
      (hD₁.isContMDiffDistribution.of_le (by simp)) (hF p.proj) (by simp) (hFx p.proj)
      (hFD p.proj) (hFD' p.proj) (hf.mdifferentiableAt (by simp)) p.snd⟩ :
      TotalSpace (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
        (fun y ↦ leviOrthogonalPullback J D₁ g y ⧸
          ((LinearMap.range (mfderiv J I₁ g y).toLinearMap).comap (D₁ (g y)).subtype).comap
            (leviOrthogonalPullback J D₁ g y).subtype)))
    fun p ↦ congrArg (TotalSpace.mk p.proj)
      (conformalSymplecticNormalEquiv_eq_mapQ hD hD₁ hf hF hFx hFD hFD' p.proj p.snd)
  rw [conformalSymplecticNormalPrebundle_eq hD hf hfD hinj,
    conformalSymplecticNormalPrebundle_eq hD₁ hg hgD hginj]
  exact h

end Map

end TauCeti
