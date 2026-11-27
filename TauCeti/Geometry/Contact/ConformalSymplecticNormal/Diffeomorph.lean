/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ConformalSymplecticNormal.Bundle
public import TauCeti.Geometry.Manifold.Distribution.Horizontal

/-!
# The conformal symplectic normal bundle under contactomorphisms

Let `D` and `D₁` be smooth contact structures on Hausdorff manifolds `M` and `M₁`, and let
`Φ : M ≃ M₁` be a contactomorphism: a smooth diffeomorphism whose differential carries `D` onto
`D₁`, `v ∈ D x ↔ dΦ_x v ∈ D₁ (Φ x)`. For a contactomorphism between open neighbourhoods of two
isotropic submanifolds, take `M` and `M₁` to be these open subsets. Let `f : N → M` be a smooth
isotropic immersion of a nonempty manifold. Then `Φ ∘ f` is again a smooth isotropic immersion,
and this file shows that `Φ` induces an isomorphism of smooth vector bundles over `N` between their
conformal symplectic normal bundles (`TauCeti.conformalSymplecticNormalPrebundle`):

`CSN(f) ≃ CSN(Φ ∘ f)`, `[u] ↦ [dΦ u]`

(`TauCeti.conformalSymplecticNormalDiffeomorph`), a smooth diffeomorphism of total spaces covering
the identity of `N` and linear on each fibre. Its fibre maps are the isomorphisms
`TauCeti.conformalSymplecticNormalEquiv` of conformal symplectic normal spaces
(`TauCeti.conformalSymplecticNormalDiffeomorph_apply`), which are conformally symplectic for the
line-valued forms induced by the Levi forms, up to the isomorphism of contact lines induced by
`dΦ` (`TauCeti.conformalSymplecticNormalForm_conformalSymplecticNormalEquiv`), and compatible with
composition (`TauCeti.conformalSymplecticNormalEquiv_trans`). These are the normal data that the
isotropic neighbourhood theorem compares.

**Smoothness.** The conformal symplectic normal bundle of `f` is the quotient of the bundle of
Levi orthogonals of the tangent images, a smooth subbundle of `f^* D`, by the tangent images
(`TauCeti.conformalSymplecticNormalPrebundle_eq`). The differential of `Φ` maps Levi orthogonals
into Levi orthogonals (`TauCeti.mfderiv_mem_leviOrthogonal`) and tangent images of `f` into tangent
images of `Φ ∘ f`. Read in `TM` and `TM₁`, the induced map of Levi orthogonal bundles is the tangent
map of `Φ`, hence smooth, and the map of quotient bundles is smooth by functoriality of quotient
bundles (`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mapQ`). Its inverse is
smooth because the fibres have finite rank (`TauCeti.bundleDiffeomorph`).

No contact form or coorientation is chosen, so the construction applies to contact structures that
are not the kernel of any global one-form.

## Main definitions

* `TauCeti.conformalSymplecticNormalDiffeomorph`: the smooth bundle isomorphism
  `CSN(f) ≃ CSN(Φ ∘ f)` induced by a contactomorphism `Φ`.

## Main results

* `TauCeti.conformalSymplecticNormalDiffeomorph_mk`: it sends the class of `u` to the class of
  `dΦ u`.
* `TauCeti.conformalSymplecticNormalDiffeomorph_apply`,
  `TauCeti.conformalSymplecticNormalDiffeomorph_symm_apply`: its fibre maps and their inverses are
  the isomorphisms `TauCeti.conformalSymplecticNormalEquiv` and their inverses.

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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ ∞ M₁] [T2Space M₁]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {D₁ : Π x : M₁, Submodule ℝ (TangentSpace I₁ x)}
  {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

/-- `C^(∞ + 1)` charts on `M`, needed by the smooth vector bundle structure of a smooth
distribution (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle`) at smoothness `∞`. -/
local instance instIsManifoldConformalSymplecticNormalDiffeomorphSource :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts on `M₁`, as for `M`. -/
local instance instIsManifoldConformalSymplecticNormalDiffeomorphTarget :
    IsManifold I₁ ((∞ : WithTop ℕ∞) + 1) M₁ :=
  IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts on `N`, as for `M`. -/
local instance instIsManifoldConformalSymplecticNormalDiffeomorphBase :
    IsManifold J ((∞ : WithTop ℕ∞) + 1) N :=
  IsManifold.of_le (n := ∞) (by simp)

/-! ### The map of Levi orthogonal bundles -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ E₁]
  [IsManifold I₁ ∞ M₁] [T2Space M₁] in
/-- Near every point, the inverse differentials of a diffeomorphism carrying `D` onto `D₁` carry
`D₁` back into `D`, as `TauCeti.conformalSymplecticNormalEquiv` requires. -/
private theorem eventually_inverse_mfderiv_mem (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) (x : M) :
    ∀ᶠ z in 𝓝 x, ∀ v ∈ D₁ (Φ z), (mfderiv I I₁ Φ z).inverse v ∈ D z :=
  Eventually.of_forall fun z _ hv ↦ (hΦD z _).2 <| by
    rwa [(Φ.isInvertible_mfderiv (by simp)).self_apply_inverse]

variable (J) in
/-- The restriction of the differential of `Φ` to the Levi orthogonals of the tangent images of
`f` and of `Φ ∘ f`, read in the pullbacks of the contact structures. -/
private def leviOrthogonalPullbackMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K} (hf : ContMDiff J I ∞ f)
    (y : N) :
    leviOrthogonalPullback J D f y →ₗ[ℝ]
      leviOrthogonalPullback J D₁ (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y :=
  (((mfderiv I I₁ Φ (f y)).toLinearMap.restrict fun v hv ↦ (hΦD _ v).1 hv) ∘ₗ
    (leviOrthogonalPullback J D f y).subtype).codRestrict _ fun u ↦
      mem_leviOrthogonalPullback_iff.2 <| mfderiv_mem_leviOrthogonal (F := Φ)
        (hD.isContMDiffDistribution.of_le (m := 1) (by simp))
        (hD₁.isContMDiffDistribution.of_le (m := 1) (by simp)) Φ.contMDiff.contMDiffAt (by simp)
        (Φ.isInvertible_mfderiv (by simp)) (fun v hv ↦ (hΦD _ v).1 hv)
        (eventually_inverse_mfderiv_mem Φ hΦD _) (hf.mdifferentiableAt (by simp)) <|
          mem_leviOrthogonalPullback_iff.1 u.property

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space M] [T2Space M₁] in
/-- Read in the tangent spaces, the map of Levi orthogonals induced by `Φ` is the differential
of `Φ`. -/
private theorem coe_leviOrthogonalPullbackMap_apply (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K} (hf : ContMDiff J I ∞ f)
    (y : N) (u : leviOrthogonalPullback J D f y) :
    (D₁ (Φ (f y))).subtype (leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf y u).val =
      mfderiv I I₁ Φ (f y) ((D (f y)).subtype u.val) :=
  (rfl)

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space M] [T2Space M₁] in
/-- The map of Levi orthogonals induced by `Φ` carries the tangent images of `f` into those of
`Φ ∘ f`. -/
private theorem comap_range_le_comap_leviOrthogonalPullbackMap (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K} (hf : ContMDiff J I ∞ f)
    (y : N) :
    ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).comap
        (leviOrthogonalPullback J D f y).subtype ≤
      (((LinearMap.range (mfderiv J I₁
          (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y).toLinearMap).comap
        (D₁ (Φ (f y))).subtype).comap (leviOrthogonalPullback J D₁
          (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y).subtype).comap
        (leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf y) := by
  rintro u ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simp only [ContinuousLinearMap.coe_coe] at ha
  exact (mfderiv_comp_apply y (Φ.mdifferentiable (by simp) (f y)) (hf.mdifferentiableAt (by simp))
    a).trans
    ((congrArg _ ha).trans (coe_leviOrthogonalPullbackMap_apply hD hD₁ Φ hΦD hf y u).symm)

/-- The map of Levi orthogonal bundles induced by `Φ` is `C^∞`: read in the tangent bundles, it is
the tangent map of `Φ`. -/
private theorem contMDiff_totalSpace_leviOrthogonalPullbackMap
    (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K} (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := hD.isContMDiffDistribution.fiberBundle
    letI := hD.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
      (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
    letI := hD₁.isContMDiffDistribution.fiberBundle
    letI := hD₁.isContMDiffDistribution.vectorBundle
    letI := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ)
      (E := ((⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) : N → M₁) *ᵖ
        fun x ↦ D₁ x)
      (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ)
      (leviOrthogonalPullback J D₁ (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)))
    letI := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).fiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ)
          (fun y ↦ leviOrthogonalPullback J D f y) ↦
        (⟨p.proj, leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf p.proj p.snd⟩ :
          TotalSpace (Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) fun y ↦
            leviOrthogonalPullback J D₁
              (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y)) := by
  set g : C(N, M₁) := ⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩
  have hg : ContMDiff J I₁ ∞ g := Φ.contMDiff.comp hf
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  have := hD.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E - 1) → ℝ)
    (E := fun x ↦ D x) (IB := I) (IB' := J) hf
  have hW := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := hW.fiberBundle
  let := hD₁.isContMDiffDistribution.fiberBundle
  let := hD₁.isContMDiffDistribution.vectorBundle
  have := hD₁.isContMDiffDistribution.contMDiffVectorBundle
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := Fin (finrank ℝ E₁ - 1) → ℝ)
    (E := fun x ↦ D₁ x) (IB := I₁) (IB' := J) hg
  have hW₁ := hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ (f := g) hg
    ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
    fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)
  let := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
    (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
  let := hW₁.fiberBundle
  -- The inclusion of the Levi orthogonals of `f` into `TM`, followed by the tangent map of `Φ`.
  have hincl := hD.isContMDiffDistribution.contMDiff_totalSpace_inclusion.comp
    ((Bundle.Pullback.contMDiff_lift f hf).comp hW.contMDiff_totalSpace_inclusion)
  have ht := (Φ.contMDiff.contMDiff_tangentMap (m := ∞) le_rfl).comp hincl
  refine hW₁.contMDiff_totalSpace_mk le_rfl ?_ fun p ↦
    (leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf p.proj p.snd).property
  refine (Bundle.Pullback.contMDiff_iff g hg).2 ⟨contMDiff_proj _, fun p ↦ ?_⟩
  exact hD₁.isContMDiffDistribution.contMDiffAt_totalSpace_mk (ht p) fun p ↦
    (leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf p.proj p.snd).val.property

/-! ### The bundle isomorphism of conformal symplectic normal bundles -/

variable (J) in
/-- The isomorphism `[u] ↦ [dΦ u]` of conformal symplectic normal spaces of `f` and `Φ ∘ f` induced
by a diffeomorphism `Φ` carrying `D` onto `D₁`: the fibre maps of
`TauCeti.conformalSymplecticNormalDiffeomorph`. -/
private def csnEquiv (hD : IsContactDistribution I ∞ D) (hD₁ : IsContactDistribution I₁ ∞ D₁)
    (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁) (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) (f : K)
    (hf : ContMDiff J I ∞ f) (y : N) :
    ConformalSymplecticNormal J D f y ≃ₗ[ℝ]
      ConformalSymplecticNormal J D₁ (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y :=
  conformalSymplecticNormalEquiv J D f y (F := Φ)
    (hD.isContMDiffDistribution.of_le (m := 1) (by simp))
    (hD₁.isContMDiffDistribution.of_le (m := 1) (by simp)) Φ.contMDiff.contMDiffAt (by simp)
    (Φ.isInvertible_mfderiv (by simp)) (fun v hv ↦ (hΦD _ v).1 hv)
    (eventually_inverse_mfderiv_mem Φ hΦD _) (hf.mdifferentiableAt (by simp))

omit [FiniteDimensional ℝ E'] [IsManifold J ∞ N] [T2Space M] [T2Space M₁] in
/-- The fibre maps send the class of `u` to the class of its image under `dΦ`. -/
private theorem csnEquiv_mk (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) (f : K) (hf : ContMDiff J I ∞ f)
    (y : N) (u : leviOrthogonalPullback J D f y) :
    csnEquiv J hD hD₁ Φ hΦD f hf y (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf y u) :=
  conformalSymplecticNormalEquiv_mk _ _ _ _ _ _ _ _ _ _ (rfl)

private theorem contMDiff_totalSpace_csnEquiv [Nonempty N] (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K} (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    ContMDiff (J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ))
      (J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)) ∞
      (fun p : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
          (fun y ↦ ConformalSymplecticNormal J D f y) ↦
        TotalSpace.mk' (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
          (E := fun y ↦ ConformalSymplecticNormal J D₁
            (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y)
          p.proj (csnEquiv J hD hD₁ Φ hΦD f hf p.proj p.snd)) := by
  set g : C(N, M₁) := ⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩
  have hg : ContMDiff J I₁ ∞ g := Φ.contMDiff.comp hf
  have hgD : IsHorizontalMap J D₁ g := (isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD
  have hginj (y : N) : Injective (mfderiv J I₁ g y) :=
    (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)
  let := hD.isContMDiffDistribution.fiberBundle
  let := hD.isContMDiffDistribution.vectorBundle
  let := subbundleTopology (Fin (finrank ℝ E - 1) → ℝ) (E := (f : N → M) *ᵖ fun x ↦ D x)
    (F' := Fin (finrank ℝ E - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D f)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD hf hfD hinj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD hf hfD hinj
  let := hD₁.isContMDiffDistribution.fiberBundle
  let := hD₁.isContMDiffDistribution.vectorBundle
  let := subbundleTopology (Fin (finrank ℝ E₁ - 1) → ℝ) (E := (g : N → M₁) *ᵖ fun x ↦ D₁ x)
    (F' := Fin (finrank ℝ E₁ - (finrank ℝ E' + 1)) → ℝ) (leviOrthogonalPullback J D₁ g)
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).fiberBundle
  let := (hasLocalContMDiffSubbundleFrames_orthogonalBilin hD₁ hg hgD hginj).vectorBundle
  have := contMDiffVectorBundle_leviOrthogonalPullback hD₁ hg hgD hginj
  have hV := hasLocalContMDiffSubbundleFrames_comap_range hD hf hfD hinj
  have hV₁ := hasLocalContMDiffSubbundleFrames_comap_range hD₁ hg hgD hginj
  have hmap := hV.contMDiff_totalSpace_mapQ (hfD.card_add_card_eq_finrank hD hf hinj) hV₁
    (hgD.card_add_card_eq_finrank hD₁ hg hginj) (f := id)
    (leviOrthogonalPullbackMap J hD hD₁ Φ hΦD hf)
    (comap_range_le_comap_leviOrthogonalPullbackMap hD hD₁ Φ hΦD hf)
    (contMDiff_totalSpace_leviOrthogonalPullbackMap hD hD₁ Φ hΦD hf hfD hinj)
  rw [conformalSymplecticNormalPrebundle_eq hD hf hfD hinj,
    conformalSymplecticNormalPrebundle_eq hD₁ hg hgD hginj]
  let := (hV.quotientPrebundle (hfD.card_add_card_eq_finrank hD hf hinj)).totalSpaceTopology
  let := (hV.quotientPrebundle (hfD.card_add_card_eq_finrank hD hf hinj)).toFiberBundle
  let := (hV₁.quotientPrebundle (hgD.card_add_card_eq_finrank hD₁ hg hginj)).totalSpaceTopology
  let := (hV₁.quotientPrebundle (hgD.card_add_card_eq_finrank hD₁ hg hginj)).toFiberBundle
  refine hmap.congr fun p ↦ ?_
  obtain ⟨y, a⟩ := p
  induction a using Submodule.Quotient.induction_on with
  | H u => exact congrArg (TotalSpace.mk y) (csnEquiv_mk hD hD₁ Φ hΦD f hf y u)

variable (J) in
/-- **The conformal symplectic normal bundle under a contactomorphism.** Let `f : N → M` be a
smooth isotropic immersion of a nonempty manifold into a smooth contact manifold `(M, D)`, and let
`Φ : M ≃ M₁` be a smooth diffeomorphism onto a smooth contact manifold `(M₁, D₁)` whose
differential carries `D` onto `D₁`. Then `[u] ↦ [dΦ u]` is a smooth diffeomorphism from the total
space of the conformal symplectic normal bundle of `f` onto that of `Φ ∘ f`, covering the identity
of `N` (`TauCeti.proj_conformalSymplecticNormalDiffeomorph`) and acting on the fibres by the
conformally symplectic isomorphisms `TauCeti.conformalSymplecticNormalEquiv`
(`TauCeti.conformalSymplecticNormalDiffeomorph_apply`): a smooth isomorphism of vector bundles
over `N`. -/
def conformalSymplecticNormalDiffeomorph [Nonempty N] (hD : IsContactDistribution I ∞ D)
    (hD₁ : IsContactDistribution I₁ ∞ D₁) (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁)
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K} (hf : ContMDiff J I ∞ f)
    (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y)) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
        (fun y ↦ ConformalSymplecticNormal J D f y) ≃ₘ^∞⟮
        J.prod 𝓘(ℝ, Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ),
        J.prod 𝓘(ℝ, Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)⟯
      TotalSpace (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
        (fun y ↦ ConformalSymplecticNormal J D₁
          (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y) :=
  letI P := conformalSymplecticNormalPrebundle hD hf hfD hinj
  letI P₁ := conformalSymplecticNormalPrebundle hD₁
    (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
    ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
    fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)
  letI := P.totalSpaceTopology
  letI := P.toFiberBundle
  letI := P.toVectorBundle
  letI := P₁.totalSpaceTopology
  letI := P₁.toFiberBundle
  letI := P₁.toVectorBundle
  bundleDiffeomorph (fun y ↦
    haveI := FiberBundle.t2Space (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y) y
    haveI := FiberBundle.t2Space (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D₁
        (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y) y
    haveI := VectorBundle.isTopologicalAddGroup ℝ
      (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D₁
        (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y) y
    haveI := VectorBundle.continuousSMul ℝ (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D₁
        (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y) y
    (csnEquiv J hD hD₁ Φ hΦD f hf y).toContinuousLinearEquiv)
    (contMDiff_totalSpace_csnEquiv hD hD₁ Φ hΦD hf hfD hinj)

section conformalSymplecticNormalDiffeomorph

variable [Nonempty N] (hD : IsContactDistribution I ∞ D) (hD₁ : IsContactDistribution I₁ ∞ D₁)
  (Φ : M ≃ₘ^∞⟮I, I₁⟯ M₁) (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I₁ Φ x v ∈ D₁ (Φ x)) {f : K}
  (hf : ContMDiff J I ∞ f) (hfD : IsHorizontalMap J D f) (hinj : ∀ y, Injective (mfderiv J I f y))

/-- The bundle isomorphism induced by `Φ` acts on each fibre by `csnEquiv`. -/
private theorem conformalSymplecticNormalDiffeomorph_eq
    (p : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y)) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    conformalSymplecticNormalDiffeomorph J hD hD₁ Φ hΦD hf hfD hinj p =
      TotalSpace.mk' (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
        (E := fun y ↦ ConformalSymplecticNormal J D₁
          (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y)
        p.proj (csnEquiv J hD hD₁ Φ hΦD f hf p.proj p.snd) := by
  let P := conformalSymplecticNormalPrebundle hD hf hfD hinj
  let P₁ := conformalSymplecticNormalPrebundle hD₁
    (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
    ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
    fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)
  let := P.totalSpaceTopology
  let := P.toFiberBundle
  let := P.toVectorBundle
  let := P₁.totalSpaceTopology
  let := P₁.toFiberBundle
  let := P₁.toVectorBundle
  exact bundleDiffeomorph_apply _ _ p

/-- The bundle isomorphism of conformal symplectic normal bundles induced by `Φ` covers the
identity of `N`. -/
@[simp]
theorem proj_conformalSymplecticNormalDiffeomorph
    (p : TotalSpace (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
      (fun y ↦ ConformalSymplecticNormal J D f y)) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    (conformalSymplecticNormalDiffeomorph J hD hD₁ Φ hΦD hf hfD hinj p).proj = p.proj :=
  congrArg TotalSpace.proj (conformalSymplecticNormalDiffeomorph_eq hD hD₁ Φ hΦD hf hfD hinj p)

/-- The bundle isomorphism of conformal symplectic normal bundles induced by `Φ` sends the class
of `u` over `y` to the class of `dΦ u`. -/
theorem conformalSymplecticNormalDiffeomorph_mk (y : N)
    (u : ((LinearMap.range (mfderiv J I f y).toLinearMap).comap (D (f y)).subtype).orthogonalBilin
      (distributionLeviForm D (f y)))
    (u' : ((LinearMap.range (mfderiv J I₁ (Φ ∘ f) y).toLinearMap).comap
      (D₁ ((Φ ∘ f) y)).subtype).orthogonalBilin (distributionLeviForm D₁ ((Φ ∘ f) y)))
    (hu : ((u' : D₁ ((Φ ∘ f) y)) : TangentSpace I₁ ((Φ ∘ f) y)) =
      mfderiv I I₁ Φ (f y) ((u : D (f y)) : TangentSpace I (f y))) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    conformalSymplecticNormalDiffeomorph J hD hD₁ Φ hΦD hf hfD hinj
        ⟨y, Submodule.Quotient.mk u⟩ =
      TotalSpace.mk' (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
        (E := fun y ↦ ConformalSymplecticNormal J D₁
          (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y)
        y (Submodule.Quotient.mk u') :=
  (conformalSymplecticNormalDiffeomorph_eq hD hD₁ Φ hΦD hf hfD hinj _).trans
    (congrArg (TotalSpace.mk y) (conformalSymplecticNormalEquiv_mk _ _ _ _ _ _ _ _ _ _ hu))

/-- The fibre maps of the bundle isomorphism induced by `Φ` are the conformally symplectic
isomorphisms `TauCeti.conformalSymplecticNormalEquiv` of conformal symplectic normal spaces. -/
theorem conformalSymplecticNormalDiffeomorph_apply (y : N) (a : ConformalSymplecticNormal J D f y)
    {k k₁ : ℕ} (hDk : IsContMDiffDistribution I 1 k D) (hD₁k : IsContMDiffDistribution I₁ 1 k₁ D₁)
    {n : ℕ∞ω} (hΦ : ContMDiffAt I I₁ n Φ (f y)) (hn : 2 ≤ n)
    (hΦx : (mfderiv I I₁ Φ (f y)).IsInvertible)
    (hΦD₁ : ∀ u ∈ D (f y), mfderiv I I₁ Φ (f y) u ∈ D₁ (Φ (f y)))
    (hΦD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (Φ z), (mfderiv I I₁ Φ z).inverse v ∈ D z)
    (hfy : MDifferentiableAt J I f y) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    conformalSymplecticNormalDiffeomorph J hD hD₁ Φ hΦD hf hfD hinj ⟨y, a⟩ =
      TotalSpace.mk' (Fin (finrank ℝ E₁ - 2 * finrank ℝ E' - 1) → ℝ)
        (E := fun y ↦ ConformalSymplecticNormal J D₁
          (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y)
        y (conformalSymplecticNormalEquiv J D f y hDk hD₁k hΦ hn hΦx hΦD₁ hΦD' hfy a) := by
  refine (conformalSymplecticNormalDiffeomorph_eq hD hD₁ Φ hΦD hf hfD hinj _).trans ?_
  induction a using Submodule.Quotient.induction_on with
  | H u => exact congrArg (TotalSpace.mk y) ((csnEquiv_mk hD hD₁ Φ hΦD f hf y u).trans
      (conformalSymplecticNormalEquiv_mk _ _ _ _ _ _ _ _ _ _ (rfl)).symm)

/-- The inverse of the bundle isomorphism induced by `Φ` acts on the fibres by the inverses of the
isomorphisms `TauCeti.conformalSymplecticNormalEquiv`. -/
theorem conformalSymplecticNormalDiffeomorph_symm_apply (y : N)
    (b : ConformalSymplecticNormal J D₁
      (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁)) y)
    {k k₁ : ℕ} (hDk : IsContMDiffDistribution I 1 k D) (hD₁k : IsContMDiffDistribution I₁ 1 k₁ D₁)
    {n : ℕ∞ω} (hΦ : ContMDiffAt I I₁ n Φ (f y)) (hn : 2 ≤ n)
    (hΦx : (mfderiv I I₁ Φ (f y)).IsInvertible)
    (hΦD₁ : ∀ u ∈ D (f y), mfderiv I I₁ Φ (f y) u ∈ D₁ (Φ (f y)))
    (hΦD' : ∀ᶠ z in 𝓝 (f y), ∀ v ∈ D₁ (Φ z), (mfderiv I I₁ Φ z).inverse v ∈ D z)
    (hfy : MDifferentiableAt J I f y) :
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD hf hfD hinj).toFiberBundle
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).totalSpaceTopology
    letI := (conformalSymplecticNormalPrebundle hD₁
      (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
      ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
      fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)).toFiberBundle
    (conformalSymplecticNormalDiffeomorph J hD hD₁ Φ hΦD hf hfD hinj).symm ⟨y, b⟩ =
      TotalSpace.mk' (Fin (finrank ℝ E - 2 * finrank ℝ E' - 1) → ℝ)
        (E := fun y ↦ ConformalSymplecticNormal J D f y)
        y ((conformalSymplecticNormalEquiv J D f y hDk hD₁k hΦ hn hΦx hΦD₁ hΦD' hfy).symm b) := by
  let P := conformalSymplecticNormalPrebundle hD hf hfD hinj
  let P₁ := conformalSymplecticNormalPrebundle hD₁
    (f := (⟨Φ ∘ f, Φ.continuous.comp (map_continuous f)⟩ : C(N, M₁))) (Φ.contMDiff.comp hf)
    ((isHorizontalMap_diffeomorph_comp_iff Φ (by simp) hΦD).2 hfD)
    fun y ↦ (Φ.mfderiv_diffeomorph_comp_injective_iff (by simp)).2 (hinj y)
  let := P.totalSpaceTopology
  let := P.toFiberBundle
  let := P₁.totalSpaceTopology
  let := P₁.toFiberBundle
  -- The bundle isomorphism sends the right-hand side to `⟨y, b⟩`, as it is computed fibrewise.
  have h := conformalSymplecticNormalDiffeomorph_apply hD hD₁ Φ hΦD hf hfD hinj y
    ((conformalSymplecticNormalEquiv J D f y hDk hD₁k hΦ hn hΦx hΦD₁ hΦD' hfy).symm b) hDk hD₁k hΦ
    hn hΦx hΦD₁ hΦD' hfy
  rw [LinearEquiv.apply_symm_apply] at h
  exact (congrArg (conformalSymplecticNormalDiffeomorph J hD hD₁ Φ hΦD hf hfD hinj).symm
    h).symm.trans (Diffeomorph.symm_apply_apply _ _)

end conformalSymplecticNormalDiffeomorph


end TauCeti
