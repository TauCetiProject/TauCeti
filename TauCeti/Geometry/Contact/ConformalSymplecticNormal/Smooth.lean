/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.ConformalSymplecticNormal.Bundle
public import TauCeti.Geometry.Manifold.Distribution.Levi.Bundle

/-!
# The smoothness of the form on the conformal symplectic normal bundle

Let `f : N → M` be a smooth isotropic immersion of a nonempty manifold into a smooth contact
manifold `(M, D)`, with conformal symplectic normal bundle `CSN(f)`, the smooth vector bundle of
the spaces `(T_y N)^⊥ ⧸ T_y N` (`TauCeti.conformalSymplecticNormalPrebundle`). Its fibres carry
the nondegenerate form induced by the Levi form, with values in the contact line `L = TM ⧸ D`
(`TauCeti.conformalSymplecticNormalForm`). This file shows that this form is a smooth bundle map,
so that `CSN(f)` is a smooth conformal symplectic vector bundle with values in the pullback of `L`.
The smoothness of the isomorphisms `CSN(f) → CSN(F ∘ f)` induced by a contactomorphism `F` is
`TauCeti.contMDiff_totalSpace_conformalSymplecticNormalEquiv`. These are the normal data of the
isotropic neighbourhood theorem.

The form of two smooth local sections of `CSN(f)` is a smooth section of the contact line along
`f`. Near each point the sections are classes of smooth sections of the bundle of Levi
orthogonals (`TauCeti.HasLocalContMDiffSubbundleFrames.exists_contMDiffOn_mk_eq`), which are
sections of `D` along `f`, and the Levi form of `D` is a smooth section of `Hom(D, Hom(D, L))`
(`TauCeti.contMDiff_distributionLeviFormL`).

## Main results

* `TauCeti.contMDiffOn_conformalSymplecticNormalForm`: the line-valued form of two smooth sections
  of the conformal symplectic normal bundle is a smooth section of the contact line along `f`.

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

end TauCeti
