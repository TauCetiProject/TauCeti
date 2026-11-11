/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Torus.Cover
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.IsotropicSection

import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Action-angle coordinates with values in the cotangent bundle of a torus

Let `σ` be a symplectic form on a boundaryless Hausdorff manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions with complete
Hamiltonian vector fields, with the conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g)`. Let
`L` be a compact connected component of a level `F⁻¹(c₀)` consisting of regular points of `F`.

This file states the Liouville–Arnold theorem near `L` as a symplectic chart with values in the
cotangent bundle `T*Tⁿ` of the torus `Tⁿ = ι → AddCircle p`, for any period `p > 0`, with its
canonical symplectic form `ω = -dλ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle_of_isCompact`). A covector `z` of `T*Tⁿ`
has the **actions** `I_i = z(e_i)`. There are an open neighbourhood `U` of `L`, an open set
`D ⊆ ℝ^ι` and a map `Φ : M → T*Tⁿ` such that

* `Φ` is injective on `U`, and maps `U` onto the covectors whose actions lie in `D`;
* `Φ` is a smooth local diffeomorphism at every point of `U`, and pulls `ω` back to `σ` there;
* on `U`, the functions `F` are a smooth function `h` of the actions: `F = h ∘ I ∘ Φ`.

So `Φ` is a symplectomorphism of `U` onto the part of `T*Tⁿ` over an open set `D` of actions, in
which the angles are the base point and the actions the covector. In particular each Hamiltonian
`K ∘ F` depends on the actions alone.

The chart `Φ` is the inverse of the angle map of an isotropic section
(`TauCeti.SmoothTwoForm.IsSymplectic.angleMap`), read through the covering
`TauCeti.CotangentBundle.torusMk` of `T*Tⁿ` by the linear cotangent space of `ι → ℝ`. On the part
of `ι → ℝ` where the action map `A` is invertible, with inverse `B`, the map

`G(q, ξ) = Ψ(2π q / p, B(p ξ(e) / 2π))`,

from `(ι → ℝ) × (ι → ℝ)*` to `M` pulls `σ` back to the linear cotangent form, as the covering does,
and identifies two points exactly when the covering does: when their covectors agree and their base
points differ by a vector of `p ℤ^ι`. Both being local diffeomorphisms, `Φ = torusMk ∘ G⁻¹` is a
well-defined local diffeomorphism on the image of `G` with the required properties.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle_of_isCompact`: action-angle coordinates
  near a compact regular component of a level, with values in `T*Tⁿ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action-angle
  variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (action-angle coordinates as a symplectomorphism onto an open subset of
  `T*Tⁿ`).
-/

public section

open Set Filter Module Topology Function Real Bundle
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff Matrix

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))

omit [I.Boundaryless] [T2Space M] in
/-- **Inverting a parametrization through the covering of `T*Tⁿ`.** Let `G` map an open set `W` of
the linear cotangent space `(ι → ℝ) × (ι → ℝ)*` smoothly into `M`, pulling `σ` back to the linear
cotangent form, and identifying two points of `W` exactly when the covering
`TauCeti.CotangentBundle.torusMk` does. Then `G '' W` is open and `Φ = torusMk ∘ G⁻¹` is a
well-defined injective local diffeomorphism on it, which pulls the canonical form of `T*Tⁿ` back to
`σ`. -/
private theorem exists_comp_invFunOn_torusMk (hσn : σ.IsNondegenerate) (p : ℝ)
    [Fact (0 < p)] (hdimV : finrank ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) = finrank ℝ E)
    {G : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) → M} {W : Set ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))}
    (hW : IsOpen W) (hGs : ContMDiffOn 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I ∞ G W)
    (hGσ : ∀ w ∈ W, ∀ u u' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ),
      SmoothBundleForm.eval₂ σ (G w) (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w u)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w u') =
      strongDualCotangentSymplecticForm u u')
    (hGT : ∀ w ∈ W, ∀ w' ∈ W, G w = G w' ↔
      CotangentBundle.torusMk (fun _ : ι ↦ p) w = CotangentBundle.torusMk (fun _ : ι ↦ p) w') :
    ∃ Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
      IsOpen (G '' W) ∧ InjOn Φ (G '' W) ∧
      (∀ w ∈ W, Φ (G w) = CotangentBundle.torusMk (fun _ : ι ↦ p) w) ∧
      (∀ y ∈ G '' W, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y) ∧
      ∀ y ∈ G '' W, ∀ v w : TangentSpace I y,
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) (Φ y)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y w) =
          SmoothBundleForm.eval₂ σ y v w := by
  set T := CotangentBundle.torusMk fun _ : ι ↦ p
  -- `G` is a local diffeomorphism on `W`: its differential is injective, as it pulls `σ` back to
  -- a nondegenerate form.
  have hGl {w} (hw : w ∈ W) : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I ∞ G w := by
    refine isLocalDiffeomorphAt_of_injective_mfderiv hGs hW hw
      BoundarylessManifold.isInteriorPoint (by simp) ?_ hdimV
    rw [injective_iff_map_eq_zero]
    intro u hu
    refine strongDualCotangentSymplecticForm.nondegenerate.1 u fun u' ↦ ?_
    have h := hGσ w hw u u'
    rw [hu] at h
    have h0 := SmoothBundleForm.eval₂_smul_left σ (G w) (0 : ℝ) 0
      (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w u')
    rw [smul_zero, zero_smul] at h0
    exact h.symm.trans h0
  -- The chart `Φ = T ∘ G⁻¹`, well defined on `G '' W`.
  set Φ := T ∘ invFunOn G W
  have hΦG {w} (hw : w ∈ W) : Φ (G w) = T w := by
    obtain ⟨h₁, h₂⟩ := invFunOn_pos (f := G) ⟨w, hw, rfl⟩
    exact (hGT _ h₁ _ hw).1 h₂
  -- Near `G w`, a local inverse `ℓ` of `G` at `w` takes values in `W` and `Φ = T ∘ ℓ`.
  have hℓ {w} (hw : w ∈ W) : ∀ᶠ y in 𝓝 (G w),
      (hGl hw).localInverse y ∈ W ∧ G ((hGl hw).localInverse y) = y := by
    have hlw : (hGl hw).localInverse (G w) = w :=
      (hGl hw).localInverse_left_inv (hGl hw).localInverse_mem_target
    filter_upwards [(hGl hw).localInverse_eventuallyEq_right,
      (hGl hw).continuousAt_localInverse.preimage_mem_nhds
        (hW.mem_nhds (by rwa [hlw]))] with y hy hyW
    exact ⟨hyW, hy⟩
  have hΦl {w} (hw : w ∈ W) : Φ =ᶠ[𝓝 (G w)] T ∘ (hGl hw).localInverse := by
    filter_upwards [hℓ hw] with y hy
    rw [Function.comp_apply, ← hΦG hy.1, hy.2]
  have hU : IsOpen (G '' W) := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    filter_upwards [hℓ hw] with y hy
    exact ⟨_, hy.1, hy.2⟩
  have hΦs : ContMDiffOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ (G '' W) := by
    rintro _ ⟨w, hw, rfl⟩
    exact (((CotangentBundle.isLocalDiffeomorph_torusMk (fun _ : ι ↦ p) _).contMDiffAt.comp (G w)
      (hGl hw).contMDiffAt_localInverse).congr_of_eventuallyEq (hΦl hw)).contMDiffWithinAt
  -- `Φ` pulls the canonical form of `T*Tⁿ` back to `σ`.
  have hpull {w} (hw : w ∈ W) (v v' : TangentSpace I (G w)) :
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) (Φ (G w))
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            Φ (G w) v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            Φ (G w) v') =
        SmoothBundleForm.eval₂ σ (G w) v v' := by
    set ℓ := (hGl hw).localInverse
    have hlw : ℓ (G w) = w := (hGl hw).localInverse_left_inv (hGl hw).localInverse_mem_target
    have hℓd := (hGl hw).mdifferentiableAt_localInverse (by simp)
    have hT : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) T (ℓ (G w))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) T w) := by
      rw [hlw]
      exact ((CotangentBundle.isLocalDiffeomorph_torusMk (fun _ : ι ↦ p) w).mdifferentiableAt
        (by simp)).hasMFDerivAt
    have hG : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G (ℓ (G w))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w) := by
      rw [hlw]
      exact ((hGl hw).mdifferentiableAt (by simp)).hasMFDerivAt
    have hΦd (v : TangentSpace I (G w)) :
        mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ (G w) v =
          mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ))
            ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) T w
            (mfderiv I 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) ℓ (G w) v) := by
      rw [((hT.comp (G w) hℓd.hasMFDerivAt).congr_of_eventuallyEq (hΦl hw)).mfderiv]
      rfl
    have hGd (v : TangentSpace I (G w)) : mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w
        (mfderiv I 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) ℓ (G w) v) = v :=
      congrArg (fun L : TangentSpace I (G w) →L[ℝ] TangentSpace I (G w) ↦ L v)
        (hasMFDerivAt_unique (hG.comp (G w) hℓd.hasMFDerivAt)
          ((hasMFDerivAt_id (G w)).congr_of_eventuallyEq
            (hGl hw).localInverse_eventuallyEq_right))
    rw [hΦd, hΦd, hΦG hw]
    refine (CotangentBundle.eval₂_mfderiv_torusMk _ w _ _).trans ?_
    refine (hGσ w hw _ _).symm.trans ?_
    rw [hGd, hGd]
  refine ⟨Φ, hU, ?_, fun w hw ↦ hΦG hw, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ h
    rw [hΦG hw, hΦG hw'] at h
    exact (hGT _ hw _ hw').2 h
  · rintro _ ⟨w, hw, rfl⟩
    refine isLocalDiffeomorphAt_of_injective_mfderiv hΦs hU ⟨w, hw, rfl⟩
      BoundarylessManifold.isInteriorPoint (by simp) ?_ hdimV.symm
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine isNondegenerate_iff_separatingLeft.1 hσn _ v fun v' ↦ ?_
    rw [← hpull hw, hv]
    have h0 := SmoothBundleForm.eval₂_smul_left
      (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (Φ (G w)) (0 : ℝ) 0 (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ (G w) v')
    rwa [smul_zero, zero_smul] at h0
  · rintro _ ⟨w, hw, rfl⟩
    exact hpull hw

include hσ hF hcomm hc in
/-- **Action-angle coordinates with values in `T*Tⁿ`** (the Liouville–Arnold theorem near a
compact regular component, for complete Hamiltonian vector fields). On a manifold of dimension
`2 |ι|`, let the connected component `L` of `x` in its level `F⁻¹(F x)` be compact and consist of
regular points of `F`, and let `p > 0`. Then there are an open set `U ⊇ L`, an open set
`D ⊆ ℝ^ι`, a map `Φ : M → T*Tⁿ` to the cotangent bundle of the torus `Tⁿ = ι → AddCircle p` and a
smooth map `h : ℝ^ι → ℝ^ι` such that

* `Φ` is injective on `U` and maps `U` onto the covectors `z` whose actions `(z(e_i))ᵢ` lie in `D`;
* `Φ` is a smooth local diffeomorphism at every point of `U`;
* `Φ` pulls the canonical symplectic form of `T*Tⁿ` back to `σ` at every point of `U`;
* `h` is smooth on `D`, and `F = h ∘ (actions) ∘ Φ` on `U`. -/
theorem exists_actionAngle_of_isCompact [DecidableEq ι] (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (p : ℝ) [Fact (0 < p)] {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ (U : Set M) (D : Set (ι → ℝ))
      (Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (h : (ι → ℝ) → ι → ℝ),
      IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧ IsOpen D ∧ InjOn Φ U ∧
      Φ '' U = {z | (fun i ↦ z.2 (Pi.single i 1)) ∈ D} ∧
      (∀ y ∈ U, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y) ∧
      (∀ y ∈ U, ∀ v w : TangentSpace I y,
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (ι → AddCircle p)) (Φ y)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              Φ y w) =
          SmoothBundleForm.eval₂ σ y v w) ∧
      ContDiffOn ℝ ∞ h D ∧ ∀ y ∈ U, F y = h fun i ↦ (Φ y).2 (Pi.single i 1) := by
  -- Outline: from an isotropic section through `x` take the angle map `Ψ` and the action map `A`,
  -- with a local inverse `B`. The map `G(q, ξ) = Ψ(κ q, B(κ⁻¹ ξ(e)))`, `κ = 2π / p`, on an open set
  -- `W` pulls `σ` back to the linear cotangent form and has the fibres of the covering `T` of
  -- `T*Tⁿ`; its image contains `L`. Then `Φ = T ∘ G⁻¹` is the chart.
  set L := connectedComponentIn (F ⁻¹' {F x}) x
  obtain ⟨t, ht, hxt, s, hsx, hs, hFs, hL⟩ :=
    hσ.exists_contMDiffOn_section_eval₂_mfderiv_eq_zero hF hcomm hc
      (hreg x (mem_connectedComponentIn rfl))
  obtain ⟨per, A, U₀, hU₀, hxU₀, hU₀t, hA, hU₀prop⟩ :=
    hσ.exists_isLocalDiffeomorphAt_angleMap_of_isCompact hF hcomm hc hdim hreg hK ht hxt hsx hs
      hFs hL
  set Ψ := hσ.angleMap hF hcomm hc s per
  -- The inverse `B` of the action map near `A (F x)`, on the open set `D₀` of actions whose
  -- values of `B` lie in `U₀`.
  set B := hA.localInverse
  set D₀ := B.source ∩ B ⁻¹' U₀
  have hD₀ : IsOpen D₀ :=
    hA.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage B.open_source hU₀
  have hAB {J : ι → ℝ} (hJ : J ∈ B.source) : A (B J) = J := hA.localInverse_right_inv hJ
  have hBA : B (A (F x)) = F x := hA.localInverse_left_inv hA.localInverse_mem_target
  have hAD₀ : A (F x) ∈ D₀ := ⟨hA.localInverse_mem_source, by simpa [hBA] using hxU₀⟩
  -- Angles `θ = κ q` and actions `B (κ⁻¹ ξ(e))` for `κ = 2π / p`.
  set κ : ℝ := 2 * π / p
  have hκ : 0 < κ := div_pos two_pi_pos (Fact.out)
  set act : ((ι → ℝ) →L[ℝ] ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)
  have hact (ξ : (ι → ℝ) →L[ℝ] ℝ) (i : ι) : act ξ i = ξ (Pi.single i 1) := rfl
  have hsum (ξ : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) : ξ v = ∑ i, v i * act ξ i := by
    refine (ξ.toLinearMap.pi_apply_eq_sum_univ v).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [smul_eq_mul, hact]
    have hi : (fun j ↦ if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [ContinuousLinearMap.coe_coe, hi]
  set k : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) → (ι → ℝ) × (ι → ℝ) := fun w ↦ (κ • w.1, B (κ⁻¹ • act w.2))
  set W : Set ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) := (fun w ↦ κ⁻¹ • act w.2) ⁻¹' D₀
  have hW : IsOpen W := hD₀.preimage (by fun_prop)
  set G := Ψ ∘ k
  -- The derivative of `k` at a point of `W`.
  have hk {w} (hw : w ∈ W) : HasFDerivAt k ((κ • ContinuousLinearMap.fst ℝ _ _).prod
      ((fderiv ℝ B (κ⁻¹ • act w.2)).comp (κ⁻¹ • act.comp (ContinuousLinearMap.snd ℝ _ _)))) w := by
    have hB : DifferentiableAt ℝ B (κ⁻¹ • act w.2) :=
      ((contMDiffOn_iff_contDiffOn.1 hA.contMDiffOn_localInverse).differentiableOn
        (by simp)).differentiableAt (B.open_source.mem_nhds hw.1)
    exact (hasFDerivAt_fst.const_smul κ).prodMk (hB.hasFDerivAt.comp w
      ((act.hasFDerivAt.comp w hasFDerivAt_snd).const_smul κ⁻¹))
  -- `dAᵢ ∘ dB = dIᵢ`, since `A ∘ B` is the identity near each point of `D₀`.
  have hdAB {J : ι → ℝ} (hJ : J ∈ D₀) (i : ι) (z : ι → ℝ) :
      fderiv ℝ (fun c ↦ A c i) (B J) (fderiv ℝ B J z) = z i := by
    obtain ⟨hAd, -⟩ := hU₀prop _ hJ.2
    have hB : DifferentiableAt ℝ B J :=
      ((contMDiffOn_iff_contDiffOn.1 hA.contMDiffOn_localInverse).differentiableOn
        (by simp)).differentiableAt (B.open_source.mem_nhds hJ.1)
    have h₁ : HasFDerivAt (fun J' ↦ A (B J') i) (proj i : (ι → ℝ) →L[ℝ] ℝ) J :=
      (proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.congr_of_eventuallyEq
        (eventually_of_mem (B.open_source.mem_nhds hJ.1) fun J' hJ' ↦ by simp [hAB hJ'])
    rw [(hAd i).fderiv]
    exact congrArg (fun T : (ι → ℝ) →L[ℝ] ℝ ↦ T z) (((hAd i).comp J hB.hasFDerivAt).unique h₁)
  -- `G` pulls `σ` back to the linear cotangent form.
  have hGσ {w} (hw : w ∈ W) (u u' : (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) :
      SmoothBundleForm.eval₂ σ (G w) (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w u)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I G w u') =
      strongDualCotangentSymplecticForm u u' := by
    obtain ⟨-, hloc, hform, -⟩ := hU₀prop _ hw.2
    have hG := ((hloc (κ • w.1)).mdifferentiableAt (by simp)).hasMFDerivAt.comp w
      (hk hw).hasMFDerivAt
    rw [hG.mfderiv]
    have := hform (κ • w.1) (κ • u.1) (κ • u'.1) (fderiv ℝ B (κ⁻¹ • act w.2) (κ⁻¹ • act u.2))
      (fderiv ℝ B (κ⁻¹ • act w.2) (κ⁻¹ • act u'.2))
    refine this.trans ?_
    simp only [hdAB hw, strongDualCotangentSymplecticForm_apply, hsum u'.2, hsum u.2,
      ← Finset.sum_sub_distrib, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
  have hdimV : finrank ℝ ((ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) = finrank ℝ E := by
    rw [Module.finrank_prod, ← LinearMap.toContinuousLinearMap.finrank_eq,
      Module.finrank_linearMap_self, Module.finrank_fintype_fun_eq_card, ← hdim, two_mul]
  -- `G` is smooth on `W`, and a local diffeomorphism there.
  have hGs : ContMDiffOn 𝓘(ℝ, (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ)) I ∞ G W := by
    intro w hw
    obtain ⟨-, hloc, -⟩ := hU₀prop _ hw.2
    have hBc : ContDiffAt ℝ ∞ B (κ⁻¹ • act w.2) :=
      (contMDiffOn_iff_contDiffOn.1 hA.contMDiffOn_localInverse).contDiffAt
        (B.open_source.mem_nhds hw.1)
    have hkc : ContDiffAt ℝ ∞ k w :=
      (contDiffAt_fst.const_smul κ).prodMk (hBc.comp w ((act.contDiff.comp contDiff_snd).const_smul
        κ⁻¹).contDiffAt)
    exact ((hloc (κ • w.1)).contMDiffAt.comp w hkc.contMDiffAt).contMDiffWithinAt
  -- `G` identifies two points of `W` exactly when the covering of `T*Tⁿ` does.
  have hact_inj {ξ ξ' : (ι → ℝ) →L[ℝ] ℝ} (h : act ξ = act ξ') : ξ = ξ' :=
    ContinuousLinearMap.ext fun v ↦ by rw [hsum ξ, hsum ξ', h]
  set T := CotangentBundle.torusMk fun _ : ι ↦ p
  have hGT {w w'} (hw : w ∈ W) (hw' : w' ∈ W) : G w = G w' ↔ T w = T w' := by
    obtain ⟨-, -, -, hinj⟩ := hU₀prop _ hw.2
    rw [CotangentBundle.torusMk_eq_torusMk_iff]
    refine (hinj _ hw'.2 _ _).trans (and_congr
      ⟨fun h ↦ hact_inj ?_, fun h ↦ congrArg (fun ξ ↦ B (κ⁻¹ • act ξ)) h⟩
      (exists_congr fun m ↦ ?_))
    · have h' := congrArg A h
      rw [hAB hw'.1, hAB hw.1] at h'
      exact smul_right_injective _ (inv_ne_zero hκ.ne') h'
    · have hm : (fun i ↦ 2 * π * m i) = κ • fun i ↦ (m i : ℝ) * p := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, κ]
        field_simp [(Fact.out : 0 < p).ne']
      rw [hm, ← smul_add, (smul_right_injective _ hκ.ne').eq_iff]
  -- The periods at `F x` are linearly independent, since `dA ∘ dB` is the identity.
  have hli : LinearIndependent ℝ fun i ↦ per i (F x) := by
    obtain ⟨hAd, -⟩ := hU₀prop _ hxU₀
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    set z := fderiv ℝ B (A (F x)) (Pi.single j 1)
    have hk (i : ι) : (2 * π)⁻¹ * (per i (F x) ⬝ᵥ z) = (Pi.single j 1 : ι → ℝ) i := by
      have h := hdAB hAD₀ i (Pi.single j 1)
      rw [hBA, (hAd i).fderiv] at h
      rw [← h]
      simp [dotProduct, Finset.mul_sum, z]
    calc a j = ∑ i, a i * (Pi.single j 1 : ι → ℝ) i := by simp [Pi.single_apply]
      _ = (2 * π)⁻¹ * ((∑ i, a i • per i (F x)) ⬝ᵥ z) := by
        simp only [← hk, sum_dotProduct, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = 0 := by rw [ha, zero_dotProduct, mul_zero]
  -- Every point of `L` is `Ψ(θ, F x)` for some angles `θ`, hence lies in `G '' W`.
  have hLW : L ⊆ G '' W := by
    intro y hy
    obtain ⟨v, rfl⟩ := hσ.exists_hamiltonianFlowAction_apply_eq hF hcomm hc hdim hreg hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
      ((hli.span_eq_top_of_card_eq_finrank' (by simp)).symm ▸ Submodule.mem_top (x := v))
    set ξ₀ : (ι → ℝ) →L[ℝ] ℝ := ∑ j, (κ * A (F x) j) • (proj j : (ι → ℝ) →L[ℝ] ℝ)
    have hξ₀ : κ⁻¹ • act ξ₀ = A (F x) := by
      funext i
      simp [hact, ξ₀, Pi.single_apply, hκ.ne']
    refine ⟨(κ⁻¹ • (2 * π) • a, ξ₀), by simpa [W, hξ₀] using hAD₀, ?_⟩
    simp only [G, k, Ψ, Function.comp_apply, hξ₀, hBA, smul_smul, mul_inv_cancel_left₀ hκ.ne',
      hσ.angleMap_apply hF hcomm hc, hsx]
    simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc, pi_ne_zero]
  obtain ⟨Φ, hU, hΦi, hΦG, hΦl, hpull⟩ := exists_comp_invFunOn_torusMk hσ.isNondegenerate p hdimV
    hW hGs (fun w hw ↦ hGσ hw) fun w hw w' hw' ↦ hGT hw hw'
  refine ⟨G '' W, {J | κ⁻¹ • J ∈ D₀}, Φ, fun J ↦ B (κ⁻¹ • J), hU, hLW,
    hD₀.preimage (continuous_const_smul _), hΦi, ?_, hΦl, hpull, ?_, ?_⟩
  · ext z
    refine ⟨?_, fun hz ↦ ?_⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rw [hΦG w hw]
      simp only [mem_ofPred_eq, CotangentBundle.torusMk_snd]
      exact hw
    · obtain ⟨w, rfl⟩ := CotangentBundle.surjective_torusMk (fun _ : ι ↦ p) z
      have hw : w ∈ W := by
        simp only [mem_ofPred_eq, CotangentBundle.torusMk_snd] at hz
        exact hz
      exact ⟨G w, ⟨w, hw, rfl⟩, hΦG w hw⟩
  · exact (contMDiffOn_iff_contDiffOn.1 hA.contMDiffOn_localInverse).comp
      (contDiff_const_smul _).contDiffOn fun J hJ ↦ hJ.1
  · rintro _ ⟨w, hw, rfl⟩
    rw [hΦG w hw]
    simp only [CotangentBundle.torusMk_snd]
    exact (hσ.apply_angleMap hF hcomm hc _).trans (hFs _ (hU₀t hw.2))

end IsSymplectic

end SmoothTwoForm

end TauCeti
