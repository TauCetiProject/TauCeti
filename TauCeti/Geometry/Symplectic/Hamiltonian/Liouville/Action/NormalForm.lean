/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart

/-!
# The Liouville–Arnold action–angle normal form

Let `(M, σ)` be a Hausdorff boundaryless symplectic manifold of dimension `2 · |ι|`, let
`F : M → ι → ℝ` be a smooth family of pairwise Poisson-commuting functions, and let
`L = connectedComponentIn (F ⁻¹' {F x₀}) x₀` be a compact connected component of a level on which
every point is regular for `F`. No completeness of the Hamiltonian flows is assumed, and other
components of the level need not be regular.

This file upgrades the lifted periodic action–angle chart of
`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact` to a
genuine symplectic diffeomorphism onto a neighbourhood of a constant-action torus in the cotangent
bundle `T*Tⁿ` of the angle torus `Tⁿ = ∀ i, AddCircle (p i)` with its canonical symplectic form
`ω = -dλ = ∑ i, dθᵢ ∧ dIᵢ`.

Specifically, for any family of positive periods `p : ι → ℝ`, there are a smooth partial
diffeomorphism `φ : M → T*Tⁿ`, a smooth partial diffeomorphism `h : ℝ^ι → ℝ^ι` on the open action
domain `h.source ⊆ ℝ^ι`, and a value `I₀ ∈ h.source` such that
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_partialDiffeomorph_actionAngle`):

* `L ⊆ φ.source`, with `φ '' L = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = I₀}`;
* `φ.target = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ h.source}`;
* `φ` pulls `ω` back to `σ` on `φ.source`;
* `F x = h (fun i ↦ (φ x).2 (Pi.single i 1))` for all `x ∈ φ.source`, with `h I₀ = F x₀`.

Taking a uniform period `p > 0` and an integrable system `F` gives the classical Liouville–Arnold
action–angle theorem (`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`).

In action–angle coordinates, any Hamiltonian `H = K ∘ I ∘ φ` depending only on the actions has
Hamiltonian vector field carried by `dφ` to the constant-frequency horizontal field `(∂K/∂I, 0)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_of_actionAngle`), and pulling
back the linear torus flow on `T*Tⁿ` yields global quasi-periodic integral curves of `X_H` on `M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_symm_of_actionAngle`).

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_partialDiffeomorph_actionAngle`: bundled partial
  diffeomorphism onto `T*Tⁿ` with arbitrary coordinatewise positive periods `p : ι → ℝ`, bundled
  action-to-integral partial diffeomorphism `h`, and image of the invariant torus `L`.
* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: the Liouville–Arnold action–angle
  theorem for a completely integrable system and a uniform period `p > 0`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_hamiltonianVectorField_of_actionAngle`: in
  action–angle coordinates, a function of the actions has horizontal Hamiltonian vector field
  `(∂K/∂I, 0)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isMIntegralCurve_symm_of_actionAngle`: global
  quasi-periodic integral curves of an action-dependent Hamiltonian in an action–angle chart.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4, Theorem 18.12(b).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
-/

public section

noncomputable section

open Function Module Real Set
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothTwoForm

section ActionAngleNormalForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] [DecidableEq ι] {F : M → ι → ℝ}

namespace IsSymplectic

/-- Action–angle partial diffeomorphism with standard `2π` periods, built by descending the lifted
periodic chart `Ψ` along the universal covering map `CotangentBundle.torusCoverMap`. -/
private theorem exists_partialDiffeomorph_actionAngle_two_pi (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x₀ : M}
    (hreg : ∀ x ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x₀}) x₀)) :
    letI : Fact (0 < 2 * π) := ⟨mul_pos two_pos pi_pos⟩
    ∃ (φ : PartialDiffeomorph I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ _ : ι, AddCircle (2 * π))) ∞)
      (h : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞) (I₀ : ι → ℝ),
      connectedComponentIn (F ⁻¹' {F x₀}) x₀ ⊆ φ.source ∧
      φ.target = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ h.source} ∧
      I₀ ∈ h.source ∧
      φ '' connectedComponentIn (F ⁻¹' {F x₀}) x₀ =
        {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = I₀} ∧
      (∀ x ∈ φ.source, ∀ v w : TangentSpace I x,
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (∀ _ : ι, AddCircle (2 * π))) (φ x)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              φ x v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              φ x w) =
          SmoothBundleForm.eval₂ σ x v w) ∧
      (∀ x ∈ φ.source, F x = h (fun i ↦ (φ x).2 (Pi.single i 1))) ∧
      h I₀ = F x₀ := by
  have : Fact (0 < 2 * π) := ⟨mul_pos two_pos pi_pos⟩
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let p₂π : ι → ℝ := fun _ ↦ 2 * π
  -- Step 1: Extract the lifted periodic chart `Ψ` and local diffeomorphism `A` at `F x₀`.
  obtain ⟨Ψ, A, Uc, hUc, hx₀Uc, hA, hrange, hUc_prop⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  set L := connectedComponentIn (F ⁻¹' {F x₀}) x₀
  -- Step 2: Invert `A` on an open neighbourhood `D` of `I₀ = A (F x₀)` mapping into `Uc`.
  let eA := hA.localInverse.symm.restrOpen Uc hUc
  let hPD := eA.symm
  let D : Set (ι → ℝ) := hPD.source
  let I₀ : ι → ℝ := A (F x₀)
  have hD_open : IsOpen D := hPD.open_source
  have hD_eq : D = hA.localInverse.source ∩ hA.localInverse ⁻¹' Uc := by
    change eA.target = _
    simp [eA]
  have hhPD_target : hPD.target = hA.localInverse.target ∩ Uc := by
    change eA.source = _
    simp [eA]
  have hhPD_coe (J : ι → ℝ) : hPD J = hA.localInverse J := by
    change eA.toPartialEquiv.symm J = _
    simp [eA]
  have hI₀_mem : I₀ ∈ D := by
    rw [hD_eq]
    refine ⟨hA.localInverse_mem_source, ?_⟩
    simpa [I₀, hA.localInverse_left_inv hA.localInverse_mem_target] using hx₀Uc
  have hh_I₀ : hPD I₀ = F x₀ := by
    rw [hhPD_coe]
    exact hA.localInverse_left_inv hA.localInverse_mem_target
  have hh_mem_Uc : ∀ J ∈ D, hPD J ∈ Uc := fun J hJ ↦ by
    have hmem : hPD J ∈ hPD.target := hPD.map_source hJ
    rw [hhPD_target] at hmem
    exact hmem.2
  have hAh : ∀ J ∈ D, A (hPD J) = J := fun J hJ ↦ by
    rw [hD_eq] at hJ
    rw [hhPD_coe]
    exact hA.localInverse_right_inv hJ.1
  have hh_diff : ∀ J ∈ D, DifferentiableAt ℝ hPD J := fun J hJ ↦
    ((contMDiffOn_iff_contDiffOn.1 hPD.contMDiffOn_toFun).contDiffAt
      (hD_open.mem_nhds hJ)).differentiableAt (by simp)
  have hA_eqOn : EqOn A hA.localInverse.symm hA.localInverse.target := fun c hc ↦ by
    have hmem : hA.localInverse.symm c ∈ hA.localInverse.source :=
      hA.localInverse.map_target hc
    have hinv := hA.localInverse_right_inv hmem
    have hright : hA.localInverse (hA.localInverse.symm c) = c :=
      hA.localInverse.right_inv hc
    rwa [hright] at hinv
  have hA_diff : ∀ J ∈ D, DifferentiableAt ℝ A (hPD J) := fun J hJ ↦ by
    have hmem : hPD J ∈ hA.localInverse.target := by
      have hm := hPD.map_source hJ
      rw [hhPD_target] at hm
      exact hm.1
    have hcd : ContDiffAt ℝ ∞ hA.localInverse.symm (hPD J) :=
      (contMDiffOn_iff_contDiffOn.1 hA.localInverse.symm.contMDiffOn_toFun).contDiffAt
        (hA.localInverse.open_target.mem_nhds hmem)
    exact (hcd.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hA.localInverse.open_target.mem_nhds hmem)
        hA_eqOn)).differentiableAt (by simp)
  have hfderiv_Ah (J : ι → ℝ) (hJ : J ∈ D) (b : ι → ℝ) (i : ι) :
      fderiv ℝ (fun c ↦ A c i) (hPD J) (fderiv ℝ hPD J b) = b i := by
    have hAi : DifferentiableAt ℝ (fun c ↦ A c i) (hPD J) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).differentiableAt.comp
        (hPD J) (hA_diff J hJ)
    have hcomp := fderiv_comp J hAi (hh_diff J hJ)
    have hfun : ((fun c ↦ A c i) ∘ hPD) =ᶠ[𝓝 J] fun K : ι → ℝ ↦ K i :=
      Filter.eventuallyEq_of_mem (hD_open.mem_nhds hJ) fun K hK ↦ by
        simp [hAh K hK]
    have hproj : fderiv ℝ (fun K : ι → ℝ ↦ K i) J =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).fderiv
    have hchain := DFunLike.congr_fun ((hfun.fderiv_eq.symm.trans hcomp).symm) b
    simpa [hproj] using hchain
  -- Step 3: Reparametrize `Ψ` in action coordinates as `Ψ'(θ, J) = Ψ(θ, h J)`.
  let Ψ' : (ι → ℝ) × (ι → ℝ) → M := fun w ↦ Ψ (w.1, hPD w.2)
  have hΨ'_loc : ∀ w : (ι → ℝ) × (ι → ℝ), w.2 ∈ D →
      IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ' w := fun w hw ↦ by
    have hprod : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ∞
        (Prod.map (id : (ι → ℝ) → (ι → ℝ)) hPD) w := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact ((Diffeomorph.refl 𝓘(ℝ, ι → ℝ) (ι → ℝ) ∞).isLocalDiffeomorph w.1).prodMap
        (hPD.isLocalDiffeomorphAt _ _ _ hw)
    exact hprod.comp (hg := (hUc_prop (hPD w.2) (hh_mem_Uc w.2 hw)).2.1 w.1)
  have hΨ'_eval₂ (w : (ι → ℝ) × (ι → ℝ)) (hw : w.2 ∈ D) (a a' b b' : ι → ℝ) :
      SmoothBundleForm.eval₂ σ (Ψ' w)
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ' w (a, b))
          (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ' w (a', b')) =
        ∑ i, (a i * b' i - a' i * b i) := by
    have hprod_deriv : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        (Prod.map (id : (ι → ℝ) → (ι → ℝ)) hPD) w
        ((ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap (fderiv ℝ hPD w.2)) :=
      ((hasFDerivAt_id w.1).prodMap w (hh_diff w.2 hw).hasFDerivAt).hasMFDerivAt
    have hΨ_mdiff : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (w.1, hPD w.2) :=
      ((hUc_prop (hPD w.2) (hh_mem_Uc w.2 hw)).2.1 w.1).mdifferentiableAt (by simp)
    have hmf (u v : ι → ℝ) : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ' w (u, v) =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (w.1, hPD w.2) (u, fderiv ℝ hPD w.2 v) := by
      change mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I (Ψ ∘ Prod.map id hPD) w (u, v) = _
      rw [mfderiv_comp w hΨ_mdiff hprod_deriv.mdifferentiableAt, hprod_deriv.mfderiv]
      rfl
    rw [hmf a b, hmf a' b',
      (hUc_prop (hPD w.2) (hh_mem_Uc w.2 hw)).2.2.1 w.1 a a'
        (fderiv ℝ hPD w.2 b) (fderiv ℝ hPD w.2 b')]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hfderiv_Ah w.2 hw b' i, hfderiv_Ah w.2 hw b i]
  have hΨ'_eq_iff {w w' : (ι → ℝ) × (ι → ℝ)} (hw : w.2 ∈ D) (hw' : w'.2 ∈ D) :
      Ψ' w = Ψ' w' ↔ CotangentBundle.torusCoverMap p₂π w =
        CotangentBundle.torusCoverMap p₂π w' := by
    rcases w with ⟨θ, J⟩
    rcases w' with ⟨θ', J'⟩
    rw [(hUc_prop (hPD J) (hh_mem_Uc J hw)).2.2.2 (hPD J') (hh_mem_Uc J' hw') θ θ',
      hPD.injOn.eq_iff hw' hw, CotangentBundle.torusCoverMap_eq_iff]
  -- Step 4: Descend `Ψ'` along `CotangentBundle.torusCoverMap p₂π` on `Ω = {ξ | action ξ ∈ D}`.
  let Ω : Set (CotangentBundle I_T (∀ _ : ι, AddCircle (2 * π))) :=
    {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D}
  have hΩ_open : IsOpen Ω :=
    hD_open.preimage (CotangentBundle.contMDiff_torusActionCoord p₂π 0).continuous
  let π_cov := CotangentBundle.torusCoverMap p₂π
  have hact_cov (w : (ι → ℝ) × (ι → ℝ)) : (fun i ↦ (π_cov w).2 (Pi.single i 1)) = w.2 :=
    funext fun i ↦ CotangentBundle.torusCoverMap_snd_apply_single p₂π w i
  have hsurj : Surjective π_cov := CotangentBundle.torusCoverMap_surjective p₂π
  let ψ : CotangentBundle I_T (∀ _ : ι, AddCircle (2 * π)) → M := fun ξ ↦ Ψ' (surjInv hsurj ξ)
  have hψ_comp : ∀ w : (ι → ℝ) × (ι → ℝ), w.2 ∈ D → ψ (π_cov w) = Ψ' w := fun w hw ↦ by
    have hcov : π_cov (surjInv hsurj (π_cov w)) = π_cov w := surjInv_eq hsurj (π_cov w)
    have hmem : (surjInv hsurj (π_cov w)).2 ∈ D := by
      have h2 := ((CotangentBundle.torusCoverMap_eq_iff p₂π _ _ _ _).1 hcov).1
      exact h2.symm ▸ hw
    exact (hΨ'_eq_iff hmem hw).2 hcov
  have hψ_loc : IsLocalDiffeomorphOn I_C I ∞ ψ Ω := by
    rintro ⟨ξ, hξ⟩
    obtain ⟨w, rfl⟩ := hsurj ξ
    have hw : w.2 ∈ D := hact_cov w ▸ hξ
    let h := hΨ'_loc w hw
    let Φ := h.localInverse.symm.restrOpen (univ ×ˢ D) (isOpen_univ.prod hD_open)
    have hcomp_loc : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ (ψ ∘ π_cov) w :=
      TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Φ)
        (by simp [Φ, h.localInverse_mem_target, hw]) fun u hu ↦ by
          have hu' : u ∈ h.localInverse.target ∧ u.2 ∈ D := by simpa [Φ] using hu
          have hΨ'_u : Ψ' u = h.localInverse.symm u := by
            have hmem : h.localInverse.symm u ∈ h.localInverse.source :=
              h.localInverse.map_target hu'.1
            have hinv := h.localInverse_right_inv hmem
            have hright : h.localInverse (h.localInverse.symm u) = u :=
              h.localInverse.right_inv hu'.1
            rwa [hright] at hinv
          simpa [Φ, hψ_comp u hu'.2] using hΨ'_u
    exact hcomp_loc.of_comp_right (CotangentBundle.isLocalDiffeomorph_torusCoverMap p₂π ∞ w)
  have hψ_inj : InjOn ψ Ω := fun ξ₁ hξ₁ ξ₂ hξ₂ hEq ↦ by
    obtain ⟨w₁, rfl⟩ := hsurj ξ₁
    obtain ⟨w₂, rfl⟩ := hsurj ξ₂
    have hw₁ : w₁.2 ∈ D := hact_cov w₁ ▸ hξ₁
    have hw₂ : w₂.2 ∈ D := hact_cov w₂ ▸ hξ₂
    rw [hψ_comp w₁ hw₁, hψ_comp w₂ hw₂] at hEq
    exact (hΨ'_eq_iff hw₁ hw₂).1 hEq
  have : Nonempty (CotangentBundle I_T (∀ _ : ι, AddCircle (2 * π))) :=
    ⟨Bundle.TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) 0 0⟩
  let ψPD := hψ_loc.partialDiffeomorphOfInjOn hΩ_open hψ_inj
  let φ := ψPD.symm
  have hφ_src : φ.source = ψ '' Ω := by simp [φ, ψPD]
  have hφ_tgt : φ.target = Ω := by simp [φ, ψPD]
  have hψPD_coe : ⇑ψPD = ψ := by simp [ψPD]
  -- Check that `ψ` maps `{ξ | action ξ = I₀}` onto `L`.
  have hψ_image_I₀ : ψ '' {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = I₀} = L := by
    ext x
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      obtain ⟨w, rfl⟩ := hsurj ξ
      have hw : w.2 = I₀ := hact_cov w ▸ hξ
      have hwD : w.2 ∈ D := hw ▸ hI₀_mem
      rw [hψ_comp w hwD, ← hrange]
      exact ⟨w.1, by simp [Ψ', hw, hh_I₀]⟩
    · intro hx
      rw [← hrange] at hx
      obtain ⟨θ, rfl⟩ := hx
      refine ⟨π_cov (θ, I₀), hact_cov (θ, I₀), ?_⟩
      rw [hψ_comp (θ, I₀) hI₀_mem]
      simp [Ψ', hh_I₀]
  have hL_sub : L ⊆ φ.source := by
    rw [← hψ_image_I₀, hφ_src]
    exact image_mono fun ξ hξ ↦ by
      change (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D
      rw [hξ]
      exact hI₀_mem
  have hφ_image_L : φ '' L = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = I₀} := by
    rw [← hψ_image_I₀]
    ext ξ
    constructor
    · rintro ⟨_, ⟨η, hη, rfl⟩, rfl⟩
      have hηΩ : η ∈ ψPD.source := by
        rw [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source]
        change (fun i ↦ η.2 (Pi.single i 1)) ∈ D
        rw [hη]
        exact hI₀_mem
      have hleft : φ (ψ η) = η := by
        simpa [φ, hψPD_coe] using ψPD.left_inv hηΩ
      rwa [hleft]
    · intro hξ
      have hξΩ : ξ ∈ ψPD.source := by
        rw [IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source]
        change (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D
        rw [hξ]
        exact hI₀_mem
      have hleft : φ (ψ ξ) = ξ := by
        simpa [φ, hψPD_coe] using ψPD.left_inv hξΩ
      exact ⟨ψ ξ, ⟨ξ, hξ, rfl⟩, hleft⟩
  -- Step 5: `ψ` pulls `σ` back to `ω` on `Ω`, hence `φ = ψ⁻¹` pulls `ω` back to `σ` on `φ.source`.
  have hψ_symp : ∀ ξ ∈ Ω, ∀ u u' : TangentSpace I_C ξ,
      SmoothBundleForm.eval₂ σ (ψ ξ) (mfderiv I_C I ψ ξ u) (mfderiv I_C I ψ ξ u') =
        SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm I_T (∀ _ : ι, AddCircle (2 * π))) ξ u u' := by
    intro ξ hξ u u'
    obtain ⟨w, rfl⟩ := hsurj ξ
    have hw : w.2 ∈ D := hact_cov w ▸ hξ
    have hcov_surj :=
      ((CotangentBundle.isLocalDiffeomorph_torusCoverMap p₂π ∞ w).isInvertible_mfderiv
        (by simp)).surjective
    obtain ⟨⟨a, b⟩, hab⟩ := hcov_surj u
    obtain ⟨⟨a', b'⟩, hab'⟩ := hcov_surj u'
    rw [← hab, ← hab']
    have hev : (ψ ∘ π_cov) =ᶠ[𝓝 w] Ψ' :=
      Filter.eventuallyEq_of_mem ((isOpen_univ.prod hD_open).mem_nhds ⟨trivial, hw⟩)
        fun z hz ↦ hψ_comp z hz.2
    have hmd_ψ : MDifferentiableAt I_C I ψ (π_cov w) :=
      (hψ_loc ⟨π_cov w, hξ⟩).mdifferentiableAt (by simp)
    have hmd_cov : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I_C π_cov w :=
      (CotangentBundle.isLocalDiffeomorph_torusCoverMap p₂π ∞ w).mdifferentiableAt (by simp)
    have hchain (v : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) w) :
        mfderiv I_C I ψ (π_cov w) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I_C π_cov w v) =
          mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ' w v := by
      rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp w hmd_ψ hmd_cov, hev.mfderiv_eq]
      rfl
    rw [hchain (a, b), hchain (a', b'), hψ_comp w hw, hΨ'_eval₂ w hw a a' b b',
      CotangentBundle.eval₂_symplecticForm_mfderiv_torusCoverMap p₂π w a a' b b']
  refine ⟨φ, hPD, I₀, hL_sub, hφ_tgt, hI₀_mem, hφ_image_L, ?_, ?_, hh_I₀⟩
  · intro x hx v w
    have hξ : φ x ∈ Ω := hφ_tgt ▸ φ.map_source hx
    have hψφ : ψPD (φ x) = x := ψPD.right_inv hx
    have hinv_v : mfderiv I_C I ψPD (φ x) (mfderiv I I_C φ x v) = v :=
      ψPD.mfderiv_apply_mfderiv_symm_apply (by simp) hx v
    have hinv_w : mfderiv I_C I ψPD (φ x) (mfderiv I I_C φ x w) = w :=
      ψPD.mfderiv_apply_mfderiv_symm_apply (by simp) hx w
    have h := hψ_symp (φ x) hξ (mfderiv I I_C φ x v) (mfderiv I I_C φ x w)
    rw [← hψPD_coe] at h
    have heval_eq : ∀ (y : M) (_ : y = x) (u₁ u₂ : E),
        SmoothBundleForm.eval₂ σ y u₁ u₂ = SmoothBundleForm.eval₂ σ x u₁ u₂ := by
      rintro _ rfl _ _; rfl
    exact h.symm.trans ((heval_eq _ hψφ _ _).trans (by rw [hinv_v, hinv_w]))
  · intro x hx
    have hξ : φ x ∈ Ω := hφ_tgt ▸ φ.map_source hx
    obtain ⟨w, hw_eq⟩ := hsurj (φ x)
    have hwD : w.2 ∈ D := hact_cov w ▸ (hw_eq.symm ▸ hξ)
    have hx_eq : x = Ψ (w.1, hPD w.2) := by
      have hψφ : ψ (φ x) = x := by
        simpa [φ, hψPD_coe] using ψPD.right_inv hx
      calc x = ψ (φ x) := hψφ.symm
        _ = ψ (π_cov w) := congrArg ψ hw_eq.symm
        _ = Ψ (w.1, hPD w.2) := hψ_comp w hwD
    have hact : (fun i ↦ (φ x).2 (Pi.single i 1)) = w.2 := by
      rw [← hw_eq]
      exact hact_cov w
    rw [hact, hx_eq, (hUc_prop (hPD w.2) (hh_mem_Uc w.2 hwD)).1 w.1]

/-- **Liouville–Arnold action–angle coordinates (bundled partial diffeomorphism).** Let `(M, σ)` be
a Hausdorff boundaryless symplectic manifold of dimension `2 · |ι|`, let `F : M → ι → ℝ` be a
smooth family of pairwise Poisson-commuting functions, and let `L` be the connected component
through `x₀` of the level `F⁻¹(F x₀)`. Assume `L` is compact and consists of regular points of `F`;
no completeness of the Hamiltonian flows and no global density of regular points are assumed.

Then for any family of positive periods `p : ι → ℝ`, there are a smooth partial diffeomorphism
`φ : M → T*Tⁿ` into the cotangent bundle of `Tⁿ = ∀ i, AddCircle (p i)`, a smooth partial
diffeomorphism `h : ℝ^ι → ℝ^ι` on the open action domain `h.source ⊆ ℝ^ι`, and a value
`I₀ ∈ h.source` such that `L ⊆ φ.source`, `φ.target = {ξ | action ξ ∈ h.source}`,
`φ '' L = {ξ | action ξ = I₀}`, `φ` pulls back the canonical symplectic form `ω = -dλ` to `σ` on
`φ.source`, and `F = h ∘ action ∘ φ` on `φ.source` with `h I₀ = F x₀`. -/
theorem exists_partialDiffeomorph_actionAngle (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x₀ : M}
    (hreg : ∀ x ∈ connectedComponentIn (F ⁻¹' {F x₀}) x₀, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x₀}) x₀))
    (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    ∃ (φ : PartialDiffeomorph I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (∀ i, AddCircle (p i))) ∞)
      (h : PartialDiffeomorph 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (ι → ℝ) (ι → ℝ) ∞) (I₀ : ι → ℝ),
      connectedComponentIn (F ⁻¹' {F x₀}) x₀ ⊆ φ.source ∧
      φ.target = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ h.source} ∧
      I₀ ∈ h.source ∧
      φ '' connectedComponentIn (F ⁻¹' {F x₀}) x₀ =
        {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = I₀} ∧
      (∀ x ∈ φ.source, ∀ v w : TangentSpace I x,
        SmoothBundleForm.eval₂
            (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
              (∀ i, AddCircle (p i))) (φ x)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              φ x v)
            (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
              φ x w) =
          SmoothBundleForm.eval₂ σ x v w) ∧
      (∀ x ∈ φ.source, F x = h (fun i ↦ (φ x).2 (Pi.single i 1))) ∧
      h I₀ = F x₀ := by
  have : Fact (0 < 2 * π) := ⟨mul_pos two_pos pi_pos⟩
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let p₂π : ι → ℝ := fun _ ↦ 2 * π
  obtain ⟨φ₀, h₀, I₀, hL₀, htgt₀, hI₀, hφL₀, hsymp₀, hF₀, hhI₀⟩ :=
    hσ.exists_partialDiffeomorph_actionAngle_two_pi hF hcomm hdim hreg hK
  -- Postcompose with the symplectic cotangent lift of coordinatewise period rescaling `2π → p`.
  let R := (AddCircle.piDiffeomorphAddCircle p₂π p ∞).cotangent
  let RPD : PartialDiffeomorph I_C I_C
      (CotangentBundle I_T (∀ _ : ι, AddCircle (2 * π)))
      (CotangentBundle I_T (∀ i, AddCircle (p i))) ∞ :=
    { toPartialEquiv := R.toHomeomorph.toPartialEquiv
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := R.contMDiff.contMDiffOn
      contMDiffOn_invFun := R.symm.contMDiff.contMDiffOn }
  let φ := φ₀.trans RPD
  -- Action coordinates rescale diagonally by `S J i = (p i)⁻¹ * (2 * π) * J i`.
  let S : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.pi fun i ↦
      ((p i)⁻¹ * (2 * π)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)
    (ContinuousLinearMap.pi fun i ↦
      ((2 * π)⁻¹ * p i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)
    (fun J ↦ funext fun i ↦ by
      have hp : p i ≠ 0 := (Fact.out (p := 0 < p i)).ne'
      simp [smul_eq_mul]
      field_simp)
    (fun J ↦ funext fun i ↦ by
      have hp : p i ≠ 0 := (Fact.out (p := 0 < p i)).ne'
      simp [smul_eq_mul]
      field_simp)
  have hR_act (z : CotangentBundle I_T (∀ _ : ι, AddCircle (2 * π))) :
      (fun i ↦ (R z).2 (Pi.single i 1)) = S (fun i ↦ z.2 (Pi.single i 1)) :=
    funext fun i ↦ by
      simp [R, S, p₂π, smul_eq_mul]
  have hRsymm_act (ξ : CotangentBundle I_T (∀ i, AddCircle (p i))) :
      (fun i ↦ (R.symm ξ).2 (Pi.single i 1)) = S.symm (fun i ↦ ξ.2 (Pi.single i 1)) := by
    apply S.injective
    rw [S.apply_symm_apply, ← hR_act (R.symm ξ), R.apply_symm_apply]
  let h := (S.symm.toPartialDiffeomorph (n := ∞)).trans h₀
  have hh_src : h.source = S.symm ⁻¹' h₀.source := by
    rw [PartialDiffeomorph.trans_source]
    simp [ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hh_coe (J : ι → ℝ) : h J = h₀ (S.symm J) := by
    rw [PartialDiffeomorph.coe_trans]
    simp [ContinuousLinearEquiv.toPartialDiffeomorph_toPartialEquiv]
  have hφ_src : φ.source = φ₀.source := by
    rw [PartialDiffeomorph.trans_source]
    exact inter_univ _
  have hφ_coe : ⇑φ = ⇑R ∘ ⇑φ₀ := rfl
  refine ⟨φ, h, S I₀, hφ_src ▸ hL₀, ?_, by simpa [hh_src] using hI₀, ?_, ?_, ?_,
    by simp [hh_coe, hhI₀]⟩
  · ext ξ
    rw [PartialDiffeomorph.trans_target]
    change ξ ∈ univ ∩ R.symm ⁻¹' φ₀.target ↔ _
    rw [univ_inter, mem_preimage, htgt₀, mem_ofPred_eq, hRsymm_act, hh_src]
    rfl
  · calc φ '' connectedComponentIn (F ⁻¹' {F x₀}) x₀
        = R '' (φ₀ '' connectedComponentIn (F ⁻¹' {F x₀}) x₀) := by
          rw [hφ_coe, image_comp]
      _ = R '' {z | (fun i ↦ z.2 (Pi.single i 1)) = I₀} := by rw [hφL₀]
      _ = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) = S I₀} := by
        ext ξ
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [mem_ofPred_eq, hR_act, hz]
        · intro hξ
          refine ⟨R.symm ξ, ?_, R.apply_symm_apply ξ⟩
          rw [mem_ofPred_eq, hRsymm_act, hξ, S.symm_apply_apply]
  · intro x hx v w
    have hx₀ : x ∈ φ₀.source := hφ_src ▸ hx
    have hmf (u : TangentSpace I x) :
        mfderiv I I_C φ x u = mfderiv I_C I_C R (φ₀ x) (mfderiv I I_C φ₀ x u) := by
      change mfderiv I I_C (R ∘ φ₀) x u = _
      rw [mfderiv_comp x ((R.contMDiff (φ₀ x)).mdifferentiableAt (by simp))
        (φ₀.mdifferentiableAt (by simp) hx₀)]
      rfl
    have hRsymp :=
      (AddCircle.piDiffeomorphAddCircle p₂π p ∞).mpullback_cotangent_symplecticForm
    have heval := SmoothForm.eval₂_mpullback R R.contMDiff
      (CotangentBundle.symplecticForm I_T (∀ i, AddCircle (p i)))
      (φ₀ x) (mfderiv I I_C φ₀ x v) (mfderiv I I_C φ₀ x w)
    rw [hmf v, hmf w]
    change SmoothBundleForm.eval₂ (CotangentBundle.symplecticForm I_T (∀ i, AddCircle (p i)))
      (R (φ₀ x)) _ _ = _
    rw [← heval, hRsymp, hsymp₀ x hx₀ v w]
  · intro x hx
    have hx₀ : x ∈ φ₀.source := hφ_src ▸ hx
    rw [hh_coe]
    change F x = h₀ (S.symm (fun i ↦ (R (φ₀ x)).2 (Pi.single i 1)))
    rw [hR_act, S.symm_apply_apply, hF₀ x hx₀]

/-- **The Liouville–Arnold action–angle theorem.** Let `F : M → ι → ℝ` be a completely integrable
system on a Hausdorff boundaryless symplectic manifold `(M, σ)` of dimension `2 · |ι|`, and let `L`
be the connected component through `x₀` of the level `F⁻¹(F x₀)`. Assume `L` is compact and every
point of `L` is a regular point of `F`; other components of the level need not be regular, and no
completeness of the Hamiltonian flows is assumed.

Then for every positive period `p` there are an open neighbourhood `U` of `L`, an open set
`D ⊆ ℝ^ι`, and a map `φ : M → T*Tⁿ` to the cotangent bundle of `Tⁿ = ι → AddCircle p` which, on
`U`, is an injective local diffeomorphism onto `{ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D}`, pulls
the canonical symplectic form `ω = -dλ = ∑ i, dθᵢ ∧ dIᵢ` back to `σ`, and along which `F` factors
through the action coordinates `fun i ↦ (φ x).2 (Pi.single i 1)`. -/
theorem exists_actionAngle (hσ : σ.IsSymplectic) {F : M → ι → ℝ}
    (hF : σ.IsIntegrableSystem F) {L : Set M} {x₀ : M}
    (hL : L = connectedComponentIn (F ⁻¹' {F x₀}) x₀) (hLc : IsCompact L)
    (hreg : ∀ x ∈ L, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F x) (p : ℝ) [Fact (0 < p)] :
    ∃ U : Set M, IsOpen U ∧ L ⊆ U ∧ ∃ D : Set (ι → ℝ), IsOpen D ∧
      ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
        InjOn φ U ∧
        IsLocalDiffeomorphOn I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ U ∧
        φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          SmoothBundleForm.eval₂
              (CotangentBundle.symplecticForm
                (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (φ x)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x v)
              (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
                𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x w) =
            SmoothBundleForm.eval₂ σ x v w) ∧
        ∃ h : (ι → ℝ) → ι → ℝ, ∀ x ∈ U, F x = h (fun i ↦ (φ x).2 (Pi.single i 1)) := by
  subst hL
  obtain ⟨φ, h, _, hLsub, htgt, -, -, hsymp, hF_eq, -⟩ :=
    hσ.exists_partialDiffeomorph_actionAngle hF.contMDiff hF.poissonBracket_eq_zero
      hF.two_mul_card_eq_finrank hreg hLc (fun _ ↦ p)
  exact ⟨φ.source, φ.open_source, hLsub, h.source, h.open_source, φ, φ.injOn,
    fun x ↦ φ.isLocalDiffeomorphAt _ _ _ x.2, φ.image_source_eq_target.trans htgt, hsymp, h, hF_eq⟩

end IsSymplectic

end ActionAngleNormalForm

/-! ### Linearization of Hamiltonian dynamics in action–angle coordinates -/

section Dynamics

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {p : ι → ℝ} [∀ i, Fact (0 < p i)]

namespace IsNondegenerate

/-- **Hamiltonian vector field of an action-dependent Hamiltonian in action–angle coordinates.** Let
`φ : M → T*Tⁿ` be a `C^n` (`n ≠ 0`) local diffeomorphism at `x` pulling the canonical symplectic
form of `T*Tⁿ` back to a nondegenerate two-form `σ` at `x`. If a Hamiltonian `H : M → ℝ` agrees
near `x` with `y ↦ K (fun i ↦ (φ y).2 (Pi.single i 1))` for a function `K` differentiable at the
actions of `φ x`, then `dφ_x` sends the Hamiltonian vector field `X_H(x)` to `(ω, 0)` where
`ωᵢ = fderiv ℝ K I (Pi.single i 1)`. -/
theorem mfderiv_hamiltonianVectorField_of_actionAngle (hσ : σ.IsNondegenerate) {n : ℕ∞ω}
    (hn : n ≠ 0)
    {φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))}
    {x : M}
    (hφ : IsLocalDiffeomorphAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) n φ x)
    (hφσ : ∀ v w : TangentSpace I x,
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (∀ i, AddCircle (p i))) (φ x)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            φ x v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            φ x w) =
        SmoothBundleForm.eval₂ σ x v w)
    {H : M → ℝ} {K : (ι → ℝ) → ℝ}
    (hHK : H =ᶠ[𝓝 x] fun y ↦ K (fun i ↦ (φ y).2 (Pi.single i 1)))
    (hK : DifferentiableAt ℝ K (fun i ↦ (φ x).2 (Pi.single i 1))) :
    mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ x
        (σ.hamiltonianVectorField H x) =
      (fun i ↦ fderiv ℝ K (fun j ↦ (φ x).2 (Pi.single j 1)) (Pi.single i 1), 0) := by
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let g : CotangentBundle I_T (∀ i, AddCircle (p i)) → ℝ :=
    fun z ↦ K (fun i ↦ z.2 (Pi.single i 1))
  have hg : MDifferentiableAt I_C 𝓘(ℝ) g (φ x) :=
    hK.mdifferentiableAt.comp (φ x)
      (CotangentBundle.hasMFDerivAt_torusActionCoord p (φ x)).mdifferentiableAt
  have hmap := hσ.map_hamiltonianVectorField_of_eval₂
    (CotangentBundle.isSymplectic_symplecticForm (I := I_T)
      (M := ∀ i, AddCircle (p i))).isNondegenerate
    (D := mfderiv I I_C φ x) (f := H) (g := g)
    ((hφ.isInvertible_mfderiv hn).surjective _) hφσ fun u ↦ by
      rw [hHK.mvfderiv_eq]
      exact (mvfderiv_comp_apply x hg (hφ.mdifferentiableAt hn) u).symm
  exact hmap.trans (CotangentBundle.hamiltonianVectorField_torus_comp_action p hK)

/-- **Quasi-periodic linear flow in an action–angle chart.** Let `φ : M → T*Tⁿ` be a `C^n` (`n ≠ 0`)
partial diffeomorphism pulling the canonical symplectic form of `T*Tⁿ` back to `σ` on `φ.source`,
whose target is `{ξ | action ξ ∈ D}` for some set `D ⊆ ℝ^ι`. If `H : M → ℝ` agrees on `φ.source`
with `y ↦ K (fun i ↦ (φ y).2 (Pi.single i 1))`, then for any `x₀ ∈ φ.source` where `K` is
differentiable at `I₀ = action (φ x₀)`, pulling back the linear torus flow at constant frequencies
`ωᵢ = fderiv ℝ K I₀ (Pi.single i 1)` gives a global integral curve of `σ.hamiltonianVectorField H`
in `M`. -/
theorem isMIntegralCurve_symm_of_actionAngle (hσ : σ.IsNondegenerate) {n : ℕ∞ω} (hn : n ≠ 0)
    {D : Set (ι → ℝ)}
    (φ : PartialDiffeomorph I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) M (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))) n)
    (htgt : φ.target = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D})
    (hφσ : ∀ x ∈ φ.source, ∀ v w : TangentSpace I x,
      SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (∀ i, AddCircle (p i))) (φ x)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            φ x v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            φ x w) =
        SmoothBundleForm.eval₂ σ x v w)
    {H : M → ℝ} {K : (ι → ℝ) → ℝ}
    (hHK : ∀ x ∈ φ.source, H x = K (fun i ↦ (φ x).2 (Pi.single i 1)))
    {x₀ : M} (hx₀ : x₀ ∈ φ.source)
    (hK : DifferentiableAt ℝ K (fun i ↦ (φ x₀).2 (Pi.single i 1))) :
    IsMIntegralCurve
      (fun t : ℝ ↦ φ.symm (Bundle.TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ)
        (fun i ↦ (φ x₀).proj i +
          (t * fderiv ℝ K (fun j ↦ (φ x₀).2 (Pi.single j 1)) (Pi.single i 1) : AddCircle (p i)))
        (φ x₀).2))
      (σ.hamiltonianVectorField H) := by
  let I_T := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)
  let I_C := I_T.prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)
  let z₀ := φ x₀
  let Ω : ι → ℝ := fun i ↦ fderiv ℝ K (fun j ↦ z₀.2 (Pi.single j 1)) (Pi.single i 1)
  let γ : ℝ → CotangentBundle I_T (∀ i, AddCircle (p i)) := fun t ↦
    Bundle.TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ z₀.proj i + (t * Ω i : AddCircle (p i))) z₀.2
  have hγ : IsMIntegralCurve γ
      ((CotangentBundle.symplecticForm I_T (∀ i, AddCircle (p i))).hamiltonianVectorField
        (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1)))) :=
    CotangentBundle.isMIntegralCurve_torus_comp_action p z₀ hK
  intro t
  have hγt_mem : γ t ∈ φ.target := by
    have hz₀_mem : z₀ ∈ φ.target := φ.map_source hx₀
    rw [htgt] at hz₀_mem ⊢
    exact hz₀_mem
  have hxt_mem : φ.symm (γ t) ∈ φ.source := φ.map_target hγt_mem
  have hφ_symm_γ : φ (φ.symm (γ t)) = γ t := φ.right_inv hγt_mem
  have hcomp := (φ.symm.mdifferentiableAt hn hγt_mem).hasMFDerivAt.comp t (hγ t)
  refine hcomp.congr_mfderiv ?_
  have hHK_ev : H =ᶠ[𝓝 (φ.symm (γ t))] fun y ↦ K (fun i ↦ (φ y).2 (Pi.single i 1)) :=
    Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hxt_mem) hHK
  have hKt : DifferentiableAt ℝ K (fun i ↦ (φ (φ.symm (γ t))).2 (Pi.single i 1)) := by
    rw [hφ_symm_γ]
    exact hK
  have hX := hσ.mfderiv_hamiltonianVectorField_of_actionAngle hn
    (φ.isLocalDiffeomorphAt _ _ _ hxt_mem) (hφσ _ hxt_mem) hHK_ev hKt
  let v : TangentSpace I_C (γ t) :=
    (CotangentBundle.symplecticForm I_T (∀ i, AddCircle (p i))).hamiltonianVectorField
      (fun z ↦ K (fun i ↦ z.2 (Pi.single i 1))) (γ t)
  have hvec : mfderiv I_C I φ.symm (γ t) v = σ.hamiltonianVectorField H (φ.symm (γ t)) := by
    have hv : v = (Ω, 0) :=
      CotangentBundle.hamiltonianVectorField_torus_comp_action p (z := γ t) hK
    have hact : (fun j ↦ (φ (φ.symm (γ t))).2 (Pi.single j 1)) =
        (fun j ↦ z₀.2 (Pi.single j 1)) := by
      rw [hφ_symm_γ]
      rfl
    have hX' : mfderiv I I_C φ (φ.symm (γ t)) (σ.hamiltonianVectorField H (φ.symm (γ t))) =
        (Ω, 0) :=
      hX.trans (Prod.ext (funext fun i ↦ congrArg (fun a ↦ fderiv ℝ K a (Pi.single i 1)) hact) rfl)
    have hinv := φ.mfderiv_symm_apply_mfderiv_apply hn hxt_mem
      (σ.hamiltonianVectorField H (φ.symm (γ t)))
    rw [hφ_symm_γ] at hinv
    calc mfderiv I_C I φ.symm (γ t) v
        = mfderiv I_C I φ.symm (γ t) (Ω, 0) := congrArg _ hv
      _ = mfderiv I_C I φ.symm (γ t)
            (mfderiv I I_C φ (φ.symm (γ t)) (σ.hamiltonianVectorField H (φ.symm (γ t)))) :=
          congrArg _ hX'.symm
      _ = σ.hamiltonianVectorField H (φ.symm (γ t)) := hinv
  refine ContinuousLinearMap.ext fun s ↦ ?_
  let r : ℝ := s
  change mfderiv I_C I φ.symm (γ t) (r • v) = r • σ.hamiltonianVectorField H (φ.symm (γ t))
  rw [map_smul, hvec]

end IsNondegenerate

end Dynamics

end SmoothTwoForm

end TauCeti
