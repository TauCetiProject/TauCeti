/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Flux
import TauCeti.Geometry.Manifold.Instances.Icc

/-!
# The flux homomorphism

Let `σ` be a closed two-form on a manifold `M` and let `φ_t` and `ψ_t`, `t ∈ [0, 1]`, be smooth
diffeotopies of `M`. Their pointwise composite `Φ.trans Ψ`, with time slices `ψ_t ∘ φ_t`
(`TauCeti.Diffeotopy.trans`), has flux form

`Flux(ψ ∘ φ) = Flux(ψ) + Flux_{ψ₁^* σ}(φ) + d g`

for a smooth function `g` (`TauCeti.Diffeotopy.fluxForm_trans_sub_sub_mem_exactForms`), where
`Flux_{ψ₁^* σ}(φ)` is the flux form of `φ` with respect to the pulled back form `ψ₁^* σ`. When
`φ₁` and `ψ₁` preserve `σ` this says that the flux is additive on pointwise composites
(`TauCeti.Diffeotopy.flux_trans`):

`Flux(ψ ∘ φ) = Flux(ψ) + Flux(φ)` in `H¹_dR(M)`.

In particular reversing a diffeotopy negates its flux (`TauCeti.Diffeotopy.flux_symm`). Only the
final diffeomorphisms are required to preserve `σ`; the intermediate diffeomorphisms of the
diffeotopies are arbitrary, and `σ` need not be nondegenerate.

## Implementation notes

The motion of `Φ.trans Ψ` is the motion of `Ψ` after the level-preserving motion
`F (x, t) = (φ_t x, t)` of the cylinder `M × [0, 1]`. The homotopy
`G ((x, t), s) = (φ_{s t} x, t)` joins the identity of the cylinder to `F`. For the closed form
`τ = ψ^* σ` on the cylinder, the cochain-homotopy identity in `s` gives `F^* τ - τ = d L` with
`L = h_s (G^* τ)`, and the cochain-homotopy identity in `t` then gives

`h_t (F^* τ) - h_t τ = ι₁^* L - ι₀^* L - d (h_t L)`.

The two ends of `L` are flux forms: `G` restricted to `t = 1` is the motion of `φ` followed by
the slice inclusion at time one, and `G` restricted to `t = 0` is stationary. Reading them off
uses the naturality of the homotopy operator along slice inclusions
(`TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`).

## Main results

* `TauCeti.Diffeotopy.fluxForm_trans_sub_sub_mem_exactForms`: the flux form of a pointwise
  composite of diffeotopies, modulo exact forms.
* `TauCeti.Diffeotopy.flux_trans`: the flux of a pointwise composite is the sum of the fluxes.
* `TauCeti.Diffeotopy.flux_symm`: the flux of the reversed diffeotopy is the negated flux.
* `TauCeti.Diffeotopy.flux_symm_trans`: the flux of `φ_t ∘ ψ_t⁻¹` is the difference of the
  fluxes.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (Φ Ψ : Diffeotopy J ∞ M)

/-- The homotopy `((x, t), s) ↦ (φ_{s t} x, t)` of the cylinder `M × [0, 1]`, from the identity at
`s = 0` to the level-preserving motion `(x, t) ↦ (φ_t x, t)` at `s = 1`. -/
private def cylinderRescale : (M × unitInterval) × unitInterval → M × unitInterval :=
  fun q ↦ (Φ (q.2 * q.1.2, q.1.1), q.1.2)

private theorem contMDiff_cylinderRescale :
    ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ Φ.cylinderRescale :=
  (Φ.contMDiff.comp (((contMDiff_mul (𝓡∂ 1) ∞).comp
    (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst))).prodMk
      (contMDiff_fst.comp contMDiff_fst))).prodMk (contMDiff_snd.comp contMDiff_fst)

/-- At `s = 0` the homotopy is the identity of the cylinder. -/
private theorem cylinderRescale_comp_zero :
    Φ.cylinderRescale ∘ (fun p ↦ (p, (0 : unitInterval))) = id :=
  funext fun p ↦ by simp [cylinderRescale]

/-- At `s = 1` the homotopy is the level-preserving motion of `Φ`. -/
private theorem cylinderRescale_comp_one :
    Φ.cylinderRescale ∘ (fun p ↦ (p, (1 : unitInterval))) = fun p ↦ (Φ.cylinderMap p, p.2) :=
  funext fun p ↦ by simp [cylinderRescale]

/-- Over the final time `t = 1` the homotopy is the motion of `Φ`, read at time one. -/
private theorem cylinderRescale_comp_prodMap_one :
    Φ.cylinderRescale ∘ Prod.map (fun x ↦ (x, (1 : unitInterval))) id =
      (fun x ↦ (x, (1 : unitInterval))) ∘ Φ.cylinderMap :=
  funext fun p ↦ by simp [cylinderRescale]

/-- Over the initial time `t = 0` the homotopy is stationary: it is the motion of the constant
diffeotopy, read at time zero. -/
private theorem cylinderRescale_comp_prodMap_zero :
    Φ.cylinderRescale ∘ Prod.map (fun x ↦ (x, (0 : unitInterval))) id =
      (fun x ↦ (x, (0 : unitInterval))) ∘ (refl J ∞ M).cylinderMap :=
  funext fun p ↦ by simp [cylinderRescale]

variable [IsManifold J ∞ M]

/-- The slice at time `c` of the homotopy operator in `s` of `G^* τ` is the flux form, with
respect to the slice of `τ` at time `c`, of a diffeotopy `Θ` whose motion is `G` over time `c`. -/
private theorem mpullback_homotopyOperator_mpullback_cylinderRescale (τ : SmoothForm
    (J.prod (𝓡∂ 1)) (M × unitInterval) ℝ 2) (c : unitInterval) (Θ : Diffeotopy J ∞ M)
    (hΘ : Φ.cylinderRescale ∘ Prod.map (fun x ↦ (x, c)) id =
      (fun x ↦ (x, c)) ∘ Θ.cylinderMap) :
    mpullback J (J.prod (𝓡∂ 1)) (fun x ↦ (x, c)) (homotopyOperator
        (SmoothForm.mpullback Φ.cylinderRescale Φ.contMDiff_cylinderRescale τ).1) =
      (Θ.fluxForm (SmoothForm.mpullback (fun x ↦ (x, c)) (contMDiff_id.prodMk contMDiff_const)
        τ)).1 := by
  have : IsManifold (J.prod (𝓡∂ 1)) 1 (M × unitInterval) := IsManifold.of_le (n := ∞) (by simp)
  have hslice : MDifferentiable J (J.prod (𝓡∂ 1)) fun x : M ↦ (x, c) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  have hprod : MDifferentiable (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      (Prod.map (fun x : M ↦ (x, c)) (id : unitInterval → unitInterval)) :=
    hslice.prodMap mdifferentiable_id
  rw [← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm hslice
      ((SmoothForm.mpullback _ _ τ).isSmoothForm.of_le (by simp)),
    SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp hprod
      (Φ.contMDiff_cylinderRescale.mdifferentiable (by simp)), hΘ,
    TauCeti.mpullback_comp (Θ.contMDiff_cylinderMap.mdifferentiable (by simp)) hslice,
    coe_fluxForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]

/-- For a closed form `τ` on the cylinder, the homotopy operator in `s` of `G^* τ` is a primitive
of `F^* τ - τ`, where `F (x, t) = (φ_t x, t)` is the level-preserving motion of `Φ`. -/
private theorem mextDeriv_homotopyOperator_mpullback_cylinderRescale
    {τ : SmoothForm (J.prod (𝓡∂ 1)) (M × unitInterval) ℝ 2} (hτ : SmoothForm.IsClosed τ) :
    mextDeriv (homotopyOperator
        (SmoothForm.mpullback Φ.cylinderRescale Φ.contMDiff_cylinderRescale τ).1) =
      mpullback (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) (fun p ↦ (Φ.cylinderMap p, p.2)) τ.1 - τ.1 := by
  have : IsManifold (J.prod (𝓡∂ 1)) 2 (M × unitInterval) := IsManifold.of_le (n := ∞) (by simp)
  have hres (c : unitInterval) : MDifferentiable (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      fun p : M × unitInterval ↦ (p, c) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  have hG := Φ.contMDiff_cylinderRescale.mdifferentiable (n := ∞) (by simp)
  funext p
  rw [mextDeriv_homotopyOperator ((SmoothForm.mpullback _ _ τ).isSmoothForm.of_le (by simp))
    ((SmoothForm.isClosed_def _).mp (hτ.mpullback _ _)) p, SmoothForm.coe_mpullback,
    ← TauCeti.mpullback_comp (hres 1) hG, ← TauCeti.mpullback_comp (hres 0) hG,
    cylinderRescale_comp_one, cylinderRescale_comp_zero, TauCeti.mpullback_id, Pi.sub_apply]

/-- **The flux form of a pointwise composite.** For a closed two-form `σ` and diffeotopies `φ`
and `ψ`, the flux form of the composite `ψ_t ∘ φ_t` differs by an exact form from the sum of the
flux form of `ψ` and the flux form of `φ` with respect to `ψ₁^* σ`. No diffeomorphism involved
needs to preserve `σ`. -/
theorem fluxForm_trans_sub_sub_mem_exactForms {σ : SmoothForm J M ℝ 2}
    (hσ : SmoothForm.IsClosed σ) :
    (Φ.trans Ψ).fluxForm σ - Ψ.fluxForm σ -
        Φ.fluxForm (SmoothForm.mpullback Ψ.final Ψ.final.contMDiff σ) ∈ exactForms J M 1 := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold (J.prod (𝓡∂ 1)) ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) (M × unitInterval) :=
    IsManifold.of_le (n := ∞) (by simp)
  have hcyl : MDifferentiable (J.prod (𝓡∂ 1)) J Ψ.cylinderMap :=
    Ψ.contMDiff_cylinderMap.mdifferentiable (by simp)
  -- `τ = ψ^* σ` on the cylinder and `η = G^* τ` on the double cylinder are closed.
  set τ := SmoothForm.mpullback Ψ.cylinderMap Ψ.contMDiff_cylinderMap σ
  set η := SmoothForm.mpullback Φ.cylinderRescale Φ.contMDiff_cylinderRescale τ
  have hτ : SmoothForm.IsClosed τ := hσ.mpullback _ _
  -- `L = h_s η` satisfies `d L = F^* τ - τ`, where `F^* τ` is the pullback of `σ` along the
  -- motion of the composite.
  set L := homotopyOperator η.1
  have hdL : mextDeriv L = (SmoothForm.mpullback (Φ.trans Ψ).cylinderMap
      (Φ.trans Ψ).contMDiff_cylinderMap σ).1 - τ.1 := by
    rw [Φ.mextDeriv_homotopyOperator_mpullback_cylinderRescale hτ, SmoothForm.coe_mpullback,
      SmoothForm.coe_mpullback, cylinderMap_trans,
      TauCeti.mpullback_comp ((Φ.contMDiff_cylinderMap.prodMk contMDiff_snd).mdifferentiable
        (by simp)) hcyl]
  -- The ends of `L` are the flux form of `φ` for `ψ₁^* σ` and the flux form of the constant
  -- diffeotopy, which vanishes.
  have hL₁ := mpullback_homotopyOperator_mpullback_cylinderRescale Φ τ 1 Φ
    Φ.cylinderRescale_comp_prodMap_one
  have hL₀ := mpullback_homotopyOperator_mpullback_cylinderRescale Φ τ 0 (refl J ∞ M)
    Φ.cylinderRescale_comp_prodMap_zero
  -- The slices of `τ` at the two ends are `ψ₁^* σ` and `σ`.
  rw [Ψ.mpullback_slice_one_mpullback_cylinderMap] at hL₁
  rw [Ψ.mpullback_slice_zero_mpullback_cylinderMap, fluxForm_refl, Submodule.coe_zero] at hL₀
  -- The cochain-homotopy identity in `t` for `L` concludes.
  have hLs : IsSmoothForm (J.prod (𝓡∂ 1)) ∞ L := IsSmoothForm.homotopyOperator η.isSmoothForm
  rw [exactForms_succ]
  refine ⟨-⟨homotopyOperator L, (IsSmoothForm.homotopyOperator hLs).mem_smoothBundleForms⟩,
    Subtype.ext (funext fun x ↦ ?_)⟩
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv (hLs.of_le (by simp)) x
  -- The homotopy operator in `t` is additive on the continuous forms `F^* τ - τ` and `τ`.
  have hadd := homotopyOperator_add
    ((SmoothForm.mpullback (Φ.trans Ψ).cylinderMap (Φ.trans Ψ).contMDiff_cylinderMap σ -
      τ).isSmoothForm.of_le (by simp)) (τ.isSmoothForm.of_le (by simp))
  rw [Submodule.coe_sub, sub_add_cancel] at hadd
  rw [hdL, hL₁, hL₀, Pi.zero_apply, sub_zero] at key
  rw [map_neg, Submodule.coe_neg, Pi.neg_apply, mextDerivₗ_apply, Submodule.coe_sub, Pi.sub_apply,
    Submodule.coe_sub, Pi.sub_apply, coe_fluxForm, coe_fluxForm, hadd, Pi.add_apply, ← key]
  abel

/-- **The flux homomorphism.** For a closed two-form `σ` preserved by the final diffeomorphisms
`φ₁` and `ψ₁`, the flux of the pointwise composite `ψ_t ∘ φ_t` is the sum of the fluxes of `φ`
and `ψ`. -/
theorem flux_trans (σ : closedForms J M 2) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (h : (Φ.trans Ψ).final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    (Φ.trans Ψ).flux σ h = Ψ.flux σ hΨ + Φ.flux σ hΦ := by
  have key := Φ.fluxForm_trans_sub_sub_mem_exactForms Ψ
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.1).mp σ.2))
  rw [SmoothForm.mem_diffeomorphStabilizer.mp hΨ, sub_sub] at key
  rw [flux_def, flux_def, flux_def, ← map_add, ← sub_eq_zero, ← map_sub,
    deRhamCohomology.mk_eq_zero_iff]
  exact key

/-- **The flux of the reversed diffeotopy.** For a closed two-form `σ` preserved by `φ₁`, the
diffeotopy `φ_t⁻¹` has the negated flux of `φ`. -/
theorem flux_symm (σ : closedForms J M 2) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (h : Φ.symm.final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    Φ.symm.flux σ h = -Φ.flux σ hΦ := by
  have hrefl : (refl J ∞ M).final ∈ SmoothForm.diffeomorphStabilizer σ.1 := by
    rw [final_refl]
    exact (SmoothForm.diffeomorphStabilizer σ.1).one_mem
  have hzero : ∀ h' : (Φ.trans Φ.symm).final ∈ SmoothForm.diffeomorphStabilizer σ.1,
      (Φ.trans Φ.symm).flux σ h' = 0 := by
    rw [self_trans_symm]
    exact flux_refl σ
  rw [eq_neg_iff_add_eq_zero, ← hzero (Φ.self_trans_symm ▸ hrefl), flux_trans]

/-- **The flux of a quotient of diffeotopies.** For a closed two-form `σ` preserved by `φ₁` and
`ψ₁`, the diffeotopy `φ_t ∘ ψ_t⁻¹` has the flux of `φ` minus the flux of `ψ`. -/
theorem flux_symm_trans (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (h : (Ψ.symm.trans Φ).final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    (Ψ.symm.trans Φ).flux σ h = Φ.flux σ hΦ - Ψ.flux σ hΨ := by
  have hΨs : Ψ.symm.final ∈ SmoothForm.diffeomorphStabilizer σ.1 := by
    rw [final_symm, ← Diffeomorph.inv_def]
    exact (SmoothForm.diffeomorphStabilizer σ.1).inv_mem hΨ
  rw [flux_trans Ψ.symm Φ σ hΨs hΦ, flux_symm Ψ σ hΨ, sub_eq_add_neg]

end Diffeotopy

end TauCeti
