/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.Normal
import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Central transport as a strict isomorphism of Lakshmibai–Seshadri path crystals

For a finite reduced root datum `P : RootDatum ι X Y` with base `b`, dominant weight `λ : X`, and
central weight `χ : X` (killed by every simple coroot), `LSPath.centralTransport` shears the
canonical timed presentation `LSPath.timed` by `t ↦ t χ`, intertwines the root operators of
`LSPath.crystal`, shifts weights by `χ`, and preserves string lengths.

## Main definitions and results

* `TauCeti.LSPath.crystal_f_centralTransport`, `TauCeti.LSPath.crystal_e_centralTransport`,
  `TauCeti.LSPath.crystal_ε_centralTransport`, `TauCeti.LSPath.crystal_φ_centralTransport`.
* `TauCeti.LSPath.centralTransportIso` (`B(λ)^(σ + χ) ≃ B(λ + χ)^σ`),
  `TauCeti.LSPath.centralTransportIsoUntwistedTarget` (`B(λ)^χ ≃ B(λ + χ)`), and their coherence
  laws (`centralTransportIso_zero`, `centralTransportIso_trans_centralTransportIso`,
  `centralTransportIso_symm`).
* `TauCeti.LSPath.centralIso`: pure-central LS crystals.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4; *Paths and root operators in representation theory*,
  Ann. of Math. 142 (1995), 499--525, Section 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti.LSPath

open RootPairing
open scoped TensorProduct

/-! ### Compatibility with `LSPath.crystal` and the twisted central-transport isomorphisms -/

section CrystalTransport

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} {lam : X}
  [Finite ι] [P.IsReduced]

section Operators

variable (hlam : lam ∈ dominantChamber P b) {χ : X}
  (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (hlam' : lam + χ ∈ dominantChamber P b)

/-- **Central transport commutes with crystal lowering operators.** -/
theorem crystal_f_centralTransport (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').f i (centralTransport χ hχ π) =
      ((crystal hlam).f i π).map (centralTransport χ hχ) := by
  -- Lift to the canonical rational realization `ℚ ⊗[ℤ] X` and lower on the time–weight graph
  -- before forgetting time.
  have := P.flip_isReduced
  have := P.finite_weylGroup_of_base b
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  let F₀ : Module.Dual ℚ (ℚ ⊗[ℤ] X) := Module.Dual.baseChange ℚ (P.coroot' i)
  have hF₀ (x : X) : F₀ (f₀ x) = (P.coroot' i x : ℚ) := by
    rw [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply,
      Module.Dual.baseChange_apply_one_tmul, eq_intCast]
  have hFχ : F₀ (f₀ χ) = 0 := by rw [hF₀ χ, hχ i i.property, Int.cast_zero]
  have hS : (Set.range fun w : P.weylGroup ↦ f₀ (w • lam)).Pairwise fun u v ↦ ¬ SameRay ℚ u v := by
    simpa only [f₀, LinearMap.toAddMonoidHom_coe] using
      P.pairwise_not_sameRay_tensorProduct_mk_orbit ℚ lam
  apply Option.map_injective (toRatPLPath_injective hlam')
  rw [← lower_toPLPath hlam' f₀ i F₀ hF₀]
  have hlow₀ := lower_toPLPath hlam f₀ i F₀ hF₀ π
  cases hf : (crystal hlam).f i π with
  | none =>
    rw [hf, Option.map_none, toPLPath_def, PLPath.lower_ofSegments_map_snd,
      Option.map_eq_none_iff] at hlow₀
    simp [lower_toPLPath_centralTransport, hFχ, hlow₀]
  | some ρ =>
    rw [hf, Option.map_some, toPLPath_def] at hlow₀
    have hmaps := P.mapsTo_preReflection_image_orbit_weylGroup i hF₀ lam
    rw [MulAction.orbit, ← Set.range_comp] at hmaps
    obtain ⟨Γ, hΓ, hseg⟩ := PLPath.distinguished_of_lower_eq_some
      (π.isDistinguished_timed ℚ f₀ hlam (P.tensorProduct_mk_injective ℚ).injOn) hmaps hS hlow₀
    have hΓeq : Γ = PLPath.ofSegments ℚ (ρ.timed ℚ f₀) := by
      rw [← PLPath.ofSegments_segments Γ, ← hseg, toPLPath_def,
        PLPath.distinguished_ofSegments
          (ρ.isDistinguished_timed ℚ f₀ hlam (P.tensorProduct_mk_injective ℚ).injOn) hS]
    rw [lower_toPLPath_centralTransport χ hχ π ℚ f₀ F₀ hFχ, hΓ, Option.map_some, hΓeq,
      PLPath.shiftGraph_ofSegments]
    simp [f₀, LinearMap.coe_snd, toPLPath_centralTransport_eq_ofSegments]

/-- **Central transport commutes with crystal raising operators.** -/
theorem crystal_e_centralTransport (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').e i (centralTransport χ hχ π) =
      ((crystal hlam).e i π).map (centralTransport χ hχ) := by
  have hχ' := (P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b χ).mp hχ
  simpa using (((crystal hlam).weightTwist χ hχ').dual.f_apply_eq_of_e_map (crystal hlam').dual
    (g := centralTransport χ hχ) (i := i) π
    (by simp [weight_centralTransport χ hχ π, add_comm])
    (fun ρ ↦ by simpa using crystal_f_centralTransport hlam hχ hlam' i ρ))

end Operators

section TransportIso

variable (hlam : lam ∈ dominantChamber P b)

/-- **The two-offset central-transport crystal isomorphism
`T_{λ, χ}^σ : B(λ)^(σ + χ) ≃ B(λ + χ)^σ`.** -/
noncomputable def centralTransportIso (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_toLinearMap_coroot_eq_zero b hlam hχ) :
    NormalCrystal.StrictIso
      ((crystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
      ((crystal hlam').weightTwist σ hσ) where
  toEquiv := centralTransport χ
    ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt, crystal_wt]
    rw [weight_centralTransport χ _ π]; abel
  e_toFun i π := by
    simpa using crystal_e_centralTransport hlam
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ)
      hlam' i π

@[simp]
theorem coe_centralTransportIso (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ⇑(centralTransportIso hlam χ σ hχ hσ hlam') = centralTransport χ
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ) :=
  (rfl)

@[simp]
theorem coe_centralTransportIso_symm (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ⇑(centralTransportIso hlam χ σ hχ hσ hlam').symm = (centralTransport χ
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr
        hχ)).symm :=
  funext fun π ↦ EquivLike.injective (centralTransportIso hlam χ σ hχ hσ hlam') (by simp)

/-- **Central transport `B(λ)^χ ≃ B(λ + χ)`**, the `σ = 0` (untwisted target) specialization of
`centralTransportIso`. -/
noncomputable def centralTransportIsoUntwistedTarget (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_toLinearMap_coroot_eq_zero b hlam hχ) :
    NormalCrystal.StrictIso ((crystal hlam).weightTwist χ hχ) (crystal hlam') :=
  ((centralTransportIso hlam χ 0 hχ (by simp) hlam').congrLeft
    (NormalCrystal.weightTwist_congr _ (zero_add χ) _ hχ)).congrRight
    (NormalCrystal.weightTwist_zero (crystal hlam'))

section TransportIsoUntwistedTargetSimp

variable (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
  (hlam' : lam + χ ∈ dominantChamber P b)

@[simp]
theorem coe_centralTransportIsoUntwistedTarget :
    ⇑(centralTransportIsoUntwistedTarget hlam χ hχ hlam') = centralTransport χ
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr
        hχ) := by
  simp [centralTransportIsoUntwistedTarget]

@[simp]
theorem coe_centralTransportIsoUntwistedTarget_symm :
    ⇑(centralTransportIsoUntwistedTarget hlam χ hχ hlam').symm =
      (centralTransport χ
        ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr
          hχ)).symm := by
  simp [centralTransportIsoUntwistedTarget]

/-- Definitional unfolding of `centralTransportIsoUntwistedTarget`. -/
theorem centralTransportIsoUntwistedTarget_def :
    centralTransportIsoUntwistedTarget hlam χ hχ hlam' =
      ((centralTransportIso hlam χ 0 hχ (by simp) hlam').congrLeft
        (NormalCrystal.weightTwist_congr _ (zero_add χ) _ hχ)).congrRight
        (NormalCrystal.weightTwist_zero (crystal hlam')) := (rfl)

end TransportIsoUntwistedTargetSimp

/-- Central transport preserves the `i`-raising string length `ε_i`. -/
theorem crystal_ε_centralTransport {χ : X} (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').ε i (centralTransport χ hχ π) = (crystal hlam).ε i π := by
  simpa using (centralTransportIsoUntwistedTarget hlam χ
    ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b χ).mp hχ)
    hlam').ε_apply i π

/-- Central transport preserves the `i`-lowering string length `φ_i`. -/
theorem crystal_φ_centralTransport {χ : X} (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').φ i (centralTransport χ hχ π) = (crystal hlam).φ i π := by
  simpa using (centralTransportIsoUntwistedTarget hlam χ
    ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b χ).mp hχ)
    hlam').φ_apply i π

/-- **Strict-map identity law `T_{λ, 0}^σ = id`** on `B(λ)^σ`. -/
theorem centralTransportIso_zero (σ : X)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam0 : lam + 0 ∈ dominantChamber P b := by simpa using hlam) :
    ((centralTransportIso hlam 0 σ (by simp) hσ hlam0).congrLeft
      (NormalCrystal.weightTwist_congr _ (add_zero σ) _ hσ)).trans
      ((congrIso (add_zero lam) hlam0 hlam).weightTwist σ hσ) =
      NormalCrystal.StrictIso.refl ((crystal hlam).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ by simp [centralTransport_zero]

/-- **Additive composition law `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^(σ + ψ) = T_{λ, χ + ψ}^σ`.** -/
theorem centralTransportIso_trans_centralTransportIso (χ ψ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlamχ : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_toLinearMap_coroot_eq_zero b hlam hχ)
    (hlamχψ : (lam + χ) + ψ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_toLinearMap_coroot_eq_zero b hlamχ hψ)
    (hlam_χψ : lam + (χ + ψ) ∈ dominantChamber P b := by rw [← add_assoc]; exact hlamχψ) :
    ((centralTransportIso hlam χ (σ + ψ) hχ (by simp [map_add, hσ, hψ]) hlamχ).trans
      (centralTransportIso hlamχ ψ σ hψ hσ hlamχψ)).congrLeft
      (NormalCrystal.weightTwist_congr _ (by abel : (σ + ψ) + χ = σ + (χ + ψ)) _
        (by simp [map_add, hσ, hχ, hψ])) =
      (centralTransportIso hlam (χ + ψ) σ (by simp [map_add, hχ, hψ]) hσ hlam_χψ).trans
        ((congrIso (add_assoc lam χ ψ).symm hlam_χψ hlamχψ).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ by
    simpa using centralTransport_centralTransport χ
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ) π
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hψ)

/-- **Inverse formula `(T_{λ, χ}^σ)⁻¹ = T_{λ + χ, -χ}^(σ + χ)`.** -/
theorem centralTransportIso_symm (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlamχ : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_toLinearMap_coroot_eq_zero b hlam hχ)
    (hlamχ_neg : (lam + χ) + (-χ) ∈ dominantChamber P b := by simpa using hlam) :
    (centralTransportIso hlam χ σ hχ hσ hlamχ).symm =
      ((centralTransportIso hlamχ (-χ) (σ + χ) (by simp [hχ])
        (by simp [map_add, hσ, hχ]) hlamχ_neg).congrLeft
        (NormalCrystal.weightTwist_congr _ (add_neg_cancel_right σ χ) _ hσ)).trans
        ((congrIso (add_neg_cancel_right lam χ) hlamχ_neg hlam).weightTwist
          (σ + χ) (by simp [map_add, hσ, hχ])) :=
  NormalCrystal.StrictIso.ext fun π ↦ by
    simpa using centralTransport_symm_apply χ
      ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ) π

end TransportIso

/-! ### Pure-central LS crystals -/

section Central

variable (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)

/-- **For any pure central weight `χ`, `crystal` is strictly isomorphic to
`NormalCrystal.central χ hχ`.** -/
noncomputable def centralIso
    (hχ_dom : χ ∈ dominantChamber P b :=
      P.mem_dominantChamber_of_forall_coroot'_eq_zero b
        ((P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ)) :
    NormalCrystal.StrictIso (crystal hχ_dom) (NormalCrystal.central χ hχ) := by
  have hχ' :=
    (P.forall_mem_support_coroot'_eq_zero_iff_forall_toLinearMap_coroot_eq_zero b _).mpr hχ
  exact
    { toEquiv :=
        { toFun _ := PUnit.unit, invFun _ := straight χ
          left_inv π := (eq_straight_of_forall_coroot'_eq_zero hχ' π).symm
          right_inv u := by cases u; rfl }
      wt_toFun π := by rw [eq_straight_of_forall_coroot'_eq_zero hχ' π]; simp
      e_toFun i π := by rw [eq_straight_of_forall_coroot'_eq_zero hχ' π]; simp }

@[simp]
theorem centralIso_apply (hχ_dom : χ ∈ dominantChamber P b) (π : LSPath P b χ) :
    centralIso χ hχ hχ_dom π = PUnit.unit := (rfl)

@[simp]
theorem centralIso_symm_apply (hχ_dom : χ ∈ dominantChamber P b) (u : PUnit) :
    (centralIso χ hχ hχ_dom).symm u = straight χ := by
  cases u; exact (centralIso χ hχ hχ_dom).symm_apply_apply (straight χ)

end Central

end CrystalTransport

end TauCeti.LSPath
