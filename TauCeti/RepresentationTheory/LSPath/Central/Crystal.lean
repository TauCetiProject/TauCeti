/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.Normal
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.LSPath.OrbitStable

/-!
# Central transport as a strict isomorphism of Lakshmibai–Seshadri path crystals

Let `P : RootDatum ι X Y` be a reduced root datum with finite index type and base `b`, let `λ : X`
be a dominant weight, and let `χ : X` be a central weight (annihilated by every simple coroot).
Adding the linear path `t ↦ t χ` is not well-defined on arbitrary reparametrization classes of
piecewise-linear paths (`TauCeti.PLPath.not_exists_shiftTimed_on_paths`), so
`TauCeti.LSPath.centralTransport` applies the shear to the canonical distinguished presentation
`TauCeti.LSPath.timed` with slopes in `W λ`.

This file proves that `TauCeti.LSPath.centralTransport` intertwines the Kashiwara root operators of
`TauCeti.LSPath.crystal`, shifts weights by `χ`, and preserves string lengths, using
`TauCeti.PLPath.lower_ofSegments_shiftTimed` and `TauCeti.PLPath.distinguished_of_lower_eq_some`.
For central weights `χ, σ : X`, we package this into the strict crystal isomorphism
`TauCeti.LSPath.centralTransportIso` (`B(λ)^(σ + χ) ≃ B(λ + χ)^σ`) and its `σ = 0` specialization
`TauCeti.LSPath.centralTransportIsoZero` (`B(λ)^χ ≃ B(λ + χ)`), prove the strict-map identity,
additive composition, and inverse coherence laws, and identify pure-central LS path crystals (in
particular for `0`) with `TauCeti.NormalCrystal.central` (`TauCeti.LSPath.centralIso`,
`TauCeti.LSPath.zeroIso`).

## Main definitions and results

* `TauCeti.LSPath.weight_centralTransport`, `TauCeti.LSPath.crystal_f_centralTransport`,
  `TauCeti.LSPath.crystal_e_centralTransport`, `TauCeti.LSPath.crystal_ε_centralTransport`, and
  `TauCeti.LSPath.crystal_φ_centralTransport`: compatibility of central transport with weights,
  root operators, and string lengths.
* `TauCeti.LSPath.centralTransportIso`, `TauCeti.LSPath.centralTransportIsoZero`,
  `TauCeti.LSPath.centralTransportIso_zero`,
  `TauCeti.LSPath.centralTransportIso_trans_centralTransportIso`, and
  `TauCeti.LSPath.centralTransportIso_symm`.
* `TauCeti.LSPath.centralIso` and `TauCeti.LSPath.zeroIso`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti.LSPath

open RootPairing
open scoped TensorProduct

/-! ### Compatibility with `LSPath.crystal` and the twisted central-transport isomorphisms -/

section CrystalTransport

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

/-- Central transport shifts the lattice-valued weight of an LS path by `χ`. -/
theorem weight_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (centralTransport χ hχ π).weight hlam' = π.weight hlam + χ :=
  (weight_eq_iff_endpoint (𝕜 := ℚ)
    (f := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom)
    (P.tensorProduct_mk_injective ℚ) hlam' _).mpr
    (by rw [endpoint_toPLPath_centralTransport, map_add, apply_weight ℚ])

/-- **Central transport commutes with crystal lowering operators.** -/
theorem crystal_f_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').f i (centralTransport χ hχ π) =
      ((crystal hlam).f i π).map (centralTransport χ hχ) := by
  have := P.flip_isReduced
  have := P.finite_weylGroup_of_base b
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  let F₀ : Module.Dual ℚ (ℚ ⊗[ℤ] X) := Module.Dual.baseChange ℚ (P.coroot' i)
  have hf₀ : Function.Injective f₀ := P.tensorProduct_mk_injective ℚ
  have hF₀ (x : X) : F₀ (f₀ x) = (P.coroot' i x : ℚ) := by simp [f₀, F₀, TensorProduct.mk_apply]
  have hFχ : F₀ (f₀ χ) = 0 := by rw [hF₀ χ, hχ i i.2, Int.cast_zero]
  have hS₀ (μ : X) := P.pairwise_not_sameRay_tensorProduct_mk_orbit ℚ μ
  apply Option.map_injective (toPLPath_injective (𝕜 := ℚ) (f := f₀) hlam' hf₀.injOn (hS₀ (lam + χ)))
  rw [← lower_toPLPath hlam' f₀ i F₀ hF₀]
  have hlow₀ := lower_toPLPath hlam f₀ i F₀ hF₀ π
  cases hf : (crystal hlam).f i π with
  | none =>
    rw [hf, Option.map_none, toPLPath_def, PLPath.lower_ofSegments_map_snd,
      Option.map_eq_none_iff] at hlow₀
    rw [Option.map_none, Option.map_none, toPLPath_centralTransport_eq_ofSegments,
      PLPath.lower_ofSegments_shiftTimed (π.timed ℚ f₀) hFχ (f₀ (P.root i)), hlow₀, Option.map_none]
  | some ρ =>
    rw [hf, Option.map_some, toPLPath_def] at hlow₀
    have hmaps := P.mapsTo_preReflection_image_orbit_weylGroup i hF₀ lam
    rw [MulAction.orbit, ← Set.range_comp] at hmaps
    obtain ⟨Γ, hΓ, hseg⟩ := PLPath.distinguished_of_lower_eq_some
      (π.isDistinguished_timed ℚ f₀ hlam hf₀.injOn) hmaps (hS₀ lam) hlow₀
    have hΓeq : Γ = PLPath.ofSegments ℚ (ρ.timed ℚ f₀) := by
      rw [← PLPath.ofSegments_segments Γ, ← hseg, toPLPath_def,
        PLPath.distinguished_ofSegments (ρ.isDistinguished_timed ℚ f₀ hlam hf₀.injOn) (hS₀ lam)]
    rw [Option.map_some, Option.map_some, toPLPath_centralTransport_eq_ofSegments,
      PLPath.lower_ofSegments_shiftTimed (π.timed ℚ f₀) hFχ (f₀ (P.root i)), hΓ, Option.map_some,
      hΓeq, PLPath.shiftGraph_ofSegments, PLPath.map_ofSegments, LinearMap.coe_snd,
      ← toPLPath_centralTransport_eq_ofSegments]

/-- **Central transport commutes with crystal raising operators.** -/
theorem crystal_e_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').e i (centralTransport χ hχ π) =
      ((crystal hlam).e i π).map (centralTransport χ hχ) := by
  cases he : (crystal hlam).e i π with
  | some ρ =>
    rw [Option.map_some, (crystal hlam').e_eq_some_iff,
      crystal_f_centralTransport hlam hχ hlam' i ρ, (crystal hlam).e_eq_some_iff.mp he,
      Option.map_some]
  | none =>
    rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
    intro τ hτ
    obtain ⟨ρ, rfl⟩ := (centralTransport χ hχ).surjective τ
    rw [(crystal hlam').e_eq_some_iff, crystal_f_centralTransport hlam hχ hlam' i ρ,
      Option.map_eq_some_iff] at hτ
    obtain ⟨π₀, hπ₀, hπeq⟩ := hτ
    obtain rfl := (centralTransport χ hχ).injective hπeq
    exact Option.some_ne_none _ (((crystal hlam).e_eq_some_iff.mpr hπ₀).symm.trans he)

/-- **The two-offset central-transport crystal isomorphism
`T_{λ, χ}^σ : B(λ)^(σ + χ) ≃ B(λ + χ)^σ`.** Its underlying bijection on LS paths is
`LSPath.centralTransport χ _`, independent of the auxiliary central offset `σ`. -/
noncomputable def centralTransportIso (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlam
        ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ)) :
    NormalCrystal.StrictIso
      ((crystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
      ((crystal hlam').weightTwist σ hσ) where
  toEquiv := centralTransport χ ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt, crystal_wt]
    rw [weight_centralTransport hlam]; abel
  e_toFun i π := by
    simpa using
      crystal_e_centralTransport hlam ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) hlam' i π

/-- The underlying path map of `centralTransportIso` is `centralTransport χ _`, independent of the
auxiliary central offset `σ`. -/
@[simp]
theorem coe_centralTransportIso (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ⇑(centralTransportIso hlam χ σ hχ hσ hlam') =
      centralTransport χ ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) :=
  (rfl)

@[simp]
theorem centralTransportIso_apply (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) (π : LSPath P b lam) :
    centralTransportIso hlam χ σ hχ hσ hlam' π =
      centralTransport χ ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π :=
  (rfl)

/-- **Central transport from the weight-twisted LS crystal `B(λ)^χ` onto `B(λ + χ)`**, defined as
the `σ = 0` specialization of `TauCeti.LSPath.centralTransportIso`. -/
noncomputable def centralTransportIsoZero (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlam
        ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ)) :
    NormalCrystal.StrictIso ((crystal hlam).weightTwist χ hχ) (crystal hlam') :=
  ((centralTransportIso hlam χ 0 hχ (by simp) hlam').congrLeft
    (NormalCrystal.weightTwist_congr _ (zero_add χ) _ hχ)).congrRight
    (NormalCrystal.weightTwist_zero (crystal hlam'))

@[simp]
theorem coe_centralTransportIsoZero (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ⇑(centralTransportIsoZero hlam χ hχ hlam') =
      centralTransport χ ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) := by
  simp [centralTransportIsoZero]

@[simp]
theorem centralTransportIsoZero_apply (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) (π : LSPath P b lam) :
    centralTransportIsoZero hlam χ hχ hlam' π =
      centralTransport χ ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π := by
  simp [centralTransportIsoZero]

/-- Specializing `centralTransportIso` to `σ = 0` recovers `centralTransportIsoZero`. -/
theorem centralTransportIso_zero_offset (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ((centralTransportIso hlam χ 0 hχ (by simp) hlam').congrLeft
      (NormalCrystal.weightTwist_congr _ (zero_add χ) _ hχ)).congrRight
      (NormalCrystal.weightTwist_zero (crystal hlam')) =
      centralTransportIsoZero hlam χ hχ hlam' :=
  (rfl)

/-- Central transport preserves the `i`-raising string length `ε_i`. -/
theorem crystal_ε_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').ε i (centralTransport χ hχ π) = (crystal hlam).ε i π := by
  simpa using
    (centralTransportIsoZero hlam χ ((P.forall_coroot'_eq_zero_iff b χ).mp hχ) hlam').ε_apply i π

/-- Central transport preserves the `i`-lowering string length `φ_i`. -/
theorem crystal_φ_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').φ i (centralTransport χ hχ π) = (crystal hlam).φ i π := by
  simpa using
    (centralTransportIsoZero hlam χ ((P.forall_coroot'_eq_zero_iff b χ).mp hχ) hlam').φ_apply i π

/-- **Strict-map identity law `T_{λ, 0}^σ = id`** on `B(λ)^σ`. -/
theorem centralTransportIso_zero (hlam : lam ∈ dominantChamber P b) (σ : X)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam0 : lam + 0 ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlam fun _ _ ↦ map_zero _) :
    ((centralTransportIso hlam 0 σ (by simp) hσ hlam0).congrLeft
      (NormalCrystal.weightTwist_congr _ (add_zero σ) _ hσ)).trans
      ((congrIso (add_zero lam) hlam0).weightTwist σ hσ) =
      NormalCrystal.StrictIso.refl ((crystal hlam).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ by simp [centralTransport_zero]

/-- **Additive composition law `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^(σ + ψ) = T_{λ, χ + ψ}^σ`** for central
transports as strict crystal isomorphisms. -/
theorem centralTransportIso_trans_centralTransportIso (hlam : lam ∈ dominantChamber P b)
    (χ ψ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlamχ : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlam
        ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ))
    (hlamχψ : (lam + χ) + ψ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlamχ
        ((P.forall_coroot'_eq_zero_iff b ψ).mpr hψ))
    (hlam_χψ : lam + (χ + ψ) ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlam
        ((P.forall_coroot'_eq_zero_iff b (χ + ψ)).mpr (by simp [map_add, hχ, hψ]))) :
    ((centralTransportIso hlam χ (σ + ψ) hχ (by simp [map_add, hσ, hψ]) hlamχ).trans
      (centralTransportIso hlamχ ψ σ hψ hσ hlamχψ)).congrLeft
      (NormalCrystal.weightTwist_congr _ (by abel : (σ + ψ) + χ = σ + (χ + ψ)) _
        (by simp [map_add, hσ, hχ, hψ])) =
      (centralTransportIso hlam (χ + ψ) σ (by simp [map_add, hχ, hψ]) hσ hlam_χψ).trans
        ((congrIso (add_assoc lam χ ψ).symm hlam_χψ).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ by
    simpa using centralTransport_centralTransport χ
      ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π
      ((P.forall_coroot'_eq_zero_iff b ψ).mpr hψ)

/-- **Inverse formula `(T_{λ, χ}^σ)⁻¹ = T_{λ + χ, -χ}^(σ + χ)`** for central transports as strict
crystal isomorphisms. -/
theorem centralTransportIso_symm (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlamχ : lam + χ ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlam
        ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ))
    (hlamχ_neg : (lam + χ) + (-χ) ∈ dominantChamber P b :=
      P.add_mem_dominantChamber_of_forall_coroot'_eq_zero b hlamχ
        ((P.forall_coroot'_eq_zero_iff b (-χ)).mpr (by simp [hχ]))) :
    (centralTransportIso hlam χ σ hχ hσ hlamχ).symm =
      ((centralTransportIso hlamχ (-χ) (σ + χ) (by simp [hχ])
        (by simp [map_add, hσ, hχ]) hlamχ_neg).congrLeft
        (NormalCrystal.weightTwist_congr _ (add_neg_cancel_right σ χ) _ hσ)).trans
        ((congrIso (add_neg_cancel_right lam χ) hlamχ_neg).weightTwist
          (σ + χ) (by simp [map_add, hσ, hχ])) :=
  NormalCrystal.StrictIso.ext fun π ↦ by
    conv_rhs => simp
    rw [← NormalCrystal.StrictIso.coe_toEquiv_symm]
    exact centralTransport_symm_apply χ ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π

/-! ### Pure-central and zero-shape LS crystals -/

/-- **For any pure central weight `χ` (including `0` and any weight over an empty root system),
`crystal` is strictly isomorphic to the one-element crystal `NormalCrystal.central χ hχ`.** -/
noncomputable def centralIso (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hχ_dom : χ ∈ dominantChamber P b :=
      P.mem_dominantChamber_of_forall_coroot'_eq_zero b
        ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ)) :
    NormalCrystal.StrictIso (crystal hχ_dom) (NormalCrystal.central χ hχ) where
  toEquiv :=
    { toFun _ := PUnit.unit
      invFun _ := straight χ
      left_inv π :=
        (eq_straight_of_forall_coroot'_eq_zero ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π).symm
      right_inv u := by cases u; rfl }
  wt_toFun π := by
    rw [eq_straight_of_forall_coroot'_eq_zero ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π]; simp
  e_toFun i π := by
    rw [eq_straight_of_forall_coroot'_eq_zero ((P.forall_coroot'_eq_zero_iff b χ).mpr hχ) π]; simp

@[simp]
theorem centralIso_symm_unit (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hχ_dom : χ ∈ dominantChamber P b) :
    (centralIso χ hχ hχ_dom).symm PUnit.unit = straight χ := by
  rw [← NormalCrystal.StrictIso.coe_toEquiv_symm]
  rfl

/-- **The LS path crystal of shape `0` is strictly isomorphic to `NormalCrystal.central 0 _`.** -/
noncomputable def zeroIso :
    NormalCrystal.StrictIso (crystal (zero_mem_dominantChamber P b))
      (NormalCrystal.central (0 : X) (by simp)) :=
  centralIso 0 (by simp) (zero_mem_dominantChamber P b)

end CrystalTransport

end TauCeti.LSPath
