/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Central.Shift
public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.Model

import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Central transport isomorphisms of Lakshmibai–Seshadri crystals

Let `P : RootDatum ι X Y` be a finite reduced root datum with base `b : P.Base`, let `λ` be a
dominant weight, and let `χ : X` be a central weight (killed by all simple coroots). Adding `χ`
preserves dominance (`RootPairing.mem_dominantChamber_add_of_forall_coroot_eq_zero`), leaves the
stabilizer walls and reflection bonds of `W / W_λ` unchanged, and therefore defines the bijection
`TauCeti.LSPath.centralTransport : LSPath P b λ ≃ LSPath P b (λ + χ)` keeping the same Weyl
directions and rational break times (`TauCeti.RepresentationTheory.LSPath.Central.Transport`).

On realized paths, `centralTransport χ` shifts the distinguished orbit presentation by `t ↦ t • f χ`
(`TauCeti.LSPath.toPLPath_centralTransport`), translating the endpoint by `f χ` while leaving all
simple-coroot running and minimum heights unchanged. Lowering on the time–weight graph commutes with
the central shear `(t, v) ↦ (t, v + t • f χ)` (`TauCeti.PLPath.lower_ofSegments_shiftTimed`), and
uniqueness of the distinguished orbit presentation (`TauCeti.PLPath.distinguished_of_lower_eq_some`)
identifies the lowered graph of an LS path with the distinguished presentation of the lowered LS
path. Consequently `centralTransport χ` commutes with all crystal raising and lowering operators and
adds `χ` to every crystal weight.

For any central offset `σ : X`, this packages `centralTransport χ` as a strict crystal isomorphism
`TauCeti.LSPath.centralTransportIso`:
$$T_{\lambda, \chi}^\sigma : B(\lambda)^{\sigma + \chi} \simeq B(\lambda + \chi)^\sigma$$
from `(normalCrystal hlam).weightTwist (σ + χ) _` to `(normalCrystal hlamχ).weightTwist σ hσ`, whose
underlying bijection is `centralTransport χ` (independent of `σ`). We establish its realization
formula via `PLPath.shiftDistinguished`, together with its identity (`χ = 0`), additive composition
(`χ` followed by `ψ` versus `χ + ψ`), and inverse (`-χ`) laws.

## Main definitions

* `TauCeti.LSPath.castIso`, `TauCeti.LSPath.castWeightTwistIso`: strict crystal isomorphisms
  transporting `LSPath.normalCrystal` and its central weight twists along equalities of shapes and
  central offsets.
* `TauCeti.LSPath.centralTransportIso`: **the central transport strict crystal isomorphism**
  `B(λ)^{σ + χ} ≃ B(λ + χ)^σ`.
* `TauCeti.LSPath.centralTransportZeroIso`: specialization `B(λ)^χ ≃ B(λ + χ)` at `σ = 0`.

## Main results

* `TauCeti.LSPath.normalCrystal_wt_centralTransport`,
  `TauCeti.LSPath.normalCrystal_f_centralTransport`,
  `TauCeti.LSPath.normalCrystal_e_centralTransport`: central transport shifts crystal weights by
  `χ` and commutes with all crystal raising and lowering operators.
* `TauCeti.LSPath.toPLPath_centralTransportIso`: in any compatible realization `(f, F)`,
  `centralTransportIso` acts on realized paths as `PLPath.shiftDistinguished`.
* `TauCeti.LSPath.centralTransportIso_zero`,
  `TauCeti.LSPath.centralTransportIso_trans_centralTransportIso`,
  `TauCeti.LSPath.symm_centralTransportIso`: categorical identity, additive composition, and inverse
  laws for `centralTransportIso`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent. Math.
  116 (1994), §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1, 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti.LSPath

open Module RootPairing Set
open scoped TensorProduct

section CrystalTransport

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]

/-! ### Casting crystals along shape and twist equalities -/

/-- Transport `LSPath.normalCrystal` as a strict crystal isomorphism along an equality of dominant
shapes. -/
noncomputable def castIso {lam₁ lam₂ : X} (h : lam₁ = lam₂)
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b} :
    NormalCrystal.StrictIso (normalCrystal hlam₁) (normalCrystal hlam₂) where
  toEquiv := cast h
  wt_toFun _ := by subst h; simp
  e_toFun _ _ := by
    subst h
    rw [show (cast rfl : LSPath P b lam₁ ≃ _) = Equiv.refl _ from Equiv.ext cast_rfl]
    simp

@[simp]
theorem castIso_apply {lam₁ lam₂ : X} (h : lam₁ = lam₂)
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b}
    (π : LSPath P b lam₁) :
    castIso h (hlam₁ := hlam₁) (hlam₂ := hlam₂) π = cast h π := by
  simp [castIso]

@[simp]
theorem castIso_rfl {lam : X} (hlam : lam ∈ dominantChamber P b) :
    castIso rfl (hlam₁ := hlam) (hlam₂ := hlam) = NormalCrystal.StrictIso.refl _ :=
  NormalCrystal.StrictIso.ext fun _ ↦ by simp

@[simp]
theorem symm_castIso {lam₁ lam₂ : X} (h : lam₁ = lam₂)
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b} :
    (castIso h (hlam₁ := hlam₁) (hlam₂ := hlam₂)).symm =
      castIso h.symm (hlam₁ := hlam₂) (hlam₂ := hlam₁) :=
  NormalCrystal.StrictIso.ext fun _ ↦
    (castIso h (hlam₁ := hlam₁) (hlam₂ := hlam₂)).toEquiv.injective (by simp)

/-- Transport a centrally twisted LS crystal along equalities of dominant shapes and central
offsets. -/
noncomputable def castWeightTwistIso {lam₁ lam₂ : X} (hlam_eq : lam₁ = lam₂)
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b}
    {σ₁ σ₂ : X} (hσ_eq : σ₁ = σ₂)
    {hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0}
    {hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0} :
    NormalCrystal.StrictIso
      ((normalCrystal hlam₁).weightTwist σ₁ hσ₁)
      ((normalCrystal hlam₂).weightTwist σ₂ hσ₂) where
  toEquiv := cast hlam_eq
  wt_toFun _ := by subst hlam_eq; subst hσ_eq; simp
  e_toFun _ _ := by
    subst hlam_eq
    rw [show (cast rfl : LSPath P b lam₁ ≃ _) = Equiv.refl _ from Equiv.ext cast_rfl]
    simp

@[simp]
theorem castWeightTwistIso_apply {lam₁ lam₂ : X} (hlam_eq : lam₁ = lam₂)
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b}
    {σ₁ σ₂ : X} (hσ_eq : σ₁ = σ₂)
    {hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0}
    {hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0}
    (π : LSPath P b lam₁) :
    castWeightTwistIso hlam_eq hσ_eq
        (hlam₁ := hlam₁) (hlam₂ := hlam₂) (hσ₁ := hσ₁) (hσ₂ := hσ₂) π =
      cast hlam_eq π := by
  simp [castWeightTwistIso]

/-! ### Central transport commutes with crystal operators -/

section Core

variable {lam : X} (hlam : lam ∈ dominantChamber P b) (χ : X)
  (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)

/-- Central transport shifts the intrinsic crystal weight of an LS path by `χ`. -/
theorem normalCrystal_wt_centralTransport (π : LSPath P b lam) :
    (normalCrystal (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ)).wt
        (centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π) =
      (normalCrystal hlam).wt π + χ := by
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  apply P.tensorProduct_mk_injective ℚ
  change f₀ _ = f₀ _
  rw [← endpoint_toPLPath_eq_apply_wt (𝕜 := ℚ) _ f₀, endpoint_toPLPath_centralTransport,
    endpoint_toPLPath_eq_apply_wt (𝕜 := ℚ) hlam f₀, map_add]

/-- Central transport commutes with the crystal lowering operators `f_i`. -/
theorem normalCrystal_f_centralTransport (i : b.support) (π : LSPath P b lam) :
    (normalCrystal (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ)).f i
        (centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π) =
      ((normalCrystal hlam).f i π).map
        (centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ)) := by
  have := P.flip_isReduced
  let hlamχ := P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  let F₀ : b.support → Dual ℚ (ℚ ⊗[ℤ] X) := fun j ↦
    LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ).comp (P.coroot' j.1))
  have hF₀ (j : b.support) (x : X) : F₀ j (f₀ x) = (P.coroot' j x : ℚ) := by
    simp [f₀, F₀, Algebra.linearMap_apply]
  have hF₀χ : F₀ i (f₀ χ) = 0 := by simp [hF₀, RootPairing.coroot', hχ i]
  cases hf_eq : (normalCrystal hlam).f i π with
  | none =>
    rw [Option.map_none, normalCrystal_f_eq_none_iff hlamχ hF₀, PLPath.lower_eq_none_iff]
    have hnone := (PLPath.lower_eq_none_iff (x := f₀ (P.root i))).mp
      ((normalCrystal_f_eq_none_iff hlam hF₀).mp hf_eq)
    rwa [endpoint_toPLPath_centralTransport,
      minHeight_toPLPath_centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π ℚ f₀ hF₀χ,
      map_add, hF₀χ, add_zero]
  | some π' =>
    rw [Option.map_some, normalCrystal_f_eq_some_iff hlamχ hF₀]
    have hlow : PLPath.lower (F₀ i) (f₀ (P.root i)) (π.toPLPath ℚ f₀) =
        some (π'.toPLPath ℚ f₀) :=
      (normalCrystal_f_eq_some_iff hlam hF₀).mp hf_eq
    have hf_orb := P.injOn_range_smul_of_coroot' b hF₀ lam
    have hray := P.pairwise_not_sameRay_range_smul_of_coroot' b hF₀ lam
    have hmap : MapsTo (preReflection (f₀ (P.root i)) (F₀ i))
        (range fun w : P.weylGroup ↦ f₀ (w • lam))
        (range fun w : P.weylGroup ↦ f₀ (w • lam)) := by
      have hm := P.mapsTo_preReflection_image_orbit_weylGroup i (hF₀ i) lam
      rwa [MulAction.orbit, ← range_comp] at hm
    rw [toPLPath_def] at hlow
    obtain ⟨Γ, hΓ, hseg⟩ := PLPath.distinguished_of_lower_eq_some
      (π.isDistinguished_timed ℚ f₀ hlam hf_orb) hmap hray hlow
    have hseg' : PLPath.distinguished (range fun w : P.weylGroup ↦ f₀ (w • lam))
        (π'.toPLPath ℚ f₀) = π'.timed ℚ f₀ := by
      rw [toPLPath_def]
      exact PLPath.distinguished_ofSegments (π'.isDistinguished_timed ℚ f₀ hlam hf_orb) hray
    have hΓ_eq : Γ = PLPath.ofSegments ℚ (π'.timed ℚ f₀) := by
      rw [← PLPath.ofSegments_segments Γ, ← hseg, hseg']
    rw [toPLPath_centralTransport_eq_ofSegments, toPLPath_centralTransport_eq_ofSegments,
      PLPath.lower_ofSegments_shiftTimed _ hF₀χ, hΓ, Option.map_some, hΓ_eq,
      PLPath.shiftGraph_ofSegments, PLPath.map_ofSegments, LinearMap.coe_snd]

/-- Central transport commutes with the crystal raising operators `e_i`. -/
theorem normalCrystal_e_centralTransport (i : b.support) (π : LSPath P b lam) :
    (normalCrystal (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ)).e i
        (centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π) =
      ((normalCrystal hlam).e i π).map
        (centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ)) := by
  let hlamχ := P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ
  let τ := centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) (lam := lam)
  cases he_eq : (normalCrystal hlam).e i π with
  | none =>
    rw [Option.map_none]
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨π', rfl⟩ := τ.surjective ρ
    have hf_τ : (normalCrystal hlamχ).f i (τ π') = some (τ π) :=
      (normalCrystal hlamχ).f_eq_some_iff.mpr hρ
    rw [normalCrystal_f_centralTransport hlam χ hχ, Option.map_eq_some_iff] at hf_τ
    obtain ⟨π'', hπ'', heq⟩ := hf_τ
    obtain rfl := τ.injective heq
    exact Option.some_ne_none _ (((normalCrystal hlam).f_eq_some_iff.mp hπ'').symm.trans he_eq)
  | some π' =>
    rw [Option.map_some, ← (normalCrystal hlamχ).f_eq_some_iff,
      normalCrystal_f_centralTransport hlam χ hχ,
      (normalCrystal hlam).f_eq_some_iff.mpr he_eq, Option.map_some]

/-! ### The central transport strict crystal isomorphism `T_{λ, χ}^σ` -/

/-- **Central transport of Lakshmibai–Seshadri crystals**
`T_{λ, χ}^σ : B(λ)^{σ + χ} ≃ B(λ + χ)^σ`: for a dominant weight `λ`, a central shift `χ`, and any
central weight offset `σ`, `TauCeti.LSPath.centralTransport` is a strict crystal isomorphism from
`(normalCrystal hlam).weightTwist (σ + χ) _` to `(normalCrystal hlamχ).weightTwist σ hσ`. -/
noncomputable def centralTransportIso
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
      ((normalCrystal (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ)).weightTwist
        σ hσ) where
  toEquiv := centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt,
      normalCrystal_wt_centralTransport hlam χ hχ]
    abel
  e_toFun i π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_e]
    exact normalCrystal_e_centralTransport hlam χ hχ i π

@[simp]
theorem centralTransportIso_apply
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (π : LSPath P b lam) :
    centralTransportIso hlam χ hχ σ hσ π =
      centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π := by
  simp [centralTransportIso]

@[simp]
theorem centralTransportIso_symm_apply
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (ρ : LSPath P b (lam + χ)) :
    (centralTransportIso hlam χ hχ σ hσ).symm ρ =
      (centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ)).symm ρ := by
  apply (centralTransportIso hlam χ hχ σ hσ).toEquiv.injective
  simp

theorem centralTransportIso_straight
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    centralTransportIso hlam χ hχ σ hσ (straight lam) = straight (lam + χ) := by
  simp [centralTransport_straight]

/-- Specialization `B(λ)^χ ≃ B(λ + χ)` of `centralTransportIso` at `σ = 0`. -/
noncomputable def centralTransportZeroIso :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist χ hχ)
      (normalCrystal (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ)) where
  toEquiv := centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt,
      normalCrystal_wt_centralTransport hlam χ hχ]
  e_toFun i π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_e]
    exact normalCrystal_e_centralTransport hlam χ hχ i π

@[simp]
theorem centralTransportZeroIso_apply (π : LSPath P b lam) :
    centralTransportZeroIso hlam χ hχ π =
      centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π := by
  simp [centralTransportZeroIso]

/-- **Realization formula for `centralTransportIso`**: in any realization `(f, F)` whose height
forms induce the simple coroots, `centralTransportIso` acts on realized paths by adding
`t ↦ t • f χ` to the distinguished presentation for the realized Weyl orbit `f(W λ)`. -/
theorem toPLPath_centralTransportIso {𝕜 V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {f : X →+ V} {F : b.support → Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (π : LSPath P b lam) :
    (centralTransportIso hlam χ hχ σ hσ π).toPLPath 𝕜 f =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) (f χ)
        (π.toPLPath 𝕜 f) := by
  rw [centralTransportIso_apply]
  exact toPLPath_centralTransport χ (P.forall_mem_support_coroot'_eq_zero hχ) π 𝕜 f hlam
    (P.injOn_range_smul_of_coroot' b hF lam)
    (P.pairwise_not_sameRay_range_smul_of_coroot' b hF lam)

end Core

/-! ### Identity, composition, and inverse laws for `centralTransportIso` -/

/-- **Identity law (`χ = 0`)**: `T_{λ, 0}^σ` is the canonical cast isomorphism along `λ = λ + 0`
and `σ + 0 = σ`. -/
theorem centralTransportIso_zero {lam : X} (hlam : lam ∈ dominantChamber P b)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    centralTransportIso hlam 0 (by simp) σ hσ =
      castWeightTwistIso (add_zero lam).symm (add_zero σ) :=
  NormalCrystal.StrictIso.ext fun _ ↦ by
    simp [centralTransport_zero_eq_cast (P.forall_mem_support_coroot'_eq_zero (b := b) (by simp))]

/-- **Additive composition law**: composing `T_{λ, χ}^{σ + ψ}` with `T_{λ + χ, ψ}^σ` equals
`T_{λ, χ + ψ}^σ` up to the canonical associativity casts `(λ + χ) + ψ = λ + (χ + ψ)` and
`(σ + ψ) + χ = σ + (χ + ψ)`. -/
theorem centralTransportIso_trans_centralTransportIso
    {lam : X} (hlam : lam ∈ dominantChamber P b) (χ ψ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    ((centralTransportIso hlam χ hχ (σ + ψ) (by simp [map_add, hσ, hψ])).trans
      (centralTransportIso
        (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ) ψ hψ σ hσ)).trans
      (castWeightTwistIso (add_assoc lam χ ψ) rfl) =
      (castWeightTwistIso rfl (by abel)).trans
        (centralTransportIso hlam (χ + ψ) (by simp [map_add, hχ, hψ]) σ hσ) := by
  refine NormalCrystal.StrictIso.ext fun π ↦ ?_
  simp [centralTransport_centralTransport_eq_cast (hχ := fun i hi ↦ hχ ⟨i, hi⟩)
    (hψ := fun i hi ↦ hψ ⟨i, hi⟩)
    (hχψ := fun i hi ↦ by simp [RootPairing.coroot', map_add, hχ ⟨i, hi⟩, hψ ⟨i, hi⟩])]

/-- **Inverse law**: the inverse of `T_{λ, χ}^σ` is `T_{λ + χ, -χ}^{σ + χ}`, up to the canonical
cancellation casts `(λ + χ) + (-χ) = λ` and `σ = (σ + χ) + (-χ)`. -/
theorem symm_centralTransportIso
    {lam : X} (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    (centralTransportIso hlam χ hχ σ hσ).symm =
      ((castWeightTwistIso rfl (add_neg_cancel_right σ χ).symm).trans
        (centralTransportIso
          (P.mem_dominantChamber_add_of_forall_coroot_eq_zero hlam hχ)
          (-χ) (by simp [hχ]) (σ + χ) (by simp [map_add, hσ, hχ]))).trans
        (castWeightTwistIso (add_neg_cancel_right lam χ) rfl) := by
  refine NormalCrystal.StrictIso.ext fun ρ ↦ ?_
  simp [centralTransport_neg_eq_cast (hχ := fun i hi ↦ hχ ⟨i, hi⟩)
    (hneg := fun i hi ↦ by simp [RootPairing.coroot', hχ ⟨i, hi⟩])]

end CrystalTransport

end TauCeti.LSPath
