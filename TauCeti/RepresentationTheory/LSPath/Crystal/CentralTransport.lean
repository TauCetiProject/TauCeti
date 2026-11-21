/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.HighestWeight

import all TauCeti.RepresentationTheory.LSPath.Crystal.HighestWeight
import TauCeti.RepresentationTheory.LSPath.Realization

/-!
# Central transport of highest-weight path crystals

Upgrades `TauCeti.LSPath.centralTransport` for dominant `λ` and central `χ, σ ∈ X` to strict
crystal isomorphisms $T_{\lambda,\chi}^\sigma : B(\lambda)^{\sigma+\chi} \to B(\lambda+\chi)^\sigma$
(`TauCeti.LSPath.centralTransportIso`, `TauCeti.LSPath.straightComponentCentralTransportIso`).

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995), §4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti.LSPath

open Module RootPairing Set
open NormalCrystal
  (StrictIso weightTwist_wt weightTwist_e weightTwist_f weightTwist_ε weightTwist_φ)

private theorem eqRec_strictIso_apply {ι X Y B B' : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootDatum ι X Y} {b : P.Base} {c : NormalCrystal P b B}
    {d₁ d₂ : NormalCrystal P b B'} (h : d₁ = d₂) (ψ : StrictIso c d₁) (x : B) :
    (h ▸ ψ) x = ψ x := by
  subst h; rfl

section EncodingCrystal

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]

/-- Central transport shifts the crystal weight of an LS path by `χ`. -/
theorem normalCrystal_wt_centralTransportOfEq {lam lam' χ : X}
    (hlam : lam ∈ dominantChamber P b) (hlam' : lam' ∈ dominantChamber P b)
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h_lam : lam + χ = lam') (π : LSPath P b lam) :
    (normalCrystal hlam').wt (centralTransportOfEq χ hχ h_lam π) =
      (normalCrystal hlam).wt π + χ := by
  apply qHom_injective P
  rw [map_add, apply_normalCrystal_wt (𝕜 := ℚ), apply_normalCrystal_wt (𝕜 := ℚ),
    endpoint_toPLPath_centralTransportOfEq]

/-- Central transport commutes with the raising operators of `LSPath.normalCrystal`. -/
theorem normalCrystal_e_centralTransportOfEq {lam lam' χ : X}
    (hlam : lam ∈ dominantChamber P b) (hlam' : lam' ∈ dominantChamber P b)
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h_lam : lam + χ = lam')
    (i : b.support) (π : LSPath P b lam) :
    (normalCrystal hlam').e i (centralTransportOfEq χ hχ h_lam π) =
      ((normalCrystal hlam).e i π).map (centralTransportOfEq χ hχ h_lam) := by
  apply Option.map_injective
    (toPLPath_injective_of_coroot' (𝕜 := ℚ) (f := qHom X) hlam' qForm_apply)
  rw [← raise_toPLPath_eq_map_normalCrystal_e hlam' qForm_apply i,
    raise_toPLPath_centralTransportOfEq_of_coroot' χ hχ π ℚ (qHom X) h_lam hlam qForm_apply i,
    raise_toPLPath_eq_map_normalCrystal_e hlam qForm_apply i, Option.map_map, Option.map_map]
  exact Option.map_congr fun π' _ ↦
    (toPLPath_centralTransportOfEq_of_coroot' χ hχ π' ℚ (qHom X) h_lam hlam qForm_apply).symm

section OfEq

variable {lam lam' χ σ τ : X}
  (hlam : lam ∈ dominantChamber P b) (hlam' : lam' ∈ dominantChamber P b)
  (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
  (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
  (hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0)
  (h_lam : lam + χ = lam')

/-- **Equation-indexed central transport strict crystal isomorphism** on `LSPath.normalCrystal`. -/
noncomputable def centralTransportIsoOfEq (h_στ : σ + χ = τ) :
    StrictIso ((normalCrystal hlam).weightTwist τ hτ) ((normalCrystal hlam').weightTwist σ hσ) where
  toEquiv := centralTransportOfEq χ (fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
    h_lam
  wt_toFun _ := by rw [weightTwist_wt, weightTwist_wt, Equiv.toFun_as_coe,
    normalCrystal_wt_centralTransportOfEq hlam, ← h_στ, add_assoc, add_comm χ σ]
  e_toFun _ _ := by rw [weightTwist_e, weightTwist_e, Equiv.toFun_as_coe,
    normalCrystal_e_centralTransportOfEq hlam]

@[simp]
theorem toEquiv_centralTransportIsoOfEq (h_στ : σ + χ = τ) :
    (centralTransportIsoOfEq hlam hlam' hχ hσ hτ h_lam h_στ).toEquiv =
      centralTransportOfEq χ (fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
        h_lam := (rfl)

@[simp]
theorem coe_centralTransportIsoOfEq (h_στ : σ + χ = τ) :
    ⇑(centralTransportIsoOfEq hlam hlam' hχ hσ hτ h_lam h_στ) =
      centralTransportOfEq χ (fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
        h_lam := (rfl)

@[simp]
theorem centralTransportIsoOfEq_apply (h_στ : σ + χ = τ) (π : LSPath P b lam) :
    centralTransportIsoOfEq hlam hlam' hχ hσ hτ h_lam h_στ π =
      centralTransportOfEq χ (fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
        h_lam π := (rfl)

/-- **Inverse formula $(T_{\lambda,\chi}^\sigma)^{-1} = T_{\lambda+\chi,-\chi}^{\sigma+\chi}$.** -/
@[simp]
theorem centralTransportIsoOfEq_symm (h_στ : σ + χ = τ) :
    (centralTransportIsoOfEq hlam hlam' hχ hσ hτ h_lam h_στ).symm =
      centralTransportIsoOfEq (χ := -χ) hlam' hlam (by simp [hχ]) hτ hσ
        (by rw [← h_lam, add_neg_cancel_right]) (by rw [← h_στ, add_neg_cancel_right]) :=
  StrictIso.ext fun π ↦ by
    obtain ⟨y, rfl⟩ := EquivLike.surjective
      (centralTransportIsoOfEq hlam hlam' hχ hσ hτ h_lam h_στ) π
    have hsymm : centralTransportOfEq (-χ)
        (fun i hi ↦ by rw [map_neg, (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩), neg_zero])
        (by rw [← h_lam, add_neg_cancel_right]) =
        (centralTransportOfEq χ
          (fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩)) h_lam).symm := by
      rw [centralTransportOfEq_symm]
    rw [StrictIso.symm_apply_apply, centralTransportIsoOfEq_apply, centralTransportIsoOfEq_apply,
      hsymm, Equiv.symm_apply_apply]

end OfEq

section Iso

variable {lam : X} (hlam : lam ∈ dominantChamber P b) (χ : X)
  (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (σ : X)
  (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)

/-- **Central transport strict crystal isomorphism** on `LSPath.normalCrystal`. -/
noncomputable def centralTransportIso : StrictIso
    ((normalCrystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
    ((normalCrystal (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
      fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))).weightTwist σ hσ) :=
  centralTransportIsoOfEq hlam
    (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
      fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
    hχ hσ (by simp [map_add, hσ, hχ]) rfl rfl

@[simp]
theorem coe_centralTransportIso :
    ⇑(centralTransportIso hlam χ hχ σ hσ) =
      centralTransport χ fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩) := (rfl)

theorem centralTransportIso_symm :
    (centralTransportIso hlam χ hχ σ hσ).symm =
      centralTransportIsoOfEq (χ := -χ)
        (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
          fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
        hlam (by simp [hχ]) (by simp [map_add, hσ, hχ]) hσ
        (add_neg_cancel_right lam χ) (add_neg_cancel_right σ χ) :=
  centralTransportIsoOfEq_symm hlam
    (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
      fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
    hχ hσ (by simp [map_add, hσ, hχ]) rfl rfl

/-- Specialization of central transport at `σ = 0`, identifying `B(λ)^χ` with `B(λ + χ)`. -/
noncomputable def centralTransportIsoZero :
    StrictIso ((normalCrystal hlam).weightTwist χ hχ)
      (normalCrystal (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
        fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))) :=
  NormalCrystal.weightTwist_zero
      (normalCrystal (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
        fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))) ▸
    centralTransportIsoOfEq hlam
      (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
        fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
      hχ (by simp) hχ rfl (zero_add χ)

@[simp]
theorem coe_centralTransportIsoZero :
    ⇑(centralTransportIsoZero hlam χ hχ) =
      centralTransport χ fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩) :=
  funext fun π ↦ by
    rw [centralTransportIsoZero, eqRec_strictIso_apply, centralTransportIsoOfEq_apply]
    rfl

end Iso

section Commute

variable {lam lam' χ : X} (hlam : lam ∈ dominantChamber P b) (hlam' : lam' ∈ dominantChamber P b)
  (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (h_lam : lam + χ = lam')
  (i : b.support) (π : LSPath P b lam)

theorem normalCrystal_f_centralTransportOfEq :
    (normalCrystal hlam').f i (centralTransportOfEq χ hχ h_lam π) =
      ((normalCrystal hlam).f i π).map (centralTransportOfEq χ hχ h_lam) := by
  have hχ' : ∀ j : b.support, P.toLinearMap χ (P.coroot j) = 0 := fun j ↦ hχ j.val j.property
  simpa using (centralTransportIsoOfEq hlam hlam' hχ' (σ := 0) (τ := χ) (by simp) hχ' h_lam
    (zero_add χ)).f_apply i π

theorem normalCrystal_ε_centralTransportOfEq :
    (normalCrystal hlam').ε i (centralTransportOfEq χ hχ h_lam π) = (normalCrystal hlam).ε i π := by
  have hχ' : ∀ j : b.support, P.toLinearMap χ (P.coroot j) = 0 := fun j ↦ hχ j.val j.property
  simpa using (centralTransportIsoOfEq hlam hlam' hχ' (σ := 0) (τ := χ) (by simp) hχ' h_lam
    (zero_add χ)).ε_apply i π

theorem normalCrystal_φ_centralTransportOfEq :
    (normalCrystal hlam').φ i (centralTransportOfEq χ hχ h_lam π) = (normalCrystal hlam).φ i π := by
  have hχ' : ∀ j : b.support, P.toLinearMap χ (P.coroot j) = 0 := fun j ↦ hχ j.val j.property
  simpa using (centralTransportIsoOfEq hlam hlam' hχ' (σ := 0) (τ := χ) (by simp) hχ' h_lam
    (zero_add χ)).φ_apply i π

end Commute

/-- **Identity law $T_{\lambda,0}^\sigma = \mathrm{id}$** for `centralTransportIsoOfEq`. -/
@[simp]
theorem centralTransportIsoOfEq_zero {lam σ : X} (hlam : lam ∈ dominantChamber P b)
    (h0 : ∀ i : b.support, P.toLinearMap (0 : X) (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    centralTransportIsoOfEq hlam hlam h0 hσ hσ (add_zero lam) (add_zero σ) =
      StrictIso.refl ((normalCrystal hlam).weightTwist σ hσ) :=
  StrictIso.ext fun _ ↦ by simp

/-- **Additive composition law** for `centralTransportIsoOfEq`. -/
@[simp]
theorem centralTransportIsoOfEq_trans {lam₁ lam₂ lam₃ χ ψ σ₁ σ₂ σ₃ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (hlam₃ : lam₃ ∈ dominantChamber P b) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0)
    (hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0)
    (hσ₃ : ∀ i : b.support, P.toLinearMap σ₃ (P.coroot i) = 0)
    (h_lam₁ : lam₁ + χ = lam₂) (h_lam₂ : lam₂ + ψ = lam₃)
    (h_σ₁ : σ₂ + χ = σ₁) (h_σ₂ : σ₃ + ψ = σ₂) :
    (centralTransportIsoOfEq hlam₁ hlam₂ hχ hσ₂ hσ₁ h_lam₁ h_σ₁).trans
      (centralTransportIsoOfEq hlam₂ hlam₃ hψ hσ₃ hσ₂ h_lam₂ h_σ₂) =
      centralTransportIsoOfEq (χ := χ + ψ) hlam₁ hlam₃ (by simp [map_add, hχ, hψ]) hσ₃ hσ₁
        (by rw [← add_assoc, h_lam₁, h_lam₂]) (by rw [← h_σ₁, ← h_σ₂, add_assoc, add_comm ψ χ]) :=
  StrictIso.ext fun _ ↦ by simp

end EncodingCrystal

section StraightComponent

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

section StraightOfEq

variable {lam lam' χ σ τ : X}
  (hlam : lam ∈ dominantChamber P b) (hlam' : lam' ∈ dominantChamber P b)
  (hf : Function.Injective f) (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
  (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
  (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
  (hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0)
  (h_lam : lam + χ = lam') (h_στ : σ + χ = τ)

/-- **Equation-indexed central transport strict crystal isomorphism on `B(λ)`.** -/
noncomputable def straightComponentCentralTransportIsoOfEq : StrictIso
    ((PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f lam),
      PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).weightTwist τ hτ)
    ((PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f lam'),
      PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam' hF⟩).weightTwist σ hσ) :=
  (((normalCrystalComponentIso hlam hf hF).symm).weightTwist τ hτ).trans
    ((centralTransportIsoOfEq hlam hlam' hχ hσ hτ h_lam h_στ).trans
      ((normalCrystalComponentIso hlam' hf hF).weightTwist σ hσ))

@[simp]
theorem straightComponentCentralTransportIsoOfEq_apply
    (x : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    (straightComponentCentralTransportIsoOfEq hlam hlam' hf hF hχ hσ hτ h_lam h_στ x).val.val =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) (f χ) x.val.val := by
  simp only [straightComponentCentralTransportIsoOfEq, StrictIso.trans_apply,
    StrictIso.weightTwist_apply, centralTransportIsoOfEq_apply, normalCrystalComponentIso_apply]
  rw [toPLPath_centralTransportOfEq_of_coroot' χ
      (fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩)) _ 𝕜 f h_lam hlam hF,
    toPLPath_normalCrystalComponentIso_symm]

/-- **Inverse formula** on the straight-path components. -/
@[simp]
theorem straightComponentCentralTransportIsoOfEq_symm :
    (straightComponentCentralTransportIsoOfEq hlam hlam' hf hF hχ hσ hτ h_lam h_στ).symm =
      straightComponentCentralTransportIsoOfEq (χ := -χ) hlam' hlam hf hF (by simp [hχ]) hτ hσ
        (by rw [← h_lam, add_neg_cancel_right]) (by rw [← h_στ, add_neg_cancel_right]) :=
  StrictIso.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := EquivLike.surjective
      (straightComponentCentralTransportIsoOfEq hlam hlam' hf hF hχ hσ hτ h_lam h_στ) x
    rw [StrictIso.symm_apply_apply]
    simp only [straightComponentCentralTransportIsoOfEq, StrictIso.trans_apply,
      StrictIso.weightTwist_apply, StrictIso.symm_apply_apply, StrictIso.apply_symm_apply,
      ← centralTransportIsoOfEq_symm hlam hlam' hχ hσ hτ h_lam h_στ]

end StraightOfEq

section StraightIso

variable {lam : X} (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
  (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
  (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
  (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)

/-- **Central transport strict crystal isomorphism** on the realized straight-path component. -/
noncomputable def straightComponentCentralTransportIso : StrictIso
    ((PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f lam),
      PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).weightTwist
      (σ + χ) (by simp [map_add, hσ, hχ]))
    ((PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f (lam + χ)),
      PLPath.isIntegralPath_straight_of_mem_dominantChamber
        (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
          fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
        hF⟩).weightTwist σ hσ) :=
  straightComponentCentralTransportIsoOfEq hlam
    (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
      fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩)) hf hF hχ
    hσ (by simp [map_add, hσ, hχ]) rfl rfl

@[simp]
theorem straightComponentCentralTransportIso_apply
    (x : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    (straightComponentCentralTransportIso hlam hf hF χ hχ σ hσ x).val.val =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) (f χ) x.val.val :=
  straightComponentCentralTransportIsoOfEq_apply hlam _ hf hF hχ hσ _ rfl rfl x

/-- Specialization at `σ = 0` on the straight-path component: `B(λ)^χ ≃ B(λ + χ)`. -/
noncomputable def straightComponentCentralTransportIsoZero : StrictIso
    ((PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f lam),
      PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).weightTwist χ hχ)
    (PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f (lam + χ)),
      PLPath.isIntegralPath_straight_of_mem_dominantChamber
        (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
          fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
        hF⟩) :=
  NormalCrystal.weightTwist_zero
      (PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f (lam + χ)),
        PLPath.isIntegralPath_straight_of_mem_dominantChamber
          (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
            fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
          hF⟩) ▸
    straightComponentCentralTransportIsoOfEq hlam
      (mem_dominantChamber_add_of_forall_coroot'_eq_zero P b hlam
        fun i hi ↦ (LinearMap.flip_apply _ _ _).trans (hχ ⟨i, hi⟩))
      hf hF hχ (by simp) hχ rfl (zero_add χ)

@[simp]
theorem straightComponentCentralTransportIsoZero_apply
    (x : (PLPath.normalCrystal hf hF).graph.connectedComponentMk
      ⟨PLPath.straight 𝕜 (f lam), PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩) :
    (straightComponentCentralTransportIsoZero hlam hf hF χ hχ x).val.val =
      PLPath.shiftDistinguished (range fun w : P.weylGroup ↦ f (w • lam)) (f χ) x.val.val := by
  rw [straightComponentCentralTransportIsoZero, eqRec_strictIso_apply,
    straightComponentCentralTransportIsoOfEq_apply]

end StraightIso

/-- **Identity law $T_{\lambda,0}^\sigma = \mathrm{id}$** on `B(λ)^σ`. -/
@[simp]
theorem straightComponentCentralTransportIsoOfEq_zero {lam σ : X}
    (hlam : lam ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (h0 : ∀ i : b.support, P.toLinearMap (0 : X) (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    straightComponentCentralTransportIsoOfEq hlam hlam hf hF h0 hσ hσ (add_zero lam) (add_zero σ) =
      StrictIso.refl ((PLPath.normalCrystalComponent hf hF ⟨PLPath.straight 𝕜 (f lam),
        PLPath.isIntegralPath_straight_of_mem_dominantChamber hlam hF⟩).weightTwist σ hσ) :=
  StrictIso.ext fun _ ↦ by simp [straightComponentCentralTransportIsoOfEq]

/-- **Additive composition law** on the straight-path components. -/
@[simp]
theorem straightComponentCentralTransportIsoOfEq_trans {lam₁ lam₂ lam₃ χ ψ σ₁ σ₂ σ₃ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    (hlam₃ : lam₃ ∈ dominantChamber P b) (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0)
    (hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0)
    (hσ₃ : ∀ i : b.support, P.toLinearMap σ₃ (P.coroot i) = 0)
    (h_lam₁ : lam₁ + χ = lam₂) (h_lam₂ : lam₂ + ψ = lam₃)
    (h_σ₁ : σ₂ + χ = σ₁) (h_σ₂ : σ₃ + ψ = σ₂) :
    (straightComponentCentralTransportIsoOfEq hlam₁ hlam₂ hf hF hχ hσ₂ hσ₁ h_lam₁ h_σ₁).trans
      (straightComponentCentralTransportIsoOfEq hlam₂ hlam₃ hf hF hψ hσ₃ hσ₂ h_lam₂ h_σ₂) =
      straightComponentCentralTransportIsoOfEq (χ := χ + ψ) hlam₁ hlam₃ hf hF
        (by simp [map_add, hχ, hψ]) hσ₃ hσ₁ (by rw [← add_assoc, h_lam₁, h_lam₂])
        (by rw [← h_σ₁, ← h_σ₂, add_assoc, add_comm ψ χ]) :=
  StrictIso.ext fun _ ↦ by simp [straightComponentCentralTransportIsoOfEq]

end StraightComponent

end TauCeti.LSPath
