/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Principal.Extension

/-!
# Linear structure of associated bundles of an extended principal bundle

Let `P` be a principal `G`-bundle, `ρ : G →* H` a continuous homomorphism, and `F` a normed space
on which `G` and `H` act linearly, with `G` acting through `ρ`. The identification
`TauCeti.PrincipalBundle.Extend.associatedEquiv` of `(P ×_ρ H) ×_H F` with `P ×_G F`,
`[[p, h], v] ↦ [p, h v]`, is fibrewise a continuous linear equivalence
(`TauCeti.PrincipalBundle.Extend.associatedContinuousLinearEquiv`), and it is continuous on total
spaces in both directions.

## Main definitions

* `TauCeti.PrincipalBundle.Extend.associatedContinuousLinearEquiv`: the fibrewise continuous linear
  equivalence `(P ×_ρ H) ×_H F ≃L[𝕜] P ×_G F`.

## Main results

* `TauCeti.PrincipalBundle.Extend.associatedContinuousLinearEquiv_inl`: it sends `[[p, 1], v]` to
  `[p, v]`.
* `TauCeti.PrincipalBundle.Extend.continuous_associatedContinuousLinearEquiv` and
  `TauCeti.PrincipalBundle.Extend.continuous_associatedContinuousLinearEquiv_symm`: it and its
  inverse are continuous on total spaces.
-/

public section

noncomputable section

open Bundle

namespace TauCeti.PrincipalBundle.Extend

variable {𝕜 B G H F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [ContinuousMul H]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]
  [DistribMulAction H F] [SMulCommClass H 𝕜 F] [ContinuousSMul H F]
  (ρ : G →* H) (hρ : Continuous ρ) (hF : ∀ (g : G) (v : F), g • v = ρ g • v)

variable (𝕜) in
/-- In the frames `[p, 1]` and `p`, `associatedEquiv` is the identity of the model `F`. -/
private theorem associatedEquiv_eq {b : B} (p : P b) (z : AssociatedBundle H (Extend P ρ hρ) F b) :
    associatedEquiv ρ hρ hF b z = AssociatedBundle.mkContinuousLinearEquiv 𝕜 G p
      ((AssociatedBundle.mkContinuousLinearEquiv 𝕜 H (inl ρ hρ p)).symm z) := by
  obtain ⟨v, rfl⟩ := (AssociatedBundle.mkContinuousLinearEquiv 𝕜 H (inl ρ hρ p)).surjective z
  rw [ContinuousLinearEquiv.symm_apply_apply, AssociatedBundle.mkContinuousLinearEquiv_apply,
    AssociatedBundle.mkContinuousLinearEquiv_apply, associatedEquiv_inl]

variable (𝕜) in
/-- The inverse of `associatedEquiv` in the frames `p` and `[p, 1]`. -/
private theorem associatedEquiv_symm_eq {b : B} (p : P b) (z : AssociatedBundle G P F b) :
    (associatedEquiv ρ hρ hF b).symm z =
      AssociatedBundle.mkContinuousLinearEquiv 𝕜 H (inl ρ hρ p)
        ((AssociatedBundle.mkContinuousLinearEquiv 𝕜 G p).symm z) := by
  rw [Equiv.symm_apply_eq, associatedEquiv_eq 𝕜 ρ hρ hF p, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.apply_symm_apply]

variable (𝕜) in
/-- **Associated vector bundle of an extended principal bundle**, at a fibre: when `G` acts on `F`
through `ρ`, the identification `[[p, h], v] ↦ [p, h v]` of `(P ×_ρ H) ×_H F` with `P ×_G F`
(`TauCeti.PrincipalBundle.Extend.associatedEquiv`) is a continuous linear equivalence. -/
def associatedContinuousLinearEquiv (b : B) :
    AssociatedBundle H (Extend P ρ hρ) F b ≃L[𝕜] AssociatedBundle G P F b :=
  have : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  { associatedEquiv ρ hρ hF b with
    map_add' z w := by
      simp only [Equiv.toFun_as_coe, associatedEquiv_eq 𝕜 ρ hρ hF (Classical.arbitrary (P b)),
        map_add]
    map_smul' c z := by
      simp only [Equiv.toFun_as_coe, associatedEquiv_eq 𝕜 ρ hρ hF (Classical.arbitrary (P b)),
        map_smul, RingHom.id_apply]
    continuous_toFun :=
      ((AssociatedBundle.mkContinuousLinearEquiv 𝕜 G (Classical.arbitrary (P b))).continuous.comp
        (AssociatedBundle.mkContinuousLinearEquiv 𝕜 H
          (inl ρ hρ (Classical.arbitrary (P b)))).symm.continuous).congr fun z ↦
        (associatedEquiv_eq 𝕜 ρ hρ hF _ z).symm
    continuous_invFun :=
      ((AssociatedBundle.mkContinuousLinearEquiv 𝕜 H
          (inl ρ hρ (Classical.arbitrary (P b)))).continuous.comp
        (AssociatedBundle.mkContinuousLinearEquiv 𝕜 G
          (Classical.arbitrary (P b))).symm.continuous).congr fun z ↦
        (associatedEquiv_symm_eq 𝕜 ρ hρ hF _ z).symm }

@[simp]
theorem coe_associatedContinuousLinearEquiv (b : B) :
    ⇑(associatedContinuousLinearEquiv 𝕜 (P := P) ρ hρ hF b) = associatedEquiv ρ hρ hF b :=
  (rfl)

@[simp]
theorem coe_associatedContinuousLinearEquiv_symm (b : B) :
    ⇑(associatedContinuousLinearEquiv 𝕜 (P := P) ρ hρ hF b).symm =
      (associatedEquiv ρ hρ hF b).symm :=
  (rfl)

/-- The identification sends `[[p, h], v]` to `[p, h v]`. -/
theorem associatedContinuousLinearEquiv_mk {b : B} (p : P b) (h : H) (v : F) :
    associatedContinuousLinearEquiv 𝕜 ρ hρ hF b (AssociatedBundle.mk H (mk ρ hρ p h) v) =
      AssociatedBundle.mk G p (h • v) :=
  associatedEquiv_mk ρ hρ hF p h v

/-- The identification sends `[[p, 1], v]` to `[p, v]`. -/
theorem associatedContinuousLinearEquiv_inl {b : B} (p : P b) (v : F) :
    associatedContinuousLinearEquiv 𝕜 ρ hρ hF b (AssociatedBundle.mk H (inl ρ hρ p) v) =
      AssociatedBundle.mk G p v :=
  associatedEquiv_inl ρ hρ hF p v

/-- The inverse identification sends `[p, v]` to `[[p, 1], v]`. -/
theorem associatedContinuousLinearEquiv_symm_mk {b : B} (p : P b) (v : F) :
    (associatedContinuousLinearEquiv 𝕜 ρ hρ hF b).symm (AssociatedBundle.mk G p v) =
      AssociatedBundle.mk H (inl ρ hρ p) v :=
  associatedEquiv_symm_mk ρ hρ hF p v

/-- **The identification is continuous on total spaces**: it is the homeomorphism
`TauCeti.PrincipalBundle.Extend.associatedHomeomorph`. -/
theorem continuous_associatedContinuousLinearEquiv :
    Continuous fun z : TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F) ↦
      TotalSpace.mk' F z.proj (associatedContinuousLinearEquiv 𝕜 ρ hρ hF z.proj z.snd) :=
  (associatedHomeomorph ρ hρ hF).continuous.congr fun z ↦ associatedHomeomorph_apply ρ hρ hF z

/-- **The inverse identification is continuous on total spaces**. -/
theorem continuous_associatedContinuousLinearEquiv_symm :
    Continuous fun z : TotalSpace F (AssociatedBundle G P F) ↦
      TotalSpace.mk' F z.proj ((associatedContinuousLinearEquiv 𝕜 ρ hρ hF z.proj).symm z.snd) :=
  (associatedHomeomorph (P := P) ρ hρ hF).symm.continuous.congr fun z ↦
    associatedHomeomorph_symm_apply ρ hρ hF z

end TauCeti.PrincipalBundle.Extend
