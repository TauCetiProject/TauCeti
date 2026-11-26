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

More generally, a continuous semilinear equivalence `f : F ≃ F'` from a `G`-space to an `H`-space
with `f (g v) = ρ(g) f v` induces the fibrewise continuous semilinear equivalence
`P ×_G F ≃ (P ×_ρ H) ×_H F'`, `[p, v] ↦ [[p, 1], f v]`
(`TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant`), continuous on total spaces in both
directions. For conjugate-linear `f` this is the form of charge conjugation of spinors.

## Main definitions

* `TauCeti.PrincipalBundle.Extend.associatedContinuousLinearEquiv`: the fibrewise continuous linear
  equivalence `(P ×_ρ H) ×_H F ≃L[𝕜] P ×_G F`.
* `TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant`: the fibrewise continuous
  semilinear equivalence `P ×_G F ≃ (P ×_ρ H) ×_H F'` induced by an equivariant model map.

## Main results

* `TauCeti.PrincipalBundle.Extend.associatedContinuousLinearEquiv_inl`: it sends `[[p, 1], v]` to
  `[p, v]`.
* `TauCeti.PrincipalBundle.Extend.continuous_associatedContinuousLinearEquiv` and
  `TauCeti.PrincipalBundle.Extend.continuous_associatedContinuousLinearEquiv_symm`: it and its
  inverse are continuous on total spaces.
* `TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant_mk` and
  `TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant_symm_mk`: the formulas
  `[p, v] ↦ [[p, 1], f v]` and `[[p, h], w] ↦ [p, f⁻¹ (h w)]`.
* `TauCeti.PrincipalBundle.Extend.continuous_associatedEquivOfEquivariant` and
  `TauCeti.PrincipalBundle.Extend.continuous_associatedEquivOfEquivariant_symm`: continuity on
  total spaces.
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

/-! ### Equivariant model maps -/

section Equivariant

variable {𝕜 B G H F F' : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [ContinuousMul H]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [DistribMulAction G F] [SMulCommClass G 𝕜 F] [ContinuousSMul G F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [DistribMulAction H F'] [SMulCommClass H 𝕜 F'] [ContinuousSMul H F']
  {σ σ' : 𝕜 →+* 𝕜} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (ρ : G →* H) (hρ : Continuous ρ) (f : F ≃SL[σ] F')
  (hf : ∀ (g : G) (v : F), f (g • v) = ρ g • f v)

include hf in
/-- In the frames `p₀` and `[p₀, 1]`, the model map `f` sends `[p, v]` to `[[p, 1], f v]`. -/
private theorem mkContinuousLinearEquiv_inl_apply_symm_mk {b : B} (p₀ p : P b) (v : F) :
    AssociatedBundle.mkContinuousLinearEquiv 𝕜 H (inl ρ hρ p₀)
        (f ((AssociatedBundle.mkContinuousLinearEquiv 𝕜 G p₀).symm (AssociatedBundle.mk G p v))) =
      AssociatedBundle.mk H (inl ρ hρ p) (f v) := by
  rw [AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, hf,
    AssociatedBundle.mkContinuousLinearEquiv_apply, ← AssociatedBundle.mk_smul, ← inl_smul,
    PrincipalBundle.smul_division]

/-- **The associated map of an equivariant model map**: a continuous semilinear equivalence
`f : F ≃ F'` induces the fibrewise continuous semilinear equivalence
`P ×_G F ≃ (P ×_ρ H) ×_H F'` for `f (g v) = ρ(g) f v`. It is defined in a chosen frame, and the
equivariance makes it `[p, v] ↦ [[p, 1], f v]` in every frame
(`TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant_mk`). -/
def associatedEquivOfEquivariant (_hf : ∀ (g : G) (v : F), f (g • v) = ρ g • f v) (b : B) :
    AssociatedBundle G P F b ≃SL[σ] AssociatedBundle H (Extend P ρ hρ) F' b :=
  have : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  ((AssociatedBundle.mkContinuousLinearEquiv 𝕜 G (Classical.arbitrary (P b))).symm.trans f).trans
    (AssociatedBundle.mkContinuousLinearEquiv 𝕜 H (inl ρ hρ (Classical.arbitrary (P b))))

include hf in
/-- **The associated map in a frame**: `[p, v] ↦ [[p, 1], f v]` for every point `p` of `P` over
`b`. -/
@[simp]
theorem associatedEquivOfEquivariant_mk {b : B} (p : P b) (v : F) :
    associatedEquivOfEquivariant ρ hρ f hf b (AssociatedBundle.mk G p v) =
      AssociatedBundle.mk H (inl ρ hρ p) (f v) :=
  mkContinuousLinearEquiv_inl_apply_symm_mk ρ hρ f hf _ p v

include hf in
/-- **The inverse associated map in a frame**: `[[p, h], w] ↦ [p, f⁻¹ (h w)]`. -/
@[simp]
theorem associatedEquivOfEquivariant_symm_mk {b : B} (p : P b) (h : H) (w : F') :
    (associatedEquivOfEquivariant ρ hρ f hf b).symm (AssociatedBundle.mk H (mk ρ hρ p h) w) =
      AssociatedBundle.mk G p (f.symm (h • w)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, associatedEquivOfEquivariant_mk ρ hρ f hf,
    ContinuousLinearEquiv.apply_symm_apply, ← AssociatedBundle.mk_smul, smul_inl]

include hf in
/-- **The associated map is continuous** on total spaces. -/
theorem continuous_associatedEquivOfEquivariant :
    Continuous fun z : TotalSpace F (AssociatedBundle G P F) ↦
      TotalSpace.mk' F' z.proj (associatedEquivOfEquivariant ρ hρ f hf z.proj z.snd) := by
  -- The total space of `P ×_G F` is a quotient of `P × F`, on which the map is
  -- `(p, v) ↦ [[p, 1], f v]`.
  refine (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk G P F).continuous_comp_iff.1 ?_
  have hc : Continuous fun y : TotalSpace G P × F ↦
      TotalSpace.mk' F' y.1.proj (AssociatedBundle.mk H (inl ρ hρ y.1.snd) (f y.2)) :=
    Continuous.totalSpaceMk_associatedBundleMk (f := fun y : TotalSpace G P × F ↦ y.1.proj)
      ((continuous_inl P ρ hρ).comp continuous_fst) (f.continuous.comp continuous_snd)
  exact hc.congr fun y ↦
    (congrArg (TotalSpace.mk _) (associatedEquivOfEquivariant_mk ρ hρ f hf y.1.snd y.2)).symm

include hf in
/-- **The inverse associated map is continuous** on total spaces. -/
theorem continuous_associatedEquivOfEquivariant_symm :
    Continuous fun z : TotalSpace F' (AssociatedBundle H (Extend P ρ hρ) F') ↦
      TotalSpace.mk' F z.proj ((associatedEquivOfEquivariant ρ hρ f hf z.proj).symm z.snd) := by
  -- The total space of `(P ×_ρ H) ×_H F'` is a quotient of `(P × H) × F'`, on which the inverse
  -- is `((p, h), w) ↦ [p, f⁻¹ (h w)]`.
  have hq := (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk H (Extend P ρ hρ) F').comp
    ((isOpenQuotientMap_totalSpaceMk_mk P ρ hρ).prodMap IsOpenQuotientMap.id)
  refine hq.continuous_comp_iff.1 ?_
  have hc : Continuous fun y : (TotalSpace G P × H) × F' ↦
      TotalSpace.mk' F y.1.1.proj (AssociatedBundle.mk G y.1.1.snd (f.symm (y.1.2 • y.2))) :=
    Continuous.totalSpaceMk_associatedBundleMk
      (f := fun y : (TotalSpace G P × H) × F' ↦ y.1.1.proj) (continuous_fst.comp continuous_fst)
      (f.symm.continuous.comp
        (continuous_smul.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  exact hc.congr fun y ↦ (congrArg (TotalSpace.mk _)
    (associatedEquivOfEquivariant_symm_mk ρ hρ f hf y.1.1.snd y.1.2 y.2)).symm

end Equivariant

end TauCeti.PrincipalBundle.Extend
