/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Associated.Basic

/-!
# Associated principal bundles, transitivity, and equivariant principal maps

When a group `H` carries a continuous left action of `G` commuting with right multiplication on `H`
(`[SMulCommClass G Hᵐᵒᵖ H]`), the associated bundle `TauCeti.AssociatedBundle G P H = P ×_G H` of a
principal `G`-bundle `P` over `B` is itself a principal `H`-bundle (`instPrincipalBundle`).

Given `F` with compatible continuous left actions of `H` and `G` (`[IsScalarTower G H F]`),
`(P ×_G H) ×_H F` is canonically homeomorphic over `B` to `P ×_G F` via `[[p, h], v] ↦ [p, h • v]`
(`assocHomeomorph`). More generally, any continuous `ρ`-equivariant map `φ : ∀ b, P b → Q b` into a
principal `H`-bundle `Q` identifies `P ×_G F` with `Q ×_H F` via `[p, v] ↦ [φ b p, v]` whenever `H`
has continuous inversion and `G` acts on `F` through `ρ` (`homeomorphOfEquivariant`).

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963, Ch. I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §§10.7 and 10.12.
* D. Husemoller, *Fibre Bundles*, 3rd ed., Springer, 1994, Ch. 4, §5 and Ch. 6, §2.
-/

public section

open Bundle Filter MulOpposite Set Topology

namespace TauCeti.AssociatedBundle

variable {G H B F : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [Group H] [TopologicalSpace H]

section Principal

variable [MulAction G H] [ContinuousSMul G H]

/-- The fibres of `AssociatedBundle G P H` carry the right multiplication action of `H`. -/
instance instMulActionOp (b : B) : MulAction Hᵐᵒᵖ (AssociatedBundle G P H b) :=
  inferInstanceAs (MulAction Hᵐᵒᵖ H)

variable [SMulCommClass G Hᵐᵒᵖ H]

@[simp] theorem smul_mk {b : B} (p : P b) (h h' : H) :
    op h' • mk G p h = mk G p (h * h') := by
  rw [mk_def, mk_def, ← op_smul_eq_mul]
  exact (smul_comm (trivializationAt G P b ⟨b, p⟩).2 (op h') h).symm

/-- **An associated bundle with a group fibre is principal** whenever the left action of `G` on `H`
commutes with right multiplication on `H`. -/
instance instPrincipalBundle : PrincipalBundle H (AssociatedBundle G P H) where
  isEquivariant_trivialization' e he := by
    obtain ⟨b', rfl⟩ := he.out
    refine ⟨fun b _ v h' ↦ ?_⟩
    let vH : H := v
    have hcomm : (trivializationAt G P b).coordChange (trivializationAt G P b') b 1 • (vH * h') =
        ((trivializationAt G P b).coordChange (trivializationAt G P b') b 1 • vH) * h' := by
      simpa only [op_smul_eq_mul] using
        smul_comm ((trivializationAt G P b).coordChange (trivializationAt G P b') b 1) (op h') vH
    rw [FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
    dsimp only; rw [associatedBundleCore_indexAt]
    exact (associatedBundleCore_coordChange (F := H) b b' b (vH * h')).trans <|
      hcomm.trans (congrArg (· * h') (associatedBundleCore_coordChange (F := H) b b' b vH).symm)

theorem division_mk {b : B} (p q : P b) (h₁ h₂ : H) :
    PrincipalBundle.division H (mk G p h₁) (mk G q h₂) =
      h₁⁻¹ * (PrincipalBundle.division G p q • h₂) :=
  PrincipalBundle.division_eq_iff.2 <| by
    rw [smul_mk, mul_inv_cancel_left, ← mk_smul, PrincipalBundle.smul_division]

@[simp] theorem division_mk_same {b : B} (p : P b) (h₁ h₂ : H) :
    PrincipalBundle.division H (mk G p h₁) (mk G p h₂) = h₁⁻¹ * h₂ := by
  rw [division_mk, PrincipalBundle.division_self, one_smul]

end Principal

section Transitivity

variable [MulAction G H] [ContinuousSMul G H] [SMulCommClass G Hᵐᵒᵖ H] [TopologicalSpace F]
  [MulAction H F] [ContinuousSMul H F] [MulAction G F] [ContinuousSMul G F] [IsScalarTower G H F]

omit [IsScalarTower G H F] in
/-- Fibrewise transitivity equivalence `(P ×_G H) ×_H F ≃ P ×_G F`, sending `[[p, h], v]` to
`[p, h • v]`. -/
noncomputable def assocEquiv (b : B) :
    AssociatedBundle H (AssociatedBundle G P H) F b ≃ AssociatedBundle G P F b :=
  let p : P b := (FiberBundle.homeomorphAt G P b).symm 1
  (Equiv.ofBijective (mk H (P := AssociatedBundle G P H) (mk G p (1 : H)))
    (mk_bijective (G := H) (P := AssociatedBundle G P H) (F := F) (mk G p (1 : H)))).symm.trans
    (Equiv.ofBijective (mk G (P := P) (F := F) p) (mk_bijective (G := G) (P := P) (F := F) p))

@[simp] theorem assocEquiv_mk {b : B} (p : P b) (h : H) (v : F) :
    assocEquiv (G := G) (P := P) (H := H) (F := F) b
        (mk H (P := AssociatedBundle G P H) (mk G p h) v) = mk G p (h • v) := by
  set p₀ : P b := (FiberBundle.homeomorphAt G P b).symm 1
  set g : G := PrincipalBundle.division G p₀ p
  have hmk : mk G p h = op ((g • (1 : H)) * h) • mk G p₀ (1 : H) := by
    rw [smul_mk, one_mul, ← op_smul_eq_mul, ← smul_comm, op_smul_eq_mul, one_mul,
      ← mk_smul, PrincipalBundle.smul_division]
  dsimp only [assocEquiv]
  rw [hmk, mk_smul, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply,
    mul_smul, smul_assoc, one_smul, ← mk_smul, PrincipalBundle.smul_division]

@[simp] theorem assocEquiv_symm_mk {b : B} (p : P b) (v : F) :
    (assocEquiv (G := G) (P := P) (H := H) (F := F) b).symm (mk G p v) =
      mk H (P := AssociatedBundle G P H) (mk G p (1 : H)) v :=
  (assocEquiv b).symm_apply_eq.2 (by rw [assocEquiv_mk, one_smul])

/-- In preferred charts, `assocEquiv` preserves fibre coordinates identically. -/
theorem trivializationAt_assocEquiv_snd {b' b : B} (hb : b ∈ (trivializationAt G P b').baseSet)
    (z : AssociatedBundle H (AssociatedBundle G P H) F b) :
    (trivializationAt F (AssociatedBundle H (AssociatedBundle G P H) F) b' ⟨b, z⟩).2 =
      (trivializationAt F (AssociatedBundle G P F) b' ⟨b, assocEquiv b z⟩).2 := by
  obtain ⟨u, v, rfl⟩ := exists_mk z; obtain ⟨p, h, rfl⟩ := exists_mk u
  have hbH : b ∈ (trivializationAt H (AssociatedBundle G P H) b').baseSet :=
    (baseSet_trivializationAt (G := G) (P := P) (F := H) b').symm ▸ hb
  rw [assocEquiv_mk, trivializationAt_mk_snd hbH, trivializationAt_mk_snd hb,
    trivializationAt_mk_snd hb, smul_assoc]

private theorem continuousAt_assocEquiv_iff {X : Type*} [TopologicalSpace X] {f : X → B}
    {q : ∀ x, AssociatedBundle H (AssociatedBundle G P H) F (f x)} {x₀ : X} :
    ContinuousAt (fun x ↦ TotalSpace.mk' F (f x) (q x)) x₀ ↔
      ContinuousAt (fun x ↦ TotalSpace.mk' F (f x) (assocEquiv (f x) (q x))) x₀ := by
  simp only [FiberBundle.continuousAt_totalSpace]
  refine and_congr_right fun hf ↦ continuousAt_congr ?_
  filter_upwards [hf ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G P (f x₀)))] with x hx
  exact trivializationAt_assocEquiv_snd hx (q x)

/-- **Transitivity of associated bundles**: `(P ×_G H) ×_H F` is canonically homeomorphic over `B`
to `P ×_G F`. -/
noncomputable def assocHomeomorph :
    TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F) ≃ₜ
      TotalSpace F (AssociatedBundle G P F) where
  toFun z := ⟨z.proj, assocEquiv z.proj z.2⟩
  invFun z := ⟨z.proj, (assocEquiv z.proj).symm z.2⟩
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_iff_continuousAt.2 fun _ ↦
    continuousAt_assocEquiv_iff.1 continuousAt_id
  continuous_invFun := continuous_iff_continuousAt.2 fun _ ↦
    continuousAt_assocEquiv_iff.2 <| by
      simp only [Equiv.apply_symm_apply, TotalSpace.eta]; exact continuousAt_id

theorem assocHomeomorph_apply (z : TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)) :
    assocHomeomorph (G := G) (P := P) (H := H) (F := F) z = ⟨z.proj, assocEquiv z.proj z.2⟩ := (rfl)

theorem assocHomeomorph_symm_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    (assocHomeomorph (G := G) (P := P) (H := H) (F := F)).symm z =
      ⟨z.proj, (assocEquiv z.proj).symm z.2⟩ := (rfl)

@[simp] theorem assocHomeomorph_proj
    (z : TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)) :
    (assocHomeomorph (G := G) (P := P) (H := H) (F := F) z).proj = z.proj := (rfl)

@[simp] theorem assocHomeomorph_symm_proj (z : TotalSpace F (AssociatedBundle G P F)) :
    ((assocHomeomorph (G := G) (P := P) (H := H) (F := F)).symm z).proj = z.proj := (rfl)

@[simp] theorem assocHomeomorph_mk {b : B} (p : P b) (h : H) (v : F) :
    assocHomeomorph (G := G) (P := P) (H := H) (F := F)
        ⟨b, mk H (P := AssociatedBundle G P H) (mk G p h) v⟩ = ⟨b, mk G p (h • v)⟩ :=
  congrArg (TotalSpace.mk b) (assocEquiv_mk p h v)

@[simp] theorem assocHomeomorph_symm_mk {b : B} (p : P b) (v : F) :
    (assocHomeomorph (G := G) (P := P) (H := H) (F := F)).symm ⟨b, mk G p v⟩ =
      ⟨b, mk H (P := AssociatedBundle G P H) (mk G p (1 : H)) v⟩ :=
  congrArg (TotalSpace.mk b) (assocEquiv_symm_mk p v)

end Transitivity

section EquivariantComparison

variable {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q] [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q]
  [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F] [MulAction H F] [ContinuousSMul H F]

/-- A `ρ`-equivariant fibrewise map `φ : ∀ b, P b → Q b` between principal bundles identifies
`AssociatedBundle G P F` fibrewise with `AssociatedBundle H Q F` whenever `G` acts on `F` through
`ρ`, sending `[p, v]` to `[φ b p, v]`. -/
noncomputable def equivOfEquivariant (ρ : G →* H) (φ : ∀ b, P b → Q b)
    (_hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (_hF : ∀ (g : G) (v : F), g • v = ρ g • v) (b : B) :
    AssociatedBundle G P F b ≃ AssociatedBundle H Q F b :=
  let p₀ : P b := (FiberBundle.homeomorphAt G P b).symm 1
  (Equiv.ofBijective (mk G p₀) (mk_bijective (G := G) (P := P) (F := F) p₀)).symm.trans
    (Equiv.ofBijective (mk H (φ b p₀)) (mk_bijective (G := H) (P := Q) (F := F) (φ b p₀)))

@[simp] theorem equivOfEquivariant_mk (ρ : G →* H) (φ : ∀ b, P b → Q b)
    (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) {b : B} (p : P b) (v : F) :
    equivOfEquivariant ρ φ hφ hF b (mk G p v) = mk H (φ b p) v := by
  set p₀ : P b := (FiberBundle.homeomorphAt G P b).symm 1
  have hp : p = op (PrincipalBundle.division G p₀ p) • p₀ :=
    (PrincipalBundle.smul_division p₀ p).symm
  dsimp only [equivOfEquivariant]
  rw [hp, mk_smul, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply,
    hF, ← mk_smul, ← hφ]

@[simp] theorem equivOfEquivariant_symm_mk (ρ : G →* H) (φ : ∀ b, P b → Q b)
    (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) {b : B} (p : P b) (v : F) :
    (equivOfEquivariant ρ φ hφ hF b).symm (mk H (φ b p) v) = mk G p v :=
  (equivOfEquivariant ρ φ hφ hF b).symm_apply_eq.2 (equivOfEquivariant_mk ρ φ hφ hF p v).symm

/-- **Associated bundles along a principal lift or reduction.** If `φ : ∀ b, P b → Q b` is a
continuous `ρ`-equivariant map of principal bundles and `H` has continuous inversion, then
`[p, v] ↦ [φ b p, v]` is a homeomorphism `P ×_G F ≃ₜ Q ×_H F` when `G` acts on `F` through `ρ`. -/
noncomputable def homeomorphOfEquivariant [ContinuousInv H] (ρ : G →* H) (φ : ∀ b, P b → Q b)
    (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (hφc : Continuous fun x : TotalSpace G P ↦ TotalSpace.mk' H x.proj (φ x.proj x.2))
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) :
    TotalSpace F (AssociatedBundle G P F) ≃ₜ TotalSpace F (AssociatedBundle H Q F) where
  toFun z := ⟨z.proj, equivOfEquivariant ρ φ hφ hF z.proj z.2⟩
  invFun z := ⟨z.proj, (equivOfEquivariant ρ φ hφ hF z.proj).symm z.2⟩
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    rw [(isOpenQuotientMap_totalSpaceMk_mk G P F).isQuotientMap.continuous_iff]
    refine (Continuous.totalSpaceMk_associatedBundleMk (G := H) (P := Q)
      (f := fun x : TotalSpace G P × F ↦ x.1.proj) (p := fun x ↦ φ x.1.proj x.1.2)
      (hφc.comp continuous_fst) continuous_snd).congr fun ⟨⟨b, p⟩, v⟩ ↦
        congrArg (TotalSpace.mk b) (equivOfEquivariant_mk ρ φ hφ hF p v).symm
  continuous_invFun := by
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    refine continuous_iff_continuousAt.2 fun z₀ ↦ ?_
    set b₀ := z₀.proj
    set eP := trivializationAt G P b₀; set eQ := trivializationAt H Q b₀
    set eQF := trivializationAt F (AssociatedBundle H Q F) b₀
    have hbP₀ : b₀ ∈ eP.baseSet := mem_baseSet_trivializationAt G P b₀
    have hbQ₀ : b₀ ∈ eQ.baseSet := mem_baseSet_trivializationAt H Q b₀
    have hσ_cont : ContinuousAt (fun b ↦ TotalSpace.mk' G b (eP.symm b 1)) b₀ :=
      (ContinuousAt.comp (x := b₀)
        (eP.toOpenPartialHomeomorph.continuousAt_symm ((eP.mem_target (x := (b₀, (1 : G)))).2 hbP₀))
        (continuousAt_id.prodMk continuousAt_const)).congr_of_eventuallyEq
        (mem_of_superset (eP.open_baseSet.mem_nhds hbP₀) fun _ hb ↦ eP.mk_symm hb 1)
    have hπ : ContinuousAt (π F (AssociatedBundle H Q F)) z₀ :=
      (FiberBundle.continuous_proj F _).continuousAt
    have hσz : ContinuousAt (fun z : TotalSpace F (AssociatedBundle H Q F) ↦
        TotalSpace.mk' G z.proj (eP.symm z.proj 1)) z₀ := hσ_cont.comp hπ
    have hg_inv : ContinuousAt (fun z : TotalSpace F (AssociatedBundle H Q F) ↦
        ((eQ ⟨z.proj, φ z.proj (eP.symm z.proj 1)⟩).2)⁻¹) z₀ :=
      (ContinuousAt.comp (x := z₀) (eQ.continuousAt (eQ.mem_source.2 hbQ₀))
        (hφc.continuousAt.comp hσz)).snd.inv
    have hv : ContinuousAt (fun z ↦ (eQF z).2) z₀ :=
      (eQF.continuousAt (eQF.mem_source.2
        ((baseSet_trivializationAt (G := H) (P := Q) (F := F) b₀).symm ▸ hbQ₀))).snd
    refine (hσz.totalSpaceMk_associatedBundleMk (F := F) (hg_inv.smul hv)).congr_of_eventuallyEq ?_
    filter_upwards [hπ.preimage_mem_nhds
      ((eP.open_baseSet.inter eQ.open_baseSet).mem_nhds ⟨hbP₀, hbQ₀⟩)] with ⟨b, y⟩ ⟨_, hzQ⟩
    obtain ⟨w, rfl⟩ := (mk_bijective (G := H) (P := Q) (F := F) (φ b (eP.symm b 1))).surjective y
    dsimp only [eQF, TotalSpace.proj] at hzQ ⊢
    rw [Pi.smul_apply', trivializationAt_mk_snd hzQ, inv_smul_smul, equivOfEquivariant_symm_mk]

section

variable [ContinuousInv H] (ρ : G →* H) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : Continuous fun x : TotalSpace G P ↦ TotalSpace.mk' H x.proj (φ x.proj x.2))
  (hF : ∀ (g : G) (v : F), g • v = ρ g • v)

theorem homeomorphOfEquivariant_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    homeomorphOfEquivariant ρ φ hφ hφc hF z =
      ⟨z.proj, equivOfEquivariant ρ φ hφ hF z.proj z.2⟩ := (rfl)

theorem homeomorphOfEquivariant_symm_apply (z : TotalSpace F (AssociatedBundle H Q F)) :
    (homeomorphOfEquivariant ρ φ hφ hφc hF).symm z =
      ⟨z.proj, (equivOfEquivariant ρ φ hφ hF z.proj).symm z.2⟩ := (rfl)

@[simp] theorem homeomorphOfEquivariant_proj (z : TotalSpace F (AssociatedBundle G P F)) :
    (homeomorphOfEquivariant ρ φ hφ hφc hF z).proj = z.proj := (rfl)

@[simp] theorem homeomorphOfEquivariant_mk {b : B} (p : P b) (v : F) :
    homeomorphOfEquivariant ρ φ hφ hφc hF ⟨b, mk G p v⟩ = ⟨b, mk H (φ b p) v⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_mk ρ φ hφ hF p v)

@[simp] theorem homeomorphOfEquivariant_symm_mk {b : B} (p : P b) (v : F) :
    (homeomorphOfEquivariant ρ φ hφ hφc hF).symm ⟨b, mk H (φ b p) v⟩ = ⟨b, mk G p v⟩ :=
  congrArg (TotalSpace.mk b) (equivOfEquivariant_symm_mk ρ φ hφ hF p v)

end

end EquivariantComparison

end TauCeti.AssociatedBundle
