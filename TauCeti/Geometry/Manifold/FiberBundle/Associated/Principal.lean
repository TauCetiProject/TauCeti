/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Topology.FiberBundle.Associated.Principal

/-!
# Smooth principal and transitivity structures on associated bundles

This file upgrades `TauCeti.Topology.FiberBundle.Associated.Principal` to `C^n` manifolds using the
charts through the fibre (`TauCeti.ManifoldTotalSpace`):

* **Smooth transitivity (`assocDiffeomorph`)**: `(P ×_G H) ×_H F ≃ₘ^n P ×_G F` under
  `[IsScalarTower G H F]`.
* **Smooth equivariant comparison (`diffeomorphOfEquivariant`)**: `P ×_G F ≃ₘ^n Q ×_H F` along a
  `C^n` `ρ`-equivariant map `φ : P → Q` of principal bundles when `H` is a `C^n` Lie group acting
  `C^n`-smoothly on `F` and `G` acts on `F` through `ρ`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963, Ch. I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §§10.7 and 10.12.
-/

public section

noncomputable section

open Bundle Filter MulOpposite Set TauCeti
open scoped Manifold ContDiff Topology

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G H F M : Type*} [NontriviallyNormedField 𝕜]
  {EB HB EF HF EM HM EG HG EH HH : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH] {IH : ModelWithCorners 𝕜 EH HH}
  [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

section Transitivity

variable [MulAction G H] [ContinuousSMul G H] [SMulCommClass G Hᵐᵒᵖ H]
  [MulAction H F] [ContinuousSMul H F] [MulAction G F] [ContinuousSMul G F] [IsScalarTower G H F]

/-- A family in `(P ×_G H) ×_H F` is `C^n` within a set at a point if and only if its image under
`assocHomeomorph` in `P ×_G F` is `C^n` there. -/
theorem contMDiffWithinAt_assocHomeomorph_iff
    {q : M → TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod IF) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F _ (q x)) s x₀ ↔
      ContMDiffWithinAt IM (IB.prod IF) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F _ (assocHomeomorph (q x))) s x₀ := by
  simp only [assocHomeomorph_apply, ManifoldTotalSpace.contMDiffWithinAt_iff]
  refine and_congr_right fun hbase ↦ Filter.EventuallyEq.contMDiffWithinAt_iff ?_
    (trivializationAt_assocEquiv_snd (mem_baseSet_trivializationAt G P (q x₀).proj) _)
  filter_upwards [hbase.continuousWithinAt ((trivializationAt G P (q x₀).proj).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G P (q x₀).proj))] with x hx
  exact trivializationAt_assocEquiv_snd hx _

/-- A family in `(P ×_G H) ×_H F` is `C^n` if and only if its image under `assocHomeomorph` is. -/
theorem contMDiff_assocHomeomorph_iff
    {q : M → TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)} :
    ContMDiff IM (IB.prod IF) n (fun x ↦ ManifoldTotalSpace.homeomorph F _ (q x)) ↔
      ContMDiff IM (IB.prod IF) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F _ (assocHomeomorph (q x))) := by
  simp only [ContMDiff, ← contMDiffWithinAt_univ,
    contMDiffWithinAt_assocHomeomorph_iff (IB := IB) (IF := IF)]

/-- **Smooth transitivity of associated bundles.** `(P ×_G H) ×_H F` is canonically `C^n`
diffeomorphic to `P ×_G F` in the charts through the fibre. -/
def assocDiffeomorph :
    ManifoldTotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)
      ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯ ManifoldTotalSpace F (AssociatedBundle G P F) where
  toFun := ManifoldTotalSpace.fiberwiseMap fun b ↦ assocEquiv b
  invFun := ManifoldTotalSpace.fiberwiseMap fun b ↦ (assocEquiv b).symm
  left_inv z := by obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective z; simp
  right_inv z := by obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective z; simp
  contMDiff_toFun := by
    change ContMDiff (IB.prod IF) (IB.prod IF) n
      (ManifoldTotalSpace.fiberwiseMap fun b ↦ assocEquiv b)
    have hid : ContMDiff (IB.prod IF) (IB.prod IF) n
        (fun y : ManifoldTotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F) ↦
          ManifoldTotalSpace.homeomorph F _ ((ManifoldTotalSpace.homeomorph F _).symm y)) :=
      (contMDiff_id (I := IB.prod IF)).congr fun y ↦
        (ManifoldTotalSpace.homeomorph F _).apply_symm_apply y
    refine ((contMDiff_assocHomeomorph_iff (IB := IB) (IF := IF)).mp hid).congr fun y ↦ ?_
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective y
    rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply,
      assocHomeomorph_apply]
  contMDiff_invFun := by
    change ContMDiff (IB.prod IF) (IB.prod IF) n
      (ManifoldTotalSpace.fiberwiseMap fun b ↦ (assocEquiv b).symm)
    have hid : ContMDiff (IB.prod IF) (IB.prod IF) n
        (fun y : ManifoldTotalSpace F (AssociatedBundle G P F) ↦
          ManifoldTotalSpace.homeomorph F _ (assocHomeomorph
            ((assocHomeomorph (H := H)).symm ((ManifoldTotalSpace.homeomorph F _).symm y)))) :=
      (contMDiff_id (I := IB.prod IF)).congr fun y ↦ by
        rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]; rfl
    refine ((contMDiff_assocHomeomorph_iff (IB := IB) (IF := IF)).mpr hid).congr fun y ↦ ?_
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective y
    rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply,
      assocHomeomorph_symm_apply]

@[simp] theorem assocDiffeomorph_apply
    (z : TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)) :
    assocDiffeomorph (n := n) (IB := IB) (IF := IF) (G := G) (P := P) (H := H) (F := F)
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ (assocHomeomorph z) := by
  rw [assocHomeomorph_apply]; exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp] theorem assocDiffeomorph_symm_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    (assocDiffeomorph (n := n) (IB := IB) (IF := IF) (G := G) (P := P) (H := H) (F := F)).symm
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ (assocHomeomorph.symm z) := by
  rw [assocHomeomorph_symm_apply]; exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

theorem assocDiffeomorph_mk {b : B} (p : P b) (h : H) (v : F) :
    assocDiffeomorph (n := n) (IB := IB) (IF := IF) (G := G) (P := P) (H := H) (F := F)
        (ManifoldTotalSpace.homeomorph F _ ⟨b, mk H (mk G p h) v⟩) =
      ManifoldTotalSpace.homeomorph F _ ⟨b, mk G p (h • v)⟩ := by
  rw [assocDiffeomorph_apply, assocHomeomorph_mk]

end Transitivity

section EquivariantComparison

variable [ChartedSpace HG G] [ChartedSpace HH H]
  {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q]

omit [Group H] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
private theorem contMDiffAt_section_comp [∀ b, Nonempty (P b)] {φ : ∀ b, P b → Q b}
    (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P ↦ ManifoldTotalSpace.homeomorph H Q
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
          φ _ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩))
    {f : M → B} {x₀ : M} (hf : ContMDiffAt IM IB n f x₀) :
    ContMDiffAt IM (IB.prod IH) n
      (fun y ↦ ManifoldTotalSpace.homeomorph H Q
        ⟨f y, φ (f y) ((trivializationAt G P (f x₀)).symm (f y) 1)⟩) x₀ := by
  have hbase : ContMDiffAt IB (IB.prod IH) n
      (fun b ↦ ManifoldTotalSpace.homeomorph H Q
        ⟨b, φ b ((trivializationAt G P (f x₀)).symm b 1)⟩) (f x₀) :=
    (hφc.contMDiffAt.comp (f x₀)
      (ManifoldTotalSpace.contMDiffAt_totalSpaceMk_trivializationAt_symm
        (f x₀) 1)).congr_of_eventuallyEq
      (.of_forall fun _ ↦ by dsimp only [Function.comp_def]; rw [Homeomorph.symm_apply_apply])
  exact hbase.comp x₀ hf

variable [MulAction G F] [ContinuousSMul G F] [MulAction H F] [ContinuousSMul H F]
  [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q]

/-- **Smooth comparison of associated bundles along an equivariant map.** If `φ : ∀ b, P b → Q b` is
a `C^n` `ρ`-equivariant map of principal bundles over `B`, `G` acts on `F` through `ρ`, `H` is a
`C^n` Lie group, and `H` acts `C^n`-smoothly on `F`, then `[p, v] ↦ [φ b p, v]` is a `C^n`
diffeomorphism `P ×_G F ≃ₘ^n Q ×_H F` in the charts through the fibre. -/
def diffeomorphOfEquivariant [LieGroup IH n H] [ContMDiffSMul IH IF n H F]
    (ρ : G →* H) (φ : ∀ b, P b → Q b)
    (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P ↦ ManifoldTotalSpace.homeomorph H Q
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
          φ _ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩))
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) :
    ManifoldTotalSpace F (AssociatedBundle G P F) ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯
      ManifoldTotalSpace F (AssociatedBundle H Q F) where
  toFun := ManifoldTotalSpace.fiberwiseMap fun b ↦ equivOfEquivariant ρ φ hφ hF b
  invFun := ManifoldTotalSpace.fiberwiseMap fun b ↦ (equivOfEquivariant ρ φ hφ hF b).symm
  left_inv z := by obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective z; simp
  right_inv z := by obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective z; simp
  contMDiff_toFun := by
    change ContMDiff (IB.prod IF) (IB.prod IF) n
      (ManifoldTotalSpace.fiberwiseMap fun b ↦ equivOfEquivariant ρ φ hφ hF b)
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    intro x₀
    let b₀ := ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm x₀).proj
    let eP := trivializationAt G P b₀
    have hπ := ManifoldTotalSpace.contMDiff_proj n F (AssociatedBundle G P F) IB IF x₀
    refine ((contMDiffAt_section_comp hφc hπ).totalSpaceMk_associatedBundleMk
      (ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IF x₀)).congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      (eP.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))] with y hy
    obtain ⟨⟨b, z⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective y
    have hbP : b ∈ eP.baseSet := by simpa using hy
    obtain ⟨v, rfl⟩ := (mk_bijective (G := G) (P := P) (F := F) (eP.symm b 1)).surjective z
    rw [ManifoldTotalSpace.fiberwiseMap_homeomorph]
    dsimp only [Function.comp_def]; rw [Homeomorph.symm_apply_apply]
    exact congrArg (fun w ↦ ManifoldTotalSpace.homeomorph F _ ⟨b, w⟩) <| by
      rw [equivOfEquivariant_mk, trivializationAt_mk_snd hbP,
        congrArg Prod.snd (eP.apply_mk_symm hbP 1), one_smul]
  contMDiff_invFun := by
    change ContMDiff (IB.prod IF) (IB.prod IF) n
      (ManifoldTotalSpace.fiberwiseMap fun b ↦ (equivOfEquivariant ρ φ hφ hF b).symm)
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    intro x₀
    let b₀ := ((ManifoldTotalSpace.homeomorph F (AssociatedBundle H Q F)).symm x₀).proj
    let eP := trivializationAt G P b₀; let eQ := trivializationAt H Q b₀
    have hπ := ManifoldTotalSpace.contMDiff_proj n F (AssociatedBundle H Q F) IB IF x₀
    have hf_eq : ManifoldTotalSpace.fiberwiseMap (fun b ↦ (equivOfEquivariant ρ φ hφ hF b).symm) =
        fun y : ManifoldTotalSpace F (AssociatedBundle H Q F) ↦ ManifoldTotalSpace.homeomorph F _
          ⟨((ManifoldTotalSpace.homeomorph F _).symm y).proj,
            (equivOfEquivariant ρ φ hφ hF _).symm
              ((ManifoldTotalSpace.homeomorph F _).symm y).2⟩ := by
      funext y; obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective y
      rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply]
    rw [hf_eq, ManifoldTotalSpace.contMDiffAt_iff]
    refine ⟨hπ, ((ManifoldTotalSpace.contMDiffAt_iff.1
      (contMDiffAt_section_comp hφc hπ)).2.inv.smul
      (ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IF x₀)).congr_of_eventuallyEq ?_⟩
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      ((eP.open_baseSet.inter eQ.open_baseSet).mem_nhds
        ⟨mem_baseSet_trivializationAt G P b₀, mem_baseSet_trivializationAt H Q b₀⟩)]
      with y ⟨hyP, hyQ⟩
    obtain ⟨⟨b, z⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph F _).surjective y
    have hbP : b ∈ eP.baseSet := by simpa using hyP
    have hbQ : b ∈ eQ.baseSet := by simpa using hyQ
    obtain ⟨v, rfl⟩ := (mk_bijective (G := H) (P := Q) (F := F) (φ b (eP.symm b 1))).surjective z
    rw [Pi.smul_apply', Homeomorph.symm_apply_apply]
    dsimp only [TotalSpace.proj, b₀]
    rw [equivOfEquivariant_symm_mk, trivializationAt_mk_snd hbP,
      congrArg Prod.snd (eP.apply_mk_symm hbP 1), one_smul, trivializationAt_mk_snd hbQ,
      inv_smul_smul]

section

variable [LieGroup IH n H] [ContMDiffSMul IH IF n H F] (ρ : G →* H) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n
    (fun x : ManifoldTotalSpace G P ↦ ManifoldTotalSpace.homeomorph H Q
      ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
        φ _ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩))
  (hF : ∀ (g : G) (v : F), g • v = ρ g • v)

@[simp] theorem diffeomorphOfEquivariant_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) (IF := IF) ρ φ hφ hφc hF
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ ⟨z.proj, equivOfEquivariant ρ φ hφ hF z.proj z.2⟩ :=
  ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp] theorem diffeomorphOfEquivariant_symm_apply (z : TotalSpace F (AssociatedBundle H Q F)) :
    (diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) (IF := IF) ρ φ hφ hφc hF).symm
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ ⟨z.proj, (equivOfEquivariant ρ φ hφ hF z.proj).symm z.2⟩ :=
  ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

theorem diffeomorphOfEquivariant_mk {b : B} (p : P b) (v : F) :
    diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) (IF := IF) ρ φ hφ hφc hF
        (ManifoldTotalSpace.homeomorph F _ ⟨b, mk G p v⟩) =
      ManifoldTotalSpace.homeomorph F _ ⟨b, mk H (φ b p) v⟩ := by
  rw [diffeomorphOfEquivariant_apply, equivOfEquivariant_mk]

theorem diffeomorphOfEquivariant_symm_mk {b : B} (p : P b) (v : F) :
    (diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) (IF := IF) ρ φ hφ hφc hF).symm
        (ManifoldTotalSpace.homeomorph F _ ⟨b, mk H (φ b p) v⟩) =
      ManifoldTotalSpace.homeomorph F _ ⟨b, mk G p v⟩ := by
  rw [diffeomorphOfEquivariant_symm_apply, equivOfEquivariant_symm_mk]

end

end EquivariantComparison

end TauCeti.AssociatedBundle
