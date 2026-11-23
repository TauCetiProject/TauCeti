/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Associated.Principal

/-!
# Smooth transitivity and equivariant comparison for associated bundles

This file upgrades the transitivity and equivariant-comparison homeomorphisms of
`TauCeti.Topology.FiberBundle.Associated.Principal` to `C^n` diffeomorphisms in the charts through
the fibre (`TauCeti.ManifoldTotalSpace`):

* **Smooth transitivity (`assocDiffeomorph`)**: `(P ×_G H) ×_H F ≃ₘ^n P ×_G F` under
  `[IsScalarTower G H F]`.
* **Smooth equivariant comparison (`diffeomorphOfEquivariant`)**: `P ×_G F ≃ₘ^n Q ×_H F` along a
  `C^n` `ρ`-equivariant map `φ : P → Q` of principal bundles when `H` is a `C^n` Lie group acting
  `C^n`-smoothly on `F` and `G` acts on `F` through `ρ`.

These statements do not require `ContMDiffFiberBundle` or `IsManifold` on the associated total
spaces, because they work directly in preferred fibre charts; when a caller needs `IsManifold` on
`ManifoldTotalSpace F (AssociatedBundle G P F)`, install
`TauCeti.AssociatedBundle.contMDiffFiberBundle` locally as an instance (matching
`TauCeti.Geometry.Manifold.FiberBundle.Associated.Pullback`).

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963, Ch. I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §§10.7 and 10.12.
-/

public section

noncomputable section

open Bundle Filter MulOpposite Set TauCeti TauCeti.ManifoldTotalSpace
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
    ContMDiffWithinAt IM (IB.prod IF) n (fun x ↦ homeomorph F _ (q x)) s x₀ ↔
      ContMDiffWithinAt IM (IB.prod IF) n
        (fun x ↦ homeomorph F _ (assocHomeomorph (q x))) s x₀ := by
  simp only [assocHomeomorph_apply, ManifoldTotalSpace.contMDiffWithinAt_iff]
  refine and_congr_right fun hbase ↦ Filter.EventuallyEq.contMDiffWithinAt_iff ?_
    (trivializationAt_assocEquiv_snd (mem_baseSet_trivializationAt G P (q x₀).proj) _)
  filter_upwards [hbase.continuousWithinAt ((trivializationAt G P (q x₀).proj).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt G P (q x₀).proj))] with x hx
  exact trivializationAt_assocEquiv_snd hx _

/-- A family in `(P ×_G H) ×_H F` is `C^n` if and only if its image under `assocHomeomorph` is. -/
theorem contMDiff_assocHomeomorph_iff
    {q : M → TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)} :
    ContMDiff IM (IB.prod IF) n (fun x ↦ homeomorph F _ (q x)) ↔
      ContMDiff IM (IB.prod IF) n (fun x ↦ homeomorph F _ (assocHomeomorph (q x))) := by
  simp only [ContMDiff, ← contMDiffWithinAt_univ,
    contMDiffWithinAt_assocHomeomorph_iff (IB := IB) (IF := IF)]

/-- **Smooth transitivity of associated bundles.** `(P ×_G H) ×_H F` is canonically `C^n`
diffeomorphic to `P ×_G F` in the charts through the fibre. -/
def assocDiffeomorph :
    ManifoldTotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)
      ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯ ManifoldTotalSpace F (AssociatedBundle G P F) :=
  diffeomorphOfCoordEq (fun b ↦ assocEquiv (G := G) (P := P) b) fun b₀ ↦
    mem_of_superset ((trivializationAt G P b₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt G P b₀)) fun _ hb z ↦ trivializationAt_assocEquiv_snd hb z

@[simp] theorem assocDiffeomorph_apply
    (z : TotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)) :
    assocDiffeomorph (n := n) (IB := IB) (IF := IF) (homeomorph F _ z) =
      homeomorph F _ (assocHomeomorph z) := by
  rw [assocHomeomorph_apply]; exact diffeomorphOfCoordEq_apply _ _ z
@[simp] theorem assocDiffeomorph_symm_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    (assocDiffeomorph (n := n) (IB := IB) (IF := IF) (H := H)).symm (homeomorph F _ z) =
      homeomorph F _ (assocHomeomorph.symm z) := by
  rw [assocHomeomorph_symm_apply]; exact diffeomorphOfCoordEq_symm_apply _ _ z
@[simp] theorem homeomorph_symm_assocDiffeomorph_apply
    (x : ManifoldTotalSpace F (AssociatedBundle H (AssociatedBundle G P H) F)) :
    (homeomorph F _).symm (assocDiffeomorph (n := n) (IB := IB) (IF := IF) x) =
      assocHomeomorph ((homeomorph F _).symm x) := by
  rw [assocHomeomorph_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_apply _ _ x
@[simp] theorem homeomorph_symm_assocDiffeomorph_symm_apply
    (x : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    (homeomorph F _).symm ((assocDiffeomorph (n := n) (IB := IB) (IF := IF) (H := H)).symm x) =
      assocHomeomorph.symm ((homeomorph F _).symm x) := by
  rw [assocHomeomorph_symm_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_symm_apply _ _ x
theorem assocDiffeomorph_mk {b : B} (p : P b) (h : H) (v : F) :
    assocDiffeomorph (n := n) (IB := IB) (IF := IF) (homeomorph F _ ⟨b, mk H (mk G p h) v⟩) =
      homeomorph F _ ⟨b, mk G p (h • v)⟩ := by rw [assocDiffeomorph_apply, assocHomeomorph_mk]
theorem assocDiffeomorph_symm_mk {b : B} (p : P b) (v : F) :
    (assocDiffeomorph (n := n) (IB := IB) (IF := IF) (H := H)).symm (homeomorph F _ ⟨b, mk G p v⟩) =
      homeomorph F _ ⟨b, mk H (mk G p (1 : H)) v⟩ := by
  rw [assocDiffeomorph_symm_apply, assocHomeomorph_symm_mk]

end Transitivity

section EquivariantComparison

variable [ChartedSpace HG G] [ChartedSpace HH H]
  {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q] [MulAction G F] [ContinuousSMul G F] [MulAction H F] [ContinuousSMul H F]
  [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q] [LieGroup IH n H] [ContMDiffSMul IH IF n H F]
  (ρ : G →* H) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n
    (fun x : ManifoldTotalSpace G P ↦ homeomorph H Q
      ⟨((homeomorph G P).symm x).proj, φ _ ((homeomorph G P).symm x).snd⟩))
  (hF : ∀ (g : G) (v : F), g • v = ρ g • v)

/-- **Smooth comparison of associated bundles along an equivariant map.** If `φ : ∀ b, P b → Q b` is
a `C^n` `ρ`-equivariant map of principal bundles over `B`, `G` acts on `F` through `ρ`, `H` is a
`C^n` Lie group, and `H` acts `C^n`-smoothly on `F`, then `[p, v] ↦ [φ b p, v]` is a `C^n`
diffeomorphism `P ×_G F ≃ₘ^n Q ×_H F` in the charts through the fibre. -/
def diffeomorphOfEquivariant :
    ManifoldTotalSpace F (AssociatedBundle G P F) ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯
      ManifoldTotalSpace F (AssociatedBundle H Q F) where
  toFun := fiberwiseMap fun b ↦ equivOfEquivariant ρ φ hφ hF b
  invFun := fiberwiseMap fun b ↦ (equivOfEquivariant ρ φ hφ hF b).symm
  left_inv z := by obtain ⟨z, rfl⟩ := (homeomorph F _).surjective z; simp
  right_inv z := by obtain ⟨z, rfl⟩ := (homeomorph F _).surjective z; simp
  contMDiff_toFun := by
    rw [Equiv.coe_fn_mk]
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    intro x₀
    let b₀ := ((homeomorph F (AssociatedBundle G P F)).symm x₀).proj
    let eP := trivializationAt G P b₀
    have hπ := contMDiff_proj n F (AssociatedBundle G P F) IB IF x₀
    refine ((contMDiffAt_section_comp 1 hφc.contMDiffAt hπ).totalSpaceMk_associatedBundleMk
      (contMDiffAt_trivializationAt_snd n IB IF x₀)).congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      (eP.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))] with y hy
    obtain ⟨⟨b, z⟩, rfl⟩ := (homeomorph F _).surjective y
    have hbP : b ∈ eP.baseSet := by simpa using hy
    obtain ⟨v, rfl⟩ := (mk_bijective (G := G) (P := P) (F := F) (eP.symm b 1)).surjective z
    rw [fiberwiseMap_homeomorph]
    dsimp only [Function.comp_def]; rw [Homeomorph.symm_apply_apply]
    exact congrArg (fun w ↦ homeomorph F _ ⟨b, w⟩) <| by
      rw [equivOfEquivariant_mk, trivializationAt_mk_snd hbP,
        congrArg Prod.snd (eP.apply_mk_symm hbP 1), one_smul]
  contMDiff_invFun := by
    rw [Equiv.coe_fn_symm_mk]
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    intro x₀
    let b₀ := ((homeomorph F (AssociatedBundle H Q F)).symm x₀).proj
    let eP := trivializationAt G P b₀; let eQ := trivializationAt H Q b₀
    have hπ := contMDiff_proj n F (AssociatedBundle H Q F) IB IF x₀
    rw [fiberwiseMap_eq, ManifoldTotalSpace.contMDiffAt_iff]
    refine ⟨hπ, ((ManifoldTotalSpace.contMDiffAt_iff.1
      (contMDiffAt_section_comp 1 hφc.contMDiffAt hπ)).2.inv.smul
      (contMDiffAt_trivializationAt_snd n IB IF x₀)).congr_of_eventuallyEq ?_⟩
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      ((eP.open_baseSet.inter eQ.open_baseSet).mem_nhds
        ⟨mem_baseSet_trivializationAt G P b₀, mem_baseSet_trivializationAt H Q b₀⟩)]
      with y ⟨hyP, hyQ⟩
    obtain ⟨⟨b, z⟩, rfl⟩ := (homeomorph F _).surjective y
    have hbP : b ∈ eP.baseSet := by simpa using hyP
    have hbQ : b ∈ eQ.baseSet := by simpa using hyQ
    obtain ⟨v, rfl⟩ := (mk_bijective (G := H) (P := Q) (F := F) (φ b (eP.symm b 1))).surjective z
    rw [Pi.smul_apply', Homeomorph.symm_apply_apply]
    dsimp only [TotalSpace.proj, b₀]
    rw [equivOfEquivariant_symm_mk, trivializationAt_mk_snd hbP,
      congrArg Prod.snd (eP.apply_mk_symm hbP 1), one_smul, trivializationAt_mk_snd hbQ,
      inv_smul_smul]

@[simp] theorem diffeomorphOfEquivariant_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    diffeomorphOfEquivariant (IF := IF) ρ φ hφ hφc hF (homeomorph F _ z) =
      homeomorph F _ ⟨z.proj, equivOfEquivariant ρ φ hφ hF z.proj z.snd⟩ :=
  fiberwiseMap_homeomorph _ z
@[simp] theorem diffeomorphOfEquivariant_symm_apply (z : TotalSpace F (AssociatedBundle H Q F)) :
    (diffeomorphOfEquivariant (IF := IF) ρ φ hφ hφc hF).symm (homeomorph F _ z) =
      homeomorph F _ ⟨z.proj, (equivOfEquivariant ρ φ hφ hF z.proj).symm z.snd⟩ :=
  fiberwiseMap_homeomorph _ z
@[simp] theorem homeomorph_symm_diffeomorphOfEquivariant_apply
    (x : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    (homeomorph F _).symm (diffeomorphOfEquivariant (IF := IF) ρ φ hφ hφc hF x) =
      ⟨((homeomorph F _).symm x).proj,
        equivOfEquivariant ρ φ hφ hF _ ((homeomorph F _).symm x).snd⟩ :=
  homeomorph_symm_fiberwiseMap _ x
@[simp] theorem homeomorph_symm_diffeomorphOfEquivariant_symm_apply
    (x : ManifoldTotalSpace F (AssociatedBundle H Q F)) :
    (homeomorph F _).symm ((diffeomorphOfEquivariant (IF := IF) ρ φ hφ hφc hF).symm x) =
      ⟨((homeomorph F _).symm x).proj,
        (equivOfEquivariant ρ φ hφ hF _).symm ((homeomorph F _).symm x).snd⟩ :=
  homeomorph_symm_fiberwiseMap _ x
theorem diffeomorphOfEquivariant_mk {b : B} (p : P b) (v : F) :
    diffeomorphOfEquivariant (IF := IF) ρ φ hφ hφc hF (homeomorph F _ ⟨b, mk G p v⟩) =
      homeomorph F _ ⟨b, mk H (φ b p) v⟩ := by
  rw [diffeomorphOfEquivariant_apply, equivOfEquivariant_mk]
theorem diffeomorphOfEquivariant_symm_mk {b : B} (p : P b) (v : F) :
    (diffeomorphOfEquivariant (IF := IF) ρ φ hφ hφc hF).symm (homeomorph F _ ⟨b, mk H (φ b p) v⟩) =
      homeomorph F _ ⟨b, mk G p v⟩ := by
  rw [diffeomorphOfEquivariant_symm_apply, equivOfEquivariant_symm_mk]

end EquivariantComparison

end TauCeti.AssociatedBundle
