/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.TotalSpace
public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Prod
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Properness of principal bundle actions

For a topological principal bundle, the map `(p, g) ↦ (p, p·g)` is a homeomorphism onto
the total space of the fibrewise product. Its inverse is `(p, q) ↦ (p, δ(p,q))`, using
the division map. The fibrewise product has the topology inherited from the product of total
spaces, and is closed when the base is Hausdorff. Consequently the right action on the total
space is proper. No local compactness, countability or smoothness is required.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer (1993), §10.2 (principal bundles and their division maps).
-/

public section

open Bundle MulOpposite Set

namespace TauCeti.PrincipalBundle

variable {B G : Type*} [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The fibrewise right action is continuous on the total space. -/
instance continuousSMul_totalSpace [ContinuousMul G] : ContinuousSMul Gᵐᵒᵖ (TotalSpace G P) where
  continuous_smul := Continuous.totalSpaceMk_smul continuous_snd
    (continuous_unop.comp continuous_fst)

/-- The image of the principal action map consists exactly of pairs in a common fibre. -/
theorem range_action :
    range (fun x : TotalSpace G P × G ↦ (x.1, op x.2 • x.1)) =
      {p | p.1.proj = p.2.proj} := by
  ext p
  constructor
  · rintro ⟨⟨q, g⟩, rfl⟩
    rfl
  · rcases p with ⟨⟨b, u⟩, ⟨b', v⟩⟩
    intro h
    dsimp at h
    subst b'
    exact ⟨(⟨b, u⟩, division G u v), by simp⟩

variable [IsTopologicalGroup G]

variable (G P) in
/-- The action identifies `P × G` with the fibrewise product of `P` with itself, by
`(p,g) ↦ (p,p·g)`. The latter carries its topology induced from `P × P`. -/
noncomputable def actionHomeomorph :
    TotalSpace G P × G ≃ₜ TotalSpace (G × G) (P ×ᵇ P) where
  toFun x := ⟨x.1.proj, x.1.snd, op x.2 • x.1.snd⟩
  invFun x := (⟨x.proj, x.snd.1⟩, division G x.snd.1 x.snd.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := (FiberBundle.Prod.isInducing_diag G P G P).continuous_iff.2
    (continuous_fst.prodMk (continuous_fst.totalSpaceMk_smul continuous_snd))
  continuous_invFun := by
    have h := (FiberBundle.Prod.isInducing_diag G P G P).continuous
    exact h.fst.prodMk (h.fst.division h.snd)

@[simp]
theorem actionHomeomorph_apply (p : TotalSpace G P) (g : G) :
    actionHomeomorph G P (p, g) = ⟨p.proj, p.snd, op g • p.snd⟩ := (rfl)

@[simp]
theorem actionHomeomorph_symm_apply (p : TotalSpace (G × G) (P ×ᵇ P)) :
    (actionHomeomorph G P).symm p = (⟨p.proj, p.snd.1⟩, division G p.snd.1 p.snd.2) := (rfl)

/-- Over a Hausdorff base the principal action map is a closed embedding: its image is the
closed relation of pairs lying over a common base point. -/
theorem isClosedEmbedding_action [T2Space B] :
    Topology.IsClosedEmbedding (fun x : TotalSpace G P × G ↦ (x.1, op x.2 • x.1)) := by
  exact (FiberBundle.Prod.isClosedEmbedding_diag
    (FiberBundle.continuous_proj G P) (FiberBundle.continuous_proj G P)).comp
      (actionHomeomorph G P).isClosedEmbedding

/-- The right action on a topological principal bundle over a Hausdorff base is proper. -/
instance properSMul_totalSpace [T2Space B] : ProperSMul Gᵐᵒᵖ (TotalSpace G P) where
  isProperMap_smul_pair := by
    have h := (isClosedEmbedding_action (G := G) (P := P)).isProperMap
    let e : Gᵐᵒᵖ × TotalSpace G P ≃ₜ TotalSpace G P × G :=
      (Homeomorph.prodComm _ _).trans ((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm)
    exact (Homeomorph.prodComm _ _).isProperMap.comp (h.comp e.isProperMap)

end TauCeti.PrincipalBundle
