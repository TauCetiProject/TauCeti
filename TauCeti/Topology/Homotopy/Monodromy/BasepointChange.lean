/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Basepoint change for the subgroup recovered by a cover

Let `p : E → X` be a covering map, let `γ : Path x₀ x₁`, and let `e₀` lie over `x₀`. The
lifted endpoint `hp.monodromy ⟦γ⟧ e₀` lies over `x₁`, and the subgroup recovered from that
pointed lift is the transport of the subgroup recovered from `e₀` along `γ`:

```text
  im (p_* : π₁(E, hp.monodromy ⟦γ⟧ e₀) → π₁(X, x₁))
    = γ_* (im (p_* : π₁(E, e₀) → π₁(X, x₀))).
```

Here `p_*` denotes the induced map on fundamental groups and `γ_*` denotes the
basepoint-change isomorphism induced by `γ`; the displayed equality is an equality of
image subgroups.

The proof combines Mathlib's path-conjugation isomorphism for fundamental groups with its
path-lifting and monodromy API, packaged for recovered subgroups in
`TauCeti.Topology.Homotopy.Monodromy.Basic`. The convention is the usual one from Hatcher,
*Algebraic Topology*, Section 1.3.

For a quotient covering map `p : E → X` by a group `G`, Mathlib reads a loop class at `x₀` as
an element of `Gᵐᵒᵖ` through a lift `e₀` of `x₀`
(`IsQuotientCoveringMap.fundamentalGroupToMulOpposite`, and
`IsQuotientCoveringMap.fundamentalGroupEquiv` for simply connected `E`). Changing the basepoint
along `γ` and the lift to `hp.isCoveringMap.monodromy ⟦γ⟧ e₀` does not change this element
(`IsQuotientCoveringMap.fundamentalGroupEquiv_fundamentalGroupMulEquivOfPath`, with additive
versions). When `G` is commutative the lift does not matter, so this gives the basepoint
independence of the winding number of the circle and of the lattice of a torus.
-/

public section

namespace IsCoveringMap

open TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {x₀ x₁ : X}

/-- **Monodromy after basepoint change.** Monodromy along the transport back along `γ` of a loop
class `g` at `x₁` is monodromy along `g`, conjugated by monodromy along `γ`: lift `γ`, then go
around `g`, then return along `γ`. -/
theorem monodromy_fundamentalGroupMulEquivOfPath_symm_apply
    (hp : IsCoveringMap p) (γ : Path x₀ x₁) (g : FundamentalGroup X x₁) (e₀ : p ⁻¹' {x₀}) :
    hp.monodromy ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g).toPath e₀ =
      (coveringFiberEquiv hp (.mk γ)).symm (hp.monodromy g.toPath (hp.monodromy (.mk γ) e₀)) := by
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, hp.monodromy_trans_apply,
    hp.monodromy_trans_apply, coveringFiberEquiv_symm_apply]

/-- The monodromy permutation of the transport back along `γ` of a loop class `g` is the monodromy
permutation of `g`, transported from the fibre over `x₁` to the fibre over `x₀` by monodromy along
`γ`. -/
theorem monodromyPerm_fundamentalGroupMulEquivOfPath_symm
    (hp : IsCoveringMap p) (γ : Path x₀ x₁) (g : FundamentalGroup X x₁) :
    hp.monodromyPerm x₀ ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g) =
      (coveringFiberEquiv hp (.mk γ)).symm.permCongr (hp.monodromyPerm x₁ g) := by
  ext e₀
  rw [Equiv.permCongr_apply, Equiv.symm_symm, coveringFiberEquiv_apply,
    IsCoveringMap.coe_monodromyPerm, IsCoveringMap.coe_monodromyPerm,
    hp.monodromy_fundamentalGroupMulEquivOfPath_symm_apply]

/-- **Conjugation law for monodromy along a path.** A class `g` at `x₁` fixes the endpoint
`hp.monodromy ⟦γ⟧ e₀` of the lift of `γ` exactly when its transport back along `γ` fixes the
starting point `e₀`. This is the path-level statement behind
`IsCoveringMap.range_mapOfEq_monodromy_path`: transporting the recovered subgroup along `γ`
amounts to conjugating the classes that the monodromy action fixes. -/
theorem monodromy_eq_self_iff_fundamentalGroupMulEquivOfPath_symm_apply
    (hp : IsCoveringMap p) (γ : Path x₀ x₁) (e₀ : p ⁻¹' {x₀})
    (g : FundamentalGroup X x₁) :
    hp.monodromy g.toPath (hp.monodromy ⟦γ⟧ e₀) = hp.monodromy ⟦γ⟧ e₀ ↔
      hp.monodromy
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g).toPath e₀ = e₀ := by
  rw [hp.monodromy_fundamentalGroupMulEquivOfPath_symm_apply, Equiv.symm_apply_eq,
    coveringFiberEquiv_apply]
  -- `⟦γ⟧` and `.mk γ` are the same class of `γ`, written with two spellings of the quotient map.
  exact Iff.rfl

/-- The subgroup recovered at the endpoint of a lifted path is the basepoint transport of the
subgroup recovered at its starting point. -/
theorem range_mapOfEq_monodromy_path (hp : IsCoveringMap p) (γ : Path x₀ x₁)
    (e₀ : p ⁻¹' {x₀}) :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩
      (hp.monodromy ⟦γ⟧ e₀).property).range =
      FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₀.property).range := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let e₁ : p ⁻¹' {x₁} := hp.monodromy γq e₀
  ext g
  -- The range criterion is stated with the subtype's endpoint proof, while `e₁` is the
  -- locally named monodromy endpoint; this change aligns those definitionally equal terms.
  change g ∈ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₁.property).range ↔
    g ∈ FundamentalGroup.basepointChangeSubgroup γ
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₀.property).range
  rw [← IsCoveringMap.monodromy_eq_self_iff_mem_range hp e₁ g,
    FundamentalGroup.mem_basepointChangeSubgroup_iff,
    ← IsCoveringMap.monodromy_eq_self_iff_mem_range hp e₀]
  exact hp.monodromy_eq_self_iff_fundamentalGroupMulEquivOfPath_symm_apply γ e₀ g

end IsCoveringMap

namespace IsQuotientCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {x₀ x₁ : X} {G : Type*} [Group G] [MulAction G E]

/-- **Basepoint change for the deck-group reading of loops.** Reading a loop class `g` at `x₀`
through the lift `e₀`, or its basepoint change along `γ` through the transported lift
`hp.isCoveringMap.monodromy ⟦γ⟧ e₀`, gives the same group element. -/
theorem fundamentalGroupToMulOpposite_fundamentalGroupMulEquivOfPath
    (hp : IsQuotientCoveringMap p G) (γ : Path x₀ x₁) (e₀ : p ⁻¹' {x₀})
    (g : FundamentalGroup X x₀) :
    hp.fundamentalGroupToMulOpposite (hp.isCoveringMap.monodromy (.mk γ) e₀)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      hp.fundamentalGroupToMulOpposite e₀ g := by
  rw [fundamentalGroupToMulOpposite_apply_eq_iff]
  have h := hp.isCoveringMap.monodromy_fundamentalGroupMulEquivOfPath_symm_apply γ
    (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) e₀
  rw [MulEquiv.symm_apply_apply, Equiv.eq_symm_apply, TauCeti.coveringFiberEquiv_apply] at h
  -- The loop `g` moves `e₀` by the fibre action of its group element, which commutes with
  -- monodromy along `γ`.
  have he : hp.isCoveringMap.monodromy g.asHom e₀ =
      hp.toPermFiber x₀ (hp.fundamentalGroupToMulOpposite e₀ g).unop e₀ :=
    Subtype.ext (hp.unop_fundamentalGroupToMulOpposite_smul).symm
  rw [← h, he, hp.monodromy_toPermFiber, toPermFiber_apply_apply_coe]

/-- **Basepoint change for the fundamental group of the base.** For a simply connected cover, the
identification `π₁(X, x) ≃* Gᵐᵒᵖ` through a lift is compatible with changing the basepoint along
a path `γ` and transporting the lift along `γ`. -/
theorem fundamentalGroupEquiv_fundamentalGroupMulEquivOfPath [SimplyConnectedSpace E]
    (hp : IsQuotientCoveringMap p G) (γ : Path x₀ x₁) (e₀ : p ⁻¹' {x₀})
    (g : FundamentalGroup X x₀) :
    hp.fundamentalGroupEquiv (hp.isCoveringMap.monodromy (.mk γ) e₀)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      hp.fundamentalGroupEquiv e₀ g :=
  hp.fundamentalGroupToMulOpposite_fundamentalGroupMulEquivOfPath γ e₀ g

end IsQuotientCoveringMap

namespace IsAddQuotientCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {x₀ x₁ : X} {G : Type*} [AddGroup G] [AddAction G E]

/-- **Basepoint change for the deck-group reading of loops**, additive version of
`IsQuotientCoveringMap.fundamentalGroupToMulOpposite_fundamentalGroupMulEquivOfPath`. -/
theorem fundamentalGroupToMulOpposite_fundamentalGroupMulEquivOfPath
    (hp : IsAddQuotientCoveringMap p G) (γ : Path x₀ x₁) (e₀ : p ⁻¹' {x₀})
    (g : FundamentalGroup X x₀) :
    hp.fundamentalGroupToMulOpposite (hp.isCoveringMap.monodromy (.mk γ) e₀)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      hp.fundamentalGroupToMulOpposite e₀ g :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_fundamentalGroupMulEquivOfPath γ e₀ g

/-- **Basepoint change for the fundamental group of the base**, additive version of
`IsQuotientCoveringMap.fundamentalGroupEquiv_fundamentalGroupMulEquivOfPath`. -/
theorem fundamentalGroupEquiv_fundamentalGroupMulEquivOfPath [SimplyConnectedSpace E]
    (hp : IsAddQuotientCoveringMap p G) (γ : Path x₀ x₁) (e₀ : p ⁻¹' {x₀})
    (g : FundamentalGroup X x₀) :
    hp.fundamentalGroupEquiv (hp.isCoveringMap.monodromy (.mk γ) e₀)
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ g) =
      hp.fundamentalGroupEquiv e₀ g :=
  hp.toMultiplicative.fundamentalGroupEquiv_fundamentalGroupMulEquivOfPath γ e₀ g

end IsAddQuotientCoveringMap
