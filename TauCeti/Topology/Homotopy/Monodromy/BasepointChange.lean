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
`TauCeti.Topology.Homotopy.Monodromy.Basic`. This is the path-level compatibility needed by
the pointed and unpointed parts of Stage 2, items 7 and 8, of
`TauCetiRoadmap/UniversalCovers/README.md`; the convention is the usual one from Hatcher,
*Algebraic Topology*, Section 1.3.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {x₀ x₁ : X}

/-- **Monodromy after basepoint change.** Monodromy along the transport back along `γ` of a loop
class `g` at `x₁` is monodromy along `g`, conjugated by monodromy along `γ`: lift `γ`, then go
around `g`, then return along `γ`. -/
theorem _root_.IsCoveringMap.monodromy_fundamentalGroupMulEquivOfPath_symm_apply
    (hp : IsCoveringMap p) (γ : Path x₀ x₁) (g : FundamentalGroup X x₁) (e₀ : p ⁻¹' {x₀}) :
    hp.monodromy ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g) e₀ =
      (coveringFiberEquiv hp (.mk γ)).symm (hp.monodromy g (hp.monodromy (.mk γ) e₀)) := by
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_symm_apply, hp.monodromy_trans_apply,
    hp.monodromy_trans_apply, coveringFiberEquiv_symm_apply]

/-- The monodromy permutation of the transport back along `γ` of a loop class `g` is the monodromy
permutation of `g`, transported from the fibre over `x₁` to the fibre over `x₀` by monodromy along
`γ`. -/
theorem _root_.IsCoveringMap.monodromyPerm_fundamentalGroupMulEquivOfPath_symm
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
theorem _root_.IsCoveringMap.monodromy_eq_self_iff_fundamentalGroupMulEquivOfPath_symm_apply
    (hp : IsCoveringMap p) (γ : Path x₀ x₁) (e₀ : p ⁻¹' {x₀})
    (g : FundamentalGroup X x₁) :
    hp.monodromy g (hp.monodromy ⟦γ⟧ e₀) = hp.monodromy ⟦γ⟧ e₀ ↔
      hp.monodromy
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g) e₀ = e₀ := by
  rw [hp.monodromy_fundamentalGroupMulEquivOfPath_symm_apply, Equiv.symm_apply_eq,
    coveringFiberEquiv_apply]
  -- `⟦γ⟧` and `.mk γ` are the same class of `γ`, written with two spellings of the quotient map.
  exact Iff.rfl

/-- The subgroup recovered at the endpoint of a lifted path is the basepoint transport of the
subgroup recovered at its starting point. -/
theorem _root_.IsCoveringMap.range_mapOfEq_monodromy_path (hp : IsCoveringMap p) (γ : Path x₀ x₁)
    (e₀ : p ⁻¹' {x₀}) :
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩
      (hp.monodromy ⟦γ⟧ e₀).2).range =
      FundamentalGroup.basepointChangeSubgroup γ
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₀.2).range := by
  let γq : Path.Homotopic.Quotient x₀ x₁ := Path.Homotopic.Quotient.mk γ
  let e₁ : p ⁻¹' {x₁} := hp.monodromy γq e₀
  ext g
  -- The range criterion is stated with the subtype's endpoint proof, while `e₁` is the
  -- locally named monodromy endpoint; this change aligns those definitionally equal terms.
  change g ∈ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₁.2).range ↔
    g ∈ FundamentalGroup.basepointChangeSubgroup γ
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ e₀.2).range
  rw [← IsCoveringMap.monodromy_eq_self_iff_mem_range hp e₁ g,
    FundamentalGroup.mem_basepointChangeSubgroup_iff,
    ← IsCoveringMap.monodromy_eq_self_iff_mem_range hp e₀]
  exact hp.monodromy_eq_self_iff_fundamentalGroupMulEquivOfPath_symm_apply γ e₀ g

end TauCeti
