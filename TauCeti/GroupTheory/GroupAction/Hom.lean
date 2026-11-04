/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Existence of equivariant maps

For actions of a group `G` on `X` and on `Y`, an equivariant map `X → Y` sends each point to a
point whose stabilizer contains the stabilizer of the first. Conversely, if every stabilizer of `X`
fixes a point of `Y`, an equivariant map is obtained by choosing a representative of each orbit of
`X` and sending it to such a fixed point.

## Main results

* `TauCeti.MulAction.nonempty_mulActionHom_iff_forall_exists_stabilizer_le`: there is a
  `G`-equivariant map `X → Y` exactly when every stabilizer of `X` lies in some stabilizer of `Y`.

## References

* J.-P. Serre, *Trees*, Chapter I, §6.1.
-/

public section

namespace TauCeti.MulAction

open _root_.MulAction

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

/-- There is a `G`-equivariant map `X → Y` exactly when the stabilizer of every point of `X` is
contained in the stabilizer of some point of `Y`. -/
theorem nonempty_mulActionHom_iff_forall_exists_stabilizer_le :
    Nonempty (X →[G] Y) ↔ ∀ x : X, ∃ y : Y, stabilizer G x ≤ stabilizer G y := by
  refine ⟨fun ⟨f⟩ x => ⟨f x, fun g hg => ?_⟩, fun hS => ?_⟩
  · rw [mem_stabilizer_iff] at hg ⊢
    rw [← f.map_smul, hg]
  · choose y hy using hS
    -- `r x` is a chosen representative of the orbit of `x`, and `c x • r x = x`.
    let r : X → X := fun x => (Quotient.mk'' x : Quotient (orbitRel G X)).out
    have hr : ∀ x, ∃ c : G, c • r x = x := fun x => by
      obtain ⟨c, hc⟩ := orbitRel_apply.mp (Quotient.mk_out' (s₁ := orbitRel G X) x)
      exact ⟨c⁻¹, by rw [inv_smul_eq_iff]; exact hc.symm⟩
    choose c hc using hr
    have hrs : ∀ (g : G) x, r (g • x) = r x := fun g x =>
      congrArg Quotient.out (Quotient.sound (orbitRel_apply.mpr (mem_orbit x g)))
    refine ⟨⟨fun x => c x • y (r x), fun g x => ?_⟩⟩
    have hgx : c (g • x) • r x = g • x := by simpa only [hrs] using hc (g • x)
    have hk : (c x)⁻¹ * g⁻¹ * c (g • x) ∈ stabilizer G (r x) := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hgx, inv_smul_smul, inv_smul_eq_iff, hc]
    have hky := mem_stabilizer_iff.mp (hy (r x) hk)
    rw [mul_smul, mul_smul, inv_smul_eq_iff, inv_smul_eq_iff] at hky
    simp only [id, hrs, hky, smul_smul]

end TauCeti.MulAction
