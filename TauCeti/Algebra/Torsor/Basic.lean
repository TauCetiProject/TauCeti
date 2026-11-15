/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Torsor.Defs

/-!
# Faithfulness and fixed-point freeness of torsor actions

In a torsor `P` under a group `G`, the action of `G` is free (`smul_eq_self_iff`) and nonempty,
hence faithful (`TauCeti.Torsor.instFaithfulSMul`). In particular, when `G` is nontrivial, no
point of `P` is fixed by every element of `G` (`TauCeti.Torsor.not_exists_forall_smul_eq_self`);
additively, an affine space over a nontrivial group has no translation-invariant origin.

## Main results

* `TauCeti.Torsor.instFaithfulSMul`, `TauCeti.AddTorsor.instFaithfulVAdd`: a torsor action is
  faithful.
* `TauCeti.Torsor.smul_eq_self_iff`, `TauCeti.AddTorsor.vadd_eq_self_iff`: a group element fixes a
  point of a torsor if and only if it is the identity.
* `TauCeti.Torsor.not_exists_forall_smul_eq_self`,
  `TauCeti.AddTorsor.not_exists_forall_vadd_eq_self`: if the acting group is nontrivial, no point
  of the torsor is fixed by the whole group.
-/

public section

namespace TauCeti.Torsor

variable {G P : Type*} [Group G] [Torsor G P]

/-- A torsor action is faithful: an element acting identically on `P` is `1`. -/
@[to_additive (attr := instance) TauCeti.AddTorsor.instFaithfulVAdd
  /-- An additive torsor action is faithful: an element acting identically on `P` is `0`. -/]
instance instFaithfulSMul : FaithfulSMul G P where
  eq_of_smul_eq_smul h := smul_right_cancel (Classical.arbitrary P) (h _)

/-- A group element fixes a point of a torsor if and only if it is `1`. -/
@[to_additive (attr := simp) TauCeti.AddTorsor.vadd_eq_self_iff
  /-- An additive group element fixes a point of an additive torsor if and only if it is `0`. -/]
theorem smul_eq_self_iff {g : G} {p : P} : g • p = p ↔ g = 1 := by
  rw [← smul_right_cancel_iff p (g₂ := 1), one_smul]

/-- Symmetric form of `smul_eq_self_iff`: `p = g • p` if and only if `g = 1`. -/
@[to_additive (attr := simp) TauCeti.AddTorsor.self_eq_vadd_iff
  /-- Symmetric form of `vadd_eq_self_iff`: `p = g +ᵥ p` if and only if `g = 0`. -/]
theorem self_eq_smul_iff {g : G} {p : P} : p = g • p ↔ g = 1 :=
  eq_comm.trans smul_eq_self_iff

variable (G P) in
/-- If the acting group `G` is nontrivial, no point of a `G`-torsor is fixed by every element of
`G`. -/
@[to_additive TauCeti.AddTorsor.not_exists_forall_vadd_eq_self
  /-- If the acting additive group `G` is nontrivial, no point of a `G`-torsor is fixed by every
  translation. -/]
theorem not_exists_forall_smul_eq_self [Nontrivial G] : ¬∃ p : P, ∀ g : G, g • p = p := by
  rintro ⟨p, hp⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (smul_eq_self_iff.mp (hp g))

end TauCeti.Torsor
