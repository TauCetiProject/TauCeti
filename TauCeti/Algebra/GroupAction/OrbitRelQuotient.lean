/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Generic orbit-relation quotient helpers

This file records small generic additions to Mathlib's `MulAction.orbitRel.Quotient` API.

## Main declarations

* `TauCeti.MulAction.orbitRelQuotientBotEquiv`: the quotient by the trivial subgroup is the
  original space.
* `TauCeti.MulAction.orbitRelQuotientMapOfLE_bot_eq_iff`: equality after the bottom-to-`H`
  quotient map is membership in an `H`-orbit.
-/

public section

namespace TauCeti

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

private lemma eq_of_bot_orbitRel {x y : X}
    (h : _root_.MulAction.orbitRel (⊥ : Subgroup G) X x y) : x = y := by
  rw [_root_.MulAction.orbitRel_apply] at h
  rcases h with ⟨g, hg⟩
  have hg_one : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  have hsmul : (g : G) • y = x := by
    simpa [Subgroup.smul_def] using hg
  rw [hg_one, one_smul] at hsmul
  exact hsmul.symm

/-- Quotienting a group action by the trivial subgroup gives back the original space. -/
noncomputable def orbitRelQuotientBotEquiv :
    _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X ≃ X :=
  { toFun := Quotient.lift (fun x : X => x) fun _ _ h => eq_of_bot_orbitRel h
    invFun := Quotient.mk''
    left_inv := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro x
      rfl
    right_inv := by
      intro x
      rfl }

/-- The bottom-subgroup quotient equivalence sends a class to its representative. -/
@[simp]
lemma orbitRelQuotientBotEquiv_mk (x : X) :
    orbitRelQuotientBotEquiv
        (G := G) (X := X) (Quotient.mk'' x :
          _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) = x :=
  (orbitRelQuotientBotEquiv (G := G) (X := X)).right_inv x

/-- The inverse bottom-subgroup quotient equivalence sends a point to its quotient class. -/
@[simp]
lemma orbitRelQuotientBotEquiv_symm_apply (x : X) :
    (orbitRelQuotientBotEquiv (G := G) (X := X)).symm x =
      (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :=
  ((orbitRelQuotientBotEquiv (G := G) (X := X)).apply_eq_iff_eq_symm_apply).mp
    (orbitRelQuotientBotEquiv_mk (G := G) (X := X) x)

/-- Equality of bottom-subgroup orbit classes is equality of representatives. -/
@[simp]
lemma orbitRelQuotientBot_mk_eq_iff (x y : X) :
    (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) =
        Quotient.mk'' y ↔
      x = y := by
  constructor
  · intro h
    exact congrArg (orbitRelQuotientBotEquiv (G := G) (X := X)) h
  · intro h
    rw [h]

/-- Orbit relations are monotone in the acting subgroup. -/
lemma orbitRel_le_of_subgroup_le {H K : Subgroup G} (hHK : H ≤ K) :
    _root_.MulAction.orbitRel H X ≤ _root_.MulAction.orbitRel K X := by
  intro x y h
  rw [_root_.MulAction.orbitRel_apply] at h ⊢
  rcases h with ⟨g, hg⟩
  exact ⟨⟨g.1, hHK g.2⟩, hg⟩

/-- The map from the bottom-subgroup quotient to the `H`-quotient is the `H`-orbit class map
under the bottom quotient equivalence. -/
@[simp]
lemma orbitRelQuotientMapOfLE_bot_eq (H : Subgroup G) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) =
      (fun x : X => (Quotient.mk'' x : _root_.MulAction.orbitRel.Quotient H X)) ∘
        orbitRelQuotientBotEquiv (G := G) (X := X) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro x
  rfl

/-- Equality in an `H`-orbit quotient can be checked after choosing representatives through
the bottom-subgroup quotient. -/
lemma orbitRelQuotientMapOfLE_bot_eq_iff (H : Subgroup G)
    (x y : _root_.MulAction.orbitRel.Quotient (⊥ : Subgroup G) X) :
    Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
        (bot_le : (⊥ : Subgroup G) ≤ H)) x =
        Setoid.map_of_le (orbitRel_le_of_subgroup_le (G := G) (X := X)
          (bot_le : (⊥ : Subgroup G) ≤ H)) y ↔
      orbitRelQuotientBotEquiv (G := G) (X := X) x ∈
        _root_.MulAction.orbit H (orbitRelQuotientBotEquiv (G := G) (X := X) y) := by
  simp [orbitRelQuotientMapOfLE_bot_eq, Quotient.eq'', _root_.MulAction.orbitRel_apply]

end MulAction

end TauCeti
