/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Converting left group actions into right actions by inversion

Any left action `g • x` of a group `G` on a type `X` determines a right action `x · g = g⁻¹ • x`,
encoded in Mathlib's convention as a left action of the opposite group `Gᵐᵒᵖ` with
`MulOpposite.op g • x = g⁻¹ • x`. Algebraically this is scalar restriction along the group
isomorphism `(MulEquiv.inv' G).symm : Gᵐᵒᵖ ≃* G` sending `op g` to `g⁻¹`.

On `G` itself, Mathlib already endows `G` with the right-multiplication action
`Monoid.toOppositeMulAction : MulAction Gᵐᵒᵖ G` (`op g • p = p * g`), whereas converting the
left-translation action `g • p = g * p` by inversion produces `op g • p = g⁻¹ * p`. To avoid
conflicting `MulAction Gᵐᵒᵖ` instances when both actions are in scope, the converted right action is
placed on a type copy `TauCeti.LeftToRightAction G X`, identified with `X` by
`TauCeti.LeftToRightAction.equiv`. Topological structure and action continuity on this copy are
developed in `TauCeti.Topology.Algebra.MulAction.LeftToRight`.

Converting a left action to this right action preserves stabilizers, faithfulness, freeness, orbits,
and pretransitivity.

## Main definitions

* `TauCeti.LeftToRightAction G X`: a type copy of `X` carrying the right action
  `op g • y = g⁻¹ • y` associated to a left `G`-action on `X`.
* `TauCeti.LeftToRightAction.equiv G X`: the canonical equivalence `X ≃ LeftToRightAction G X`.

## Main results

* `TauCeti.LeftToRightAction.op_smul_equiv`: `op g • equiv G X x = equiv G X (g⁻¹ • x)`.
* `TauCeti.LeftToRightAction.forall_op_smul_eq_imp_eq_iff`: the converted right action is free if
  and only if the original left action is free.
* `TauCeti.LeftToRightAction.isPretransitive_iff`: the converted right action is pretransitive if
  and only if the original left action is pretransitive.
* `TauCeti.LeftToRightAction.op_smul_equiv_self`: for `G` acting on itself by left multiplication,
  the converted right action is `op g • equiv G G p = equiv G G (g⁻¹ * p)`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.2 and §10.6 (conversion between left and right principal actions via inversion).
-/

public section

open MulOpposite Set

namespace TauCeti

/-- A copy of `X` on which a group `G` acting on the left on `X` acts on the right via inversion:
`MulOpposite.op g • x = g⁻¹ • x`. Using a type copy keeps this right action distinct from
`Monoid.toOppositeMulAction` when `X = G`. -/
-- Lean's module system needs this body to transport topological and manifold instances to the copy.
@[expose] def LeftToRightAction (_ : Type*) (X : Type*) : Type _ :=
  X

namespace LeftToRightAction

section Equiv

variable {G X : Type*}

variable (G X) in
/-- The identity equivalence from `X` to `LeftToRightAction G X`. -/
-- Lean's module system needs this body to lift `equiv` to `LeftToRightAction.homeomorph` and
-- `LeftToRightAction.diffeomorph`, and to identify basepoints of tangent spaces across `equiv`.
@[expose] def equiv : X ≃ LeftToRightAction G X where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

instance instNonempty [Nonempty X] : Nonempty (LeftToRightAction G X) :=
  inferInstanceAs (Nonempty X)

instance instSubsingleton [Subsingleton X] : Subsingleton (LeftToRightAction G X) :=
  inferInstanceAs (Subsingleton X)

instance instInhabited [Inhabited X] : Inhabited (LeftToRightAction G X) :=
  inferInstanceAs (Inhabited X)

end Equiv

section Algebra

variable {G X : Type*} [Group G] [MulAction G X]

/-- The right action of `G` (as a left action of `Gᵐᵒᵖ`) obtained from a left `G`-action on `X` by
restricting scalars along `(MulEquiv.inv' G).symm : Gᵐᵒᵖ ≃* G`, so `op g` acts as `g⁻¹`. -/
instance instMulAction : MulAction Gᵐᵒᵖ (LeftToRightAction G X) :=
  MulAction.compHom X (MulEquiv.inv' G).symm.toMonoidHom

/-- The converted right action of `g` on `equiv G X x` applies `g⁻¹` on the left. -/
@[simp]
theorem op_smul_equiv (g : G) (x : X) :
    op g • equiv G X x = equiv G X (g⁻¹ • x) :=
  (rfl)

/-- Reading the converted right action of `g` back in `X` applies `g⁻¹` on the left. -/
@[simp]
theorem equiv_symm_op_smul (g : G) (y : LeftToRightAction G X) :
    (equiv G X).symm (op g • y) = g⁻¹ • (equiv G X).symm y :=
  (rfl)

/-- An element `g : Gᵐᵒᵖ` acts on `equiv G X x` by `g.unop⁻¹` on the left. -/
theorem smul_equiv (g : Gᵐᵒᵖ) (x : X) :
    g • equiv G X x = equiv G X (g.unop⁻¹ • x) :=
  (rfl)

/-- Reading the action of `g : Gᵐᵒᵖ` back in `X` applies `g.unop⁻¹` on the left. -/
theorem equiv_symm_smul (g : Gᵐᵒᵖ) (y : LeftToRightAction G X) :
    (equiv G X).symm (g • y) = g.unop⁻¹ • (equiv G X).symm y :=
  (rfl)

/-- An element `g` fixes `equiv G X x` under the converted right action if and only if `g` fixes `x`
under the original left action. -/
theorem op_smul_eq_self_iff {g : G} {x : X} :
    op g • equiv G X x = equiv G X x ↔ g • x = x := by
  rw [op_smul_equiv, Equiv.apply_eq_iff_eq, inv_smul_eq_iff, eq_comm]

/-- Membership in the stabilizer of `equiv G X x` for the converted right action agrees with
membership in the stabilizer of `x` for the left action. -/
theorem mem_stabilizer_op_iff {g : G} {x : X} :
    op g ∈ MulAction.stabilizer Gᵐᵒᵖ (equiv G X x) ↔ g ∈ MulAction.stabilizer G x := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, op_smul_eq_self_iff]

/-- Pointwise freeness at `x` is preserved under converting a left action to a right action. -/
theorem forall_op_smul_eq_imp_eq_at_iff {x : X} :
    (∀ g h : G, op g • equiv G X x = op h • equiv G X x → g = h) ↔
      ∀ g h : G, g • x = h • x → g = h := by
  constructor <;> intro hfree g h heq
  · exact inv_injective (hfree g⁻¹ h⁻¹
      (by simpa only [op_smul_equiv, inv_inv, Equiv.apply_eq_iff_eq] using heq))
  · exact inv_injective (hfree g⁻¹ h⁻¹
      (by simpa only [op_smul_equiv, Equiv.apply_eq_iff_eq] using heq))

/-- Freeness of the action on the whole space is preserved under converting a left action to a right
action. -/
theorem forall_op_smul_eq_imp_eq_iff :
    (∀ (y : LeftToRightAction G X) (g h : G), op g • y = op h • y → g = h) ↔
      ∀ (x : X) (g h : G), g • x = h • x → g = h := by
  refine ⟨fun h x ↦ forall_op_smul_eq_imp_eq_at_iff.1 (h (equiv G X x)), fun h y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (equiv G X).surjective y
  exact forall_op_smul_eq_imp_eq_at_iff.2 (h x)

/-- Faithfulness is preserved under converting a left action to a right action. -/
theorem faithfulSMul_iff :
    FaithfulSMul Gᵐᵒᵖ (LeftToRightAction G X) ↔ FaithfulSMul G X := by
  constructor <;> intro h
  · refine ⟨fun {g₁ g₂} hgg ↦ ?_⟩
    have hop : op g₁⁻¹ = op g₂⁻¹ := h.eq_of_smul_eq_smul fun y ↦ by
      obtain ⟨x, rfl⟩ := (equiv G X).surjective y
      simpa only [op_smul_equiv, inv_inv, Equiv.apply_eq_iff_eq] using hgg x
    exact inv_injective (op_injective hop)
  · refine ⟨fun {g₁ g₂} hgg ↦ ?_⟩
    have hunop : g₁.unop⁻¹ = g₂.unop⁻¹ := h.eq_of_smul_eq_smul fun x ↦ by
      simpa only [smul_equiv, Equiv.apply_eq_iff_eq] using hgg (equiv G X x)
    exact unop_injective (inv_injective hunop)

instance instFaithfulSMul [FaithfulSMul G X] : FaithfulSMul Gᵐᵒᵖ (LeftToRightAction G X) :=
  faithfulSMul_iff.2 ‹_›

/-- The orbit of `equiv G X x` under the converted right action is the image of the left orbit of
`x`. -/
theorem orbit_equiv (x : X) :
    MulAction.orbit Gᵐᵒᵖ (equiv G X x) = equiv G X '' MulAction.orbit G x := by
  ext y
  obtain ⟨z, rfl⟩ := (equiv G X).surjective y
  simp only [MulAction.mem_orbit_iff, mem_image, Equiv.apply_eq_iff_eq, exists_eq_right,
    MulOpposite.exists, op_smul_equiv]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g⁻¹, hg⟩, fun ⟨g, hg⟩ ↦ ⟨g⁻¹, by simpa only [inv_inv] using hg⟩⟩

/-- Pretransitivity is preserved under converting a left action to a right action. -/
theorem isPretransitive_iff :
    MulAction.IsPretransitive Gᵐᵒᵖ (LeftToRightAction G X) ↔ MulAction.IsPretransitive G X :=
  ⟨fun h ↦ MulAction.IsPretransitive.of_compHom (MulEquiv.inv' G).symm.toMonoidHom (h := h),
    fun h ↦ have := h; MulAction.isPretransitive_compHom (G := X) (MulEquiv.inv' G).symm.surjective⟩

instance instIsPretransitive [MulAction.IsPretransitive G X] :
    MulAction.IsPretransitive Gᵐᵒᵖ (LeftToRightAction G X) :=
  isPretransitive_iff.2 ‹_›

/-- For a group `G` acting on itself by left multiplication, the converted right action is
`p · g = g⁻¹ * p`. -/
theorem op_smul_equiv_self {H : Type*} [Group H] (g p : H) :
    op g • equiv H H p = equiv H H (g⁻¹ * p) :=
  (rfl)

end Algebra

end LeftToRightAction

end TauCeti
