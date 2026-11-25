/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Group.Cyclic
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Monoid.Submonoid
import TauCeti.Algebra.GroupWithZero.Range

/-!
# Transporting the value group along an equivalence of valuations

Mathlib's `Valuation.IsEquiv.orderMonoidIso` transports value groups along an equivalence
of valuations. This file records its functoriality, using the corresponding results for
`Valuation.IsEquiv.orderMonoidIso₀` on value groups with zero adjoined, and its rigidity for
cyclic value groups: two equivalent valuations into a linearly ordered commutative group with
zero whose value groups are the same cyclic subgroup of the units of the target are equal. That
the value groups are isomorphic as ordered groups is not enough: equivalence always provides such
an isomorphism.

## Main results

* `Valuation.IsEquiv.orderMonoidIso_symm_eq`,
  `Valuation.IsEquiv.orderMonoidIso_self` and
  `Valuation.IsEquiv.orderMonoidIso_trans_eq` : the transport respects inverses, identities
  and composition.
* `Valuation.eq_of_isEquiv_of_valueGroup_eq`: two equivalent valuations into a linearly ordered
  commutative group with zero `Γ₀` whose value groups are equal and cyclic, as subgroups of `Γ₀ˣ`,
  are equal.

-/

public section

namespace Valuation

open MonoidWithZeroHom LinearOrderedCommGroup

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-- Transport along the inverse equivalence is the inverse transport. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso₀_symm`. -/
theorem IsEquiv.orderMonoidIso_symm_eq {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) (h' : w.IsEquiv v) :
    h.orderMonoidIso.symm = h'.orderMonoidIso :=
  (rfl)

/-- Transport along a valuation's equivalence with itself is the identity. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso₀_eq_refl`. -/
@[simp]
theorem IsEquiv.orderMonoidIso_self {v : Valuation A Γ₀}
    (h : v.IsEquiv v) : h.orderMonoidIso = .refl _ := by
  ext1 γ
  apply WithZero.coe_injective
  simpa only [Valuation.IsEquiv.orderMonoidIso₀_coe, OrderMonoidIso.coe_refl, id_eq] using
    congrArg (fun e : v.ValueGroup₀ ≃*o v.ValueGroup₀ ↦ e γ) h.orderMonoidIso₀_eq_refl

/-- Transport along a composite equivalence is the composite transport. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso₀_trans`. -/
@[simp]
theorem IsEquiv.orderMonoidIso_trans_eq {Γ₀'' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀''] {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    {u : Valuation A Γ₀''} (h : v.IsEquiv w) (h' : w.IsEquiv u) :
    h.orderMonoidIso.trans h'.orderMonoidIso = (h.trans h').orderMonoidIso := by
  ext1 γ
  apply WithZero.coe_injective
  simpa only [OrderMonoidIso.trans_apply, Valuation.IsEquiv.orderMonoidIso₀_coe] using
    congrArg (fun e : v.ValueGroup₀ ≃*o u.ValueGroup₀ ↦ e γ) (h.orderMonoidIso₀_trans h')

/-- **Equivalent valuations with equal cyclic value groups are equal**, for valuations into a
linearly ordered commutative group with zero `Γ₀`. The value groups must be equal as subgroups of
`Γ₀ˣ`. Equivalence always induces an order-preserving isomorphism between
them, so isomorphic value groups would not suffice: the `p`-adic valuation and its square are
equivalent and not equal. When the two subgroups are equal and cyclic, that isomorphism is an
order-preserving automorphism of a cyclic group. It fixes the generator below one, hence every
element, so the two valuations agree.

Cyclicity cannot be dropped: a valuation and its square are equivalent and, for a surjective
valuation onto `ℝ≥0`, share the value group, without being equal. -/
theorem eq_of_isEquiv_of_valueGroup_eq {v w : Valuation A Γ₀} [IsCyclic v.valueGroup]
    (h : v.IsEquiv w) (hvw : v.valueGroup = w.valueGroup) : v = w := by
  -- An order-preserving isomorphism between two equal cyclic subgroups of `Γ₀ˣ` fixes the
  -- generator below one, which generates, so it fixes every element.
  have rigid : ∀ (H K : Subgroup Γ₀ˣ) [IsCyclic H] (e : H ≃*o K), H = K →
      ∀ γ : H, ((e γ : K) : Γ₀ˣ) = γ := by
    rintro H K _ e rfl γ
    rcases subsingleton_or_nontrivial H with _ | _
    · rw [Subsingleton.elim γ 1, map_one]
    have he : e.toMulEquiv = MulEquiv.refl H :=
      (MulEquiv.eq_iff_eq_on_generator
        (fun x ↦ (Subgroup.genLTOne_zpowers_eq_top (⊤ : Subgroup H)).symm ▸ Subgroup.mem_top x)
        _ _).mpr e.map_genLTOne
    exact congrArg Subtype.val (DFunLike.congr_fun he γ)
  -- Write `v x` through `v.restrict x`, and `w x` through
  -- `w.restrict x = h.orderMonoidIso₀ (v.restrict x)`.
  refine Valuation.ext fun x ↦ ?_
  rw [← v.embedding_restrict, ← w.embedding_restrict, ← h.orderMonoidIso₀_spec]
  generalize v.restrict x = a
  induction a using WithZero.recZeroCoe with
  | zero => simp
  | coe γ =>
    rw [IsEquiv.orderMonoidIso₀_coe, ValueGroup₀.embedding_coe, ValueGroup₀.embedding_coe,
      rigid _ _ h.orderMonoidIso hvw γ]

end Valuation
