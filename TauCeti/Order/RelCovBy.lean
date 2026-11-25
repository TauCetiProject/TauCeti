/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Cover

/-!
# The covering relation of an arbitrary relation

Mathlib's covering relation `CovBy` (`u ⋖ v`) needs an order instance. A relation `r` on a type
with no order instance, such as the relation read off a code of an order, has the same notion:
reading `r` as a non-strict order, `RelCovBy r u v` says that `u < v` and that no `w` satisfies
`u < w < v`, where `a < b` means `r a b` and not `r b a`. For the order of a preorder it is
`CovBy` (`TauCeti.relCovBy_le_iff_covBy`).

## Main definitions

* `TauCeti.RelCovBy r u v`: `v` covers `u` for the relation `r` read as a non-strict order.

## Main results

* `TauCeti.relCovBy_le_iff_covBy`: for the order of a preorder, `RelCovBy` is `CovBy`.
* `TauCeti.relCovBy_comap_equiv`: `RelCovBy` is unchanged by relabelling along an equivalence.
-/

public section

namespace TauCeti

variable {V : Type*}

/-- In a relation `r` read as a non-strict order, `u` **is covered by** `v` (Mathlib's `CovBy`,
`u ⋖ v`, for the relation `r`): `u < v`, and no `w` satisfies `u < w < v`, where `a < b` means
`r a b` and not `r b a`. -/
def RelCovBy (r : V → V → Prop) (u v : V) : Prop :=
  (r u v ∧ ¬ r v u) ∧ ∀ w, ¬ ((r u w ∧ ¬ r w u) ∧ (r w v ∧ ¬ r v w))

/-- Unfolding lemma for `RelCovBy`. -/
theorem relCovBy_iff {r : V → V → Prop} {u v : V} :
    RelCovBy r u v ↔ (r u v ∧ ¬ r v u) ∧ ∀ w, ¬ ((r u w ∧ ¬ r w u) ∧ (r w v ∧ ¬ r v w)) :=
  Iff.rfl

/-- `RelCovBy` is unchanged by relabelling along an equivalence: `u` is covered by `v` for the
relation `r` pulled back along `e` exactly when `e u` is covered by `e v` for `r`. -/
theorem relCovBy_comap_equiv {W : Type*} (e : V ≃ W) {r : W → W → Prop} {u v : V} :
    RelCovBy (fun a b => r (e a) (e b)) u v ↔ RelCovBy r (e u) (e v) := by
  simp only [relCovBy_iff]
  exact and_congr Iff.rfl (e.forall_congr fun _ => Iff.rfl)

/-- For the order of a preorder, `RelCovBy` is Mathlib's `CovBy`. -/
@[simp]
theorem relCovBy_le_iff_covBy {α : Type*} [Preorder α] {u v : α} :
    RelCovBy (· ≤ ·) u v ↔ u ⋖ v := by
  simp only [relCovBy_iff, ← lt_iff_le_not_ge, CovBy, not_and]

end TauCeti
