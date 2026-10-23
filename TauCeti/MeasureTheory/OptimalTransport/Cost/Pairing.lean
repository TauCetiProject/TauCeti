/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity

/-!
# The transport cost induced by a pairing

Let `E` and `F` be real vector spaces paired by `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, written `⟪x, y⟫ = B x y`.
This file defines the transport cost `c (x, y) = -⟪x, y⟫` induced by the pairing and identifies
its `c`-cyclically monotone sets with the cyclically monotone sets of convex analysis: those
sets `Γ ⊆ E × F` for which no rearrangement of the targets of finitely many points increases the
total pairing, `∑ i, ⟪x i, y (σ i)⟫ ≤ ∑ i, ⟪x i, y i⟫`. The `c`-transform vocabulary of this
cost is the Legendre–Fenchel vocabulary of the pairing with the signs reversed; that dictionary
is recorded in `TauCeti.MeasureTheory.OptimalTransport.CTransform.Pairing`.

## Main definitions

* `TauCeti.pairingCost B` — the transport cost `(x, y) ↦ -B x y` induced by a pairing.

## Main statements

* `TauCeti.pairingCost_flip` — the pairing cost of the transposed pairing is the transposed
  pairing cost;
* `TauCeti.isCyclicallyMonotone_pairingCost_iff` — cyclical monotonicity for the pairing cost
  is the sum inequality `∑ i, B (x i) (y (σ i)) ≤ ∑ i, B (x i) (y i)`.

## References

* R. T. Rockafellar, *Characterization of the subdifferentials of convex functions*, Pacific J.
  Math. 17 (1966), 497--510, where cyclically monotone sets are introduced.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1 and §2.4.
-/

public section

noncomputable section

namespace TauCeti

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- The transport cost `(x, y) ↦ -B x y` induced by a pairing `B`. Its `c`-transform
vocabulary is the Legendre–Fenchel vocabulary of the pairing with the signs reversed. -/
def pairingCost (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (p : E × F) : ℝ := -B p.1 p.2

variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

@[simp]
theorem pairingCost_apply (p : E × F) : pairingCost B p = -B p.1 p.2 := (rfl)

/-- The pairing cost of the transposed pairing is the transposed pairing cost. -/
theorem pairingCost_flip : pairingCost B.flip = fun p : F × E => pairingCost B (p.2, p.1) := by
  funext p
  simp only [pairingCost_apply, LinearMap.flip_apply]

/-- Cyclical monotonicity for the pairing cost is the classical condition: no rearrangement of
the targets of finitely many points of the set increases the total pairing. -/
theorem isCyclicallyMonotone_pairingCost_iff {Γ : Set (E × F)} :
    IsCyclicallyMonotone (pairingCost B) Γ ↔
      ∀ (n : ℕ) (x : Fin n → E) (y : Fin n → F), (∀ i, (x i, y i) ∈ Γ) →
        ∀ σ : Equiv.Perm (Fin n), ∑ i, B (x i) (y (σ i)) ≤ ∑ i, B (x i) (y i) := by
  simp only [isCyclicallyMonotone_iff, pairingCost_apply, Finset.sum_neg_distrib,
    neg_le_neg_iff]

end TauCeti

end

end
