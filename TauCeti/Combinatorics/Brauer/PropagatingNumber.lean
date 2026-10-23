/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Compose

/-!
# The propagating number of a Brauer diagram

The arcs of a Brauer diagram on `k` strands are of three kinds: through strands, caps and cups.
The **propagating number** `TauCeti.BrauerDiagram.propagatingNumber` counts the through strands.
It is the basic numerical invariant of a diagram: it is at most `k`, it has the same parity as `k`
because the remaining bottom points are matched in pairs by the caps, and it equals `k` exactly
for the permutation diagrams.

The point of the invariant is that vertical stacking can only destroy through strands, never
create them: a through strand of `TauCeti.composeDiagram D₁ D₂` is a through strand of `D₂`
continued by a through strand of `D₁`, so the propagating number of a composite is at most the
propagating number of either factor. Consequently the diagrams of propagating number at most `t`
absorb stacking on both sides -- the diagram-level shadow of the ideals in the cell filtration of
the Brauer algebra -- and, at the top of the filtration, a product of diagrams is a permutation
diagram only if both factors already are
(`TauCeti.BrauerDiagram.composeDiagram_eq_permToBrauer_iff`). That last statement is the precise
sense in which `TauCeti.permToBrauer` is the inclusion of the *invertible* diagrams: a diagram
divides the identity diagram exactly when it is a permutation diagram
(`TauCeti.BrauerDiagram.exists_composeDiagram_right_eq_permToBrauer_one_iff`).

## Main definitions

* `TauCeti.BrauerDiagram.propagatingNumber`: the number of through strands of a Brauer diagram.

## Main results

* `TauCeti.BrauerDiagram.propagatingNumber_add_card_bottomCap`: the through strands and the capped
  bottom points exhaust the bottom boundary, so the propagating number is at most `k`
  (`TauCeti.BrauerDiagram.propagatingNumber_le`) and `k` minus it is even
  (`TauCeti.BrauerDiagram.even_sub_propagatingNumber`).
* `TauCeti.BrauerDiagram.propagatingNumber_eq_iff_exists_eq_permToBrauer`: the propagating number
  is `k` exactly for the permutation diagrams, and
  `TauCeti.BrauerDiagram.propagatingNumber_eq_zero_iff`: it is `0` exactly for the diagrams built
  out of caps and cups alone.
* `TauCeti.BrauerDiagram.propagatingNumber_composeDiagram_le_left` and
  `TauCeti.BrauerDiagram.propagatingNumber_composeDiagram_le_right`: **stacking cannot raise the
  propagating number.**
* `TauCeti.BrauerDiagram.composeDiagram_eq_permToBrauer_iff` and
  `TauCeti.BrauerDiagram.exists_composeDiagram_right_eq_permToBrauer_one_iff`: **the diagrams
  dividing a permutation diagram are exactly the permutation diagrams.**

## Implementation notes

The propagating number is defined as the number of bottom endpoints of the through strands, that
is as the cardinality of `TauCeti.BrauerDiagram.bottomThrough`, and
`TauCeti.BrauerDiagram.propagatingNumber_eq_card_topThrough` proves it equal to the number of top
endpoints.

Stacking is left as `TauCeti.composeDiagram` rather than being packaged as a multiplication: the
multiplication of the Brauer algebra weights the stacking by the number of loops closed up in the
middle, which the bounds below do not need.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* T. Halverson and T. N. Jacobson, [*Set-partition tableaux and representations of diagram
  algebras*][halverson-jacobson2020], Algebraic Combinatorics 3 (2020), 509-538, §2.4, for the
  propagating number of a diagram and the two-sided ideals of a diagram algebra it filters by.

[halverson-jacobson2020]: https://doi.org/10.5802/alco.102
-/

public section

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ}

/-- **The propagating number of a Brauer diagram**: the number of its through strands, counted at
their bottom endpoints. -/
def propagatingNumber (D : BrauerDiagram k) : ℕ := D.bottomThrough.card

variable (D : BrauerDiagram k)

/-- The propagating number counts the bottom endpoints of the through strands. -/
theorem propagatingNumber_def : D.propagatingNumber = D.bottomThrough.card := (rfl)

/-- The propagating number counts the top endpoints of the through strands just as well: following
an arc through matches the two sets of endpoints. -/
theorem propagatingNumber_eq_card_topThrough : D.propagatingNumber = D.topThrough.card :=
  D.card_bottomThrough_eq_card_topThrough

/-- **Every bottom point lies on a through strand or on a cap**, so the two counts add up to the
number of bottom points. -/
theorem propagatingNumber_add_card_bottomCap :
    D.propagatingNumber + D.bottomCap.card = k := by
  rw [propagatingNumber_def, bottomCap_eq_compl, Finset.card_add_card_compl, Fintype.card_fin]

/-- A diagram on `k` strands has at most `k` through strands. -/
theorem propagatingNumber_le : D.propagatingNumber ≤ k := by
  have := D.propagatingNumber_add_card_bottomCap
  omega

/-- **The propagating number has the parity of `k`**: the bottom points off the through strands
are matched in pairs by the caps. -/
theorem even_sub_propagatingNumber : Even (k - D.propagatingNumber) := by
  have hsum := D.propagatingNumber_add_card_bottomCap
  have heven := D.even_card_bottomCap
  have : k - D.propagatingNumber = D.bottomCap.card := by omega
  rwa [this]

/-- Relabelling the boundary does not change the propagating number. -/
@[simp]
theorem propagatingNumber_relabel (σ τ : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).propagatingNumber = D.propagatingNumber := by
  rw [propagatingNumber_def, propagatingNumber_def, card_bottomThrough_relabel]

/-- **A diagram has full propagating number exactly when all its arcs go through.** -/
theorem propagatingNumber_eq_iff_forall_isThrough :
    D.propagatingNumber = k ↔ ∀ x, D.IsThrough x := by
  rw [forall_isThrough_iff_bottomCap_eq_empty, ← Finset.card_eq_zero]
  have := D.propagatingNumber_add_card_bottomCap
  omega

/-- **A diagram has full propagating number exactly when it is a permutation diagram.** -/
theorem propagatingNumber_eq_iff_exists_eq_permToBrauer :
    D.propagatingNumber = k ↔ ∃ σ : Equiv.Perm (Fin k), D = permToBrauer σ := by
  rw [propagatingNumber_eq_iff_forall_isThrough, forall_isThrough_iff_bottomCap_eq_empty,
    ← exists_eq_permToBrauer_iff_bottomCap_eq_empty]

/-- A permutation diagram has `k` through strands. -/
@[simp]
theorem propagatingNumber_permToBrauer (σ : Equiv.Perm (Fin k)) :
    (permToBrauer σ).propagatingNumber = k :=
  (propagatingNumber_eq_iff_exists_eq_permToBrauer _).mpr ⟨σ, rfl⟩

/-- **A single horizontal arc already lowers the propagating number.** -/
theorem propagatingNumber_lt_of_isCap {x : Fin k ⊕ Fin k} (h : D.IsCap x) :
    D.propagatingNumber < k :=
  lt_of_le_of_ne D.propagatingNumber_le fun hk =>
    D.not_isThrough_of_isCap x h ((D.propagatingNumber_eq_iff_forall_isThrough).mp hk x)

/-- **A diagram propagates nothing exactly when none of its arcs goes through**, that is, when it
is built out of caps and cups alone. -/
theorem propagatingNumber_eq_zero_iff : D.propagatingNumber = 0 ↔ ∀ x, ¬D.IsThrough x := by
  constructor
  · intro h x
    have htop : D.topThrough = ∅ := by
      rw [← Finset.card_eq_zero, ← D.propagatingNumber_eq_card_topThrough, h]
    have hbot : D.bottomThrough = ∅ := by
      rw [← Finset.card_eq_zero, ← D.propagatingNumber_def, h]
    rcases x with i | j
    · exact fun hx => (Finset.eq_empty_iff_forall_notMem.mp hbot i) ((mem_bottomThrough _).mpr hx)
    · exact fun hx => (Finset.eq_empty_iff_forall_notMem.mp htop j) ((mem_topThrough _).mpr hx)
  · intro h
    rw [propagatingNumber_def, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact fun i hi => h _ ((mem_bottomThrough _).mp hi)

/-! ### Stacking cannot raise the propagating number -/

variable (D₁ D₂ : BrauerDiagram k)

/-- **A through strand of a composite comes from a through strand of the upper diagram**, so
stacking cannot raise the propagating number. -/
theorem propagatingNumber_composeDiagram_le_left :
    (composeDiagram D₁ D₂).propagatingNumber ≤ D₁.propagatingNumber := by
  rw [propagatingNumber_eq_card_topThrough, propagatingNumber_eq_card_topThrough]
  exact Finset.card_le_card (topThrough_composeDiagram_subset D₁ D₂)

/-- **A through strand of a composite comes from a through strand of the lower diagram**, so
stacking cannot raise the propagating number. -/
theorem propagatingNumber_composeDiagram_le_right :
    (composeDiagram D₁ D₂).propagatingNumber ≤ D₂.propagatingNumber :=
  Finset.card_le_card (bottomThrough_composeDiagram_subset D₁ D₂)

/-! ### The diagrams dividing a permutation diagram -/

variable {D D₁ D₂}

/-- **A composite is a permutation diagram only if the upper factor already is.** -/
theorem exists_eq_permToBrauer_left_of_composeDiagram_eq_permToBrauer {σ : Equiv.Perm (Fin k)}
    (h : composeDiagram D₁ D₂ = permToBrauer σ) :
    ∃ ρ : Equiv.Perm (Fin k), D₁ = permToBrauer ρ := by
  refine (propagatingNumber_eq_iff_exists_eq_permToBrauer D₁).mp
    (le_antisymm (propagatingNumber_le D₁) ?_)
  calc k = (composeDiagram D₁ D₂).propagatingNumber := by
        rw [h, propagatingNumber_permToBrauer]
    _ ≤ D₁.propagatingNumber := propagatingNumber_composeDiagram_le_left D₁ D₂

/-- **A composite is a permutation diagram only if the lower factor already is.** -/
theorem exists_eq_permToBrauer_right_of_composeDiagram_eq_permToBrauer {σ : Equiv.Perm (Fin k)}
    (h : composeDiagram D₁ D₂ = permToBrauer σ) :
    ∃ ρ : Equiv.Perm (Fin k), D₂ = permToBrauer ρ := by
  refine (propagatingNumber_eq_iff_exists_eq_permToBrauer D₂).mp
    (le_antisymm (propagatingNumber_le D₂) ?_)
  calc k = (composeDiagram D₁ D₂).propagatingNumber := by
        rw [h, propagatingNumber_permToBrauer]
    _ ≤ D₂.propagatingNumber := propagatingNumber_composeDiagram_le_right D₁ D₂

/-- **Stacking yields a permutation diagram exactly when both factors are permutation diagrams**,
and then the permutations multiply. -/
theorem composeDiagram_eq_permToBrauer_iff {σ : Equiv.Perm (Fin k)} :
    composeDiagram D₁ D₂ = permToBrauer σ ↔
      ∃ ρ τ : Equiv.Perm (Fin k), D₁ = permToBrauer ρ ∧ D₂ = permToBrauer τ ∧ ρ * τ = σ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨ρ, rfl⟩ := exists_eq_permToBrauer_left_of_composeDiagram_eq_permToBrauer h
    obtain ⟨τ, rfl⟩ := exists_eq_permToBrauer_right_of_composeDiagram_eq_permToBrauer h
    rw [composeDiagram_permToBrauer] at h
    exact ⟨ρ, τ, rfl, rfl, permToBrauer_injective k h⟩
  · rintro ⟨ρ, τ, rfl, rfl, rfl⟩
    exact composeDiagram_permToBrauer ρ τ

/-- **The invertible Brauer diagrams are exactly the permutation diagrams**: a diagram admits a
right stacking factor giving the identity diagram exactly when it is a permutation diagram. -/
theorem exists_composeDiagram_right_eq_permToBrauer_one_iff :
    (∃ E : BrauerDiagram k, composeDiagram D E = permToBrauer 1) ↔
      ∃ σ : Equiv.Perm (Fin k), D = permToBrauer σ := by
  refine ⟨fun ⟨_, hE⟩ => exists_eq_permToBrauer_left_of_composeDiagram_eq_permToBrauer hE, ?_⟩
  rintro ⟨σ, rfl⟩
  exact ⟨permToBrauer σ⁻¹, by rw [composeDiagram_permToBrauer, mul_inv_cancel]⟩

/-- **The invertible Brauer diagrams are exactly the permutation diagrams**, in the left-factor
form. -/
theorem exists_composeDiagram_left_eq_permToBrauer_one_iff :
    (∃ E : BrauerDiagram k, composeDiagram E D = permToBrauer 1) ↔
      ∃ σ : Equiv.Perm (Fin k), D = permToBrauer σ := by
  refine ⟨fun ⟨_, hE⟩ => exists_eq_permToBrauer_right_of_composeDiagram_eq_permToBrauer hE, ?_⟩
  rintro ⟨σ, rfl⟩
  exact ⟨permToBrauer σ⁻¹, by rw [composeDiagram_permToBrauer, inv_mul_cancel]⟩

-- On two strands the identity diagram propagates both strands, so the bound
-- `propagatingNumber_le` is attained.
example : (permToBrauer (1 : Equiv.Perm (Fin 2))).propagatingNumber = 2 :=
  propagatingNumber_permToBrauer 1

end BrauerDiagram

end TauCeti
