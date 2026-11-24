/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Nilpotent.LowerCentralSeries
import TauCeti.GroupTheory.Commutator

/-!
# Commutators of terms of the lower central series

Write `γ₁ = H, γ₂ = ⁅H, H⁆, …` for the lower central series of a subgroup `H`, so that
`γ_{n+1}` is Mathlib's `H.lowerCentralSeries n`. This file proves that the series is a filtration
for commutators, `⁅γ_i, γ_j⁆ ≤ γ_{i+j}`, by induction on `j` with the Three Subgroups Lemma. As a
consequence the `k`-th derived subgroup of a group lies in `γ_{2^k}`, which bounds the derived
length of a nilpotent group logarithmically in its nilpotency class. Mathlib's
`Subgroup.derivedSeries_le_lowerCentralSeries_top` only gives `G⁽ᵏ⁾ ≤ γ_{k+1}`.

## Main results

* `Subgroup.commutator_lowerCentralSeries_le`: `⁅γ_{i+1}, γ_{j+1}⁆ ≤ γ_{i+j+2}`, written with
  Mathlib's indexing as `⁅H.lowerCentralSeries i, H.lowerCentralSeries j⁆ ≤
  H.lowerCentralSeries (i + j + 1)`.
* `TauCeti.derivedSeries_le_lowerCentralSeries_top_two_pow_sub_one`: `G⁽ᵏ⁾ ≤ γ_{2^k}`.

## References

* D. J. S. Robinson, *A Course in the Theory of Groups*, 2nd ed., Graduate Texts in
  Mathematics 80, Springer, 1996, §5.1.
-/

public section

open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Subgroup

/-- The case of a normal subgroup, where every term of the series is normal in `G`, so that the
Three Subgroups Lemma applies modulo a term of the series. -/
private theorem commutator_lowerCentralSeries_le_of_normal (N : Subgroup G) [N.Normal]
    (i j : ℕ) :
    ⁅N.lowerCentralSeries i, N.lowerCentralSeries j⁆ ≤ N.lowerCentralSeries (i + j + 1) := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    -- `⁅γ_i, ⁅γ_j, N⁆⁆ = ⁅⁅γ_j, N⁆, γ_i⁆`, and the Three Subgroups Lemma reduces it to
    -- `⁅⁅N, γ_i⁆, γ_j⁆ = ⁅γ_{i+1}, γ_j⁆` and `⁅⁅γ_i, γ_j⁆, N⁆ ≤ ⁅γ_{i+j+1}, N⁆`.
    rw [lowerCentralSeries_succ, commutator_comm]
    refine TauCeti.commutator_commutator_le_of_rotate ?_ ?_
    · rw [commutator_comm N, ← lowerCentralSeries_succ]
      exact (ih (i + 1)).trans_eq (by congr 1; omega)
    · exact (commutator_mono (ih i) le_rfl).trans_eq
        (by rw [← lowerCentralSeries_succ, add_assoc i j 1])

/-- The lower central series of a subgroup `H` is a filtration for commutators:
`⁅γ_{i+1}, γ_{j+1}⁆ ≤ γ_{i+j+2}`, where `γ_{n+1} = H.lowerCentralSeries n`. -/
theorem commutator_lowerCentralSeries_le (H : Subgroup G) (i j : ℕ) :
    ⁅H.lowerCentralSeries i, H.lowerCentralSeries j⁆ ≤ H.lowerCentralSeries (i + j + 1) := by
  -- Transport the case `⊤` in the group `H` along the inclusion `H → G`.
  simpa only [map_commutator, top_subtype_lowerCentralSeries] using
    map_mono (f := H.subtype) (commutator_lowerCentralSeries_le_of_normal (⊤ : Subgroup H) i j)

end Subgroup

namespace TauCeti

open Subgroup

/-- The `k`-th derived subgroup lies in the `2^k`-th term `γ_{2^k}` of the lower central series,
which is `(⊤ : Subgroup G).lowerCentralSeries (2 ^ k - 1)`. -/
theorem derivedSeries_le_lowerCentralSeries_top_two_pow_sub_one (k : ℕ) :
    Subgroup.derivedSeries G k ≤ (⊤ : Subgroup G).lowerCentralSeries (2 ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Subgroup.derivedSeries_succ]
    refine (commutator_mono ih ih).trans
      ((commutator_lowerCentralSeries_le ⊤ _ _).trans_eq ?_)
    congr 1
    have := Nat.one_le_two_pow (n := k)
    rw [pow_succ]
    omega

end TauCeti
