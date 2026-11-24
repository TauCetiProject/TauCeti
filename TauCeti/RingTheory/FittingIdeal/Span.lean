/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.RingTheory.FittingIdeal.Basic

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Prod

/-!
# Minors ideals and generating families

Let `F` be a module over a commutative ring `R`. This file relates the ideals of minors
`Submodule.minorsIdeal` to explicit generating families:

* Adjoining a finite family of `m` generators to a submodule `N` shifts its minors ideals by at
  most `m`: `(N ⊔ span R (range v)).minorsIdeal (p + Nat.card ι) ≤ N.minorsIdeal p`
  (`Submodule.minorsIdeal_sup_span_range_add_le`), proved directly from
  `Submodule.minorsIdeal_prod_top` and `Submodule.minorsIdeal_map_le` via the surjection
  `N × (ι → R) → N ⊔ span R (range v)`. Specializing to a single generator gives
  `(N ⊔ R ∙ x).minorsIdeal (p + 1) ≤ N.minorsIdeal p`
  (`Submodule.minorsIdeal_sup_span_singleton_succ_le`).
* Taking `N = ⊥` shows that if a submodule is contained in the span of fewer than `p` vectors, its
  `p × p` minors ideal vanishes (`Submodule.minorsIdeal_span_range_eq_bot_of_lt`,
  `Submodule.minorsIdeal_eq_bot_of_le_span_range`).

These span-cardinality and single-generator shift bounds control `Module.Grassmannian.rankLocus` on
bounded-rank quotients and across flag steps, enabling the full-flag reduction of Schubert rank
ideals to their jump conditions (`Module.Grassmannian.iSup_rankLocus_flag_succ_eq`).

## Main results

* `Submodule.minorsIdeal_sup_span_range_add_le`: adjoining a finite family of `m` generators shifts
  the minors ideals by at most `m`.
* `Submodule.minorsIdeal_sup_span_singleton_succ_le`: adjoining one generator shifts the minors
  ideals by at most one.
* `Submodule.minorsIdeal_span_range_eq_bot_of_lt`: the `p × p` minors ideal of the span of fewer
  than `p` vectors vanishes.
* `Submodule.minorsIdeal_eq_bot_of_le_span_range`: the `p × p` minors ideal of a submodule
  contained in the span of fewer than `p` vectors vanishes.

## References

* [Stacks Project, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6)
-/

public section

open Module

namespace Submodule

variable {R F : Type*} [CommRing R] [AddCommGroup F] [Module R F]

/-- Adjoining a finite family `v : ι → F` of generators to a submodule `N` shifts its minors ideals
by at most `Nat.card ι`. -/
theorem minorsIdeal_sup_span_range_add_le {ι : Type*} [Finite ι] (N : Submodule R F) (v : ι → F)
    (p : ℕ) :
    (N ⊔ Submodule.span R (Set.range v)).minorsIdeal (p + Nat.card ι) ≤ N.minorsIdeal p := by
  nontriviality R
  cases nonempty_fintype ι
  have hmap : (N.prod (⊤ : Submodule R (ι → R))).map
      (LinearMap.id.coprod (Fintype.linearCombination R v)) =
      N ⊔ Submodule.span R (Set.range v) := by
    rw [LinearMap.map_coprod_prod, Submodule.map_id, Submodule.map_top,
      Fintype.range_linearCombination]
  rw [← hmap, Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card R]
  exact (Submodule.minorsIdeal_map_le _ _ _).trans_eq (Submodule.minorsIdeal_prod_top N p)

/-- Adjoining a single generator `x` to a submodule `N` shifts its minors ideals by at most one:
every `(p + 1) × (p + 1)` minor of `N ⊔ R ∙ x` lies in `N.minorsIdeal p`. -/
theorem minorsIdeal_sup_span_singleton_succ_le (N : Submodule R F) (x : F) (p : ℕ) :
    (N ⊔ R ∙ x).minorsIdeal (p + 1) ≤ N.minorsIdeal p := by
  simpa [Set.range_const] using minorsIdeal_sup_span_range_add_le N (fun _ : Unit ↦ x) p

/-- The `p × p` minors ideal of the span of fewer than `p` vectors vanishes. -/
theorem minorsIdeal_span_range_eq_bot_of_lt {ι : Type*} [Finite ι] {p : ℕ}
    (h : Nat.card ι < p) (v : ι → F) :
    (Submodule.span R (Set.range v)).minorsIdeal p = ⊥ := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt h)
  have hp : (q + 1) + Nat.card ι = p := by omega
  refine le_bot_iff.mp ?_
  calc (Submodule.span R (Set.range v)).minorsIdeal p
      = (⊥ ⊔ Submodule.span R (Set.range v)).minorsIdeal ((q + 1) + Nat.card ι) := by
          rw [bot_sup_eq, hp]
    _ ≤ (⊥ : Submodule R F).minorsIdeal (q + 1) := minorsIdeal_sup_span_range_add_le ⊥ v (q + 1)
    _ = ⊥ := minorsIdeal_bot q

/-- If a submodule `N` is contained in the span of fewer than `p` vectors, its `p × p` minors ideal
vanishes. -/
theorem minorsIdeal_eq_bot_of_le_span_range {ι : Type*} [Finite ι] {N : Submodule R F} {p : ℕ}
    {v : ι → F} (hN : N ≤ Submodule.span R (Set.range v)) (hp : Nat.card ι < p) :
    N.minorsIdeal p = ⊥ :=
  le_bot_iff.mp <| (minorsIdeal_mono hN p).trans_eq (minorsIdeal_span_range_eq_bot_of_lt hp v)

end Submodule
