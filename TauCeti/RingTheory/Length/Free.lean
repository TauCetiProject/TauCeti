/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.AlgebraTower

/-!
# Length of a free module under restriction of scalars

The length over the base ring of a free module in a scalar tower is its rank over the middle
ring times the length of that ring over the base. The formula includes infinite rank and is the
restriction-of-scalars form of `Module.length_of_free`.
-/

public section

/-- In a scalar tower `R → S → M` with `M` free over `S`, its length over `R` is the product of
the extended natural rank over `S` and the length of `S` over `R`. -/
theorem Module.length_eq_rank_mul_length_of_free (R S M : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [Module R S] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Free S M] :
    Module.length R M = (Module.rank S M).toENat * Module.length R S := by
  nontriviality S using Module.subsingleton S M
  nontriviality M using rank_subsingleton'
  let b := Module.Free.chooseBasis S M
  have := b.isScalarTower_finsupp R
  rw [(b.repr.restrictScalars R).length_eq, Module.length_finsupp]
  by_cases h : Module.length R S = ⊤
  · simp [h, ENat.card_ne_zero, rank_pos_of_free.ne']
  have := b.isScalarTower_of_nonempty R
  have : IsNoetherianRing S := isNoetherianRing_iff.mpr <| isNoetherian_of_tower R
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h)).1
  rw [Module.Free.rank_eq_card_chooseBasisIndex, ENat.card]

/-- The `ENat.toNat` of the length of a restricted free module is its `finrank` over the
middle ring times the `ENat.toNat` of that ring's length over the base. -/
theorem Module.toNat_length_eq_finrank_mul_of_free (R S M : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [Module R S] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Free S M] :
    (Module.length R M).toNat = Module.finrank S M * (Module.length R S).toNat := by
  rw [Module.length_eq_rank_mul_length_of_free R S, ENat.toNat_mul, Cardinal.toNat_toENat,
    Module.finrank]
