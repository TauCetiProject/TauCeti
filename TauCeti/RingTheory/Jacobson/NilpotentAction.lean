/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.Jacobson.Ideal

import TauCeti.RingTheory.Jacobson.Basic

/-!
# Elements of the Jacobson radical act nilpotently on finite modules

Let `R` be a ring and `N` an `R`-module with finitely many elements. An element `r`
of the Jacobson radical of `R` acts nilpotently on `N`: the maps `x ↦ r ^ i • x` cannot all be
distinct, and if `r ^ i` and `r ^ j` act alike with `i < j`, then `1 - r ^ (j - i)` is a unit
killing every `r ^ i • x`. In particular, if a prime `p` lies in the Jacobson radical of `R`, every
finite `R`-module is an additive `p`-group, so its cardinality is a power of `p`.

For instance, a finite module over a local ring with residue characteristic `p`, such as a finite
module over the Iwasawa algebra `O⟦X⟧` of a complete discrete valuation ring `O` of residue
characteristic `p`, has `p`-power order; this is how the bounded error terms in Iwasawa's growth
formula become powers of `p`.

## Main results

* `TauCeti.exists_pow_smul_eq_zero_of_mem_jacobson`: an element of the Jacobson radical has a
  power acting as zero on a finite module.
* `TauCeti.isAddPGroup_of_natCast_mem_jacobson`: if `p` lies in the Jacobson radical, then every
  finite module is an additive `p`-group.
* `TauCeti.exists_natCard_eq_pow_of_natCast_mem_jacobson`: if the prime `p` lies in the Jacobson
  radical, then every finite module has `p`-power cardinality.
-/

public section

namespace TauCeti

variable {R N : Type*} [Ring R] [AddCommGroup N] [Module R N] [Finite N]

variable (N) in
/-- **Elements of the Jacobson radical act nilpotently on finite modules.** If `r` lies in the
Jacobson radical of `R` and the `R`-module `N` is finite, then some power of `r` acts as zero
on `N`. -/
theorem exists_pow_smul_eq_zero_of_mem_jacobson {r : R} (hr : r ∈ Ring.jacobson R) :
    ∃ n : ℕ, ∀ x : N, r ^ n • x = 0 := by
  -- Two of the finitely many maps `x ↦ r ^ i • x` agree.
  obtain ⟨i, j, hij, h⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun i : ℕ ↦ fun x : N ↦ r ^ i • x
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm h.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  refine ⟨i, fun x ↦ ?_⟩
  have hmem : r ^ (j - i) ∈ Ring.jacobson R :=
    Ideal.pow_mem_of_mem _ hr _ (Nat.sub_pos_of_lt hlt)
  have hunit : IsUnit (1 - r ^ (j - i)) := by
    simpa [sub_eq_add_neg] using Ring.mem_jacobson_iff_isUnit_one_add_mul_left.1 hmem (-1)
  have hzero : (1 - r ^ (j - i)) • r ^ i • x = 0 := by
    rw [sub_smul, one_smul, smul_smul, ← pow_add, Nat.sub_add_cancel hlt.le]
    exact sub_eq_zero.2 (congrFun h x)
  exact (hunit.smul_eq_zero).1 hzero

/-- **Finite modules are `p`-groups when `p` is in the Jacobson radical.** If `p` lies in the
Jacobson radical of `R`, for instance if `R` is local of residue characteristic `p`, then every
finite `R`-module is an additive `p`-group. -/
theorem isAddPGroup_of_natCast_mem_jacobson {p : ℕ} (hp : (p : R) ∈ Ring.jacobson R) :
    IsAddPGroup p N := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_mem_jacobson N hp
  exact fun x ↦ ⟨n, by simpa [← Nat.cast_smul_eq_nsmul R] using hn x⟩

variable (N) in
/-- **Finite modules have `p`-power order when `p` is in the Jacobson radical.** If the prime `p`
lies in the Jacobson radical of `R`, for instance if `R` is local of residue characteristic `p`,
then every finite `R`-module has cardinality a power of `p`. -/
theorem exists_natCard_eq_pow_of_natCast_mem_jacobson {p : ℕ} [Fact p.Prime]
    (hp : (p : R) ∈ Ring.jacobson R) : ∃ k : ℕ, Nat.card N = p ^ k :=
  (isAddPGroup_of_natCast_mem_jacobson hp).exists_card_eq

end TauCeti
