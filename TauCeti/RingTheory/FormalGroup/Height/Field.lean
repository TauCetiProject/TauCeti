/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Height.Ideal
import TauCeti.RingTheory.FormalGroup.BaseChange
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# Detecting formal-group height bounds on fields

For a commutative formal group over an arbitrary ring and `n > 0`, the height ideal `I_n` is the
unit ideal if and only if every specialization to a field of characteristic `p` has
height less than `n`. Thus field-valued height bounds imply ideal-theoretic bounds on
families, without reducedness or Noetherian hypotheses. Only fields in the universe
of the coefficient ring are needed: maximal-ideal quotients already detect a proper ideal.

Landweber's recursion identifies this condition for `I_(n+1)` with invertibility of
`v_n`, the coefficient of degree `pⁿ` of the `p`-series, modulo `I_n`.

## References

* P. S. Landweber, *Homological properties of comodules over MU_*(MU) and BP_*(BP)*,
  Amer. J. Math. 98 (1976), 591–610.
-/

public section

namespace FormalGroup

universe u

variable {R : Type u} [CommRing R] (F : FormalGroup R) [F.IsComm] {p : ℕ}

/-- A positive-index height ideal is the unit ideal exactly when all characteristic-`p` field
specializations have height below its index. The coefficient ring need not be reduced. -/
theorem heightIdeal_eq_top_iff_forall_height_lt (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    F.heightIdeal p n = ⊤ ↔
      ∀ (K : Type u) [Field K] [CharP K p] (f : R →+* K), (F.map f).height p < n := by
  constructor
  · intro h K _ _ f
    rw [← heightIdeal_eq_top_iff_height_lt, ← map_heightIdeal, h, Ideal.map_top]
  · intro h
    by_contra hI
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (F.heightIdeal p n) hI
    let : m.IsMaximal := hm
    let := Ideal.Quotient.field m
    have hp_mem : (p : R) ∈ m := by
      apply hle
      rw [← F.coeff_one_nsmulSeries p]
      exact coeff_nsmulSeries_mem_heightIdeal (Nat.one_lt_pow hn hp.one_lt)
    let : CharP (R ⧸ m) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
      exact hp_mem)
    have htop := (heightIdeal_eq_top_iff_height_lt _).mpr (h (R ⧸ m) (Ideal.Quotient.mk m))
    have hbot : (F.map (Ideal.Quotient.mk m)).heightIdeal p n = ⊥ := by
      rw [← map_heightIdeal]
      exact Ideal.map_mk_eq_bot_of_le hle
    exact bot_ne_top (hbot.symm.trans htop)

/-- Landweber's element `v_n` is a unit modulo `I_n` exactly when the next height
ideal is the unit ideal. This also applies when the quotient is the zero ring. -/
theorem isUnit_mk_coeff_nsmulSeries_iff (hp : p.Prime) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (F.heightIdeal p n)
      (PowerSeries.coeff (p ^ n) (F.nsmulSeries p))) ↔ F.heightIdeal p (n + 1) = ⊤ := by
  rw [Ideal.Quotient.isUnit_mk_iff, F.heightIdeal_succ hp, sup_comm]

end FormalGroup
