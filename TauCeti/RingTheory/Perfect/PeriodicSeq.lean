/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.Nat.Periodic
public import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Periodic sequences over a ring, perfectness, and shift splitting

For a commutative ring `R`, `TauCeti.periodicSeq R` is the `R`-subalgebra of `ℕ → R` consisting
of sequences for which `n !` is a period for all sufficiently large `n` (equivalently, sequences
with a positive period).

We define the shift endomorphism `TauCeti.periodicSeq.shift` (`(γ f) k = f (k + 1)`), show that
`periodicSeq R` is a `PerfectRing` of characteristic `p` whenever `R` is, and construct an
explicit `A`-linear splitting of `0 → R → periodicSeq R →^{shift - 1} periodicSeq R → 0`
whenever `(m : R) = 0` for some `m > 0` (in particular, in characteristic `p`). This splitting
gives Koszul-exactness of `(algebraMap R (periodicSeq R), shift)` after tensoring with any
`A`-module.

## Main definitions and results

* `TauCeti.periodicSeq`: the `R`-subalgebra of periodic sequences `ℕ → R`.
* `TauCeti.periodicSeq.shift`: the shift `A`-algebra endomorphism `(γ f) k = f (k + 1)`.
* `TauCeti.periodicSeq.mem_of_periodic`: every sequence with a positive period lies in
  `periodicSeq R`.
* `TauCeti.periodicSeq.partialSum`: when `(m : R) = 0` for some `m > 0`, the `A`-linear partial
  sum operator `f ↦ (k ↦ ∑ i ∈ range k, f i)` on `periodicSeq R`.
* `TauCeti.periodicSeq.shift_sub_one_partialSum` and
  `TauCeti.periodicSeq.algebraMap_evalZero_add_partialSum_shift_sub_one`: the splitting
  identities showing `0 → R → periodicSeq R →^{shift - 1} periodicSeq R → 0` is split exact.
* `TauCeti.periodicSeq.perfectRing`: if `R` is a perfect ring of exponential characteristic `p`,
  then so is `periodicSeq R`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/PadicComparison/ToricTower.lean`
(`New.Variety.periodicSeq`, `New.Variety.periodicSeq.shift`,
`New.Variety.periodicSeq.mem_of_periodic`, `New.Variety.periodicSeq.koszulExact_shift`,
`New.Variety.periodicSeq.perfectRing`).
-/

public section

namespace TauCeti

open Filter Finset Nat

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- The `R`-subalgebra of `ℕ → R` consisting of periodic sequences, written as those for which
`n !` is a period for all sufficiently large `n`. -/
def periodicSeq (R : Type*) [CommRing R] : Subalgebra R (ℕ → R) where
  carrier := {f : ℕ → R | ∀ᶠ n : ℕ in atTop, Function.Periodic f n !}
  mul_mem' hf hg := (hf.and hg).mono fun _ h ↦ h.left.mul h.right
  add_mem' hf hg := (hf.and hg).mono fun _ h ↦ h.left.add h.right
  algebraMap_mem' _ := Eventually.of_forall fun _ _ ↦ rfl

namespace periodicSeq

/-- The shift `A`-algebra endomorphism of `periodicSeq R`, sending `f` to `k ↦ f (k + 1)`. -/
def shift (A R : Type*) [CommRing A] [CommRing R] [Algebra A R] :
    periodicSeq R →ₐ[A] periodicSeq R where
  toFun f := ⟨fun k ↦ f.val (k + 1), f.property.mono fun n hn k ↦ by
    simpa [Nat.add_right_comm] using hn (k + 1)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- A sequence with any positive period `n` lies in `periodicSeq R`. -/
theorem mem_of_periodic {f : ℕ → R} {n : ℕ} (hn_pos : 0 < n) (h : Function.Periodic f n) :
    f ∈ periodicSeq R := by
  filter_upwards [eventually_ge_atTop n] with m hm
  simpa [Nat.div_mul_cancel (Nat.dvd_factorial hn_pos hm)] using h.nsmul (m ! / n)

/-- When `m > 0` annihilates `R`, the partial sums of a periodic sequence are periodic, yielding
an `A`-linear right inverse to `shift - 1`. -/
def partialSum (A R : Type*) [CommRing A] [CommRing R] [Algebra A R] {m : ℕ} (hm : 0 < m)
    (hm0 : (m : R) = 0) : periodicSeq R →ₗ[A] periodicSeq R where
  toFun f := ⟨fun k ↦ ∑ i ∈ range k, f.val i, by
    obtain ⟨n, hn⟩ := f.property.exists
    let s (k : ℕ) : R := ∑ i ∈ range k, f.val i
    have h_step (k : ℕ) : s (k + n !) = s k + s n ! := by
      simp_rw [s, add_comm k, sum_range_add, add_comm n !, hn _, add_comm]
    have h_iter : ∀ q k : ℕ, s (k + q * n !) = s k + q • s n ! := by
      intro q
      induction q with
      | zero => intro k; simp
      | succ q ih =>
        intro k
        rw [Nat.succ_mul, ← add_assoc, h_step, ih, add_assoc, succ_nsmul]
    refine mem_of_periodic (Nat.mul_pos hm (Nat.factorial_pos n)) fun k ↦ ?_
    simpa [nsmul_eq_mul, hm0] using h_iter m k⟩
  map_add' _ _ := Subtype.ext (funext fun _ ↦ by simp [sum_add_distrib])
  map_smul' _ _ := Subtype.ext (funext fun _ ↦ by simp [smul_sum])

/-- `(shift - 1) (partialSum f) = f`. -/
theorem shift_sub_one_partialSum {m : ℕ} (hm : 0 < m) (hm0 : (m : R) = 0) (f : periodicSeq R) :
    shift A R (partialSum A R hm hm0 f) - partialSum A R hm hm0 f = f := by
  ext k
  exact sum_range_succ_sub_sum f.val

/-- Every periodic sequence decomposes as its constant term at `0` plus
`partialSum ((shift - 1) f)`. Together with `shift_sub_one_partialSum`, this splits
`0 → R → periodicSeq R →^{shift - 1} periodicSeq R → 0`. -/
theorem algebraMap_evalZero_add_partialSum_shift_sub_one {m : ℕ} (hm : 0 < m) (hm0 : (m : R) = 0)
    (f : periodicSeq R) :
    algebraMap R (periodicSeq R) (f.val 0) +
      partialSum A R hm hm0 (shift A R f - f) = f := by
  ext k
  have h : (partialSum A R hm hm0 (shift A R f - f)).val k = f.val k - f.val 0 :=
    sum_range_sub f.val k
  rw [Subalgebra.coe_add, Pi.add_apply, h]
  simp

/-- If `R` is a perfect ring of exponential characteristic `p`, then so is `periodicSeq R`. -/
instance perfectRing (p : ℕ) [ExpChar R p] [PerfectRing R p] : PerfectRing (periodicSeq R) p where
  bijective_frobenius := by
    let e : (ℕ → R) ≃ (ℕ → R) := (Equiv.refl ℕ).arrowCongr (frobeniusEquiv R p).toEquiv
    have h_mem (f : ℕ → R) : f ∈ periodicSeq R ↔ e f ∈ periodicSeq R := by
      simp [periodicSeq, e, -RingEquiv.toEquiv_eq_coe]
    exact (e.subtypeEquiv h_mem).bijective

end periodicSeq

end TauCeti
