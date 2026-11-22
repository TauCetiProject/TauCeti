/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Order.Prod.Lex.Basic
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Data.Set.Card

/-!
# The zeros of a function in the sector `π/3 < ph z < π/2`

The nonreal zeros of `Bi` and `Bi′` in the upper half-plane lie in the sector `π/3 < ph z < π/2`,
where they are listed as `β₁, β₂, …` and `β′₁, β′₂, …` in order of increasing modulus
(DLMF §9.9(i)). This file defines the `k`th zero `TauCeti.airySectorZero f k` of a function
`f : ℂ → ℂ` in that sector: the zero of `f` in the sector preceded by exactly `k − 1` others, in the
order by modulus and, among zeros of equal modulus, by phase. A complex number is determined by
its modulus and its phase, so this order is the lexicographic order of `(‖z‖, arg z)`, a strict
total order on `ℂ`; it lists the zeros without knowing in advance that their moduli are distinct.

Suppose only finitely many zeros of `f` in the sector lie in each closed disc about `0`. Then a
zero preceded by exactly `k − 1` others is `airySectorZero f k` (`TauCeti.airySectorZero_eq`), and
every zero of `f` in the sector is `airySectorZero f k` for some `k ≥ 1`
(`TauCeti.exists_airySectorZero_eq`). If `f` moreover has infinitely many zeros in the sector, then
every `airySectorZero f k` is such a zero, preceded by exactly `k − 1` others
(`TauCeti.airySectorZero_spec`), and for `k ≥ 1` the zeros are listed in increasing order
(`TauCeti.strictMonoOn_toLex_airySectorZero`), so with nondecreasing moduli
(`TauCeti.monotoneOn_norm_airySectorZero`). The finiteness hypothesis holds for every entire `f`
that is not identically zero (`TauCeti.finite_setOf_airySector_eq_zero_and_norm_le`), such as `Bi`
and `Bi′`.

## Main definitions

* `TauCeti.airySectorZero f k`: the `k`th zero of `f` in `π/3 < ph z < π/2`.

## Main results

* `TauCeti.airySectorZero_eq`, `TauCeti.exists_airySectorZero_eq`: uniqueness, and every zero in
  the sector is listed.
* `TauCeti.airySectorZero_spec`: `airySectorZero f k` is attained.
* `TauCeti.strictMonoOn_toLex_airySectorZero`, `TauCeti.monotoneOn_norm_airySectorZero`: the zeros
  are listed in increasing order, with nondecreasing moduli.
* `TauCeti.finite_setOf_airySector_eq_zero_and_norm_le`: an entire `f` that is not identically
  zero, such as `Bi` or `Bi′`, has finitely many zeros in the sector in each closed disc about `0`.

## References

* NIST Digital Library of Mathematical Functions, §9.9(i), <https://dlmf.nist.gov/9.9>.
-/

public section

noncomputable section

open Complex Set
open scoped Real

namespace TauCeti

/-- The `k`th zero of `f` in `π/3 < ph z < π/2`, ordered by modulus and, among zeros of equal
modulus, by phase: exactly `k − 1` zeros of `f` in the sector precede it in that order. It is
attained and unique when `f` has infinitely many zeros in the sector, finitely many in each closed
disc about `0` (`TauCeti.airySectorZero_spec`, `TauCeti.airySectorZero_eq`). The value at `k = 0`
is that at `k = 1`. -/
def airySectorZero (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon fun z : ℂ =>
    (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z))}.ncard = k - 1

/-- The defining formula of `airySectorZero`. -/
theorem airySectorZero_def (f : ℂ → ℂ) (k : ℕ) :
    airySectorZero f k = Classical.epsilon fun z : ℂ =>
      (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧
        {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
          (‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z))}.ncard = k - 1 := (rfl)

/-- The zeros of `f` in the sector `π/3 < ph z < π/2`. -/
private def sectorZeros (f : ℂ → ℂ) : Set ℂ := {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}

private theorem mem_sectorZeros {f : ℂ → ℂ} {z : ℂ} :
    z ∈ sectorZeros f ↔ π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0 :=
  Iff.rfl

private theorem toLex_norm_arg_lt_iff {w z : ℂ} :
    toLex (‖w‖, arg w) < toLex (‖z‖, arg z) ↔ ‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z) :=
  Prod.Lex.toLex_lt_toLex

private theorem injective_toLex_norm_arg :
    Function.Injective fun z : ℂ => toLex (‖z‖, arg z) := fun w z h => by
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (toLex.injective h)
  exact ext_norm_arg h₁ h₂

/-- The zeros preceding `z` in the definition of `airySectorZero`. -/
private theorem setOf_precedes_eq (f : ℂ → ℂ) (z : ℂ) :
    {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
      (‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z))} =
      {w ∈ sectorZeros f | toLex (‖w‖, arg w) < toLex (‖z‖, arg z)} :=
  Set.ext fun _ => and_congr Iff.rfl toLex_norm_arg_lt_iff.symm

private theorem airySectorZero_eq_epsilon (f : ℂ → ℂ) (k : ℕ) :
    airySectorZero f k = Classical.epsilon fun z : ℂ =>
      z ∈ sectorZeros f ∧
        {w ∈ sectorZeros f | toLex (‖w‖, arg w) < toLex (‖z‖, arg z)}.ncard = k - 1 := by
  simp only [airySectorZero, setOf_precedes_eq, mem_sectorZeros]

private theorem finite_sep_toLex_norm_arg_lt {f : ℂ → ℂ}
    (hfin : ∀ R, {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite) (z : ℂ) :
    {w ∈ sectorZeros f | toLex (‖w‖, arg w) < toLex (‖z‖, arg z)}.Finite :=
  (hfin ‖z‖).subset fun _ hw =>
    ⟨hw.1, (toLex_norm_arg_lt_iff.1 hw.2).elim le_of_lt fun h => h.1.le⟩

/-- If some zero `z` of `f` in the sector is preceded by exactly `k − 1` others, then so is
`airySectorZero f k`. -/
private theorem airySectorZero_mem {f : ℂ → ℂ} {k : ℕ} {z : ℂ} (hz : z ∈ sectorZeros f)
    (hk : {w ∈ sectorZeros f | toLex (‖w‖, arg w) < toLex (‖z‖, arg z)}.ncard = k - 1) :
    airySectorZero f k ∈ sectorZeros f ∧
      {w ∈ sectorZeros f |
        toLex (‖w‖, arg w) < toLex (‖airySectorZero f k‖, arg (airySectorZero f k))}.ncard =
          k - 1 := by
  rw [airySectorZero_eq_epsilon]
  exact Classical.epsilon_spec (p := fun z : ℂ => z ∈ sectorZeros f ∧
    {w ∈ sectorZeros f | toLex (‖w‖, arg w) < toLex (‖z‖, arg z)}.ncard = k - 1) ⟨z, hz, hk⟩

/-- **Uniqueness.** If `f` has only finitely many zeros in `π/3 < ph z < π/2` in each closed disc
about `0`, then a zero `z` of `f` in the sector preceded by exactly `k − 1` others is
`airySectorZero f k`. -/
theorem airySectorZero_eq {f : ℂ → ℂ}
    (hfin : ∀ R, {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite) {k : ℕ}
    {z : ℂ} (hz : π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0)
    (hk : {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
      (‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z))}.ncard = k - 1) :
    airySectorZero f k = z := by
  rw [setOf_precedes_eq] at hk
  obtain ⟨hmem, hcard⟩ := airySectorZero_mem (mem_sectorZeros.2 hz) hk
  exact (injective_toLex_norm_arg.injOn.injOn_ncard_sep_lt
    fun a _ => finite_sep_toLex_norm_arg_lt hfin a) hmem (mem_sectorZeros.2 hz)
    (hcard.trans hk.symm)

/-- **Every zero is listed.** If `f` has only finitely many zeros in `π/3 < ph z < π/2` in each
closed disc about `0`, then every zero of `f` in the sector is `airySectorZero f k` for some
`k ≥ 1`. -/
theorem exists_airySectorZero_eq {f : ℂ → ℂ}
    (hfin : ∀ R, {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite) {z : ℂ}
    (hz : π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) :
    ∃ k, 1 ≤ k ∧ airySectorZero f k = z :=
  ⟨_, Nat.le_add_left 1 _, airySectorZero_eq hfin hz (Nat.add_sub_cancel _ _).symm⟩

/-- **Attainment.** If `f` has infinitely many zeros in `π/3 < ph z < π/2`, finitely many in each
closed disc about `0`, then `airySectorZero f k` is a zero of `f` in the sector preceded by exactly
`k − 1` others. -/
theorem airySectorZero_spec {f : ℂ → ℂ}
    (hfin : ∀ R, {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite) (k : ℕ) :
    (π / 3 < arg (airySectorZero f k) ∧ arg (airySectorZero f k) < π / 2 ∧
        f (airySectorZero f k) = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖airySectorZero f k‖ ∨
          (‖w‖ = ‖airySectorZero f k‖ ∧ arg w < arg (airySectorZero f k)))}.ncard = k - 1 := by
  obtain ⟨z, hz, hk⟩ := Infinite.exists_mem_ncard_sep_lt_eq (s := sectorZeros f) hinf
    injective_toLex_norm_arg.injOn (fun a _ => finite_sep_toLex_norm_arg_lt hfin a) (k - 1)
  rw [setOf_precedes_eq, ← mem_sectorZeros]
  exact airySectorZero_mem hz hk

/-- **The zeros are listed in increasing order.** If `f` has infinitely many zeros in
`π/3 < ph z < π/2`, finitely many in each closed disc about `0`, then for `1 ≤ j < k` the zero
`airySectorZero f j` precedes `airySectorZero f k` in the lexicographic order of modulus and
phase. -/
theorem strictMonoOn_toLex_airySectorZero {f : ℂ → ℂ}
    (hfin : ∀ R, {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite) :
    StrictMonoOn (fun k => toLex (‖airySectorZero f k‖, arg (airySectorZero f k))) (Ici 1) := by
  intro j hj k hk hjk
  have hspec (n : ℕ) := airySectorZero_spec hfin hinf n
  simp only [setOf_precedes_eq] at hspec
  simp only [mem_Ici] at hj hk
  -- The counts `j − 1 < k − 1` of preceding zeros rule out `β_k ≤ β_j`.
  refine lt_of_not_ge fun hle => ?_
  beta_reduce at hle
  rcases hle.lt_or_eq with h | h
  · have := ncard_sep_lt_lt_ncard_sep_lt (f := fun z : ℂ => toLex (‖z‖, arg z)) (hspec k).1 h
      (finite_sep_toLex_norm_arg_lt hfin _)
    rw [(hspec j).2, (hspec k).2] at this
    omega
  · have := (hspec k).2
    rw [h, (hspec j).2] at this
    omega

/-- **The moduli are nondecreasing.** If `f` has infinitely many zeros in `π/3 < ph z < π/2`,
finitely many in each closed disc about `0`, then `‖airySectorZero f k‖` is monotone in `k ≥ 1`. -/
theorem monotoneOn_norm_airySectorZero {f : ℂ → ℂ}
    (hfin : ∀ R, {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite)
    (hinf : {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite) :
    MonotoneOn (fun k => ‖airySectorZero f k‖) (Ici 1) := fun _ hj _ hk hjk =>
  Prod.Lex.monotone_fst _ _ ((strictMonoOn_toLex_airySectorZero hfin hinf).monotoneOn hj hk hjk)

/-- An entire function `f` that is not identically zero has only finitely many zeros in
`π/3 < ph z < π/2` in each closed disc about `0`. This applies to `Bi` and `Bi′`, which are nonzero
at `0` (`TauCeti.airyBi_zero_ne_zero`, `TauCeti.deriv_airyBi_zero_ne_zero`). -/
theorem finite_setOf_airySector_eq_zero_and_norm_le {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {z₀ : ℂ} (h₀ : f z₀ ≠ 0) (R : ℝ) :
    {z | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite := by
  refine (hf.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (mem_univ z₀) h₀
    (isCompact_closedBall 0 R) (subset_univ _)).subset fun z hz => ⟨?_, hz.1.2.2⟩
  simpa using hz.2

end TauCeti
