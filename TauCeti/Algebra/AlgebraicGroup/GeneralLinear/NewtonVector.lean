/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Set.Finite.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.TwoWeylVectorPairing
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.Floor.Ring

/-!
# Newton vectors of the general linear group

The isocrystals of height `n` over an algebraically closed field of characteristic `p` are
classified by their slopes (Dieudonné–Manin), so the set `B(GL_n)` of `σ`-conjugacy classes is
the set of *Newton vectors*: weakly decreasing rational vectors `ν₁ ≥ ⋯ ≥ νₙ` in which a slope `λ`
occurring with multiplicity `m` satisfies `m λ ∈ ℤ`. This file develops the combinatorics of
these vectors that the Newton stratification needs.

* The order on `B(GL_n)` is the dominance order `TauCeti.Dominates`: equal total slopes and
  inequalities of the leading partial sums. For integer vectors it is the coroot order
  (`TauCeti.GeneralLinear.dominates_iff_rootLE_flip`).
* For an integral cocharacter `μ` in its dominant form, that is, a weakly decreasing integer
  vector representing its conjugacy class, the set `B(GL_n, μ)` of `μ`-admissible classes
  consists of the Newton vectors dominated by `μ`. The definition does not sort `μ`: for an
  arbitrary integer vector it is the set of Newton vectors dominated by that vector, which is
  `B(GL_n, μ)` once `μ` is replaced by its decreasing rearrangement. It is finite for every
  integer vector `μ`: the coordinates of an admissible vector lie between the last and the first
  coordinate of `μ`, and the multiplicity condition makes `n! • ν` integral.
* The invariant `d_b = ⟨2ρ, ν_b⟩` of a Newton class is
  `TauCeti.GeneralLinear.twoWeylVectorPairing`, which is strictly monotone for dominance.

For `μ = (1, 0)` the admissible set has exactly the two elements `(1, 0)` (ordinary) and
`(1/2, 1/2)` (basic), and the basic class is the smaller one. The multiplicity condition is what
excludes vectors such as `(3/4, 1/4)`, which are weakly decreasing and dominated by `(1, 0)`: a
slope of multiplicity one must be an integer.

## Main definitions

* `TauCeti.GeneralLinear.IsNewtonVector`: weakly decreasing rational vectors satisfying the
  multiplicity condition.
* `TauCeti.GeneralLinear.admissibleNewtonVectors μ`: the Newton vectors dominated by the integral
  cocharacter `μ`.

## Main results

* `TauCeti.GeneralLinear.IsNewtonVector.exists_factorial_mul_eq_intCast`: the coordinates of a
  Newton vector of height `n` lie in `(1 / n!) ℤ`.
* `TauCeti.GeneralLinear.admissibleNewtonVectors_finite`: `B(GL_n, μ)` is finite.
* `TauCeti.GeneralLinear.admissibleNewtonVectors_one_zero`: `B(GL_2, (1, 0))` consists of the
  ordinary and the basic class.
* `TauCeti.GeneralLinear.dominates_half_half_one_zero`,
  `TauCeti.GeneralLinear.not_dominates_one_zero_half_half`: in `B(GL_2, (1, 0))` the basic class
  lies strictly below the ordinary class.

## References

* A. Caraiani and P. Scholze, *On the generic part of the cohomology of compact unitary Shimura
  varieties*, Ann. of Math. 186 (2017), §3.1.
* R. Kottwitz, *Isocrystals with additional structure*, Compositio Math. 56 (1985), §4.
* M. Rapoport and M. Richartz, *On the classification and specialization of `F`-isocrystals with
  additional structure*, Compositio Math. 103 (1996), Theorem 1.15.
-/

public section

open Finset

namespace TauCeti.GeneralLinear

variable {n : ℕ}

/-- A **Newton vector** of height `n`: a weakly decreasing vector `ν₁ ≥ ⋯ ≥ νₙ` of rational slopes
in which every slope `λ`, occurring with multiplicity `m`, satisfies `m λ ∈ ℤ`. By the
Dieudonné–Manin classification these are the slope vectors of the isocrystals of height `n`, that
is, the elements of `B(GL_n)`. -/
structure IsNewtonVector (ν : Fin n → ℚ) : Prop where
  /-- The slopes are weakly decreasing. -/
  antitone : Antitone ν
  /-- A slope `λ` of multiplicity `m` satisfies `m λ ∈ ℤ`. -/
  exists_card_mul_eq_intCast : ∀ i, ∃ m : ℤ, (#{j | ν j = ν i} : ℚ) * ν i = m

/-- **The coordinates of a Newton vector of height `n` lie in `(1 / n!) ℤ`**: the multiplicity of
each slope divides `n!`. -/
theorem IsNewtonVector.exists_factorial_mul_eq_intCast {ν : Fin n → ℚ} (hν : IsNewtonVector ν)
    (i : Fin n) : ∃ m : ℤ, (n.factorial : ℚ) * ν i = m := by
  obtain ⟨m, hm⟩ := hν.exists_card_mul_eq_intCast i
  have hpos : 0 < #{j | ν j = ν i} := card_pos.mpr ⟨i, by simp⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hpos ((card_filter_le _ _).trans (card_fin n).le)
  exact ⟨c * m, by rw [hc]; push_cast; rw [← hm]; ring⟩

/-- The **`μ`-admissible Newton vectors** `B(GL_n, μ)` of an integral cocharacter `μ`: the Newton
vectors dominated by `μ`, that is, with the total slope of `μ` and leading partial sums at most
those of `μ`. For the dominant (weakly decreasing) representative `μ` of a conjugacy class of
cocharacters these are the classes `b ∈ B(GL_n)` with `ν_b ≼ μ`; for `GL_n` the condition
`κ(b) = μ♭` on the Kottwitz invariant is the equality of total slopes. The definition does not
sort `μ`, so it is `B(GL_n, μ)` only for weakly decreasing `μ`; for another integer vector it is
the set of Newton vectors dominated by that vector. -/
def admissibleNewtonVectors (μ : Fin n → ℤ) : Set (Fin n → ℚ) :=
  {ν | IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ)}

@[simp]
theorem mem_admissibleNewtonVectors {μ : Fin n → ℤ} {ν : Fin n → ℚ} :
    ν ∈ admissibleNewtonVectors μ ↔ IsNewtonVector ν ∧ Dominates ν fun i ↦ (μ i : ℚ) :=
  Iff.rfl

/-- **`B(GL_n, μ)` is finite**, for every integer vector `μ`. The coordinates of an admissible
Newton vector lie between the last and the first coordinate of `μ`, and in `(1 / n!) ℤ`. -/
theorem admissibleNewtonVectors_finite (μ : Fin n → ℤ) : (admissibleNewtonVectors μ).Finite := by
  cases n with
  | zero => exact Set.toFinite _
  | succ n =>
    refine (Set.Finite.pi (t := fun _ ↦ {q : ℚ | q ∈ Set.Icc (μ (Fin.last n) : ℚ) (μ 0) ∧
        ∃ m : ℤ, ((n + 1).factorial : ℚ) * q = m}) fun _ ↦
      finite_setOf_mem_Icc_natCast_mul_eq_intCast (Nat.factorial_ne_zero _) _ _).subset ?_
    rintro ν ⟨hν, hdom⟩ i -
    exact ⟨⟨hdom.apply_last_le_apply hν.antitone i, hdom.apply_le_apply_zero hν.antitone i⟩,
      hν.exists_factorial_mul_eq_intCast i⟩

/-- **`B(GL_2, (1, 0))` has exactly two elements**: the ordinary class with slopes `(1, 0)` and the
basic class with slopes `(1/2, 1/2)`. -/
theorem admissibleNewtonVectors_one_zero :
    admissibleNewtonVectors ![1, 0] = {![1, 0], ![1 / 2, 1 / 2]} := by
  have hcard (ν : Fin 2 → ℚ) (i : Fin 2) :
      (#{j | ν j = ν i} : ℚ) = (if ν 0 = ν i then 1 else 0) + (if ν 1 = ν i then 1 else 0) := by
    rw [card_filter, Fin.sum_univ_two]
    push_cast [apply_ite (Nat.cast (R := ℚ))]
    simp
  ext ν
  simp only [mem_admissibleNewtonVectors, dominates_iff_fin_two, Set.mem_insert_iff,
    Set.mem_singleton_iff, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_zero]
  constructor
  · rintro ⟨hν, hsum, h0⟩
    have h10 : ν 1 ≤ ν 0 := hν.antitone (Fin.zero_le 1)
    rcases h10.lt_or_eq with hlt | heq
    · -- The slope `ν 0` has multiplicity one, so it is an integer in `[1/2, 1]`.
      obtain ⟨m, hm⟩ := hν.exists_card_mul_eq_intCast 0
      simp only [hcard, ↓reduceIte, hlt.ne, add_zero, one_mul] at hm
      have hm1 : m = 1 := by
        have hlo : (0 : ℚ) < m := by linarith
        have hhi : (m : ℚ) ≤ 1 := by linarith
        have : (0 : ℤ) < m := by exact_mod_cast hlo
        have : m ≤ (1 : ℤ) := by exact_mod_cast hhi
        omega
      left
      ext i
      fin_cases i
      · simp [hm, hm1]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hm, hm1] at hsum
        push_cast at hsum
        linarith
    · right
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]
        linarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
  · rintro (rfl | rfl)
    · refine ⟨⟨Fin.antitone_iff_succ_le.mpr fun i ↦ ?_, fun i ↦ ?_⟩, by simp, le_rfl⟩
      · fin_cases i
        simp
      · fin_cases i
        · exact ⟨1, by rw [hcard]; simp⟩
        · exact ⟨0, by simp⟩
    · refine ⟨⟨fun i j _ ↦ ?_, fun i ↦ ⟨1, ?_⟩⟩, by norm_num, by norm_num⟩
      · fin_cases i <;> fin_cases j <;> simp
      · rw [hcard]
        fin_cases i <;> norm_num

/-- **The basic class lies below the ordinary class** in `B(GL_2, (1, 0))`: the basic slopes
`(1/2, 1/2)` are dominated by the ordinary slopes `(1, 0)`. -/
theorem dominates_half_half_one_zero : Dominates (![1 / 2, 1 / 2] : Fin 2 → ℚ) ![1, 0] := by
  rw [dominates_iff_fin_two]
  norm_num

/-- **The ordinary class does not lie below the basic class** in `B(GL_2, (1, 0))`: the ordinary
slopes `(1, 0)` are not dominated by the basic slopes `(1/2, 1/2)`. Together with
`TauCeti.GeneralLinear.dominates_half_half_one_zero`, the basic class is strictly smaller. -/
theorem not_dominates_one_zero_half_half : ¬ Dominates (![1, 0] : Fin 2 → ℚ) ![1 / 2, 1 / 2] := by
  rw [dominates_iff_fin_two]
  norm_num

end TauCeti.GeneralLinear
