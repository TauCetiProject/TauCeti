/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import TauCeti.Data.Fin.StrictAnti

/-!
# Strictly monotone finite selections of naturals

A strictly monotone selection `k : Fin m → ℕ` of `m` natural numbers extends to a strictly
monotone self-map `φ : ℕ → ℕ` agreeing with `k` on the first `m` inputs. The extension can be
chosen to be an eventual translation, `φ n = n + C` for `m ≤ n`: past the selection it shifts by
a constant. That clause is what is needed when a reindexing of a sequence by `φ` must agree, past a
finite prefix, with a fixed iterate of the one-sided shift.

A strictly monotone sequence of naturals indexed by `Fin m` grows by at least the index gap. This
is deduced from its decreasing counterpart `StrictAnti.add_sub_le_nat` by reversing the indices.
Consequently, for a strictly increasing `p : Fin r → Fin n`, the complementary gaps
`n - r + i - p i` are antitone in `i`, and summed together with the gaps `p i - i` they give
`r (n - r)`.

## Main results

* `StrictMono.exists_strictMono_nat_extending_fin_eventually_add`: the extension, as an eventual
  translation.
* `StrictMono.exists_strictMono_nat_extending_fin`: the extension, without the translation clause.
* `StrictMono.add_sub_le_nat`: a strictly monotone sequence of naturals grows by at least the index
  gap; the increasing counterpart of `StrictAnti.add_sub_le_nat`.
* `StrictMono.antitone_sub_sub`, `StrictMono.sum_sub_add_sum_sub_eq_mul`: for `p : Fin r → Fin n`
  strictly increasing, `n - r + i - p i` is antitone in `i` and
  `∑ i, (p i - i) + ∑ i, (n - r + i - p i) = r (n - r)`.

The extension is adapted from `cameronfreer/exchangeability`, pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`.
-/

public section

variable {m : ℕ} {k : Fin m → ℕ}

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing self-map
of `ℕ` that agrees with `k` on the first `m` inputs and is **eventually a translation**: beyond the
selection it adds a fixed constant `C`. -/
theorem StrictMono.exists_strictMono_nat_extending_fin_eventually_add (hk : StrictMono k) :
    ∃ (φ : ℕ → ℕ) (C : ℕ), StrictMono φ ∧ (∀ i : Fin m, φ i.val = k i) ∧
      ∀ n, m ≤ n → φ n = n + C := by
  let C := Finset.univ.sup k + 1
  let φ : ℕ → ℕ := fun n => if h : n < m then k ⟨n, h⟩ else n + C
  refine ⟨φ, C, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only [φ]
    by_cases ha : a < m
    · by_cases hb : b < m
      · rw [dite_eq_left ha, dite_eq_left hb]
        exact hk (Fin.lt_def.mpr hab)
      · rw [dite_eq_left ha, dite_eq_right hb]
        have hle_sup : k ⟨a, ha⟩ ≤ Finset.univ.sup k :=
          Finset.le_sup (f := k) (Finset.mem_univ (⟨a, ha⟩ : Fin m))
        exact (Nat.lt_succ_of_le hle_sup).trans_le (Nat.le_add_left C b)
    · by_cases hb : b < m
      · exact (ha (hab.trans hb)).elim
      · rw [dite_eq_right ha, dite_eq_right hb]
        exact Nat.add_lt_add_right hab C
  · intro i
    simp [φ, i.isLt]
  · intro n hn
    simp [φ, Nat.not_lt.mpr hn]

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing
self-map of `ℕ` that agrees with `k` on the first `m` inputs.

`StrictMono.exists_strictMono_nat_extending_fin_eventually_add` additionally records that the
extension is eventually a translation. -/
theorem StrictMono.exists_strictMono_nat_extending_fin (hk : StrictMono k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i : Fin m, φ i.val = k i :=
  let ⟨φ, _, hφ, hφ_eq, _⟩ := hk.exists_strictMono_nat_extending_fin_eventually_add
  ⟨φ, hφ, hφ_eq⟩

/-- **A strictly monotone sequence of naturals grows by at least the index gap**: it gains at least
one unit at each step, hence at least `j - i` units between the indices `i ≤ j`. -/
theorem StrictMono.add_sub_le_nat {η : Fin m → ℕ} (hη : StrictMono η) {i j : Fin m}
    (hij : i ≤ j) : η i + ((j : ℕ) - (i : ℕ)) ≤ η j := by
  have h := (hη.comp_strictAnti Fin.rev_strictAnti).add_sub_le_nat (Fin.rev_le_rev.mpr hij)
  have := Fin.le_def.mp hij
  have := j.isLt
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev] at h
  omega

namespace StrictMono

variable {n r : ℕ} {p : Fin r → Fin n}

/-- For a strictly increasing `p : Fin r → Fin n`, the sequence `n - r + i - p i` is antitone,
since `p` grows by at least the index gap (`StrictMono.add_sub_le_nat`). -/
theorem antitone_sub_sub (hp : StrictMono p) : Antitone fun i : Fin r ↦ n - r + i - p i := by
  intro i k hik
  have := (Fin.val_strictMono.comp hp).add_sub_le_nat hik
  have := Fin.le_def.mp hik
  simp only [Function.comp_apply] at *
  omega

/-- For a strictly increasing `p : Fin r → Fin n`, the gaps `p i - i` and the complementary gaps
`n - r + i - p i` add up to `n - r` at each index, hence to `r (n - r)` in total. -/
theorem sum_sub_add_sum_sub_eq_mul (hp : StrictMono p) :
    ∑ i, ((p i : ℕ) - i) + ∑ i, (n - r + i - p i) = r * (n - r) := by
  have hp' := Fin.val_strictMono.comp hp
  have h (i : Fin r) : (p i : ℕ) - i + (n - r + i - p i) = n - r := by
    have h₀ := hp'.add_sub_le_nat (Fin.le_def.mpr (Nat.zero_le i) : (⟨0, i.pos⟩ : Fin r) ≤ i)
    have h₁ := hp'.add_sub_le_nat (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.isLt) :
      i ≤ ⟨r - 1, by omega⟩)
    have := (p ⟨r - 1, by omega⟩).isLt
    simp only [Function.comp_apply] at h₀ h₁
    omega
  simp [← Finset.sum_add_distrib, h]

end StrictMono
