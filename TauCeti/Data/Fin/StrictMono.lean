/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Extending strictly monotone finite selections of naturals

A strictly monotone selection `k : Fin m → ℕ` of `m` natural numbers extends to a strictly
monotone self-map `φ : ℕ → ℕ` agreeing with `k` on the first `m` inputs. The extension can be
chosen to be an eventual translation, `φ n = n + C` for `m ≤ n`: past the selection it shifts by
a constant. That clause is what is needed when a reindexing of a sequence by `φ` must agree, past a
finite prefix, with a fixed iterate of the one-sided shift.

## Main results

* `StrictMono.exists_strictMono_nat_extending_fin_eventually_add`: the extension, as an eventual
  translation.
* `StrictMono.exists_strictMono_nat_extending_fin`: the extension, without the translation clause.

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
