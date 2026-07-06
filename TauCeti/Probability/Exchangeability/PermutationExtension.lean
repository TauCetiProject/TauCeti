module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Permutation extensions for finite exchangeability

This file records the combinatorial extension lemmas used in the Layer 0
exchangeability API:

* injective finite selections extend to permutations of a finite prefix;
* strictly monotone finite selections have the named finite-permutation wrapper;
* injective finite selections of `ℕ` extend to permutations of `ℕ`;
* strictly increasing finite subsequences extend to strictly increasing self-maps of `ℕ`.

These declarations discharge the finite-extension prerequisites named in
`TauCetiRoadmap/Exchangeability/README.md`, Layer 0. They are adapted from the
`cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses; the
finite-permutation wrappers are thin wrappers around Mathlib's
`Equiv.Perm.exists_extending_pair`.
-/

public section

namespace TauCeti

namespace Probability

/-- An injective selection `k : Fin m → Fin n` extends to a permutation of `Fin n`, agreeing
with `k` on the first `m` coordinates embedded by `Fin.castLE hmn`. -/
theorem exists_perm_extending_castLE {m n : ℕ} (hmn : m ≤ n) (k : Fin m → Fin n)
    (hk : Function.Injective k) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m, σ (Fin.castLE hmn i) = k i :=
  Equiv.Perm.exists_extending_pair (Fin.castLE hmn) k
    (fun _ _ h => Fin.castLE_injective hmn h) hk

/-- A strictly monotone selection `k : Fin m → Fin n` extends to a permutation of `Fin n`,
agreeing with `k` on the first `m` coordinates embedded by `Fin.castLE hmn`. -/
theorem exists_perm_extending_strictMono {m n : ℕ} (hmn : m ≤ n) (k : Fin m → Fin n)
    (hk : StrictMono k) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m, σ (Fin.castLE hmn i) = k i :=
  exists_perm_extending_castLE hmn k hk.injective

/-- An injective finite selection of `ℕ` extends to a permutation of `ℕ`, agreeing with the
selection on the first `n` natural numbers. -/
theorem exists_perm_nat_extending {n : ℕ} (k : Fin n → ℕ) (hk : Function.Injective k) :
    ∃ π : Equiv.Perm ℕ, ∀ i : Fin n, π i.val = k i :=
  Equiv.Perm.exists_extending_pair (fun i : Fin n => i.val) k Fin.val_injective hk

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing
self-map of `ℕ`.  The extension agrees with `k` on the first `m` inputs and then follows
the identity shifted above the finite range of `k`. -/
theorem exists_strictMono_nat_extending_fin {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i : Fin m, φ i.val = k i := by
  classical
  let C := Finset.univ.sup k + 1
  let φ : ℕ → ℕ := fun n => if h : n < m then k ⟨n, h⟩ else n + C
  refine ⟨φ, ?_, ?_⟩
  · intro a b hab
    dsimp only [φ]
    by_cases ha : a < m
    · by_cases hb : b < m
      · rw [dif_pos ha, dif_pos hb]
        exact hk (Fin.lt_def.mpr hab)
      · rw [dif_pos ha, dif_neg hb]
        have hle_sup : k ⟨a, ha⟩ ≤ Finset.univ.sup k :=
          Finset.le_sup (f := k) (Finset.mem_univ (⟨a, ha⟩ : Fin m))
        exact (Nat.lt_succ_of_le hle_sup).trans_le (Nat.le_add_left C b)
    · by_cases hb : b < m
      · exact (ha (hab.trans hb)).elim
      · rw [dif_neg ha, dif_neg hb]
        exact Nat.add_lt_add_right hab C
  · intro i
    simp [φ, i.isLt]

end Probability

end TauCeti
