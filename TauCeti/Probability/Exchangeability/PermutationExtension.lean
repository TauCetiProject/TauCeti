module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Permutation extensions for finite exchangeability

This file records the combinatorial extension lemma used in the Layer 0
exchangeability API. A strictly increasing finite subsequence can be extended to a
strictly increasing self-map of `ℕ`.

This lemma discharges the finite-extension prerequisite named in
`TauCetiRoadmap/Exchangeability/README.md`, Layer 0. The extension is the
order-preserving tail completion used to bridge finite contractability to path-law
reindexing.
-/

public section

namespace TauCeti

namespace Probability

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
