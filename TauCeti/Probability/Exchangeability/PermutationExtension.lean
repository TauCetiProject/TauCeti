module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Permutation extensions for finite exchangeability

This file records the finite combinatorial extension lemmas used in the Layer 0
exchangeability API.  A finite injective or strictly monotone coordinate selection can be
completed to a permutation of the ambient finite prefix, and a strictly increasing finite
subsequence can be extended to a strictly increasing self-map of `ℕ`.

These lemmas discharge the `exists_perm_extending_strictMono` / finite-extension
prerequisite named in `TauCetiRoadmap/Exchangeability/README.md`, Layer 0.  The finite
permutation proofs are thin specializations of Mathlib's
`Equiv.Perm.exists_extending_pair`; the `ℕ` extension is the order-preserving tail
completion used to bridge finite contractability to path-law reindexing.
-/

public section

namespace TauCeti

namespace Probability

/-- An injective map `k : Fin m → Fin n` extends across the canonical inclusion
`Fin.castLE hmn` to a permutation of `Fin n`. -/
theorem exists_perm_extending_castLE {m n : ℕ} (hmn : m ≤ n)
    (k : Fin m → Fin n) (hk : Function.Injective k) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i : Fin m, σ (Fin.castLE hmn i) = k i :=
  Equiv.Perm.exists_extending_pair (Fin.castLE hmn) k
    (fun _ _ h => Fin.castLE_injective hmn h)
    hk

/-- A strictly monotone map `k : Fin m → Fin n` extends across the canonical inclusion
`Fin.castLE hmn` to a permutation of `Fin n`.  This is the finite permutation-extension
form used when a contractable subsequence sits inside a longer prefix. -/
theorem exists_perm_extending_strictMono {m n : ℕ} (hmn : m ≤ n)
    (k : Fin m → Fin n) (hk : StrictMono k) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i : Fin m, σ (Fin.castLE hmn i) = k i :=
  exists_perm_extending_castLE hmn k hk.injective

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

/-- A permutation of `Fin n` is the restriction of some permutation of `ℕ`: there is
`π : Equiv.Perm ℕ` with `π i = σ i` on the first `n` coordinates.  This is the finite
approximation step used when passing from path-law invariance to finite exchangeability. -/
theorem exists_perm_nat_extending_fin {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ π : Equiv.Perm ℕ, ∀ i : Fin n, π i.val = (σ i).val :=
  Equiv.Perm.exists_extending_pair (fun i : Fin n => i.val) (fun i => (σ i).val)
    Fin.val_injective (fun _ _ h => σ.injective (Fin.val_injective h))

end Probability

end TauCeti
