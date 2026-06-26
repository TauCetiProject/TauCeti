module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype

/-!
# Contractability API

This file records basic lemmas for `Contractable` processes. The definitions live in
`TauCeti.Probability.Exchangeability.Basic`; this file is the Layer 0 home for
contractability-specific API.

It also provides `map_blockLaw_reindex`, the coordinate-reindexing pushforward of block laws
(the companion of `Basic`'s value-reindexing `map_blockLaw`), used here to project
finite-dimensional laws onto sub-blocks.

The main result is `contractable_of_exchangeable` (with dot-notation form
`Exchangeable.contractable`): every exchangeable sequence is contractable. The proof realizes a
strictly increasing finite selection as the first coordinates of a permutation of a large enough
`Fin n` (`exists_perm_extending_strictMono`, a thin wrapper around Mathlib's
`Equiv.Perm.exists_extending_pair`), applies exchangeability at that dimension, and projects back
to the chosen sub-block.

These declarations are adapted from the `cameronfreer/exchangeability` Layer 0 sources pinned
at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses; the
combinatorial core is Mathlib's `Equiv.Perm.exists_extending_pair` (Cameron Freer, Mathlib
#34599).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A contractable process has the same finite-dimensional block law as the corresponding
prefix law along any strictly increasing finite index map. -/
theorem Contractable.map {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    blockLaw μ X k = prefixLaw μ X m :=
  h m k hk

/-- The one-coordinate specialization of contractability. -/
theorem Contractable.map_single {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    (k : Fin 1 → ℕ) :
    blockLaw μ X k = prefixLaw μ X 1 := by
  exact h.map (by
    intro i j hij
    fin_cases i
    fin_cases j
    omega)

/-- The two-coordinate specialization of contractability. -/
theorem Contractable.map_pair {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {i j : ℕ} (hij : i < j) :
    blockLaw μ X (fun r : Fin 2 => if r = 0 then i else j) = prefixLaw μ X 2 := by
  refine h.map ?_
  intro r s hrs
  fin_cases r <;> fin_cases s <;> simp_all

/-- Contractability is preserved by passing to a strictly increasing subsequence. -/
theorem Contractable.comp {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Contractable μ (fun n ω => X (φ n) ω) := by
  intro m k hk
  calc
    blockLaw μ (fun n ω => X (φ n) ω) k =
        blockLaw μ X (φ ∘ k) := rfl
    _ = prefixLaw μ X m := h.map (hφ.comp hk)
    _ = blockLaw μ (fun n ω => X (φ n) ω) (fun i : Fin m => i.val) := by
      exact (h.map (hφ.comp (Fin.val_strictMono : StrictMono (fun i : Fin m => i.val)))).symm
    _ = prefixLaw μ (fun n ω => X (φ n) ω) m := rfl

/-- For a contractable process, any two strictly increasing selections of the same length have
the same block law. -/
theorem Contractable.allStrictMono_eq {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {m : ℕ} {k₁ k₂ : Fin m → ℕ} (hk₁ : StrictMono k₁) (hk₂ : StrictMono k₂) :
    blockLaw μ X k₁ = blockLaw μ X k₂ :=
  (h.map hk₁).trans (h.map hk₂).symm

/-- For a contractable process, every length-`m` consecutive block starting at `c`, namely
`(X c, X (c+1), …, X (c+m-1))`, has the prefix law. -/
theorem Contractable.shift_segment_eq {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    (m c : ℕ) :
    blockLaw μ X (fun i : Fin m => c + i.val) = prefixLaw μ X m :=
  h.map fun _ _ hij => Nat.add_lt_add_left hij c

/-- For a contractable process, a strictly increasing selection shifted by an offset `c` has the
prefix law. -/
theorem Contractable.shift_and_select {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {m : ℕ} (k : Fin m → ℕ) (c : ℕ) (hk : StrictMono k) :
    blockLaw μ X (fun i => c + k i) = prefixLaw μ X m :=
  h.map fun _ _ hij => Nat.add_lt_add_left (hk hij) c

/-- For a contractable process, a strictly increasing selection of coordinates from `Fin n` has
the prefix law. -/
theorem Contractable.restrict {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {n m : ℕ} (k : Fin m → Fin n) (hk : StrictMono k) :
    blockLaw μ X (fun i => (k i).val) = prefixLaw μ X m :=
  h.map fun _ _ hij => hk hij

/-- Any strictly increasing finite selection extends to a permutation of a large enough `Fin n`:
given `k : Fin m → ℕ` strictly increasing with every value `< n` and `m ≤ n`, there is a
permutation `σ` of `Fin n` with `(σ ⟨i, _⟩).val = k i` for every `i : Fin m`.

This is a thin wrapper around Mathlib's `Equiv.Perm.exists_extending_pair` (Cameron Freer,
Mathlib #34599), applied to the initial-segment inclusion `Fin.castLE hmn` and the strictly
monotone embedding `i ↦ ⟨k i, _⟩`, both injective. -/
theorem exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m,
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hmn)
    (fun i => ⟨k i, hk_bound i⟩)
    (fun i j h => by
      apply Fin.val_injective
      exact (congrArg Fin.val h : (Fin.castLE hmn i).val = (Fin.castLE hmn j).val))
    (fun i j hij => hk.injective (Fin.mk.inj hij))
  exact ⟨σ, fun i => congrArg Fin.val (hσ i)⟩

/-- **Every exchangeable sequence is contractable.** Along any strictly increasing finite
selection `k : Fin m → ℕ`, the block law equals the prefix law.

The proof extends `k` to a permutation `σ` of a large enough `Fin n`
(`exists_perm_extending_strictMono`), invokes exchangeability at dimension `n`, and projects both
laws onto the first `m` coordinates with `map_blockLaw_reindex`. -/
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X := by
  intro m k hk
  cases m with
  | zero =>
    rw [blockLaw_apply, prefixLaw_apply, blockLaw_apply]
    congr 1
    funext ω i
    exact i.elim0
  | succ m' =>
    set n := max (m' + 1) (k (Fin.last m') + 1) with hn
    have hmn : m' + 1 ≤ n := le_max_left _ _
    have hk_bound : ∀ i, k i < n := by
      intro i
      have h₁ : k i ≤ k (Fin.last m') := hk.monotone (Fin.le_last i)
      omega
    obtain ⟨σ, hσ⟩ := exists_perm_extending_strictMono k hk hk_bound hmn
    have hexch : blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n :=
      (hX.exchangeableAt n).permute σ
    have hLHS : (blockLaw μ X (fun i : Fin n => (σ i).val)).map
          (fun x : Fin n → α => fun i : Fin (m' + 1) => x (Fin.castLE hmn i)) = blockLaw μ X k := by
      have hidx : (fun i : Fin n => (σ i).val) ∘ Fin.castLE hmn = k := by
        funext i; exact hσ i
      rw [map_blockLaw_reindex μ _ (Fin.castLE hmn) (fun j => hX_meas (σ j).val), hidx]
    have hRHS : (prefixLaw μ X n).map
          (fun x : Fin n → α => fun i : Fin (m' + 1) => x (Fin.castLE hmn i)) =
            prefixLaw μ X (m' + 1) :=
      map_prefixLaw_castLE μ hmn hX_meas
    have key := congrArg
      (Measure.map (fun x : Fin n → α => fun i : Fin (m' + 1) => x (Fin.castLE hmn i))) hexch
    rwa [hLHS, hRHS] at key

/-- Every exchangeable sequence is contractable (dot-notation form of
`contractable_of_exchangeable`). -/
theorem Exchangeable.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X :=
  contractable_of_exchangeable hX hX_meas

end Probability

end TauCeti
