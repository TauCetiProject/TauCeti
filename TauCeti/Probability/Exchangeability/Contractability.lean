module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype

/-!
# Contractability API

This file records basic lemmas for `Contractable` processes. The definitions live in
`TauCeti.Probability.Exchangeability.Basic`; this file is the Layer 0 home for
contractability-specific API.

The main result is `contractable_of_exchangeable` (with dot-notation form
`Exchangeable.contractable`): every exchangeable sequence with a.e. measurable coordinates is
contractable.

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

/-- A strictly increasing finite selection `k : Fin m → ℕ` whose values lie below `n` (with
`m ≤ n`) is realized by a permutation `σ` of `Fin n`: `(σ ⟨i, _⟩).val = k i` for every
`i : Fin m`. -/
private theorem exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin m,
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  -- thin wrapper over Mathlib's `Equiv.Perm.exists_extending_pair` (Cameron Freer, #34599)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hmn)
    (fun i => ⟨k i, hk_bound i⟩)
    (fun i j h => by
      apply Fin.val_injective
      exact (congrArg Fin.val h : (Fin.castLE hmn i).val = (Fin.castLE hmn j).val))
    (fun i j hij => hk.injective (Fin.mk.inj hij))
  exact ⟨σ, fun i => congrArg Fin.val (hσ i)⟩

/-- **Every exchangeable sequence with a.e. measurable coordinates is contractable**: along any
strictly increasing finite selection `k : Fin m → ℕ`, the block law `blockLaw μ X k` equals the
prefix law `prefixLaw μ X m`. One direction of the de Finetti–Ryll-Nardzewski equivalence. -/
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
      map_prefixLaw_castLE μ hmn (fun j => hX_meas j.val)
    have key := congrArg
      (Measure.map (fun x : Fin n → α => fun i : Fin (m' + 1) => x (Fin.castLE hmn i))) hexch
    rwa [hLHS, hRHS] at key

/-- Every exchangeable sequence with a.e. measurable coordinates is contractable (dot-notation
form of `contractable_of_exchangeable`). -/
theorem Exchangeable.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X :=
  contractable_of_exchangeable hX hX_meas

end Probability

end TauCeti
