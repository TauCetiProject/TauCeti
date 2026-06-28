module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Logic.Equiv.Fintype
import TauCeti.Probability.Exchangeability.FiniteMarginals

/-!
# Contractability API

This file records basic lemmas for `Contractable` processes. The definitions live in
`TauCeti.Probability.Exchangeability.Basic`; this file is the Layer 0 home for
contractability-specific API.

The main result is `contractable_of_exchangeable` (with dot-notation form
`Exchangeable.contractable`): every exchangeable sequence with a.e. measurable coordinates is
contractable. The file also provides `Exchangeable.blockLaw_eq_prefixLaw_of_injective` (the
injective-selection analogue) and `Contractable.measurePreserving_reindex` /
`Contractable.measurePreserving_shift` (a contractable path law is invariant under strictly monotone
time-reindexing, in particular the shift).

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

/-- **An exchangeable sequence has the prefix law along any injective finite selection:**
`blockLaw μ X k = prefixLaw μ X n` for injective `k : Fin n → ℕ`. -/
theorem Exchangeable.blockLaw_eq_prefixLaw_of_injective {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {n : ℕ} (k : Fin n → ℕ) (hk : Function.Injective k) :
    blockLaw μ X k = prefixLaw μ X n := by
  cases n with
  | zero =>
    rw [blockLaw_apply, prefixLaw_apply, blockLaw_apply]
    congr 1
    funext ω i
    exact i.elim0
  | succ m =>
    set N := max (m + 1) (Finset.univ.sup k + 1) with hN
    have hnN : m + 1 ≤ N := le_max_left _ _
    have hk_bound : ∀ i, k i < N := by
      intro i
      have h1 : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
      have h2 : Finset.univ.sup k + 1 ≤ N := le_max_right _ _
      omega
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hnN)
      (fun i => (⟨k i, hk_bound i⟩ : Fin N))
      (fun a b h => by
        apply Fin.val_injective
        exact (congrArg Fin.val h : (Fin.castLE hnN a).val = (Fin.castLE hnN b).val))
      (fun _ _ h => hk (Fin.mk.inj h))
    have hexch : blockLaw μ X (fun j : Fin N => (σ j).val) = prefixLaw μ X N :=
      (hX.exchangeableAt N).permute σ
    have hLHS : (blockLaw μ X (fun j : Fin N => (σ j).val)).map
          (fun x : Fin N → α => fun i : Fin (m + 1) => x (Fin.castLE hnN i)) = blockLaw μ X k := by
      have hidx : (fun j : Fin N => (σ j).val) ∘ Fin.castLE hnN = k := by
        funext i; exact congrArg Fin.val (hσ i)
      rw [map_blockLaw_reindex μ _ (Fin.castLE hnN) (fun j => hX_meas (σ j).val), hidx]
    have hRHS : (prefixLaw μ X N).map (fun x : Fin N → α => fun i : Fin (m + 1) =>
          x (Fin.castLE hnN i)) = prefixLaw μ X (m + 1) :=
      map_prefixLaw_castLE μ hnN (fun j => hX_meas j.val)
    have key := congrArg
      (Measure.map (fun x : Fin N → α => fun i : Fin (m + 1) => x (Fin.castLE hnN i))) hexch
    rwa [hLHS, hRHS] at key

/-- **Every exchangeable sequence with a.e. measurable coordinates is contractable**: along any
strictly increasing finite selection `k`, `blockLaw μ X k = prefixLaw μ X m`. One direction of the
de Finetti–Ryll-Nardzewski equivalence. -/
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X :=
  fun _ k hk => Exchangeable.blockLaw_eq_prefixLaw_of_injective hX hX_meas k hk.injective

/-- Every exchangeable sequence with a.e. measurable coordinates is contractable (dot-notation
form of `contractable_of_exchangeable`). -/
theorem Exchangeable.contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Contractable μ X :=
  contractable_of_exchangeable hX hX_meas

/-- Projecting the `φ`-reindexed path law onto its first `n` coordinates gives the law of the block
`(X (φ 0), …, X (φ (n-1)))`. -/
private theorem map_reindex_prefixProj_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) (n : ℕ) :
    ((pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k))).map (prefixProj α n)
      = blockLaw μ X (fun i : Fin n => φ i.val) := by
  have hφ_meas : Measurable (fun x : ℕ → α => fun k => x (φ k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (φ k)
  rw [pathLaw_apply,
    AEMeasurable.map_map_of_aemeasurable hφ_meas.aemeasurable
      (aemeasurable_pi_lambda _ hX_meas),
    AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable
      (hφ_meas.comp_aemeasurable (aemeasurable_pi_lambda _ hX_meas))]
  rfl

/-- **A contractable process's path law is invariant under strictly monotone time-reindexing:** for
`StrictMono φ`, the reindexing `x ↦ x ∘ φ` preserves `pathLaw μ X`. -/
theorem Contractable.measurePreserving_reindex {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) (pathLaw μ X) (pathLaw μ X) := by
  refine ⟨measurable_pi_lambda _ fun k => measurable_pi_apply (φ k), ?_⟩
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_apply]; infer_instance
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  rw [map_reindex_prefixProj_pathLaw hX_meas φ n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n]
  exact hX n (fun i : Fin n => φ i.val) (hφ.comp Fin.val_strictMono)

/-- **A contractable process has a shift-invariant path law:** `shift` preserves `pathLaw μ X`. -/
theorem Contractable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) :=
  Contractable.measurePreserving_reindex hX hX_meas (φ := fun k => k + 1)
    (fun _ _ h => Nat.add_lt_add_right h 1)

end Probability

end TauCeti
