module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import TauCeti.Probability.Exchangeability.FiniteMarginals
import TauCeti.Probability.Exchangeability.Contractability
import Mathlib.Logic.Equiv.Fintype

/-!
# Full exchangeability and shift-preservation

The Layer 0 bridges between finite exchangeability, full exchangeability, and the shift dynamics
on path space:

* `exchangeable_iff_fullyExchangeable` — finite exchangeability (invariance under permutations of
  each `Fin n`) is equivalent to full exchangeability (invariance under all permutations of `ℕ`)
  for a measurable process under a finite measure.
* `FullyExchangeable.measurePreserving_shift` — a fully exchangeable process has a shift-invariant
  path law, the bridge from symmetry to the Koopman/ergodic lane.

Both bridges are thin: they reuse the merged Layer 0 API and Mathlib — finite-marginal uniqueness
(`FiniteMarginals`), the contractability bridge (`Contractability`), and
`Equiv.Perm.exists_extending_pair` — rather than new measure theory.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A permutation of `Fin n` is the restriction of some permutation of `ℕ`: there is `π : Perm ℕ`
with `π i = σ i` on `{0, …, n-1}`. Thin wrapper over `Equiv.Perm.exists_extending_pair`. -/
private theorem exists_perm_nat_extending {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ π : Equiv.Perm ℕ, ∀ i : Fin n, π i.val = (σ i).val :=
  Equiv.Perm.exists_extending_pair (fun i : Fin n => i.val) (fun i => (σ i).val)
    Fin.val_injective (fun _ _ h => σ.injective (Fin.val_injective h))

/-- **Full exchangeability implies finite exchangeability at every dimension.** Extend the `Fin n`
permutation to one of `ℕ`, apply full invariance, and project to the first `n` coordinates. -/
theorem FullyExchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) (n : ℕ) :
    ExchangeableAt μ X n := by
  intro σ
  obtain ⟨π, hπ⟩ := exists_perm_nat_extending σ
  have hLHS : (μ.map fun ω i => X (π i) ω).map (prefixProj α n)
      = blockLaw μ X (fun j : Fin n => π j.val) := by
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable
      (aemeasurable_pi_lambda _ fun i => hX_meas (π i))]
    rfl
  have hidx : (fun j : Fin n => π j.val) = fun j : Fin n => (σ j).val := by
    funext j; exact hπ j
  calc blockLaw μ X (fun j : Fin n => (σ j).val)
      = blockLaw μ X (fun j : Fin n => π j.val) := by rw [hidx]
    _ = (μ.map fun ω i => X (π i) ω).map (prefixProj α n) := hLHS.symm
    _ = (pathLaw μ X).map (prefixProj α n) := by rw [hX π]
    _ = prefixLaw μ X n := map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n

/-- **Full exchangeability implies finite exchangeability.** -/
theorem FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Exchangeable μ X :=
  fun n => hX.exchangeableAt hX_meas n

/-- **An exchangeable process has the prefix law along any injective finite selection.** Extend the
injective `k : Fin n → ℕ` to a permutation of a large enough `Fin N` and project, exactly as in
`contractable_of_exchangeable` but with `Equiv.Perm.exists_extending_pair` (no monotonicity). -/
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

/-- **Finite exchangeability implies full exchangeability** (finite law, measurable process). For
each `π`, the reindexed path law and the path law agree on every prefix marginal (the reindexed
block is an injective selection, so its law is the prefix law); finite-marginal uniqueness lifts
this to the whole path law. -/
theorem Exchangeable.fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : FullyExchangeable μ X := by
  intro π
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  have hLmar : (μ.map fun ω i => X (π i) ω).map (prefixProj α n)
      = blockLaw μ X (fun j : Fin n => π j.val) := by
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable
      (aemeasurable_pi_lambda _ fun i => hX_meas (π i))]
    rfl
  have hRmar : (pathLaw μ X).map (prefixProj α n) = prefixLaw μ X n :=
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n
  have hblock : blockLaw μ X (fun j : Fin n => π j.val) = prefixLaw μ X n :=
    hX.blockLaw_eq_prefixLaw_of_injective hX_meas _
      (fun _ _ h => Fin.val_injective (π.injective h))
  rw [hLmar, hRmar, hblock]

/-- **Finite exchangeability ↔ full exchangeability** for a measurable process under a finite
measure. -/
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX_meas : ∀ i, AEMeasurable (X i) μ) : Exchangeable μ X ↔ FullyExchangeable μ X :=
  ⟨fun h => h.fullyExchangeable hX_meas, fun h => h.exchangeable hX_meas⟩

/-- Projecting the shifted path law onto its first `n` coordinates gives the law of the block
`(X 1, …, X n)`. -/
private theorem map_shift_prefixProj_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (n : ℕ) :
    ((pathLaw μ X).map (shift α)).map (prefixProj α n)
      = blockLaw μ X (fun i : Fin n => i.val + 1) := by
  rw [pathLaw_apply,
    AEMeasurable.map_map_of_aemeasurable measurable_shift.aemeasurable
      (aemeasurable_pi_lambda _ hX_meas),
    AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable
      (measurable_shift.comp_aemeasurable (aemeasurable_pi_lambda _ hX_meas))]
  rfl

/-- **A fully exchangeable process has a shift-invariant path law.** The bridge from symmetry to the
shift dynamics: `shift` preserves `pathLaw μ X`. -/
theorem FullyExchangeable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) := by
  have hcontr : Contractable μ X := contractable_of_exchangeable (hX.exchangeable hX_meas) hX_meas
  refine ⟨measurable_shift, ?_⟩
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_apply]; infer_instance
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  rw [map_shift_prefixProj_pathLaw hX_meas n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n]
  exact hcontr n (fun i : Fin n => i.val + 1) (fun _ _ h => Nat.add_lt_add_right h 1)

end Probability

end TauCeti
