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
  for a process with a.e. measurable coordinates under a finite measure.
* `FullyExchangeable.measurePreserving_shift` — a fully exchangeable process has a shift-invariant
  path law, the bridge from symmetry to the Koopman/ergodic lane.

Both bridges are thin: they reuse the merged Layer 0 API and Mathlib — finite-marginal uniqueness
(`FiniteMarginals`), the contractability bridge (`Contractability`), and
`Equiv.Perm.exists_extending_pair` — rather than new measure theory.

These declarations are adapted from the `cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
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

/-- The first-`n` prefix marginal of the `π`-reindexed path law is the block law along the
selection `j ↦ π j`. -/
private theorem map_reindex_prefixProj {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (π : Equiv.Perm ℕ) (n : ℕ) :
    (μ.map fun ω i => X (π i) ω).map (prefixProj α n)
      = blockLaw μ X (fun j : Fin n => π j.val) := by
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable
    (aemeasurable_pi_lambda _ fun i => hX_meas (π i))]
  rfl

/-- **Full exchangeability implies finite exchangeability at each dimension `n`.** -/
theorem FullyExchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) (n : ℕ) :
    ExchangeableAt μ X n := by
  intro σ
  obtain ⟨π, hπ⟩ := exists_perm_nat_extending σ
  have hidx : (fun j : Fin n => π j.val) = fun j : Fin n => (σ j).val := by
    funext j; exact hπ j
  calc blockLaw μ X (fun j : Fin n => (σ j).val)
      = blockLaw μ X (fun j : Fin n => π j.val) := by rw [hidx]
    _ = (μ.map fun ω i => X (π i) ω).map (prefixProj α n) :=
        (map_reindex_prefixProj hX_meas π n).symm
    _ = (pathLaw μ X).map (prefixProj α n) := by rw [hX π]
    _ = prefixLaw μ X n := map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n

/-- **Full exchangeability implies finite exchangeability.** -/
theorem FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Exchangeable μ X :=
  fun n => hX.exchangeableAt hX_meas n

/-- **Finite exchangeability implies full exchangeability** for a finite law with a.e. measurable
coordinates: the path law is invariant under every permutation of `ℕ`. -/
theorem Exchangeable.fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : FullyExchangeable μ X := by
  intro π
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  rw [map_reindex_prefixProj hX_meas π n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n]
  exact Exchangeable.blockLaw_eq_prefixLaw_of_injective hX hX_meas _
    (fun _ _ h => Fin.val_injective (π.injective h))

/-- **Finite exchangeability ↔ full exchangeability** for a process with a.e. measurable
coordinates under a finite measure. -/
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX_meas : ∀ i, AEMeasurable (X i) μ) : Exchangeable μ X ↔ FullyExchangeable μ X :=
  ⟨fun h => h.fullyExchangeable hX_meas, fun h => h.exchangeable hX_meas⟩

/-- **A fully exchangeable process has a shift-invariant path law** — the Layer 0 shift-preservation
bridge. -/
theorem FullyExchangeable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) := by
  have hc : Contractable μ X := contractable_of_exchangeable (hX.exchangeable hX_meas) hX_meas
  exact Contractable.measurePreserving_shift hc hX_meas

end Probability

end TauCeti
