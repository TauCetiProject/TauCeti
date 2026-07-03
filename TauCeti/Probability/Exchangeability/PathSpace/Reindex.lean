module

public import TauCeti.Probability.Exchangeability.Basic

/-!
# Permutation reindexing on path space

This file contains the bare path-space map induced by a permutation of time, together with
the ambient measurability and path-law pushforward lemmas used by Layer 0 exchangeability
bridges and by the exchangeable σ-algebra.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*}

/-- Reindex a one-sided path by a permutation of time. -/
abbrev permReindex (π : Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α :=
  fun n => x (π n)

/-- Coordinates of a permutation-reindexed path. -/
@[simp]
theorem permReindex_apply (π : Equiv.Perm ℕ) (x : ℕ → α) (n : ℕ) :
    permReindex π x n = x (π n) :=
  rfl

/-- Composition rule for time reindexing. -/
@[simp]
theorem permReindex_permReindex (π σ : Equiv.Perm ℕ) (x : ℕ → α) :
    permReindex (α := α) π (permReindex (α := α) σ x) =
      permReindex (α := α) (σ * π) x := by
  rfl

variable [MeasurableSpace Ω] [MeasurableSpace α]

omit [MeasurableSpace Ω] in
/-- Reindexing by a time permutation is measurable for the ambient path-space σ-algebra. -/
theorem measurable_permReindex (π : Equiv.Perm ℕ) :
    Measurable (permReindex (α := α) π) :=
  measurable_reindex π

/-- Pushing a path law forward by a time permutation gives the law of the reindexed process. -/
theorem map_permReindex_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (π : Equiv.Perm ℕ) :
    (pathLaw μ X).map (permReindex (α := α) π) =
      pathLaw μ (fun i ω => X (π i) ω) :=
  map_reindex_pathLaw μ hX π

end Probability

end TauCeti
