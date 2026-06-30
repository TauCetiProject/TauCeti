module

public import TauCeti.Probability.Exchangeability.Contractability

/-!
# Pair-law equality from contractability

`Contractable.pairLaw_eq`: for a contractable process `X` and `k ≤ m`, the joint law of the
coordinate `X m` with the future tail `(X (m+1), X (m+2), …)` equals the joint law of `X k` with the
**same** tail:
```
μ.map (fun ω => (X m ω, fun n => X (m + 1 + n) ω))
  = μ.map (fun ω => (X k ω, fun n => X (m + 1 + n) ω)).
```

This is the distributional input the de Finetti block-product factorisation feeds to
`condExp_indicator_eq_of_pair_law_eq` (the pair-law → conditional-expectation bridge): it lets the
per-coordinate conditional law of `X 0` given the tail be transported to every `X m`.

## Note on the proof

The reference derives this through a bespoke rectangle **π-system** on `α × (ℕ → α)` (building
cylinders, proving `IsPiSystem`, and re-deriving that cylinders generate the product σ-algebra —
~185 lines of generic measure theory). Here it is a short consequence of the existing TauCeti
contractability API: a head/tail split composed with two strictly-monotone time-reindexings
collapses *both* sides to the single measure `(pathLaw μ X).map headTail` via
`Contractable.measurePreserving_reindex` and `map_reindex_pathLaw`. No cylinders, no π-system, and
it needs only `[IsFiniteMeasure μ]` — strictly weaker than the reference's
`[IsProbabilityMeasure μ]` and `[StandardBorelSpace α]`.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/FutureRectangles.lean`,
`contractable_dist_eq`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Pair-law equality from contractability.** For a contractable process and `k ≤ m`, the joint
law of `X m` with the future tail `(X (m+1), X (m+2), …)` equals the joint law of `X k` with the
same tail. -/
theorem Contractable.pairLaw_eq {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {k m : ℕ} (hk : k ≤ m) :
    μ.map (fun ω => (X m ω, fun n => X (m + 1 + n) ω))
      = μ.map (fun ω => (X k ω, fun n => X (m + 1 + n) ω)) := by
  classical
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  -- The head/tail split on path space.
  let headTail : (ℕ → α) → α × (ℕ → α) := fun f => (f 0, fun n => f (n + 1))
  have hheadTail_meas : Measurable headTail :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1))
  -- Strictly-monotone time-reindexing preserves the path law of a contractable process.
  have hreindex : ∀ φ : ℕ → ℕ, StrictMono φ →
      μ.map (fun ω (i : ℕ) => X (φ i) ω) = pathLaw μ X := by
    intro φ hφ
    calc μ.map (fun ω (i : ℕ) => X (φ i) ω)
        = (pathLaw μ X).map (fun x : ℕ → α => fun j => x (φ j)) :=
          (map_reindex_pathLaw μ hX_ae φ).symm
      _ = pathLaw μ X := (hX.measurePreserving_reindex hX_ae hφ).map_eq
  -- For a selection `φ` whose head is `j` and whose successors enumerate the tail, the joint law
  -- of `(X j, tail)` collapses to `(pathLaw μ X).map headTail`.
  have side : ∀ (j : ℕ) (φ : ℕ → ℕ), StrictMono φ → φ 0 = j → (∀ n, φ (n + 1) = m + 1 + n) →
      μ.map (fun ω => (X j ω, fun n => X (m + 1 + n) ω)) = (pathLaw μ X).map headTail := by
    intro j φ hφ hφ0 hφsucc
    have hpath_meas : Measurable (fun ω (i : ℕ) => X (φ i) ω) :=
      measurable_pi_lambda _ fun i => hX_meas (φ i)
    have hfun : (fun ω => (X j ω, fun n => X (m + 1 + n) ω))
        = headTail ∘ (fun ω (i : ℕ) => X (φ i) ω) := by
      funext ω
      simp only [headTail, Function.comp_apply, hφ0]
      congr 1
      funext n
      rw [hφsucc n]
    rw [hfun, ← Measure.map_map hheadTail_meas hpath_meas, hreindex φ hφ]
  -- φ₁ = (k at 0, else m + ·) is strictly monotone (using k ≤ m) and enumerates the tail.
  have hφ₁mono : StrictMono fun i => if i = 0 then k else m + i := by
    intro a b hab
    dsimp only
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rw [if_pos rfl, if_neg (by omega : b ≠ 0)]; omega
    · rw [if_neg (by omega : a ≠ 0), if_neg (by omega : b ≠ 0)]; omega
  have hφ₁succ : ∀ n, (fun i => if i = 0 then k else m + i) (n + 1) = m + 1 + n := by
    intro n
    dsimp only
    rw [if_neg (by omega : ¬ (n + 1 = 0))]
    omega
  rw [side m (fun i => m + i) (fun a b h => by simpa using Nat.add_lt_add_left h m) rfl
        (fun n => by omega),
      side k (fun i => if i = 0 then k else m + i) hφ₁mono (by simp) hφ₁succ]

end Probability

end TauCeti
