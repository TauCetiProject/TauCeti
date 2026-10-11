/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoodComponents
public import TauCeti.Combinatorics.PermutationTriple.CycleData

/-!
# Points of the filled cover

For a map to the thrice-punctured sphere, one point is added for each connected component
over each of the three standard punctured neighborhoods. For a finite cover, the
component-cycle equivalences identify the
number of added points with the sum of the three full cycle counts of its monodromy triple.

These are the new points in the compactification of a finite cover. Their puncture labels
determine where the extended map sends them.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7 (one added point for each component over a puncture).
-/

public section

noncomputable section

namespace TauCeti

open ThricePuncturedSphere Set

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

/-- The components above the punctures `0`, `1`, and `∞`, respectively. Each component
contributes one point to the filled cover. -/
def FilledPoint : Type _ :=
  ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero) ⊕
    ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) ⊕
      ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)

namespace FilledPoint

/-- Add a point over the puncture `0` for each component of its punctured preimage. -/
def overZero : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero) → FilledPoint p :=
  Sum.inl

/-- Add a point over the puncture `1` for each component of its punctured preimage. -/
def overOne : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) → FilledPoint p :=
  Sum.inr ∘ Sum.inl

/-- Add a point over the puncture `∞` for each component of its punctured preimage. -/
def overInf : ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf) → FilledPoint p :=
  Sum.inr ∘ Sum.inr

theorem overZero_injective : Function.Injective (overZero p) := Sum.inl_injective

theorem overOne_injective : Function.Injective (overOne p) :=
  Sum.inr_injective.comp Sum.inl_injective

theorem overInf_injective : Function.Injective (overInf p) :=
  Sum.inr_injective.comp Sum.inr_injective

/-- The puncture over which an added point lies, with `0`, `1`, and `2` representing
`0`, `1`, and `∞`. -/
def puncture : FilledPoint p → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

@[simp]
theorem puncture_overZero (c) : puncture p (overZero p c) = 0 := (rfl)

@[simp]
theorem puncture_overOne (c) : puncture p (overOne p c) = 1 := (rfl)

@[simp]
theorem puncture_overInf (c) : puncture p (overInf p c) = 2 := (rfl)

/-- Every added point lies over exactly one of the three punctures. -/
theorem cases (y : FilledPoint p) :
    (∃ c, y = overZero p c) ∨ (∃ c, y = overOne p c) ∨
      (∃ c, y = overInf p c) := by
  cases y with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr y =>
    cases y with
    | inl c => exact Or.inr (Or.inl ⟨c, rfl⟩)
    | inr c => exact Or.inr (Or.inr ⟨c, rfl⟩)

variable {n : ℕ} (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

/-- The number of points added to a numbered finite cover is the sum of the cycle counts
of its three monodromy permutations. Fixed points count as cycles of length one. -/
theorem natCard_eq_cycleCounts :
    Nat.card (FilledPoint p) =
      (hp.monodromyTriple ν).cycleCounts.1 +
        (hp.monodromyTriple ν).cycleCounts.2.1 +
          (hp.monodromyTriple ν).cycleCounts.2.2 := by
  let : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν)
  let : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν)
  let : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν)
  rw [FilledPoint, Nat.card_sum, Nat.card_sum,
    Nat.card_congr (hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm,
    Nat.card_congr (hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm,
    Nat.card_congr (hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm]
  rw [← orbitCount_def, ← orbitCount_def, ← orbitCount_def,
    ← PermutationTriple.cycleCounts_σ0, ← PermutationTriple.cycleCounts_σ1,
    ← PermutationTriple.cycleCounts_σinf]
  omega

end FilledPoint

end TauCeti
