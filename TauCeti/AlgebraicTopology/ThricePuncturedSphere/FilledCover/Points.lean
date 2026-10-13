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

/-- The three kinds of added point, as an explicit sum for defining maps out of them. -/
def equivSum : FilledPoint p ≃
    ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero) ⊕
      ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne) ⊕
        ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf) := Equiv.refl _

@[simp]
theorem equivSum_overZero (c) : equivSum p (overZero p c) = Sum.inl c := (rfl)

@[simp]
theorem equivSum_overOne (c) : equivSum p (overOne p c) = Sum.inr (Sum.inl c) := (rfl)

@[simp]
theorem equivSum_overInf (c) : equivSum p (overInf p c) = Sum.inr (Sum.inr c) := (rfl)

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

/-- The points labelled `0` are exactly those constructed over `0`. -/
theorem puncture_eq_zero_iff (y : FilledPoint p) :
    puncture p y = 0 ↔ ∃ c, y = overZero p c := by
  constructor
  · intro h
    rcases FilledPoint.cases p y with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ⟨c, rfl⟩
    · simp at h
    · simp at h
  · rintro ⟨c, rfl⟩
    simp

/-- The points labelled `1` are exactly those constructed over `1`. -/
theorem puncture_eq_one_iff (y : FilledPoint p) :
    puncture p y = 1 ↔ ∃ c, y = overOne p c := by
  constructor
  · intro h
    rcases FilledPoint.cases p y with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simp at h
    · exact ⟨c, rfl⟩
    · simp at h
  · rintro ⟨c, rfl⟩
    simp

/-- The points labelled `2` (the puncture `∞`) are exactly those constructed over `∞`. -/
theorem puncture_eq_two_iff (y : FilledPoint p) :
    puncture p y = 2 ↔ ∃ c, y = overInf p c := by
  constructor
  · intro h
    rcases FilledPoint.cases p y with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · simp at h
    · simp at h
    · exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    simp

variable {n : ℕ}

/-- A numbered finite cover has only finitely many added points. -/
theorem finite (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n) :
    Finite (FilledPoint p) := by
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν)
  rw [FilledPoint]
  infer_instance

variable (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

/-- The number of points added to a numbered finite cover is the sum of the cycle counts
of its three monodromy permutations. Fixed points count as cycles of length one. -/
theorem natCard_eq_cycleCounts :
    Nat.card (FilledPoint p) =
      (hp.monodromyTriple ν).cycleCounts.1 +
        (hp.monodromyTriple ν).cycleCounts.2.1 +
          (hp.monodromyTriple ν).cycleCounts.2.2 := by
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ0EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσ1EquivConnectedComponents ν)
  have : Finite (ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) :=
    Finite.of_equiv _ (hp.sameCycleQuotientσinfEquivConnectedComponents ν)
  have : Finite (FilledPoint p) := finite p hp ν
  simp only [PermutationTriple.cycleCounts_σ0, PermutationTriple.cycleCounts_σ1,
    PermutationTriple.cycleCounts_σinf, orbitCount_def]
  rw [FilledPoint, Nat.card_sum, Nat.card_sum,
    Nat.card_congr (hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm,
    Nat.card_congr (hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm,
    Nat.card_congr (hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm]
  omega

end FilledPoint

end TauCeti
