/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.TateTwist
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Cyclotomic

/-!
# Complex conjugation on Tate twists

For a field `F` and an embedding `ι : F^alg →+* ℂ`, the conjugation `σ ∈ G_F` of `ι`
(Mathlib's `NumberField.ComplexEmbedding.IsConj ι σ`) has `χ_ℓ(σ) = -1`
(`TauCeti.localCyclotomicCharacter_eq_neg_one_of_isConj`): it acts on `ℤ_ℓ(1)` by `-1` and on a
Tate twist `M(n)` by `(-1)ⁿ ρ(σ)`, in particular on `M(1)` by `-ρ(σ)`.

## Main results

* `TauCeti.cyclotomicPow_apply_of_isConj`: `χ_ℓ(σ)ⁿ = (-1)ⁿ`.
* `TauCeti.ContinuousRep.cyclotomicLine_apply_of_isConj`: `σ` acts on `ℤ_ℓ(1)` by `-1`.
* `TauCeti.ContinuousRep.tateTwist_apply_of_isConj`,
  `TauCeti.ContinuousRep.tateTwist_one_apply_of_isConj`: `σ` acts on `M(n)` by `(-1)ⁿ ρ(σ)`, and
  on `M(1)` by `-ρ(σ)`.
-/

public section

noncomputable section

open NumberField.ComplexEmbedding

namespace TauCeti

section Character

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] (A : Type*) [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[p] A] [ContinuousSMul ℤ_[p] A]

/-- **`χ_ℓ(σ)ⁿ = (-1)ⁿ`** for the conjugation `σ ∈ G_F` of an embedding `ι : F^alg →+* ℂ`. -/
theorem cyclotomicPow_apply_of_isConj {ι : AlgebraicClosure F →+* ℂ}
    {σ : Field.absoluteGaloisGroup F} (hσ : IsConj ι σ) (n : ℤ) :
    cyclotomicPow p F A n σ = (-1) ^ n := by
  have h : ContinuousRep.unitsMapCharacter A (continuousLocalCyclotomicCharacter p F) σ = -1 :=
    Units.ext <| by
      rw [ContinuousRep.coe_unitsMapCharacter_apply, continuousLocalCyclotomicCharacter_apply,
        localCyclotomicCharacter_eq_neg_one_of_isConj p hσ]
      simp
  rw [cyclotomicPow_apply, h]

end Character

namespace ContinuousRep

variable {ℓ : ℕ} [Fact ℓ.Prime] {F : Type*} [Field F] {ι : AlgebraicClosure F →+* ℂ}
  {σ : Field.absoluteGaloisGroup F}

/-- **Complex conjugation acts on `ℤ_ℓ(1)` by `-1`.** -/
theorem cyclotomicLine_apply_of_isConj (hσ : IsConj ι σ) (a : ℤ_[ℓ]) :
    cyclotomicLine ℓ F σ a = -a := by
  simp [localCyclotomicCharacter_eq_neg_one_of_isConj ℓ hσ]

variable {A M : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Algebra ℤ_[ℓ] A]
  [ContinuousSMul ℤ_[ℓ] A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [ContinuousSMul A M]

/-- **Complex conjugation on a Tate twist**: `σ` acts on `M(n)` by `(-1)ⁿ ρ(σ)`. -/
theorem tateTwist_apply_of_isConj (hσ : IsConj ι σ)
    (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (n : ℤ) (x : M) :
    ρ.tateTwist ℓ n σ x = ((-1 : Aˣ) ^ n : Aˣ) • ρ σ x := by
  rw [tateTwist_apply, cyclotomicPow_apply_of_isConj A hσ, Units.smul_def]

/-- **Complex conjugation on the first Tate twist**: `σ` acts on `M(1)` by `-ρ(σ)`. -/
theorem tateTwist_one_apply_of_isConj (hσ : IsConj ι σ)
    (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (x : M) :
    ρ.tateTwist ℓ 1 σ x = -ρ σ x := by
  simp [tateTwist_apply_of_isConj hσ]

end ContinuousRep

end TauCeti
