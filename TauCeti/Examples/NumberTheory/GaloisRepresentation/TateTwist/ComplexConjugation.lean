/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.GaloisRepresentation.TateTwist.ComplexConjugation
import TauCeti.NumberTheory.NumberField.ComplexConjugation.AlgebraicClosure

/-!
# Checks: complex conjugation on Tate twists over `ℚ`

For a complex conjugation `c ∈ G_ℚ` (an element of
`TauCeti.NumberField.complexConjugations ℚ^alg`, which is nonempty):

* `c` acts on `ℤ_ℓ(1)` by `-1` and on `M(1)` by `-ρ(c)`;
* `c` also acts on `ℤ_ℓ(−1)` by `-1`, so this sign does not distinguish `χ_ℓ` from `χ_ℓ⁻¹`;
* in particular `c ≠ 1`.
-/

open TauCeti TauCeti.NumberField ContinuousRep

variable (ℓ : ℕ) [Fact ℓ.Prime]

-- `G_ℚ` has complex conjugations.
example : (complexConjugations (AlgebraicClosure ℚ)).Nonempty :=
  complexConjugations_nonempty _

-- A complex conjugation acts on `ℤ_ℓ(1)` by `-1` ...
example {c : Field.absoluteGaloisGroup ℚ} (hc : c ∈ complexConjugations (AlgebraicClosure ℚ))
    (a : ℤ_[ℓ]) : cyclotomicLine ℓ ℚ c a = -a := by
  obtain ⟨ι, hι⟩ := mem_complexConjugations_iff.1 hc
  exact cyclotomicLine_apply_of_isConj hι a

-- ... and on the first Tate twist `M(1)` by `-ρ(c)`.
example {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] [TopologicalSpace M]
    [ContinuousSMul ℤ_[ℓ] M] (ρ : ContinuousRep (Field.absoluteGaloisGroup ℚ) ℤ_[ℓ] M)
    {c : Field.absoluteGaloisGroup ℚ} (hc : c ∈ complexConjugations (AlgebraicClosure ℚ))
    (x : M) : ρ.tateTwist ℓ 1 c x = -ρ c x := by
  obtain ⟨ι, hι⟩ := mem_complexConjugations_iff.1 hc
  exact tateTwist_one_apply_of_isConj hι ρ x

-- A twist by `χ_ℓ⁻¹` gives the same sign: `c` acts on `ℤ_ℓ(−1)` by `-1` as well.
example {c : Field.absoluteGaloisGroup ℚ} (hc : c ∈ complexConjugations (AlgebraicClosure ℚ))
    (a : ℤ_[ℓ]) :
    (trivial (Field.absoluteGaloisGroup ℚ) ℤ_[ℓ] ℤ_[ℓ]).tateTwist ℓ (-1) c a = -a := by
  obtain ⟨ι, hι⟩ := mem_complexConjugations_iff.1 hc
  rw [tateTwist_apply_of_isConj hι]
  simp

-- A complex conjugation is not the identity of `G_ℚ`.
example {c : Field.absoluteGaloisGroup ℚ} (hc : c ∈ complexConjugations (AlgebraicClosure ℚ)) :
    c ≠ 1 := by
  obtain ⟨ι, hι⟩ := mem_complexConjugations_iff.1 hc
  rintro rfl
  have h := localCyclotomicCharacter_eq_neg_one_of_isConj ℓ hι
  rw [map_one] at h
  have h' := congrArg (fun u : ℤ_[ℓ]ˣ ↦ ((u : ℤ_[ℓ]) : ℚ_[ℓ])) h
  norm_num at h'
