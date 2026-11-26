/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.TateTwist
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex conjugation on Tate twists

Let `φ : L →+* ℂ` be an embedding of a field and `σ` an automorphism of `L` with
`φ ∘ σ = conj ∘ φ` (Mathlib's `NumberField.ComplexEmbedding.IsConj φ σ`). Every root of unity `ζ`
of `L` has `|φ ζ| = 1`, so `σ ζ = ζ⁻¹`, and the `p`-adic cyclotomic character of `σ` is `-1`
(`TauCeti.cyclotomicCharacter_eq_neg_one_of_isConj`). For a field `F` and an embedding
`ι : F^alg →+* ℂ`, the conjugation `σ ∈ G_F` of `ι` therefore has `χ_ℓ(σ) = -1`
(`TauCeti.localCyclotomicCharacter_eq_neg_one_of_isConj`): it acts on `ℤ_ℓ(1)` by `-1` and on a
Tate twist `M(n)` by `(-1)ⁿ ρ(σ)`, in particular on `M(1)` by `-ρ(σ)`.

## Main results

* `TauCeti.cyclotomicCharacter_eq_neg_one_of_isConj`,
  `TauCeti.localCyclotomicCharacter_eq_neg_one_of_isConj`: complex conjugation has cyclotomic
  character `-1`.
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

variable (p : ℕ) [Fact p.Prime]

/-- **Complex conjugation has cyclotomic character `-1`.** If `σ` is the conjugation of an
embedding `φ : L →+* ℂ` of a field with all roots of unity of `p`-power order, then `σ` inverts
them, so `χ_p(σ) = -1`. -/
theorem cyclotomicCharacter_eq_neg_one_of_isConj {k L : Type*} [Field k] [Field L] [Algebra k L]
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] {φ : L →+* ℂ} {σ : L ≃ₐ[k] L} (hσ : IsConj φ σ) :
    cyclotomicCharacter L p σ.toRingEquiv = -1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine cyclotomicCharacter_eq_neg_one p fun n t ht ↦ φ.injective ?_
  have hnorm : ‖φ t‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht, map_one]) (NeZero.ne _)
  have ht0 : φ t ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hσt : φ (σ.toRingEquiv t) = (φ t)⁻¹ := by
    rw [Complex.inv_eq_conj hnorm, ← Complex.star_def]
    exact hσ.eq t
  rw [map_mul, map_one, hσt, inv_mul_cancel₀ ht0]

/-- **Complex conjugation in `G_F` has cyclotomic character `-1`.** For an embedding
`ι : F^alg →+* ℂ` and its conjugation `σ ∈ G_F`, `χ_p(σ) = -1`. -/
theorem localCyclotomicCharacter_eq_neg_one_of_isConj {F : Type*} [Field F]
    {ι : AlgebraicClosure F →+* ℂ} {σ : Field.absoluteGaloisGroup F} (hσ : IsConj ι σ) :
    localCyclotomicCharacter p F σ = -1 := by
  have : CharZero (AlgebraicClosure F) := ι.charZero
  have : NeZero (p : AlgebraicClosure F) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  rw [localCyclotomicCharacter_apply]
  exact cyclotomicCharacter_eq_neg_one_of_isConj p hσ

variable {p} {F : Type*} [Field F] (A : Type*) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [Algebra ℤ_[p] A] [ContinuousSMul ℤ_[p] A]

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
  rw [tateTwist_apply, cyclotomicPow_apply_of_isConj A hσ]
  rfl

/-- **Complex conjugation on the first Tate twist**: `σ` acts on `M(1)` by `-ρ(σ)`. -/
theorem tateTwist_one_apply_of_isConj (hσ : IsConj ι σ)
    (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M) (x : M) :
    ρ.tateTwist ℓ 1 σ x = -ρ σ x := by
  simp [tateTwist_apply_of_isConj hσ]

end ContinuousRep

end TauCeti
