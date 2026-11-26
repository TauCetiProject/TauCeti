/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Basic
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Complex conjugation and the cyclotomic character

The conjugation attached to a complex infinite place above a real place acts on roots of unity
by inversion. Its cyclotomic exponent is therefore `-1`. This identifies the arithmetic
complex-conjugation element when a character on modular units is used to cut out a subfield.

More generally, let `φ : L →+* ℂ` be an embedding of a field and `σ` an automorphism of `L` with
`φ ∘ σ = conj ∘ φ` (Mathlib's `NumberField.ComplexEmbedding.IsConj φ σ`). Every root of unity `ζ`
of `L` has `|φ ζ| = 1`, so `σ ζ = ζ⁻¹`, and the `p`-adic cyclotomic character of `σ` is `-1`.

## Main results

* `NumberField.ComplexEmbedding.IsConj.apply_eq_inv_of_pow_eq_one`: a complex conjugation
  inverts every root of unity.
* `IsPrimitiveRoot.autToPow_complexConjugationAt`: the cyclotomic exponent of the conjugation at
  a ramified infinite place is `-1`.
* `TauCeti.cyclotomicCharacter_eq_neg_one_of_isConj`,
  `TauCeti.localCyclotomicCharacter_eq_neg_one_of_isConj`: complex conjugation has `p`-adic
  cyclotomic character `-1`.

## Reference

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3,
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>.
-/

public section

namespace NumberField.ComplexEmbedding.IsConj

variable {k L : Type*} [Field k] [Field L] [Algebra k L] {φ : L →+* ℂ} {σ : L ≃ₐ[k] L}

/-- A complex conjugation inverts every root of unity: if `φ ∘ σ = conj ∘ φ` and `t ^ m = 1` with
`m ≠ 0`, then `σ t = t⁻¹`. -/
theorem apply_eq_inv_of_pow_eq_one (hσ : IsConj φ σ) {m : ℕ} (hm : m ≠ 0) {t : L}
    (ht : t ^ m = 1) : σ t = t⁻¹ := by
  apply φ.injective
  rw [hσ.eq, map_inv₀, Complex.star_def]
  exact (Complex.inv_eq_conj
    (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ht, map_one]) hm)).symm

end NumberField.ComplexEmbedding.IsConj

open NumberField NumberField.InfinitePlace TauCeti.NumberField

namespace IsPrimitiveRoot

variable {K L : Type*} [Field K] [Field L]
  [Algebra K L] [IsGalois K L] {m : ℕ} [NeZero m] {ζ : L}

/-- Complex conjugation at a ramified infinite place has cyclotomic exponent `-1` on every
primitive root of unity. -/
theorem autToPow_complexConjugationAt (hζ : IsPrimitiveRoot ζ m)
    (w : InfinitePlace L) (hw : w.IsRamified K) :
    hζ.autToPow K (complexConjugationAt K w hw) = -1 := by
  have hinv : ζ ^ (m - 1) = ζ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos m), hζ.pow_eq_one]
  have hc : complexConjugationAt K w hw ζ = ζ ^ (m - 1) := by
    rw [hinv, (isConj_complexConjugationAt K w hw).apply_eq_inv_of_pow_eq_one (NeZero.ne m)
      hζ.pow_eq_one]
  apply Units.ext
  rw [hζ.coe_autToPow_eq_natCast_iff.2 hc, Nat.cast_sub (NeZero.pos m), ZMod.natCast_self]
  simp

end IsPrimitiveRoot

namespace TauCeti

open NumberField.ComplexEmbedding

variable (p : ℕ) [Fact p.Prime]

/-- **Complex conjugation has cyclotomic character `-1`.** If `σ` is the conjugation of an
embedding `φ : L →+* ℂ` of a field with all roots of unity of `p`-power order, then `σ` inverts
them, so `χ_p(σ) = -1`. -/
theorem cyclotomicCharacter_eq_neg_one_of_isConj {k L : Type*} [Field k] [Field L] [Algebra k L]
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] {φ : L →+* ℂ} {σ : L ≃ₐ[k] L} (hσ : IsConj φ σ) :
    cyclotomicCharacter L p σ.toRingEquiv = -1 :=
  cyclotomicCharacter_eq_neg_one p fun _ t ht ↦ by
    have ht0 : t ≠ 0 := by rintro rfl; simp [(Fact.out : p.Prime).ne_zero] at ht
    rw [AlgEquiv.coe_toRingEquiv,
      hσ.apply_eq_inv_of_pow_eq_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) ht,
      inv_mul_cancel₀ ht0]

/-- **Complex conjugation in `G_F` has cyclotomic character `-1`.** For an embedding
`ι : F^alg →+* ℂ` and its conjugation `σ ∈ G_F`, `χ_p(σ) = -1`. -/
theorem localCyclotomicCharacter_eq_neg_one_of_isConj {F : Type*} [Field F]
    {ι : AlgebraicClosure F →+* ℂ} {σ : Field.absoluteGaloisGroup F} (hσ : IsConj ι σ) :
    localCyclotomicCharacter p F σ = -1 := by
  have : CharZero (AlgebraicClosure F) := ι.charZero
  have : NeZero (p : AlgebraicClosure F) := ⟨Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero⟩
  rw [localCyclotomicCharacter_apply]
  exact cyclotomicCharacter_eq_neg_one_of_isConj p hσ

end TauCeti
