/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Basic
public import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Complex conjugation and the cyclotomic character

The conjugation attached to a complex infinite place above a real place acts on roots of unity
by inversion. Its cyclotomic exponent is therefore `-1`. This identifies the arithmetic
complex-conjugation element when a character on modular units is used to cut out a subfield.

## Reference

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3,
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>.
-/

public section

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
    apply w.embedding.injective
    rw [(isConj_complexConjugationAt K w hw).eq, hinv, map_inv₀, Complex.star_def]
    have hz : (w.embedding ζ) ^ m = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne m))).symm
  apply Units.ext
  rw [hζ.coe_autToPow_eq_natCast hc, Nat.cast_sub (NeZero.pos m), ZMod.natCast_self]
  simp

end IsPrimitiveRoot
