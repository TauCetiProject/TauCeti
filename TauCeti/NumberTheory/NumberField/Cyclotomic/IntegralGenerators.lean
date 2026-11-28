/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.NumberTheory.NumberField.Cyclotomic.Different

/-!
# Integral generators of cyclotomic composita

If the cyclotomic order is coprime to the base discriminant, the image of a generating set
of the base integers together with a primitive root generates the integers of the
extension over `ℤ`. Over a quadratic field of odd squarefree discriminant this gives
the two generators `(1 + √D) / 2` and `ζ`. In particular, to compare two ring maps out of
the integers (for instance into a residue ring), it suffices to compare their values on
these two elements.

This uses the coprime-discriminant computation of the ring of integers, as in Neukirch,
*Algebraic Number Theory*, Chapter I §10. The two-generator form occurs in
`New.Parameters.adjoin_betaKInE_zetaInt_eq_top` in `New/Derivatives/Field/PrimeDecomposition.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh).
-/

public section

open NumberField Polynomial
open scoped NumberField

namespace IsPrimitiveRoot

variable {K E : Type*} [Field K] [NumberField K] [Field E] [Algebra K E]
  {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} K E] {ζ : E}

/-- For a cyclotomic extension of order coprime to the base discriminant, adjoining the
primitive root to the images of any `ℤ`-algebra generators of the base integers gives
all the integers of the extension. -/
theorem adjoin_insert_toInteger_image_eq_top_of_coprime_discr (hζ : IsPrimitiveRoot ζ n)
    (hcop : (discr K).natAbs.Coprime n) {S : Set (𝓞 K)} (hS : Algebra.adjoin ℤ S = ⊤) :
    Algebra.adjoin ℤ (insert hζ.toInteger (algebraMap (𝓞 K) (𝓞 E) '' S)) = ⊤ := by
  rw [Set.insert_eq, Set.union_comm, ← Algebra.adjoin_eq_adjoin_union ℤ S _ hS,
    hζ.adjoin_toInteger_eq_top_of_coprime_discr hcop, Subalgebra.restrictScalars_top]

/-- In a cyclotomic extension of `ℚ(√D)` with `D` squarefree and `D ≡ 1 (mod 4)`, and with
order coprime to `|D|`, the ring of integers is generated over `ℤ` by the primitive root
and the image of `(1 + √D) / 2`. -/
theorem adjoin_toInteger_halfGen_eq_top (hζ : IsPrimitiveRoot ζ n) {θ : 𝓞 K} {D : ℤ}
    (hmin : minpoly ℤ θ = X ^ 2 - C D) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree D) (hd4 : D % 4 = 1) (hcop : D.natAbs.Coprime n) :
    Algebra.adjoin ℤ {hζ.toInteger, algebraMap (𝓞 K) (𝓞 E) (halfGen hmin hd4)} = ⊤ := by
  rw [← discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4] at hcop
  simpa only [Set.image_singleton] using
    hζ.adjoin_insert_toInteger_image_eq_top_of_coprime_discr hcop
      (adjoin_halfGen_eq_top_of_mod_four_eq_one hmin hgen hsf hd4)

end IsPrimitiveRoot
