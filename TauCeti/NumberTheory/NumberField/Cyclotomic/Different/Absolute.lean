/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Different.Basic
import TauCeti.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The absolute different of a cyclotomic compositum

For a compositum of coprime discriminants, the derivative at a primitive root in the
cyclotomic factor times the other factor's different generator gives the absolute different.
One can multiply by any unit, in particular a correction making the derivative real as in
`New.Parameters.differentIdeal_eq_span_deltaE` in lsernau/grh-lean
(`grh/src/New/Derivatives/Field/PrimeDecomposition.lean`, revision `72fead1`).
-/

public section

open NumberField Polynomial
open scoped NumberField

namespace IsPrimitiveRoot

/-- In a compositum of coprime discriminants, the cyclotomic derivative times the generator of
the other factor's different generates the absolute different, even after rescaling by a unit. -/
theorem differentIdeal_eq_span_unit_mul_cyclotomic_derivative_mul
    {E : Type*} [Field E] [NumberField E] {F K : IntermediateField ℚ E}
    {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (hsup : F ⊔ K = ⊤) (hcop : IsCoprime (discr F) (discr K)) {b : 𝓞 K}
    (hb : differentIdeal ℤ (𝓞 K) = Ideal.span {b}) (c : (𝓞 E)ˣ) :
    differentIdeal ℤ (𝓞 E) = Ideal.span
      {(c : 𝓞 E) * aeval (algebraMap (𝓞 F) (𝓞 E) hζ.toInteger) (cyclotomic n ℤ).derivative *
        algebraMap (𝓞 K) (𝓞 E) b} := by
  have ha : differentIdeal ℤ (𝓞 F) =
      Ideal.span {aeval hζ.toInteger (cyclotomic n ℤ).derivative} := by
    rw [← TauCeti.differentIdeal_ringOfIntegers_rat_eq_int]
    exact hζ.differentIdeal_eq_span_derivative_cyclotomic_of_coprime_discr (by simp)
  let : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  have hld := linearDisjoint_of_isGalois_isCoprime_discr E F K hcop
  have hcop' := isCoprime_differentIdeal_of_isCoprime_discr E hcop
  rw [ha, hb, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.isCoprime_span_singleton_iff] at hcop'
  simpa only [aeval_algebraMap_apply, mul_assoc, Ideal.span_singleton_mul_left_unit c.isUnit] using
    hld.differentIdeal_eq_span_mul hsup ha hb hcop'

end IsPrimitiveRoot
