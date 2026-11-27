/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel.Index.Dedekind
import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Splitting

/-!
# Bianchi levels above five

The prime ideal `(2 + i)` in the fourth cyclotomic field has norm five. Its upper-triangular
congruence subgroup has index six in the full integral general linear group. At level `(5)`,
both primes above five contribute and the index is thirty-six.
-/

open NumberField UniqueFactorizationMonoid
open scoped NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K] {ζ : K}

example (hζ : IsPrimitiveRoot ζ 4) :
    (GL2K0 (Ideal.span {2 + hζ.toInteger})).index = 6 := by
  let P := Ideal.span {2 + hζ.toInteger}
  have hN : Ideal.absNorm P = 5 := NumberField.GaussianRationals.absNorm_span_two_add
    hζ.minpoly_toInteger_eq_X_sq_add_one (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
  have hp : Irreducible P := Ideal.irreducible_of_irreducible_absNorm (by rw [hN]; decide)
  have : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hp.ne_zero
  rw [GL2K0.index_eq_prod_absNorm_pow_mul P hp.ne_zero]
  simp [factors_eq_normalizedFactors, normalizedFactors_irreducible hp, hN]

example (hζ : IsPrimitiveRoot ζ 4) :
    (GL2K0 (Ideal.span {(5 : 𝓞 K)})).index = 36 := by
  let P := Ideal.span {2 + hζ.toInteger}
  let Q := Ideal.span {2 - hζ.toInteger}
  have hmin := hζ.minpoly_toInteger_eq_X_sq_add_one
  have hgen : Algebra.adjoin ℚ {(hζ.toInteger : K)} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have hP : Ideal.absNorm P = 5 := NumberField.GaussianRationals.absNorm_span_two_add hmin hgen
  have hQ : Ideal.absNorm Q = 5 := NumberField.GaussianRationals.absNorm_span_two_sub hmin hgen
  have hp : Irreducible P := Ideal.irreducible_of_irreducible_absNorm (by rw [hP]; decide)
  have hq : Irreducible Q := Ideal.irreducible_of_irreducible_absNorm (by rw [hQ]; decide)
  have hne : P ≠ Q := NumberField.GaussianRationals.span_two_add_ne_span_two_sub hmin
  have hPQ : P * Q = Ideal.span {(5 : 𝓞 K)} := by
    simp only [P, Q, Ideal.span_singleton_mul_span_singleton,
      NumberField.GaussianRationals.two_add_mul_two_sub_eq_five hmin]
  have : Finite (𝓞 K ⧸ (P * Q)) := Ring.HasFiniteQuotients.finiteQuotient
    (mul_ne_zero hp.ne_zero hq.ne_zero)
  rw [← hPQ, GL2K0.index_eq_prod_absNorm_pow_mul _ (mul_ne_zero hp.ne_zero hq.ne_zero)]
  norm_num [factors_eq_normalizedFactors, normalizedFactors_mul hp.ne_zero hq.ne_zero,
    normalizedFactors_irreducible hp, normalizedFactors_irreducible hq, hne, Ne.symm hne, hP, hQ]

end TauCeti
