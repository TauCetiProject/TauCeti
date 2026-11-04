/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Integral power substitutions in Laurent polynomials

For every positive natural number `n`, the substitution `T ↦ Tⁿ` is integral over any
commutative coefficient ring. Together with injectivity of the exponent map, lying over
therefore makes the corresponding morphism of spectra surjective. This applies even when
`n` vanishes in the coefficient ring, as in inseparable power maps of the multiplicative group.
-/

public section

namespace LaurentPolynomial

open scoped LaurentPolynomial

/-- Substituting `Tⁿ` for `T` is integral when `n > 0`, with no assumption on the
characteristic or reducedness of the coefficient ring. -/
theorem isIntegral_mapDomain_mulRight (R : Type*) [CommRing R] {n : ℕ} (hn : 0 < n) :
    (AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.mulRight (n : ℤ))).IsIntegral := by
  let f := AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.mulRight (n : ℤ))
  let := f.toAlgebra
  have hC (a : R) : IsIntegral R[T;T⁻¹] (C a : R[T;T⁻¹]) := by
    simpa only [RingHom.algebraMap_toAlgebra, f, ← single_eq_C,
      AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero] using
      (isIntegral_algebraMap (R := R[T;T⁻¹]) (A := R[T;T⁻¹]) (x := C a))
  have hT (m : ℤ) : IsIntegral R[T;T⁻¹] (T m : R[T;T⁻¹]) := by
    apply IsIntegral.of_pow hn
    rw [T_pow]
    simpa only [RingHom.algebraMap_toAlgebra, f, T,
      AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidHom.coe_mulRight, mul_comm] using
      (isIntegral_algebraMap (R := R[T;T⁻¹]) (A := R[T;T⁻¹]) (x := T m))
  intro x
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq => exact IsIntegral.add hp hq
  | C_mul_T m a => exact (hC a).mul (hT m)

end LaurentPolynomial
