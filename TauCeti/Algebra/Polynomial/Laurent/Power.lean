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

By contrast, over a nonzero coefficient ring `R` no power `T n` with `n ≠ 0` is integral over `R`
(`LaurentPolynomial.not_isIntegral_T`).
-/

public section

namespace LaurentPolynomial

open scoped LaurentPolynomial Polynomial

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

/-- Over a nonzero ring `R`, the Laurent monomial `T n` with `n ≠ 0` is not integral over `R`. -/
theorem not_isIntegral_T {R : Type*} [CommRing R] [Nontrivial R] {n : ℤ} (hn : n ≠ 0) :
    ¬ IsIntegral R (T n : R[T;T⁻¹]) := by
  have hX : ¬ IsIntegral R (Polynomial.X : R[X]) := fun ⟨p, hp, h⟩ ↦ hp.ne_zero (by simpa using h)
  have h1 : ¬ IsIntegral R (T 1 : R[T;T⁻¹]) := by
    rwa [← Polynomial.toLaurent_X, ← Polynomial.toLaurentAlg_apply,
      isIntegral_algHom_iff _ Polynomial.toLaurent_injective]
  obtain ⟨m, hm, rfl | rfl⟩ : ∃ m : ℕ, 0 < m ∧ (n = m ∨ n = -m) :=
    ⟨n.natAbs, Int.natAbs_pos.2 hn, Int.natAbs_eq n⟩
  · exact fun h ↦ h1 (.of_pow hm (by rwa [T_pow, mul_one]))
  · rw [← invert_T, isIntegral_algEquiv]
    exact fun h ↦ h1 (.of_pow hm (by rwa [T_pow, mul_one]))

end LaurentPolynomial
