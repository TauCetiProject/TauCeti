/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import TauCeti.RingTheory.Polynomial.ScaleRoots

/-!
# Integral normalization in coefficient coordinates

The lower coefficients of the integral normalization of a nonzero degree `n` polynomial `f`
are `f.coeff i * f.leadingCoeff ^ (n - 1 - i)`. Expressing the normalization through
`monicOfCoeff` makes sense even when these coefficients specialize to a lower-degree polynomial:
the monic leading term is retained. This is the coefficient construction needed to normalize
analytic families across a vanishing leading coefficient.

`Polynomial.isRoot_integralNormalization_mul_iff` recovers the original root equation from
a normalized root scaled by the leading coefficient, including zero and constant polynomials.
The same scaling preserves root multiplicities
(`Polynomial.rootMultiplicity_integralNormalization_mul`).
`Polynomial.integralNormalization_eq_prod_X_sub_C` transports a complete linear
factorization, including repeated roots, to the normalized polynomial over any commutative ring.
`Polynomial.Monic.integralNormalization_C_mul` gives the underlying scalar-multiple identity
over a commutative semiring, even for a nonzero scalar that is a zero divisor.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [CommSemiring R] [Nontrivial R] {f : R[X]} {n : ℕ}

/-- Integral normalization is the monic polynomial with its explicitly scaled lower
coefficients. Keeping the degree parameter fixed in this expression permits specialization
through a degree drop. -/
theorem monicOfCoeff_mul_pow_eq_integralNormalization (hf : f ≠ 0)
    (hdeg : f.natDegree = n) :
    monicOfCoeff (fun i : Fin n ↦ f.coeff i * f.leadingCoeff ^ (n - 1 - i)) =
      f.integralNormalization := by
  rw [← monicOfCoeff_coeff (monic_integralNormalization hf)
    (by simpa only [natDegree_integralNormalization] using hdeg)]
  congr 1
  funext i
  rw [integralNormalization_coeff_ne_natDegree (by omega), hdeg]

end TauCeti.Polynomial

namespace Polynomial

/-- Normalizing a nonzero scalar multiple of a monic polynomial scales its roots by that
scalar. This holds even when the scalar is a zero divisor. -/
theorem Monic.integralNormalization_C_mul {R : Type*} [CommSemiring R] {p : R[X]}
    (hp : p.Monic) {a : R} (ha : a ≠ 0) :
    (C a * p).integralNormalization = p.scaleRoots a := by
  have hdeg : (C a * p).natDegree = p.natDegree :=
    natDegree_C_mul_of_mul_ne_zero (by rwa [hp.leadingCoeff, mul_one])
  have hne : C a * p ≠ 0 := hp.mul_left_ne_zero (C_ne_zero.mpr ha)
  ext i
  by_cases hi : i = p.natDegree
  · rw [hi, coeff_scaleRoots, tsub_self, pow_zero, mul_one, hp.coeff_natDegree]
    simpa only [hdeg] using integralNormalization_coeff_natDegree hne
  · rw [integralNormalization_coeff_ne_natDegree (by rwa [hdeg]), hdeg,
      hp.leadingCoeff_C_mul, coeff_C_mul, coeff_scaleRoots]
    by_cases hil : i < p.natDegree
    · have hsub : p.natDegree - 1 - i + 1 = p.natDegree - i := by omega
      rw [mul_comm a, mul_assoc, ← pow_succ', hsub]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

variable {K : Type*} [CommSemiring K] [IsDomain K]

/-- Integral normalization preserves the root equation after scaling by the leading coefficient.
This includes the zero polynomial and nonzero constants. -/
theorem isRoot_integralNormalization_mul_iff (f : K[X]) (z : K) :
    f.integralNormalization.IsRoot (f.leadingCoeff * z) ↔ f.IsRoot z := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  rcases Nat.eq_zero_or_pos f.natDegree with hd | hd
  · rw [eq_C_of_natDegree_eq_zero hd] at hf ⊢
    simp [integralNormalization_C (C_ne_zero.1 hf), C_ne_zero.1 hf]
  · have heval := integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id K) z
    simp only [RingHom.id_apply, eval₂_id] at heval
    rw [IsRoot.def, IsRoot.def, heval,
      mul_eq_zero, or_iff_right (pow_ne_zero _ (leadingCoeff_ne_zero.2 hf))]

/-- Integral normalization preserves the multiplicity of a root scaled by the leading
coefficient. Zero polynomials and constants are included. -/
@[simp]
theorem rootMultiplicity_integralNormalization_mul {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (z : R) :
    f.integralNormalization.rootMultiplicity (f.leadingCoeff * z) = f.rootMultiplicity z := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  have hlc := leadingCoeff_ne_zero.2 hf
  have h := f.rootMultiplicity_scaleRoots (a := z) (IsRegular.of_ne_zero hlc).left
  rwa [← integralNormalization_mul_C_leadingCoeff,
    rootMultiplicity_mul (mul_ne_zero (monic_integralNormalization hf).ne_zero (C_ne_zero.2 hlc)),
    rootMultiplicity_C, add_zero] at h

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A complete linear factorization becomes a monic factorization under integral
normalization, with every root multiplied by the original leading coefficient.
Repeated roots and constant polynomials are included, and the coefficient ring may have
zero divisors. -/
theorem integralNormalization_eq_prod_X_sub_C (f : R[X]) (r : ι → R)
    (hf : f ≠ 0) (hfac : f = C f.leadingCoeff * ∏ i, (X - C (r i))) :
    f.integralNormalization = ∏ i, (X - C (r i * f.leadingCoeff)) := by
  classical
  have hmonic := monic_prod_X_sub_C r Finset.univ
  calc
    f.integralNormalization = (∏ i, (X - C (r i))).scaleRoots f.leadingCoeff := by
      conv_lhs => rw [hfac]
      exact hmonic.integralNormalization_C_mul (leadingCoeff_ne_zero.mpr hf)
    _ = ∏ i, (X - C (r i * f.leadingCoeff)) := by
      rw [prod_scaleRoots_of_monic _ _ _ (fun i _ ↦ monic_X_sub_C (r i))]
      simp

end Polynomial
