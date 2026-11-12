/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom

/-!
# Finiteness of the `p`-th power map

Let `p` be a prime and `A` a commutative ring in which `p` vanishes. The `p`-th power map
`TauCeti.powRingHom A p h : A →+* A` is always integral: the power map sends the monic polynomial
`X ^ p - C a` of the source to `X ^ p - C (a ^ p)`, which vanishes at `a`. If moreover `A` is of
finite type over a perfect ring `R`, then `A` is of finite type over its subring of `p`-th powers,
because that subring contains the image of `R`; so the `p`-th power map is finite. This is the
algebraic input to the finiteness of the absolute Frobenius of a scheme locally of finite type over
a perfect field.

Without the finite-type hypothesis the `p`-th power map need not be finite: for instance it is not
finite on the field of rational functions over `𝔽_p` in infinitely many variables.

## Main results

* `TauCeti.powRingHom_isIntegral`: the `p`-th power map is integral.
* `TauCeti.powRingHom_finiteType`: it is of finite type when `A` is of finite type over a perfect
  ring.
* `TauCeti.powRingHom_finite`: it is finite when `A` is of finite type over a perfect ring.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii.
-/

public section

open Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {p : ℕ} [hp : Fact p.Prime]

/-- The `p`-th power map is integral: its image of `X ^ p - C a` is `X ^ p - C (a ^ p)`, which
vanishes at `a`. -/
theorem powRingHom_isIntegral (h : (p : A) = 0) : (powRingHom A p h).IsIntegral := fun a ↦
  ⟨X ^ p - C a, monic_X_pow_sub_C a hp.out.ne_zero, by simp⟩

/-- If `A` is of finite type over a perfect ring `R`, then the `p`-th power map of `A` is of finite
type: the image of `R` consists of `p`-th powers. -/
theorem powRingHom_finiteType {R : Type*} [CommRing R] [ExpChar R p] [PerfectRing R p]
    (h : (p : A) = 0) (f : R →+* A) (hf : f.FiniteType) : (powRingHom A p h).FiniteType := by
  refine RingHom.FiniteType.of_comp_finiteType (f := f.comp (frobeniusEquiv R p).symm.toRingHom) ?_
  convert hf
  ext r
  simp [← map_pow f, frobeniusEquiv_symm_pow_p]

/-- If `A` is of finite type over a perfect ring `R`, then the `p`-th power map of `A` is
finite. -/
theorem powRingHom_finite {R : Type*} [CommRing R] [ExpChar R p] [PerfectRing R p]
    (h : (p : A) = 0) (f : R →+* A) (hf : f.FiniteType) : (powRingHom A p h).Finite :=
  (powRingHom_isIntegral h).to_finite (powRingHom_finiteType h f hf)

end TauCeti
