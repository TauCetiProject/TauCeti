/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# The universal strict coordinate

For a commutative ring `A`, the strict formal coordinate

  `X + ∑_{i ≥ 1} bᵢ X^(i + 1)`

over the polynomial ring `A[b₁, b₂, …] = MvPolynomial ℕ+ A`, whose coefficients are the variables,
is universal among strict coordinates over `A`-algebras: a ring homomorphism
`A[b₁, b₂, …] →+* R` is the same as a ring homomorphism `A →+* R` together with a strict coordinate
over `R`, and it specializes the universal strict coordinate to that coordinate.

Taking for `A` a ring classifying formal group laws of some kind, such as the Lazard ring, this
makes the strict isomorphisms between such formal group laws representable by `A[b₁, b₂, …]`.

## Main definitions

* `TauCeti.FormalCoordinate.universalStrictCoordinate`: the strict coordinate `X + ∑ bᵢ X^(i + 1)`
  over `A[b₁, b₂, …]`.
* `TauCeti.FormalCoordinate.strictLift`: the bijection between pairs of a ring homomorphism
  `A →+* R` and a strict coordinate over `R` and ring homomorphisms `A[b₁, b₂, …] →+* R`.

## Main results

* `TauCeti.FormalCoordinate.map_strictLift_universalStrictCoordinate`: the homomorphism attached to
  `(f, φ)` specializes the universal strict coordinate to `φ`.
* `TauCeti.FormalCoordinate.ringHom_ext_universalStrictCoordinate`: a ring homomorphism out of
  `A[b₁, b₂, …]` is determined by its restriction to `A` and by its base change of the universal
  strict coordinate.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

namespace TauCeti.FormalCoordinate

open MvPolynomial

variable {A R : Type*} [CommRing A] [CommRing R]

/-- The universal strict coordinate `X + ∑_{i ≥ 1} bᵢ X^(i + 1)` over `A[b₁, b₂, …]`, whose
coefficients are the variables `bᵢ`. -/
def universalStrictCoordinate : FormalCoordinate (MvPolynomial ℕ+ A) :=
  ofStrictCoeffs X

/-- The strict coordinate `universalStrictCoordinate` has the variable `bᵢ` as its coefficient of
`X^(i + 1)`. -/
@[simp]
theorem coeff_succ_universalStrictCoordinate (i : ℕ+) :
    PowerSeries.coeff (i + 1) (universalStrictCoordinate (A := A)).toPowerSeries = X i :=
  coeff_succ_ofStrictCoeffs X i

/-- The base change of the universal strict coordinate along `f` is the strict coordinate
`X + ∑ f(bᵢ) X^(i + 1)`. -/
theorem map_universalStrictCoordinate (f : MvPolynomial ℕ+ A →+* R) :
    map f universalStrictCoordinate = ofStrictCoeffs (f ∘ X) :=
  map_ofStrictCoeffs f X

/-- Base change of the universal strict coordinate is strict. -/
theorem map_universalStrictCoordinate_mem_ker (f : MvPolynomial ℕ+ A →+* R) :
    map f universalStrictCoordinate ∈ (linearCoeff (R := R)).ker := by
  rw [map_universalStrictCoordinate]
  exact ofStrictCoeffs_mem_ker_linearCoeff _

/-- Applying `f : A →+* B` to the coefficients of `A[b₁, b₂, …]` carries the universal strict
coordinate over `A[b₁, b₂, …]` to the universal strict coordinate over `B[b₁, b₂, …]`. -/
@[simp]
theorem map_map_universalStrictCoordinate {B : Type*} [CommRing B] (f : A →+* B) :
    map (MvPolynomial.map f) (universalStrictCoordinate (A := A)) = universalStrictCoordinate := by
  rw [map_universalStrictCoordinate, universalStrictCoordinate]
  congr 1
  funext i
  simp

/-- A ring homomorphism out of `A[b₁, b₂, …]` is determined by its restriction to `A` and by its
base change of the universal strict coordinate. -/
theorem ringHom_ext_universalStrictCoordinate {f g : MvPolynomial ℕ+ A →+* R}
    (hC : f.comp C = g.comp C)
    (hφ : map f universalStrictCoordinate = map g universalStrictCoordinate) : f = g :=
  ringHom_ext' hC fun i ↦ by
    simpa using congrArg (fun φ ↦ PowerSeries.coeff (i + 1) φ.toPowerSeries) hφ

/-- **`A[b₁, b₂, …]` represents strict coordinates over `A`-algebras**: pairs of a ring
homomorphism `f : A →+* R` and a strict coordinate `φ` over `R` correspond to ring homomorphisms
`A[b₁, b₂, …] →+* R`. The homomorphism attached to `(f, φ)` restricts to `f` and sends `bᵢ` to the
coefficient of `X^(i + 1)` in `φ`. -/
def strictLift : (A →+* R) × (linearCoeff (R := R)).ker ≃ (MvPolynomial ℕ+ A →+* R) where
  toFun p := eval₂Hom p.1 (strictCoeffsEquiv.symm p.2)
  invFun f := (f.comp C, strictCoeffsEquiv (f ∘ X))
  left_inv p := by
    have h : ⇑(eval₂Hom p.1 (strictCoeffsEquiv.symm p.2)) ∘ X = strictCoeffsEquiv.symm p.2 :=
      funext fun i ↦ eval₂Hom_X' _ _ i
    refine Prod.ext (RingHom.ext (eval₂Hom_C _ _)) ?_
    dsimp only
    rw [h, Equiv.apply_symm_apply]
  right_inv f := ringHom_ext' (RingHom.ext fun r ↦ by simp) fun i ↦ by simp

/-- The ring homomorphism out of `A` attached to `f : A[b₁, b₂, …] →+* R` is its restriction. -/
@[simp]
theorem strictLift_symm_apply_fst (f : MvPolynomial ℕ+ A →+* R) :
    (strictLift.symm f).1 = f.comp C :=
  (rfl)

/-- The strict coordinate attached to `f : A[b₁, b₂, …] →+* R` has coefficients `f (bᵢ)`. -/
@[simp]
theorem strictLift_symm_apply_snd (f : MvPolynomial ℕ+ A →+* R) :
    (strictLift.symm f).2 = strictCoeffsEquiv (f ∘ X) :=
  (rfl)

/-- The homomorphism attached to `(f, φ)` restricts along `C` to `f`. -/
@[simp]
theorem strictLift_comp_C (p : (A →+* R) × (linearCoeff (R := R)).ker) :
    (strictLift p).comp C = p.1 :=
  RingHom.ext (eval₂Hom_C _ _)

/-- The homomorphism attached to `(f, φ)` agrees with `f` on constants. -/
@[simp]
theorem strictLift_C (p : (A →+* R) × (linearCoeff (R := R)).ker) (r : A) :
    strictLift p (C r) = p.1 r :=
  eval₂Hom_C _ _ r

/-- The homomorphism attached to `(f, φ)` sends `bᵢ` to the coefficient of `X^(i + 1)` in `φ`. -/
@[simp]
theorem strictLift_X (p : (A →+* R) × (linearCoeff (R := R)).ker) (i : ℕ+) :
    strictLift p (X i) = PowerSeries.coeff (i + 1) p.2.1.toPowerSeries :=
  (eval₂Hom_X' _ _ _).trans (strictCoeffsEquiv_symm_apply p.2 i)

/-- The homomorphism attached to `(f, φ)` specializes the universal strict coordinate to `φ`. -/
@[simp]
theorem map_strictLift_universalStrictCoordinate (p : (A →+* R) × (linearCoeff (R := R)).ker) :
    map (strictLift p) universalStrictCoordinate = p.2.1 := by
  have h : ⇑(strictLift p) ∘ X = strictCoeffsEquiv.symm p.2 := funext fun i ↦ by simp
  rw [map_universalStrictCoordinate, h, ← coe_strictCoeffsEquiv_apply, Equiv.apply_symm_apply]

end TauCeti.FormalCoordinate
