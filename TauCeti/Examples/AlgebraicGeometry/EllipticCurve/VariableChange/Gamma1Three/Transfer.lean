/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Gamma1Three.Transfer

/-!
# Examples of the `Γ₁(3)` algebraic transfer

Concrete specializations of `TauCeti.Gamma1ThreeHopfAlgebroid.transfer`:

* evaluating `transfer R (27 * a₃²)` at `(a₁, a₃) = (1, 1)` yields `2 * (-1 + 36 - 216) = -362`;
* over any localization `R` of a commutative ring `A` at a prime ideal `P` not containing `3`,
  `IsLocalization.AtPrime.isUnit_to_map_iff` supplies `Invertible (3 : R)`;
* in particular, over `ℤ_{(2)} = Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)})`,
  `ArrowRing ℤ_{(2)}` is free of rank `8` over `BaseRing ℤ_{(2)}`, every transfer lies in
  `invariantSubalgebra ℤ_{(2)}`, and `{8, 2c₄, 2c₆}` lies in `LinearMap.range (transfer ℤ_{(2)})`
  (Carrick, Davies and van Nigtevecht, arXiv:2412.01640v2, Corollary 4.9).
-/

namespace TauCeti.Gamma1ThreeHopfAlgebroid

open MvPolynomial

-- Evaluating `transfer R (27 * a₃²) = 2c₆` at `(a₁, a₃) = (1, 1)` gives `-362` whenever `3` is
-- invertible in `R`.
example {R : Type*} [CommRing R] [Invertible (3 : R)] :
    eval₂ (RingHom.id R) ![1, 1] (transfer R (27 * a₃ R ^ 2)) = -362 := by
  rw [transfer_twentySeven_mul_a₃_sq, universalCurve_c₆, a₁_def, a₃_def]
  simp
  ring

-- Over any localization `R` of a commutative ring `A` at a prime ideal `P` with `3 ∉ P`, `3` is a
-- unit in `R`, so `{8, 2c₄, 2c₆}` lies in the range of `transfer R`.
example {A : Type*} [CommRing A] (R : Type*) [CommRing R] [Algebra A R]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (h3 : (3 : A) ∉ P) :
    ({8, 2 * (universalCurve R).c₄, 2 * (universalCurve R).c₆} : Set (BaseRing R)) ⊆
      LinearMap.range (transfer R) := by
  have h3u : IsUnit (3 : R) := by
    simpa only [map_ofNat] using (IsLocalization.AtPrime.isUnit_to_map_iff R P (3 : A)).mpr h3
  let _ := h3u.invertible
  exact eight_two_c₄_two_c₆_subset_range_transfer R

-- Over `ℤ_{(2)}`, `ArrowRing` has rank `8` over `BaseRing`.
example :
    let Z2 := Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)})
    Module.finrank (BaseRing Z2) (ArrowRing Z2) = 8 := by
  intro Z2
  have h3 : (3 : ℤ) ∉ Ideal.span {((2 : ℕ) : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    decide
  have h3u : IsUnit (3 : Z2) := by
    simpa only [map_ofNat] using
      (IsLocalization.AtPrime.isUnit_to_map_iff Z2 (Ideal.span {((2 : ℕ) : ℤ)}) (3 : ℤ)).mpr h3
  let _ := h3u.invertible
  have : Nontrivial Z2 := IsLocalization.AtPrime.nontrivial Z2 (Ideal.span {((2 : ℕ) : ℤ)})
  exact finrank_arrowRing_eq_eight Z2

-- Over `ℤ_{(2)}`, `{8, 2c₄, 2c₆}` lies in `LinearMap.range (transfer ℤ_{(2)})`.
example :
    let Z2 := Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)})
    ({8, 2 * (universalCurve Z2).c₄, 2 * (universalCurve Z2).c₆} : Set (BaseRing Z2)) ⊆
      LinearMap.range (transfer Z2) := by
  intro Z2
  have h3 : (3 : ℤ) ∉ Ideal.span {((2 : ℕ) : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    decide
  have h3u : IsUnit (3 : Z2) := by
    simpa only [map_ofNat] using
      (IsLocalization.AtPrime.isUnit_to_map_iff Z2 (Ideal.span {((2 : ℕ) : ℤ)}) (3 : ℤ)).mpr h3
  let _ := h3u.invertible
  exact eight_two_c₄_two_c₆_subset_range_transfer Z2

-- Over `ℤ_{(2)}`, every algebraic transfer is a Hopf-algebroid invariant.
example (x : BaseRing (Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)}))) :
    transfer (Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)})) x ∈
      invariantSubalgebra (Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)})) := by
  set Z2 := Localization.AtPrime (Ideal.span {((2 : ℕ) : ℤ)})
  have h3 : (3 : ℤ) ∉ Ideal.span {((2 : ℕ) : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    decide
  have h3u : IsUnit (3 : Z2) := by
    simpa only [map_ofNat] using
      (IsLocalization.AtPrime.isUnit_to_map_iff Z2 (Ideal.span {((2 : ℕ) : ℤ)}) (3 : ℤ)).mpr h3
  let _ := h3u.invertible
  exact transfer_mem_invariantSubalgebra Z2 x

end TauCeti.Gamma1ThreeHopfAlgebroid
