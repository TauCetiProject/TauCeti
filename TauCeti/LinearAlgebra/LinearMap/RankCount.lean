/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearMap.SurjectionCount
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import Mathlib.Data.FunLike.Fintype
import Mathlib.Data.SetLike.Fintype
import Mathlib.RingTheory.Finiteness.Cardinality
import TauCeti.Data.Nat.Cast.Basic
import TauCeti.LinearAlgebra.LinearMap.Range
import TauCeti.LinearAlgebra.Submodule.CardFinrank

/-!
# Counting linear maps of fixed rank over finite fields

`TauCeti.natCard_linearMap_finrank_range_eq_gaussianBinomial_mul_prod` counts linear maps of
a specified rank without choosing bases, using `TauCeti.card_submodule_finrank_eq_gaussianBinomial`
and `TauCeti.natCard_linearMap_surjective` for the possible images and their fibres.
`TauCeti.natCast_card_linearMap_finrank_range_eq_prod_div` gives the same count as a product of
rational quotients using `TauCeti.gaussianBinomial_mul_prod_pow_sub_pow`. These counts give the
rank distribution on a finite space of linear maps after dividing by the total number of maps.
-/

public section

open Finset Module

namespace TauCeti

/-- The number of rank-`r` maps from an `n`-dimensional space to an `m`-dimensional space
over a field of order `q` is `[m r]_q ∏_{i<r} (q^n - q^i)`. -/
theorem natCard_linearMap_finrank_range_eq_gaussianBinomial_mul_prod
    (K V W : Type*) [DivisionRing K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (r : ℕ) :
    Nat.card {f : V →ₗ[K] W // finrank K f.range = r} =
      gaussianBinomial (Nat.card K) (finrank K W) r *
        ∏ i : Fin r, (Nat.card K ^ finrank K V - Nat.card K ^ i.val) := by
  classical
  let := Fintype.ofFinite K
  have : Finite V := Module.finite_of_finite K
  have : Finite W := Module.finite_of_finite K
  have : Finite (V →ₗ[K] W) := FunLike.finite _
  let := Fintype.ofFinite W
  have countFiber (U : {U : Submodule K W // finrank K U = r}) :
      Nat.card {f : V →ₗ[K] W // f.range = U.val} =
        ∏ i : Fin r, (Nat.card K ^ finrank K V - Nat.card K ^ i.val) := by
    rw [Nat.card_congr (U.val.rangeEqEquivSurjective (M := V)),
      natCard_linearMap_surjective, U.property]
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (LinearMap.range : (V →ₗ[K] W) → Submodule K W)
    (q := fun U ↦ finrank K U = r) (fun _ ↦ Iff.rfl)
  calc
    _ = Nat.card {U : Submodule K W // finrank K U = r} *
        ∏ i : Fin r, (Nat.card K ^ finrank K V - Nat.card K ^ i.val) := by
      rw [Nat.card_congr e.symm, Nat.card_sigma,
        Nat.card_eq_fintype_card (α := {U : Submodule K W // finrank K U = r})]
      simp only [countFiber, sum_const, card_univ, Nat.nsmul_eq_mul]
    _ = _ := by
      rw [card_submodule_finrank_eq_gaussianBinomial, Nat.card_eq_fintype_card (α := K)]

/-- The rank-`r` count for maps from dimension `n` to dimension `m` over a field of order `q`
equals `∏_{i<r} (q^m - q^i) (q^n - q^i) / (q^r - q^i)` in `ℚ`. -/
theorem natCast_card_linearMap_finrank_range_eq_prod_div
    (K V W : Type*) [DivisionRing K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (r : ℕ) :
    (Nat.card {f : V →ₗ[K] W // finrank K f.range = r} : ℚ) =
      ∏ i : Fin r, (((Nat.card K : ℚ) ^ finrank K W - (Nat.card K : ℚ) ^ i.val) *
        ((Nat.card K : ℚ) ^ finrank K V - (Nat.card K : ℚ) ^ i.val) /
        ((Nat.card K : ℚ) ^ r - (Nat.card K : ℚ) ^ i.val)) := by
  let q := Nat.card K
  have hq : 1 < q := Finite.one_lt_card
  have hqRat : 1 < (q : ℚ) := Nat.one_lt_cast.mpr hq
  have hden : (∏ i : Fin r, ((q : ℚ) ^ r - (q : ℚ) ^ i.val)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ ↦ sub_ne_zero.mpr (pow_lt_pow_right₀ hqRat i.isLt).ne'
  have hGaussian := gaussianBinomial_mul_prod_pow_sub_pow (q : ℚ) (finrank K W) r
  simp only [← Fin.prod_univ_eq_prod_range] at hGaussian
  have hcast : ((gaussianBinomial q (finrank K W) r : ℕ) : ℚ) =
      gaussianBinomial (q : ℚ) (finrank K W) r :=
    map_gaussianBinomial (Nat.castRingHom ℚ) q _ r
  rw [natCard_linearMap_finrank_range_eq_gaussianBinomial_mul_prod, Nat.cast_mul, hcast,
    Nat.cast_prod_pow_sub_pow hq.le]
  rw [prod_div_distrib, prod_mul_distrib]
  apply (eq_div_iff hden).mpr
  rw [mul_right_comm, hGaussian]

end TauCeti
