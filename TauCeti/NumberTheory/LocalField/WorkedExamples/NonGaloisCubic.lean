/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Rational
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import TauCeti.FieldTheory.Kummer.Extension

/-!
# The non-Galois cubic `ℚ₅(∛5)`

Adjoining a root of the Eisenstein polynomial `X³ − 5` to `ℚ₅` gives a totally ramified cubic
extension `ℚ₅(∛5)`. It is **not** Galois: a nontrivial `ℚ₅`-automorphism would send `∛5` to
`ζ ∛5` for a primitive cube root of unity `ζ`, and `ζ`, a root of the irreducible quadratic
`X² + X + 1` over `ℚ₅` (since `−3` is not a square in `ℚ₅`), would generate a quadratic subfield
of a cubic extension. So its automorphism group is trivial, of order `1 < 3 = [ℚ₅(∛5) : ℚ₅]`.

This makes `ℚ₅(∛5)` the standard instance of a finite layer of `p`-adic fields whose automorphism
group is finite but smaller than its degree. On such a layer the rational decomposition
`A(L) ⊗ ℚ_p ≃ ℚ_p[Gal(L/K)]^N ⊕ ℚ_p` of the completed multiplicative module fails: here the two
`ℚ₅`-dimensions are `[L : ℚ₅] + 1 = 4` and `N · #Aut(L) + 1 = 2`
(`TauCeti.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt`). The field is an
explicit witness that the Galois hypothesis of that decomposition cannot be replaced by finiteness
of the automorphism group.

## Main definitions

* `TauCeti.NonGaloisCubic`: the field `ℚ₅(∛5)`.
* `TauCeti.NonGaloisCubic.cbrtFive`: the cube root of `5` generating it.

## Main results

* `TauCeti.NonGaloisCubic.finrank_eq_three`: `[ℚ₅(∛5) : ℚ₅] = 3`.
* `TauCeti.NonGaloisCubic.eq_one_of_pow_three_eq_one`: `ℚ₅(∛5)` has no nontrivial cube root of
  unity.
* `TauCeti.NonGaloisCubic.subsingleton_algEquiv`: the automorphism group of `ℚ₅(∛5)/ℚ₅` is
  trivial, so `TauCeti.NonGaloisCubic.natCard_algEquiv_lt_finrank` and
  `TauCeti.NonGaloisCubic.not_isGalois`.
* `TauCeti.NonGaloisCubic.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv`: the rational
  decomposition of `A(ℚ₅(∛5))` as `ℤ₅[Aut]`-module fails.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (7.4.4).
* J.-P. Serre, *Local Fields*, Chapter I, §6.
-/

public section
noncomputable section

open Polynomial IntermediateField

namespace TauCeti

/-- The prime `5`, as a `Fact`, so that `ℚ_[5]` can be written. -/
instance NonGaloisCubic.factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The field `ℚ₅(∛5)`, obtained from `ℚ₅` by adjoining a root of `X³ − 5`. -/
def NonGaloisCubic : Type := AdjoinRoot (X ^ 3 - C 5 : ℚ_[5][X])

namespace NonGaloisCubic

/-- `X³ − 5` is irreducible over `ℚ₅`: it is Eisenstein at `5`. -/
local instance factIrreducible : Fact (Irreducible (X ^ 3 - C 5 : ℚ_[5][X])) :=
  ⟨by
    have := X_pow_sub_C_irreducible_of_irreducible (R := ℤ_[5]) (K := ℚ_[5])
      PadicInt.irreducible_p three_ne_zero
    rwa [map_natCast, Nat.cast_ofNat] at this⟩

instance : Field NonGaloisCubic := inferInstanceAs (Field (AdjoinRoot (X ^ 3 - C 5 : ℚ_[5][X])))

instance : Algebra ℚ_[5] NonGaloisCubic :=
  inferInstanceAs (Algebra ℚ_[5] (AdjoinRoot (X ^ 3 - C 5 : ℚ_[5][X])))

/-- The power basis `1, ∛5, ∛5²` of `ℚ₅(∛5)` over `ℚ₅`. -/
private def powerBasis : PowerBasis ℚ_[5] NonGaloisCubic :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 3 - C 5 : ℚ_[5][X])).ne_zero

instance : FiniteDimensional ℚ_[5] NonGaloisCubic := powerBasis.finite

instance : CharZero NonGaloisCubic :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[5] NonGaloisCubic).injective

/-- The cube root `∛5` of `5` in `ℚ₅(∛5)`, the class of `X`. -/
def cbrtFive : NonGaloisCubic := AdjoinRoot.root (X ^ 3 - C 5 : ℚ_[5][X])

/-- The cube of `∛5` is `5`. -/
@[simp]
theorem cbrtFive_pow_three : cbrtFive ^ 3 = 5 :=
  (root_X_pow_sub_C_pow 3 (5 : ℚ_[5])).trans (map_ofNat (AdjoinRoot.of _) 5)

/-- `ℚ₅(∛5)` is a cubic extension of `ℚ₅`. -/
theorem finrank_eq_three : Module.finrank ℚ_[5] NonGaloisCubic = 3 := by
  rw [powerBasis.finrank, powerBasis, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

/-- `ℚ₅(∛5)` contains no nontrivial cube root of unity: such a root would generate a quadratic
subfield of a cubic extension. -/
theorem eq_one_of_pow_three_eq_one {ζ : NonGaloisCubic} (hζ : ζ ^ 3 = 1) : ζ = 1 := by
  by_contra hne
  have hq : ζ ^ 2 + ζ + 1 = 0 := by
    have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  have hmin : minpoly ℚ_[5] ζ = X ^ 2 + X + 1 :=
    (minpoly.eq_of_irreducible_of_monic Padic.irreducible_X_sq_add_X_add_one
      (by simpa using hq)
      (by monicity!)).symm
  have hdeg : Module.finrank ℚ_[5] ℚ_[5]⟮ζ⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ), hmin]
    compute_degree!
  have htower := Module.finrank_mul_finrank ℚ_[5] ℚ_[5]⟮ζ⟯ NonGaloisCubic
  rw [hdeg, finrank_eq_three] at htower
  omega

/-- Every `ℚ₅`-automorphism of `ℚ₅(∛5)` fixes `∛5`, since the only cube root of unity in
`ℚ₅(∛5)` is `1`. -/
theorem apply_cbrtFive (σ : NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic) : σ cbrtFive = cbrtFive := by
  have h5 : cbrtFive ≠ 0 := by
    intro h
    have := cbrtFive_pow_three
    rw [h, zero_pow three_ne_zero] at this
    exact (by norm_num : (0 : NonGaloisCubic) ≠ 5) this
  have hζ : (σ cbrtFive / cbrtFive) ^ 3 = 1 := by
    rw [div_pow, ← map_pow, cbrtFive_pow_three, map_ofNat, div_self (by norm_num)]
  exact (div_eq_one_iff_eq h5).mp (eq_one_of_pow_three_eq_one hζ)

/-- The automorphism group of `ℚ₅(∛5)/ℚ₅` is trivial. -/
instance subsingleton_algEquiv : Subsingleton (NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic) :=
  ⟨fun σ τ ↦ AlgEquiv.ext fun x ↦ AlgHom.congr_fun
    (AdjoinRoot.algHom_ext (g₁ := (σ : NonGaloisCubic →ₐ[ℚ_[5]] NonGaloisCubic))
      (g₂ := (τ : NonGaloisCubic →ₐ[ℚ_[5]] NonGaloisCubic))
      ((apply_cbrtFive σ).trans (apply_cbrtFive τ).symm)) x⟩

/-- The automorphism group of `ℚ₅(∛5)/ℚ₅` has order `1`, less than the degree `3`. -/
theorem natCard_algEquiv_lt_finrank :
    Nat.card (NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic) < Module.finrank ℚ_[5] NonGaloisCubic := by
  rw [Nat.card_unique, finrank_eq_three]
  norm_num

/-- `ℚ₅(∛5)/ℚ₅` is not Galois. -/
theorem not_isGalois : ¬ IsGalois ℚ_[5] NonGaloisCubic := fun _ ↦
  natCard_algEquiv_lt_finrank.ne (IsGalois.card_aut_eq_finrank ℚ_[5] NonGaloisCubic)

open scoped TensorProduct in
/-- **The rational decomposition fails on the non-Galois cubic.** `A(ℚ₅(∛5)) ⊗ ℚ₅` is not
`ℤ₅[Aut]`-isomorphic to `(ℤ₅[Aut]^1 × ℤ₅[Aut] ⧸ I) ⊗ ℚ₅`, for `Aut` the (trivial) automorphism
group of `ℚ₅(∛5)/ℚ₅` and `I` its augmentation ideal: the two sides have `ℚ₅`-dimensions
`3 + 1 = 4` and `1 · 1 + 1 = 2`. -/
theorem not_nonempty_padicCompletionUnits_tensorRat_linearEquiv :
    ¬ Nonempty ((Additive ↑(padicCompletionUnits 5 NonGaloisCubic) ⊗[ℤ_[5]] ℚ_[5])
      ≃ₗ[MonoidAlgebra ℤ_[5] (NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic)]
      (((Fin 1 → MonoidAlgebra ℤ_[5] (NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic)) ×
        (MonoidAlgebra ℤ_[5] (NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic) ⧸
          RingHom.ker (MonoidAlgebra.augmentation ℤ_[5]
            (NonGaloisCubic ≃ₐ[ℚ_[5]] NonGaloisCubic)))) ⊗[ℤ_[5]] ℚ_[5])) := by
  have h := TauCeti.not_nonempty_padicCompletionUnits_tensorRat_linearEquiv_of_card_lt 5
    (K := ℚ_[5]) natCard_algEquiv_lt_finrank
  rwa [Module.finrank_self] at h

end NonGaloisCubic

end TauCeti
