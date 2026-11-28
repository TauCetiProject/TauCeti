/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.TorsionClass
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.RingTheory.FractionalIdeal.Torsion

/-!
# The number of `I`-torsion points of `(𝔸_f/Ô)ⁿ`

Let `R` be a Dedekind domain with fraction field `K` and `n` a finite type. The `R`-module
`T_n = (𝔸_f/Ô)ⁿ` is isomorphic to `(K/R)ⁿ` (`IsDedekindDomain.FiniteAdeleRing.adelicTorsionEquiv`),
and the elements of a product killed by a set of scalars are the families of elements killed by
it (`Submodule.torsionBySet_pi`). So for every set `s ⊆ R` the `s`-torsion of `T_n` has
`#(K/R)[s] ^ |n|` elements.

For the ring of integers `𝓞_E` of a number field `E` and an ideal `I ≠ 0`, the `I`-torsion of
`E/𝓞_E` is `I⁻¹/𝓞_E`, of size `N(I)` (`NumberField.natCard_torsionBySet_quotient_one`). Hence the
`I`-torsion of `T_n` has `N(I) ^ |n|` elements. The count also holds for `I = 0` with the
convention that `Nat.card` of an infinite type is `0`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.natCard_torsionBySet_pi_adeleQuotient`: the `s`-torsion of
  `(𝔸_f/Ô)ⁿ` has `#(K/R)[s] ^ |n|` elements.
* `IsDedekindDomain.FiniteAdeleRing.natCard_torsionBySet_pi_adeleQuotient_eq_absNorm_pow`: over
  a number field, the `I`-torsion of `(𝔸_f/Ô)ⁿ` has `N(I) ^ |n|` elements.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.card_torsionBySet_adelicTorsion`).
-/

public section

open NumberField Submodule

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

variable (R K) in
/-- **The `s`-torsion of `(𝔸_f/Ô)ⁿ` has `#(K/R)[s] ^ |n|` elements**, for every set `s` of
scalars: transport along `(K/R)ⁿ ≃ (𝔸_f/Ô)ⁿ` (`adelicTorsionEquiv`) and take the torsion
coordinatewise (`Submodule.torsionBySet_pi`). -/
theorem natCard_torsionBySet_pi_adeleQuotient (n : Type*) [Fintype n] (s : Set R) :
    Nat.card (torsionBySet R (n → AdeleQuotient R K) s) =
      Nat.card (torsionBySet R (K ⧸ (1 : Submodule R K)) s) ^ Fintype.card n := by
  have he : Nat.card (torsionBySet R (n → K ⧸ (1 : Submodule R K)) s) =
      Nat.card (torsionBySet R (n → AdeleQuotient R K) s) :=
    Nat.card_congr <| (adelicTorsionEquiv R K n).toEquiv.subtypeEquiv fun x ↦ by
      simp only [mem_torsionBySet_iff, LinearEquiv.coe_toEquiv, ← map_smul,
        LinearEquiv.map_eq_zero_iff]
  rw [← he, torsionBySet_pi, ← Nat.card_eq_fintype_card, ← Nat.card_fun]
  exact Nat.card_congr (Equiv.Set.univPi fun _ ↦ _)

/-- **The `I`-torsion of `(𝔸_f/Ô)ⁿ` has `N(I) ^ |n|` elements**, for an ideal `I` of the ring of
integers of a number field `E`: the `I`-torsion of `E/𝓞_E` has `N(I)` elements
(`NumberField.natCard_torsionBySet_quotient_one`). For `I = 0` and `n` nonempty both sides are
`0`, as `Nat.card` of an infinite type is `0`. -/
theorem natCard_torsionBySet_pi_adeleQuotient_eq_absNorm_pow {E : Type*} [Field E]
    [NumberField E] (n : Type*) [Fintype n] (I : Ideal (𝓞 E)) :
    Nat.card (torsionBySet (𝓞 E) (n → AdeleQuotient (𝓞 E) E) I) =
      Ideal.absNorm I ^ Fintype.card n := by
  rw [natCard_torsionBySet_pi_adeleQuotient, NumberField.natCard_torsionBySet_quotient_one]

end IsDedekindDomain.FiniteAdeleRing
