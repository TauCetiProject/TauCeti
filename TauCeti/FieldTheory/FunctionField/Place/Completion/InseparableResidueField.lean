/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.CoefficientField
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import Mathlib.RingTheory.LaurentSeries
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.RingTheory.Valuation.Discrete.Frobenius

/-!
# No coefficient field over the constants at an inseparable residue field

At a place `P` of `F / k` whose residue field `F_P` is separable over `k`, the completed valuation
ring `𝒪̂_P` contains a unique copy of `F_P` over `k` lifting the residue field
(`TauCeti.Place.completionResidueFieldSection`), and a uniformizer identifies `𝒪̂_P` with
`F_P[[T]]` and the completion `F̂_P` with `F_P((T))` over `k`
(`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField`,
`TauCeti.Place.completionEquivLaurentSeriesResidueField`). This file shows that the separability
hypothesis of these constructions cannot be dropped.

Let `k` have characteristic `p`, let `c ∈ k`, and let `z ∈ F` be such that `z ^ p - c` has
positive order at `P`, not divisible by `p`. Then the value `z(P)` is a `p`-th root of `c` in
`F_P`, but `c` has no `p`-th root in `F̂_P`: if `b ^ p = c`, then `z ^ p - c = (z - b) ^ p` would
have order divisible by `p`. So there is no `k`-algebra map `F_P → F̂_P` at all, and in particular
no coefficient field over `k` and no `k`-linear identification of `𝒪̂_P` with `F_P[[T]]` or of
`F̂_P` with `F_P((T))`; the residue field `F_P` is inseparable over `k`.

The hypotheses hold over every imperfect field. If `a ∈ k` is not a `p`-th power, the polynomial
`X ^ p - a` is irreducible, and at its place on `k(x)` the function `x ^ p - a` is a prime element.
For example, `a` may be the variable of `k = 𝔽_p(a)` (`TauCeti.ratFunc_pow_ne_X`). Expansions and
residues at places with inseparable residue field therefore cannot be set up over `k` in the way
they are at places with separable residue field.

## Main results

* `TauCeti.Place.pow_ne_algebraMap_completion`: `c` has no `p`-th root in `F̂_P`.
* `TauCeti.Place.isEmpty_algHom_residueField_completion`: there is no `k`-algebra map
  `F_P → F̂_P`.
* `TauCeti.Place.not_isSeparable_residueField`: `F_P` is not separable over `k`.
* `TauCeti.Place.isEmpty_completionIntegers_algEquiv_powerSeries` and
  `TauCeti.Place.isEmpty_completion_algEquiv_laurentSeries`: `𝒪̂_P` is not `k`-isomorphic to
  `F_P[[T]]`, and `F̂_P` is not `k`-isomorphic to `F_P((T))`.
* `TauCeti.Place.isEmpty_completionIntegers_algEquiv_powerSeries_adicOfIrreducible_X_pow_sub_C`:
  the example of the place of an irreducible `X ^ p - a` on `k(x)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2, where the constant field is perfect throughout.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §4.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F) {p : ℕ} [ExpChar k p]

/-- **No `p`-th root of `c` in the completion.** If `z ^ p - c` has order at `P` not divisible
by `p`, then the constant `c` is not a `p`-th power in `F̂_P`: otherwise `z ^ p - c = (z - b) ^ p`
there. -/
theorem pow_ne_algebraMap_completion {z : F} {c : k}
    (hz : ¬(p : ℤ) ∣ P.ord (z ^ p - algebraMap k F c)) (b : P.Completion) :
    b ^ p ≠ algebraMap k P.Completion c := by
  have := expChar_of_injective_algebraMap (algebraMap k P.Completion).injective p
  intro hb
  apply hz
  rw [← P.ord_completionEmbedding, map_sub, map_pow, AlgHom.commutes, ← hb, ord_def,
    ← Valuation.ord_def]
  exact Valuation.natCast_dvd_ord_pow_sub_pow _ p _ _

omit [ExpChar k p] in
/-- If `z ^ n - c` vanishes at `P`, then `z` is regular at `P` and its value there is an `n`-th
root of `c` in the residue field. -/
private theorem exists_pow_eq_algebraMap_residueField {n : ℕ} (hn : n ≠ 0) {z : F} {c : k}
    (hpos : 0 < P.ord (z ^ n - algebraMap k F c)) :
    ∃ r : P.ResidueField, r ^ n = algebraMap k P.ResidueField c := by
  have hne : z ^ n - algebraMap k F c ≠ 0 := fun h ↦ by simp [h] at hpos
  have hlt := (P.valuation_lt_one_iff_ord_pos hne).mpr hpos
  -- `z ^ n` is the sum of `z ^ n - c` and the constant `c`, both regular at `P`.
  have hz : z ∈ P.integers := by
    have h : P.valuation (z ^ n) ≤ 1 := by
      rw [← sub_add_cancel (z ^ n) (algebraMap k F c)]
      exact (Valuation.map_add _ _ _).trans
        (max_le hlt.le (P.mem_integers_iff.mp (P.algebraMap_mem_integers c)))
    rw [map_pow] at h
    exact P.mem_integers_iff.mpr ((pow_le_one_iff hn).mp h)
  refine ⟨residue P.integers ⟨z, hz⟩, ?_⟩
  rw [algebraMap_residueField, ← map_pow, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff_valuation_lt_one]
  simpa using hlt

/-- **No `k`-algebra map from the residue field to the completion.** If `z ^ p - c` has positive
order at `P`, not divisible by `p`, then `z(P)` is a `p`-th root of `c` in `F_P`, which `F̂_P`
does not have. -/
theorem isEmpty_algHom_residueField_completion {z : F} {c : k}
    (hpos : 0 < P.ord (z ^ p - algebraMap k F c))
    (hz : ¬(p : ℤ) ∣ P.ord (z ^ p - algebraMap k F c)) :
    IsEmpty (P.ResidueField →ₐ[k] P.Completion) := by
  refine ⟨fun φ ↦ ?_⟩
  obtain ⟨r, hr⟩ := P.exists_pow_eq_algebraMap_residueField (expChar_ne_zero k p) hpos
  exact P.pow_ne_algebraMap_completion hz (φ r) (by rw [← map_pow, hr, AlgHom.commutes])

/-- **The residue field is inseparable** over `k` when some `z ^ p - c` has positive order at `P`,
not divisible by `p`: otherwise `TauCeti.Place.completionResidueFieldSection` would be a
`k`-algebra map from `F_P` to the completion. -/
theorem not_isSeparable_residueField {z : F} {c : k}
    (hpos : 0 < P.ord (z ^ p - algebraMap k F c))
    (hz : ¬(p : ℤ) ∣ P.ord (z ^ p - algebraMap k F c)) :
    ¬Algebra.IsSeparable k P.ResidueField := fun _ ↦
  (P.isEmpty_algHom_residueField_completion hpos hz).false
    ((IsScalarTower.toAlgHom k P.completionPlace.integers P.Completion).comp
      P.completionResidueFieldSection)

/-- **The completed valuation ring is not `F_P[[T]]` over `k`** when some `z ^ p - c` has
positive order at `P`, not divisible by `p`: the separability hypothesis of
`TauCeti.Place.completionIntegersEquivPowerSeriesResidueField` cannot be dropped. -/
theorem isEmpty_completionIntegers_algEquiv_powerSeries {z : F} {c : k}
    (hpos : 0 < P.ord (z ^ p - algebraMap k F c))
    (hz : ¬(p : ℤ) ∣ P.ord (z ^ p - algebraMap k F c)) :
    IsEmpty (P.completionPlace.integers ≃ₐ[k] PowerSeries P.ResidueField) :=
  ⟨fun e ↦ (P.isEmpty_algHom_residueField_completion hpos hz).false
    ((IsScalarTower.toAlgHom k P.completionPlace.integers P.Completion).comp
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom k P.ResidueField _)))⟩

/-- **The completion is not `F_P((T))` over `k`** when some `z ^ p - c` has positive order at
`P`, not divisible by `p`: the separability hypothesis of
`TauCeti.Place.completionEquivLaurentSeriesResidueField` cannot be dropped. -/
theorem isEmpty_completion_algEquiv_laurentSeries {z : F} {c : k}
    (hpos : 0 < P.ord (z ^ p - algebraMap k F c))
    (hz : ¬(p : ℤ) ∣ P.ord (z ^ p - algebraMap k F c)) :
    IsEmpty (P.Completion ≃ₐ[k] LaurentSeries P.ResidueField) :=
  ⟨fun e ↦ (P.isEmpty_algHom_residueField_completion hpos hz).false
    (e.symm.toAlgHom.comp
      { toRingHom := algebraMap P.ResidueField (LaurentSeries P.ResidueField)
        commutes' := fun c ↦ by
          rw [HahnSeries.algebraMap_apply',
            IsScalarTower.algebraMap_apply k P.ResidueField (PowerSeries P.ResidueField)]
          exact (HahnSeries.algebraMap_apply' ℤ _).symm })⟩

/-! ### The place of `X ^ p - a` over an imperfect field -/

section RatFunc

variable {a : k} (hq : Irreducible (X ^ p - C a : k[X]))

omit [ExpChar k p] in
include hq in
/-- At the place of `X ^ p - a`, the function `x ^ p - a` is a prime element. -/
private theorem ord_adicOfIrreducible_X_pow_sub_algebraMap :
    (adicOfIrreducible hq).ord (RatFunc.X ^ p - algebraMap k (RatFunc k) a) = 1 := by
  have h : (RatFunc.X ^ p - algebraMap k (RatFunc k) a : RatFunc k) =
      algebraMap k[X] (RatFunc k) (X ^ p - C a) := by
    rw [map_sub, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [h, ord_adicOfIrreducible_algebraMap_irreducible hq hq]
  simp

/-- **The completion of `k(x)` at the place of an irreducible `X ^ p - a` is not `F_P[[T]]` over
`k`**: the residue field `k[X] / (X ^ p - a)` has no copy over `k` in the completed valuation
ring. For `p` prime, `X ^ p - a` is irreducible as soon as `a` is not a `p`-th power
(`X_pow_sub_C_irreducible_of_prime`), so this happens over every imperfect field, for example
over `𝔽_p(a)` (`TauCeti.ratFunc_pow_ne_X`). The hypothesis `p ≠ 1` excludes characteristic
zero, where the place of `X - a` is rational. -/
theorem isEmpty_completionIntegers_algEquiv_powerSeries_adicOfIrreducible_X_pow_sub_C
    (hp : p ≠ 1) :
    IsEmpty ((adicOfIrreducible hq).completionPlace.integers ≃ₐ[k]
      PowerSeries (adicOfIrreducible hq).ResidueField) := by
  have hord := ord_adicOfIrreducible_X_pow_sub_algebraMap hq
  refine isEmpty_completionIntegers_algEquiv_powerSeries _ (hord ▸ one_pos) ?_
  rw [hord]
  exact fun h ↦ hp (by exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h)

end RatFunc

end TauCeti.Place
