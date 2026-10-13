/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.NSmul
public import TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The order of the Selmer group

Let `R` be a Dedekind domain with fraction field `K`, let `S` be a set of height-one primes of `R`
and let `n ≠ 0`. The fundamental exact sequence
```
1 → 𝒪_S(K)ˣ / (𝒪_S(K)ˣ)ⁿ → K⟮S, n⟯ → Cl_S(R)[n] → 1
```
of `TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic` computes the order of the Selmer
group:

`#K⟮S, n⟯ = (𝒪_S(K)ˣ : (𝒪_S(K)ˣ)ⁿ) · #Cl_S(R)[n]`.

For `S = ∅` the `S`-integers are `R` itself, so `#K⟮∅, n⟯ = (Rˣ : (Rˣ)ⁿ) · #Cl(R)[n]`. When `n = 2`,
`2 ≠ 0` in `R` and `Rˣ` is finitely generated of rank `r`, the torsion of `Rˣ` contributes exactly
the two square roots of unity `±1`, so `(Rˣ : (Rˣ)²) = 2 ^ (r + 1)` and

`#K⟮∅, 2⟯ = 2 ^ (r + 1) · #Cl(R)[2]`.

This is the count through which the `2`-Selmer group of an elliptic curve is bounded by the unit
ranks and class groups of the field factors of its étale algebra.

The identities hold with `Nat.card` and `Subgroup.index` as stated, with no finiteness hypothesis:
when the class group torsion or the index is infinite, both sides are `0`.

## Main results

* `IsDedekindDomain.selmerGroup.card_eq`: `#K⟮S, n⟯ = (𝒪_S(K)ˣ : (𝒪_S(K)ˣ)ⁿ) · #Cl_S(R)[n]`.
* `IsDedekindDomain.selmerGroup.card_empty_eq`: `#K⟮∅, n⟯ = (Rˣ : (Rˣ)ⁿ) · #Cl(R)[n]`.
* `IsDedekindDomain.selmerGroup.card_empty_two_eq`: `#K⟮∅, 2⟯ = 2 ^ (r + 1) · #Cl(R)[2]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Proposition VIII.1.6, where
  `K(S, m)` is shown to be finite through the same exact sequence.

## Provenance

The count of `K⟮∅, 2⟯` follows the bound `IsDedekindDomain.card_selmerGroup_empty_le` and the
count `Units.card_modPow_two` of Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `3bfe124`),
`EllipticCurves/Mathlib/SelmerGroup.lean`. There the class group is assumed trivial and only an
upper bound is proved; here the order is computed exactly from the fundamental exact sequence, for
every class group.
-/

public section

open Module

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace selmerGroup

/-- **The order of the Selmer group.** For `n ≠ 0`,
`#K⟮S, n⟯ = (𝒪_S(K)ˣ : (𝒪_S(K)ˣ)ⁿ) · #Cl_S(R)[n]`: the fundamental exact sequence identifies the
kernel of `toClassGroup` with the `S`-units modulo `n`-th powers and its image with the `n`-torsion
of the `S`-class group. -/
theorem card_eq (S : Set (HeightOneSpectrum R)) (n : ℕ) [NeZero n] :
    Nat.card (selmerGroup (K := K) (S := S) (n := n)) =
      (powMonoidHom n : S.unit K →* S.unit K).range.index *
        Nat.card (powMonoidHom n : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker := by
  rw [← Subgroup.card_ker_mul_card_range (toClassGroup K S n), ker_toClassGroup, range_toClassGroup,
    ← range_fromSUnitLift, Subgroup.index_eq_card]
  congr 1
  exact (Nat.card_congr (MonoidHom.ofInjective (fromSUnitLift_injective K S n)).toEquiv).symm

/-- **The order of the unramified Selmer group.** For `n ≠ 0`,
`#K⟮∅, n⟯ = (Rˣ : (Rˣ)ⁿ) · #Cl(R)[n]`. This is `card_eq` for `S = ∅`, whose `S`-integers are `R`. -/
theorem card_empty_eq (n : ℕ) [NeZero n] :
    Nat.card (selmerGroup (R := R) (K := K) (S := ∅) (n := n)) =
      (powMonoidHom n : Rˣ →* Rˣ).range.index *
        Nat.card (powMonoidHom n : ClassGroup R →* ClassGroup R).ker := by
  set S : Set (HeightOneSpectrum R) := ∅
  -- the class group of the `∅`-integers is that of `R`, divided by the trivial subgroup
  let e : ClassGroup (S.integer K) ≃* ClassGroup R :=
    (integerClassGroupEquiv K S).trans <|
      (QuotientGroup.quotientMulEquivOfEq (by simp [S])).trans QuotientGroup.quotientBot
  have hker : (powMonoidHom n : ClassGroup (S.integer K) →* _).ker.map e.toMonoidHom =
      (powMonoidHom n).ker := by
    ext c
    rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker, powMonoidHom_apply,
      powMonoidHom_apply, ← map_pow, MulEquiv.map_eq_one_iff]
  rw [card_eq K S n, ← Subgroup.index_map_equiv _ (Set.unitEmptyEquivUnits K),
    MulEquiv.map_range_powMonoidHom, ← hker]
  exact congrArg _ (Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv)

/-- **The unramified `2`-Selmer group.** If `2 ≠ 0` in `R` and `Rˣ` is finitely generated of rank
`r`, then `#K⟮∅, 2⟯ = 2 ^ (r + 1) · #Cl(R)[2]`. In particular it has order `2 ^ (r + 1)` when the
class number of `R` is odd. -/
theorem card_empty_two_eq [Group.FG Rˣ] (h2 : (2 : R) ≠ 0) :
    Nat.card (selmerGroup (R := R) (K := K) (S := ∅) (n := 2)) =
      2 ^ (finrank ℤ (Additive Rˣ) + 1) *
        Nat.card (powMonoidHom 2 : ClassGroup R →* ClassGroup R).ker := by
  -- `(Rˣ : (Rˣ)²) = 2 ^ r · #μ₂(R)`, and `μ₂(R) = {±1}` has two elements
  rw [card_empty_eq K 2, Subgroup.index_range_powMonoidHom_of_fg Rˣ two_ne_zero,
    ← rootsOfUnity_eq_ker, TauCeti.card_rootsOfUnity_two h2, pow_succ]

end selmerGroup

end IsDedekindDomain

end
