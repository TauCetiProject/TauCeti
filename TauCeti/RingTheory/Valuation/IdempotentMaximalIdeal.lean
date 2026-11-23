/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Idempotent maximal ideals of valuation rings

The maximal ideal of a valuation ring is idempotent if it is not finitely generated.
Conversely, a nonzero idempotent maximal ideal cannot be finitely generated. This is the
algebraic input for almost mathematics over nondiscrete valuation rings; no rank or
completeness assumption is needed.

Both results are stated for a nontrivial commutative ring whose elements are totally ordered by
divisibility (a `PreValuationRing`); valuation domains are the main example. They need no domain
assumption, so they also cover such rings with zero divisors.

More generally, any radical ideal in which every element has an `n`-th root for some `n ≥ 2` is
idempotent (`Ideal.IsRadical.isIdempotentElem_of_exists_pow_eq`), which covers both rings with
surjective Frobenius (`n = p`) and rings integrally closed in an algebraically closed field
(`n = 2`, `Ideal.IsRadical.isIdempotentElem_of_isAlgClosed`). In particular, the maximal ideal of
a valuation ring whose fraction field is algebraically closed is idempotent, and hence, if nonzero,
not finitely generated.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §2.1, Example 2.1.2(i).
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and its proof.
-/

public section

open IsLocalRing

namespace TauCeti.ValuationRing

variable {V : Type*} [CommRing V] [Nontrivial V] [PreValuationRing V]

/-- The maximal ideal of a nontrivial ring whose elements are totally ordered by divisibility,
such as a valuation ring, is idempotent when it is not finitely generated. -/
theorem isIdempotentElem_maximalIdeal_of_not_fg (hfg : ¬ (maximalIdeal V).FG) :
    IsIdempotentElem (maximalIdeal V) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  -- Some `y ∈ m` is not a multiple of `x`, since otherwise `m = (x)` would be finitely generated.
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ maximalIdeal V, ¬ x ∣ y := by
    by_contra! h
    have heq : Ideal.span {x} = maximalIdeal V := le_antisymm
      ((Ideal.span_singleton_le_iff_mem _).mpr hx) fun y hy ↦ Ideal.mem_span_singleton.mpr (h y hy)
    exact hfg (heq ▸ Submodule.fg_span_singleton x)
  obtain ⟨z, rfl⟩ := (_root_.ValuationRing.dvd_total x y).resolve_left hxy
  -- The cofactor `z` is not a unit, since otherwise `x = y * z` would divide `y`.
  have hz : z ∈ maximalIdeal V := by
    by_contra hz
    exact hxy ((notMem_maximalIdeal.mp hz).mul_right_dvd.mpr dvd_rfl)
  exact Ideal.mul_mem_mul hy hz

/-- A nonzero maximal ideal of a nontrivial ring whose elements are totally ordered by
divisibility, such as a valuation ring, is idempotent exactly when it is not finitely generated.
The nonzero assumption excludes the maximal ideal of a field. -/
theorem isIdempotentElem_maximalIdeal_iff (hne : maximalIdeal V ≠ ⊥) :
    IsIdempotentElem (maximalIdeal V) ↔ ¬ (maximalIdeal V).FG := by
  refine ⟨fun hi hfg ↦ hne ?_, isIdempotentElem_maximalIdeal_of_not_fg⟩
  -- Nakayama's lemma: a finitely generated `m` with `m = m • m` vanishes.
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson _ _ hfg (by rw [smul_eq_mul, hi.eq])
    (ringJacobson_eq_maximalIdeal V).ge

end TauCeti.ValuationRing

namespace Ideal.IsRadical

/-- A radical ideal in which every element has an `n`-th root for some `n ≥ 2` is idempotent.
This covers radical ideals in rings with surjective Frobenius (`n = p`) as well as rings integrally
closed in an algebraically closed field (`n = 2`). -/
theorem isIdempotentElem_of_exists_pow_eq {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : I.IsRadical) {n : ℕ} (hn : 2 ≤ n) (hroot : ∀ x ∈ I, ∃ y : R, y ^ n = x) :
    IsIdempotentElem I := by
  refine le_antisymm Ideal.mul_le_left fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := hroot x hx
  -- Since `y ^ n ∈ I` and `I` is radical, `y ∈ I`, so `y ^ n ∈ I ^ n ≤ I ^ 2 = I * I`.
  exact sq I ▸ Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow (hI ⟨n, hx⟩) n)

/-- In a ring that is integrally closed in an algebraically closed field `K`, every radical ideal
is idempotent: each of its elements is the square of an element of the ideal. This covers the
maximal ideal of a valuation ring whose fraction field is algebraically closed. -/
theorem isIdempotentElem_of_isAlgClosed {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsRadical)
    (K : Type*) [Field K] [Algebra R K] [IsIntegrallyClosedIn R K] [IsAlgClosed K] :
    IsIdempotentElem I := by
  refine hI.isIdempotentElem_of_exists_pow_eq (n := 2) le_rfl fun x _ ↦ ?_
  -- A square root of `x` in `K` is integral over `R`, so it is the image of some `c ∈ R`.
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R K x) two_pos
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow (R := R) two_pos
    (hy ▸ isIntegral_algebraMap)
  exact ⟨c, IsIntegralClosure.algebraMap_injective R R K (by simpa using hy)⟩

end Ideal.IsRadical
