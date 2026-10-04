/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.RingTheory.KrullDimension.Fiber
public import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Krull dimension of standard smooth algebras over a field

Let `S` be a standard smooth algebra of relative dimension `n` over a field `k`. Then every
maximal ideal of `S` has height `n`, and so `S` has Krull dimension `n` when it is nonzero. This
is the dimension count behind the relative dimension of a smooth scheme over a field: the local
ring at a closed point has dimension equal to the relative dimension.

By Mathlib's `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`, `S` is étale
over the polynomial ring `P = k[X₁, …, Xₙ]`. Étale algebras are flat and quasi-finite, so heights
of primes are preserved along `P → S` (`Ideal.height_eq_height_under_of_quasiFinite`). A maximal
ideal `q` of `S` contracts to a maximal ideal of `P` (`Ideal.isMaximal_under_of_finiteType`),
and every maximal ideal of `P` has height `n` (`MvPolynomial.height_eq_natCard_of_isMaximal`).

## Main declarations

* `TauCeti.height_eq_of_isStandardSmoothOfRelativeDimension`: every maximal ideal of a standard
  smooth algebra of relative dimension `n` over a field has height `n`;
* `TauCeti.ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension`: a nonzero standard smooth
  algebra of relative dimension `n` over a field has Krull dimension `n`.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 15.1, for the dimension formula along flat
  local homomorphisms that underlies the preservation of heights.
-/

public section

namespace TauCeti

variable (k : Type*) {S : Type*} [Field k] [CommRing S] [Algebra k S] (n : ℕ)
  [Algebra.IsStandardSmoothOfRelativeDimension n k S]

include k

/-- Every maximal ideal of a standard smooth algebra of relative dimension `n` over a field has
height `n`. -/
theorem height_eq_of_isStandardSmoothOfRelativeDimension (q : Ideal S) [q.IsMaximal] :
    q.height = n := by
  -- `S` is étale over `P = k[X₁, …, Xₙ]`.
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n k S
  let P := MvPolynomial (Fin n) k
  let := g.toRingHom.toAlgebra
  have : Algebra.Etale P S := hg
  have : IsScalarTower k P S := .of_algebraMap_eq fun r ↦ (g.commutes r).symm
  have : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  -- Heights are preserved along `P → S`, and `q` contracts to a maximal ideal of `P`.
  have := q.isMaximal_under_of_finiteType k (A := P)
  rw [Ideal.height_eq_height_under_of_quasiFinite (R := P) q,
    MvPolynomial.height_eq_natCard_of_isMaximal (q.under P), Nat.card_fin]

/-- A nonzero standard smooth algebra of relative dimension `n` over a field has Krull dimension
`n`. -/
theorem ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension [Nontrivial S] :
    ringKrullDim S = n := by
  refine le_antisymm ((ringKrullDim_le_iff_height_le _).mpr fun p hp ↦ ?_) ?_
  · obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
    have := height_eq_of_isStandardSmoothOfRelativeDimension k n m
    exact_mod_cast this ▸ Ideal.height_mono hpm
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal S
    have := height_eq_of_isStandardSmoothOfRelativeDimension k n m
    exact_mod_cast this ▸ Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top

end TauCeti
