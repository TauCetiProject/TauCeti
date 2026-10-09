/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.RingTheory.KrullDimension.Fiber
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.RingTheory.Ideal.MinimalPrime.Localization
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import TauCeti.RingTheory.Smooth.Regular

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

Moreover `Spec S` is pure-dimensional of dimension `n`: for every minimal prime `P` of `S`, the
quotient `S ⧸ P` has dimension `n`. Choose a maximal ideal `m ⊇ P`. The local ring `S_m` is
regular, hence a domain, so every prime contained in `m` contains `P`; thus a chain of primes
below `m` realizing its height `n` is a chain in `V(P)`.

## Main declarations

* `TauCeti.height_eq_of_isStandardSmoothOfRelativeDimension`: every maximal ideal of a standard
  smooth algebra of relative dimension `n` over a field has height `n`;
* `TauCeti.ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension`: a nonzero standard smooth
  algebra of relative dimension `n` over a field has Krull dimension `n`;
* `TauCeti.ringKrullDim_quotient_of_isStandardSmoothOfRelativeDimension` and
  `TauCeti.isPureDimensional_primeSpectrum_of_isStandardSmoothOfRelativeDimension`: every
  irreducible component of its spectrum has dimension `n`.

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

/-- For every minimal prime `P` of a standard smooth algebra `S` of relative dimension `n` over a
field, the quotient `S ⧸ P` has Krull dimension `n`. -/
theorem ringKrullDim_quotient_of_isStandardSmoothOfRelativeDimension {P : Ideal S}
    (hP : P ∈ minimalPrimes S) : ringKrullDim (S ⧸ P) = n := by
  have hPp : P.IsPrime := hP.1.1
  have : Nontrivial (S ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPp.ne_top
  have : Nontrivial S := (Ideal.Quotient.mk P).domain_nontrivial
  have : Algebra.IsStandardSmooth k S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : IsRegularRing S := IsRegularRing.of_smooth (R := k)
  refine le_antisymm ?_ ?_
  · rw [← ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension k (S := S) n]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  · -- A maximal ideal `m ⊇ P` has height `n`, and every prime below `m` contains `P`, since
    -- the regular local ring `S_m` is a domain.
    obtain ⟨m, hm, hPm⟩ := P.exists_le_maximal hPp.ne_top
    let M : PrimeSpectrum S := ⟨m, hm.isPrime⟩
    have hM : (Order.height M : WithBot ℕ∞) = n := by
      rw [← M.height_eq_orderHeight]
      exact_mod_cast height_eq_of_isStandardSmoothOfRelativeDimension k n m
    rw [ringKrullDim_quotient, ← hM, Order.height_eq_krullDim_Iic]
    exact Order.krullDim_le_of_strictMono
      (fun q ↦ ⟨q.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
        (le_of_mem_minimalPrimes_of_isDomain_localization hP hPm q.2)⟩)
      fun _ _ h ↦ h

/-- The spectrum of a standard smooth algebra of relative dimension `n` over a field is
pure-dimensional of dimension `n`: each of its irreducible components has dimension `n`. -/
theorem isPureDimensional_primeSpectrum_of_isStandardSmoothOfRelativeDimension :
    IsPureDimensional n (PrimeSpectrum S) :=
  isPureDimensional_primeSpectrum_iff.mpr fun _ hP ↦
    ringKrullDim_quotient_of_isStandardSmoothOfRelativeDimension k n hP

end TauCeti
