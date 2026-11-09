/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.FiniteIndex
import Mathlib.Data.DFinsupp.FiniteInfinite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import TauCeti.Algebra.Regular.NatCast
import TauCeti.GroupTheory.Finiteness
import TauCeti.RingTheory.Localization.FiniteFree
import TauCeti.RingTheory.Localization.FractionRing
import TauCeti.RingTheory.NovikovSeries.LeadingTerm

/-!
# Total rings of fractions of Novikov series

Let `H` be a finitely generated abelian group, possibly with torsion, `N : H →+ ℝ` a period
homomorphism, injective or not, and `R` a domain. Then `Nov(R, H, N)` need not be a domain, and
this file studies its total ring of fractions `Q(Nov(R, H, N))`, the ring in which the torsion of
a based Novikov complex takes its values.

The group `H` has a torsion-free subgroup `K` of finite index, and for each such `K` the ring
`Nov(R, K, N|K)` is a domain (`TauCeti.NovikovSeries.isDomain_of_fg`), over which `Nov(R, H, N)`
is free of rank `[H : K]` (`TauCeti.NovikovSeries.cosetBasis`). Every non-zero-divisor of
`Nov(R, H, N)` divides its norm over `Nov(R, K, N|K)`, so `Q(Nov(R, H, N))` is the localization of
`Nov(R, H, N)` at the nonzero series on `K`, a finite-dimensional algebra over the field of
fractions of `Nov(R, K, N|K)` (`IsFractionRing.isLocalization_algebraMapSubmonoid_iff`, in
`TauCeti.RingTheory.Localization.FiniteFree`). Hence `Q(Nov(R, H, N))` is an Artinian ring
(`TauCeti.NovikovSeries.isArtinianRing_of_isFractionRing`), so it has finitely many maximal ideals,
and once it is known to be reduced, Mathlib's `IsArtinianRing.equivPi` presents it as the product
of its residue fields. When `R` has no additive torsion, for instance `R = ℤ`, these residue
fields have characteristic zero (`TauCeti.NovikovSeries.charZero_quotient_of_isFractionRing`).

## Main results

* `TauCeti.NovikovSeries.exists_finiteIndex_isDomain`: a finitely generated abelian group has a
  subgroup of finite index whose Novikov ring over a domain is a domain.
* `TauCeti.NovikovSeries.isArtinianRing_of_isFractionRing`: the total ring of fractions of the
  Novikov series over a domain on a finitely generated abelian group is Artinian.
* `TauCeti.NovikovSeries.charZero_quotient_of_isFractionRing`: if the coefficients have no
  additive torsion, every quotient of that total ring of fractions by a proper ideal has
  characteristic zero.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

namespace NovikovSeries

variable {H : Type*} [AddCommGroup H]

/-- A finitely generated abelian group `H` has a subgroup `K` of finite index such that, over a
domain, the Novikov ring of `K` for the restricted period homomorphism is a domain. Any
torsion-free subgroup of finite index will do. -/
theorem exists_finiteIndex_isDomain {R : Type*} [CommRing R] [IsDomain R] [AddGroup.FG H]
    (N : H →+ ℝ) :
    ∃ K : AddSubgroup H, K.FiniteIndex ∧ IsDomain (NovikovSeries R K (N.comp K.subtype)) := by
  classical
  -- Write `H ≃ ℤⁿ × T` with `T` finite, and take for `K` the kernel of the projection to `T`.
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod H
  have (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i ↦ ZMod (p i ^ e i)) :=
    (inferInstance : Finite (Π₀ i, ZMod (p i ^ e i)))
  let K := ((AddMonoidHom.snd _ _).comp f.toAddMonoidHom).ker
  refine ⟨K, AddSubgroup.finiteIndex_ker _, ?_⟩
  -- The projection to `ℤⁿ` is injective on `K`, so `K` is torsion-free.
  have hinj : Function.Injective ((AddMonoidHom.fst _ _).comp (f.toAddMonoidHom.comp K.subtype)) :=
    fun x y hxy ↦ Subtype.ext <| f.injective <| Prod.ext hxy <|
      (AddMonoidHom.mem_ker.mp x.2).trans (AddMonoidHom.mem_ker.mp y.2).symm
  have := hinj.hasUniqueDiv _
  exact isDomain_of_fg _

/-- If the coefficients have no additive torsion, for instance for `ℤ`, then every quotient of the
total ring of fractions of the Novikov series by a proper ideal has characteristic zero. -/
theorem charZero_quotient_of_isFractionRing (R : Type*) [CommRing R] [IsAddTorsionFree R]
    (N : H →+ ℝ) (T : Type*) [CommRing T] [Algebra (NovikovSeries R H N) T]
    [IsFractionRing (NovikovSeries R H N) T] {I : Ideal T} (hI : I ≠ ⊤) : CharZero (T ⧸ I) :=
  IsFractionRing.charZero_quotient (NovikovSeries R H N) T
    (fun _ hn ↦ natCast_mem_nonZeroDivisors hn) hI

/-- Over a domain, the total ring of fractions of the Novikov series on a finitely generated
abelian group, with any period homomorphism, is an Artinian ring. -/
theorem isArtinianRing_of_isFractionRing (R : Type*) [CommRing R] [IsDomain R] [AddGroup.FG H]
    (N : H →+ ℝ) (T : Type*) [CommRing T] [Algebra (NovikovSeries R H N) T]
    [IsFractionRing (NovikovSeries R H N) T] : IsArtinianRing T := by
  obtain ⟨K, _, _⟩ := exists_finiteIndex_isDomain (R := R) N
  exact IsFractionRing.isArtinianRing_of_free (NovikovSeries R K (N.comp K.subtype))
    (S := NovikovSeries R H N) T

end NovikovSeries

end TauCeti
